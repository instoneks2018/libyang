/**
 * @file parser_json.c
 * @author Radek Krejci <rkrejci@cesnet.cz>
 * @brief JSON data parser for libyang
 *
 * Copyright (c) 2019 CESNET, z.s.p.o.
 *
 * This source code is licensed under BSD 3-Clause License (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://opensource.org/licenses/BSD-3-Clause
 */

#define _GNU_SOURCE

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "compat.h"
#include "config.h"
#include "context.h"
#include "json.h"
#include "parser_internal.h"
#include "tree_data.h"
#include "tree_data_internal.h"
#include "tree_schema.h"
#include "validation.h"

/**
 * @brief Internal context for JSON YANG data parser.
 *
 * Note that the structure maps to the lyd_ctx which is common for all the data parsers
 */
struct lyd_json_ctx {
    uint32_t parse_options;        /**< various @ref dataparseroptions. */
    uint32_t validate_options;     /**< various @ref datavalidationoptions. */
    uint32_t int_opts;             /**< internal data parser options */
    uint32_t path_len;             /**< used bytes in the path buffer */
    char path[LYD_PARSER_BUFSIZE]; /**< buffer for the generated path */
    struct ly_set unres_node_type; /**< set of nodes validated with LY_EINCOMPLETE result */
    struct ly_set unres_meta_type; /**< set of metadata validated with LY_EINCOMPLETE result */
    struct ly_set when_check;      /**< set of nodes with "when" conditions */
    struct lyd_node *op_node;      /**< if an RPC/action/notification is being parsed, store the pointer to it */

    /* callbacks */
    lyd_ctx_free_clb free;           /* destructor */
    ly_resolve_prefix_clb resolve_prefix;

    struct lyjson_ctx *jsonctx;    /**< JSON context */
};

/**
 * @brief Free the JSON data parser context.
 *
 * JSON implementation of lyd_ctx_free_clb().
 */
static void
lyd_json_ctx_free(struct lyd_ctx *lydctx)
{
    struct lyd_json_ctx *ctx = (struct lyd_json_ctx *)lydctx;

    if (lydctx) {
        lyd_ctx_free(lydctx);
        lyjson_ctx_free(ctx->jsonctx);
        free(ctx);
    }
}

const struct lys_module *
lydjson_resolve_prefix(const struct ly_ctx *ctx, const char *prefix, size_t prefix_len, void *UNUSED(parser))
{
    const struct lys_module *mod;
    char *name;

    name = strndup(prefix, prefix_len);
    if (!name) {
        return NULL;
    }

    mod = ly_ctx_get_module_implemented(ctx, name);
    free(name);
    return mod;
}

/**
 * @brief Parse JSON member-name as [\@][prefix:][name]
 *
 * \@ - metadata flag, maps to 1 in @p is_attr_p
 * prefix - name of the module of the data node
 * name - name of the data node
 *
 * All the output parameter are mandatory. Function only parse the member-name, all the appropriate checks are up to the caller.
 *
 * @param[in] value String to parse
 * @param[in] value_len Length of the @p str.
 * @param[out] name_p Pointer to the beginning of the parsed name.
 * @param[out] name_len_p Pointer to the length of the parsed name.
 * @param[out] prefix_p Pointer to the beginning of the parsed prefix. If the member-name does not contain prefix, result is NULL.
 * @param[out] prefix_len_p Pointer to the length of the parsed prefix. If the member-name does not contain prefix, result is 0.
 * @param[out] is_attr_p Pointer to the metadata flag, set to 1 if the member-name contains \@, 0 otherwise.
 */
static void
lydjson_parse_name(const char *value, size_t value_len, const char **name_p, size_t *name_len_p, const char **prefix_p, size_t *prefix_len_p, int *is_attr_p)
{
    const char *name, *prefix = NULL;
    size_t name_len, prefix_len = 0;
    int is_attr = 0;

    name = memchr(value, ':', value_len);
    if (name != NULL) {
        prefix = value;
        if (*prefix == '@') {
            is_attr = 1;
            prefix++;
        }
        prefix_len = name - prefix;
        name++;
        name_len = value_len - (prefix_len + 1) - is_attr;
    } else {
        name = value;
        if (name[0] == '@') {
            is_attr = 1;
            name++;
        }
        name_len = value_len - is_attr;
    }

    *name_p = name;
    *name_len_p = name_len;
    *prefix_p = prefix;
    *prefix_len_p = prefix_len;
    *is_attr_p = is_attr;
}

/**
 * return LY_SUCCES on success, note that even in this case the returned snode can be NULL, so the data are expected to be parsed as opaq.
 * return LY_EVALID on failure, error message is logged
 * return LY_ENOT in case the input data are expected to be skipped
 */
static LY_ERR
lydjson_get_snode(const struct lyd_json_ctx *lydctx, int is_attr, const char *prefix, size_t prefix_len, const char *name, size_t name_len,
                  const struct lyd_node_inner *parent, const struct lysc_node **snode_p)
{
    struct lys_module *mod = NULL;

    /* leave if-feature check for validation */
    int getnext_opts = LYS_GETNEXT_NOSTATECHECK | (lydctx->int_opts & LYD_INTOPT_REPLY ? LYS_GETNEXT_OUTPUT : 0);

    /* init return value */
    *snode_p = NULL;

    /* get the element module */
    if (prefix) {
        mod = ly_ctx_get_module_implemented2(lydctx->jsonctx->ctx, prefix, prefix_len);
    } else if (parent) {
        if (parent->schema) {
            mod = parent->schema->module;
        }
    } else {
        LOGVAL(lydctx->jsonctx->ctx, LY_VLOG_LYD, parent, LYVE_SYNTAX_JSON, "Top-level JSON object member \"%.*s\" must be namespace-qualified.",
               is_attr ? name_len + 1 : name_len, is_attr ? name - 1 : name);
        return LY_EVALID;
    }
    if (!mod) {
        if (lydctx->parse_options & LYD_PARSE_STRICT) {
            LOGVAL(lydctx->jsonctx->ctx, LY_VLOG_LYD, parent, LYVE_REFERENCE, "No module named \"%.*s\" in the context.", prefix_len, prefix);
            return LY_EVALID;
        }
        if (!(lydctx->parse_options & LYD_PARSE_OPAQ)) {
            return LY_ENOT;
        }
    }

    /* get the schema node */
    if (mod && (!parent || parent->schema)) {
        *snode_p = lys_find_child(parent ? parent->schema : NULL, mod, name, name_len, 0, getnext_opts);
        if (!*snode_p) {
            if (lydctx->parse_options & LYD_PARSE_STRICT) {
                LOGVAL(lydctx->jsonctx->ctx, LY_VLOG_LYD, parent, LYVE_REFERENCE, "Node \"%.*s\" not found in the \"%s\" module.",
                    name_len, name, mod->name);
                return LY_EVALID;
            } else if (!(lydctx->parse_options & LYD_PARSE_OPAQ)) {
                /* skip element with children */
                return LY_ENOT;
            }
        } else {
            /* check that schema node is valid and can be used */
            LY_CHECK_RET(lyd_parser_check_schema((struct lyd_ctx *)lydctx, *snode_p));
        }
    }

    return LY_SUCCESS;
}

/**
 * @brief Skip the currently open JSON object/array
 * @param[in] jsonctx JSON context with the input data to skip.
 * @return LY_ERR value.
 */
static LY_ERR
lydjson_data_skip(struct lyjson_ctx *jsonctx)
{
    enum LYJSON_PARSER_STATUS status, current;
    size_t sublevels = 1;

    status = lyjson_ctx_status(jsonctx, 0);

    /* skip after the content */
    do {
        LY_CHECK_RET(lyjson_ctx_next(jsonctx, &current));
        if (current == status) {
            sublevels++;
        } else if (current == status + 1) {
            sublevels--;
        }
    } while (current != status + 1 && sublevels);
    /* open the next sibling */
    LY_CHECK_RET(lyjson_ctx_next(jsonctx, NULL));

    return LY_SUCCESS;
}

/**
 * @brief Go through the @p value and find all possible prefixes and store them in @p val_prefs_p [sized array](@ref sizedarrays).
 *
 * @param[in] ctx libyang context
 * @param[in] value Pointer to the beginning of the value to check.
 * @param[in] value_len Length of the string to examine in @p value.
 * @param[out] val_prefs_p Pointer to the resulting [sized array](@ref sizedarrays) of found prefixes. NULL in case there are no prefixes.
 * @return LY_EMEM on memory allocation failure.
 * @return LY_SUCCESS on success, empty @p val_prefs_p (NULL) is valid result if there are no possible prefixes
 */
static LY_ERR
lydjson_get_value_prefixes(const struct ly_ctx *ctx, const char *value, size_t value_len, struct ly_prefix **val_prefs_p)
{
    LY_ERR ret;
    LY_ARRAY_COUNT_TYPE u;
    uint32_t c;
    const char *start, *stop;
    struct ly_prefix *prefixes = NULL;
    size_t len;

    for (stop = start = value; (size_t)(stop - value) < value_len; start = stop) {
        size_t bytes;
        ly_getutf8(&stop, &c, &bytes);
        if (is_yangidentstartchar(c)) {
            for (ly_getutf8(&stop, &c, &bytes);
                    is_yangidentchar(c) && (size_t)(stop - value) < value_len;
                    ly_getutf8(&stop, &c, &bytes));
            stop = stop - bytes;
            if (*stop == ':') {
                /* we have a possible prefix */
                struct ly_prefix *p = NULL;

                len = stop - start;

                /* check whether we do not already have this prefix stored */
                LY_ARRAY_FOR(prefixes, u) {
                    if (!ly_strncmp(prefixes[u].id, start, len)) {
                        p = &prefixes[u];
                        break;
                    }
                }
                if (!p) {
                    LY_ARRAY_NEW_GOTO(ctx, prefixes, p, ret, error);
                    p->id = lydict_insert(ctx, start, len);
                    p->module_name = lydict_insert(ctx, start, len);
                } /* else the prefix already present */
            }
            stop = stop + bytes;
        }
    }

    *val_prefs_p = prefixes;
    return LY_SUCCESS;

error:
    LY_ARRAY_FOR(prefixes, u) {
        lydict_remove(ctx, prefixes[u].id);
        lydict_remove(ctx, prefixes[u].module_name);
    }
    LY_ARRAY_FREE(prefixes);
    return ret;
}

/**
 * @brief Check that the input data are parseable as the @p list.
 *
 * Checks for all the list's keys. Function does not revert the context state.
 *
 * @param[in] jsonctx JSON parser context.
 * @param[in] list List schema node corresponding to the input data object.
 * @return LY_SUCCESS in case the data are ok for the @p list
 * @return LY_ENOT in case the input data are not sufficient to fully parse the list instance.
 */
static LY_ERR
lydjson_check_list(struct lyjson_ctx *jsonctx, const struct lysc_node *list)
{
    LY_ERR ret = LY_SUCCESS;
    enum LYJSON_PARSER_STATUS status = lyjson_ctx_status(jsonctx, 0);
    struct ly_set key_set = {0};
    const struct lysc_node *snode;
    uint32_t i, status_count;

    assert(list && (list->nodetype == LYS_LIST));
    assert(status == LYJSON_OBJECT);

    /* get all keys into a set (keys do not have if-features or anything) */
    snode = NULL;
    while ((snode = lys_getnext(snode, list, NULL, LYS_GETNEXT_NOSTATECHECK)) && (snode->flags & LYS_KEY)) {
        ly_set_add(&key_set, (void *)snode, LY_SET_OPT_USEASLIST);
    }

    if (status != LYJSON_OBJECT_EMPTY) {
        status_count = jsonctx->status.count;

        while (key_set.count && status != LYJSON_OBJECT_CLOSED) {
            const char *name, *prefix;
            size_t name_len, prefix_len;
            int is_attr;

            /* match the key */
            snode = NULL;
            lydjson_parse_name(jsonctx->value, jsonctx->value_len, &name, &name_len, &prefix, &prefix_len, &is_attr);

            if (!is_attr && !prefix) {
                for (i = 0; i < key_set.count; ++i) {
                    snode = (const struct lysc_node *)key_set.objs[i];
                    if (!ly_strncmp(snode->name, name, name_len)) {
                        break;
                    }
                }
                /* go into the item to a) process it as a key or b) start skipping it as another list child */
                ret = lyjson_ctx_next(jsonctx, &status);
                LY_CHECK_GOTO(ret, cleanup);

                if (snode) {
                    /* we have the key, validate the value */
                    if (status < LYJSON_NUMBER) {
                        /* not a terminal */
                        ret = LY_ENOT;
                        goto cleanup;
                    }

                    ret = _lys_value_validate(NULL, snode, jsonctx->value, jsonctx->value_len, lydjson_resolve_prefix, jsonctx, LYD_JSON);
                    LY_CHECK_GOTO(ret, cleanup);

                    /* key with a valid value, remove from the set */
                    ly_set_rm_index(&key_set, i, NULL);
                }
            } else {
                /* start skipping the member we are not interested in */
                ret = lyjson_ctx_next(jsonctx, &status);
                LY_CHECK_GOTO(ret, cleanup);
            }
            /* move to the next child */
            while (status_count < jsonctx->status.count) {
                ret = lyjson_ctx_next(jsonctx, &status);
                LY_CHECK_GOTO(ret, cleanup);
            }
        }
    }

    if (key_set.count) {
        /* some keys are missing/did not validate */
        ret = LY_ENOT;
    }

cleanup:
    ly_set_erase(&key_set, NULL);
    return ret;
}

static LY_ERR
lydjson_value_type_hint(struct lyd_json_ctx *lydctx, enum LYJSON_PARSER_STATUS *status, int *type_hint)
{
    *type_hint = 0;

    if (*status == LYJSON_ARRAY) {
        /* only [null] */
        LY_CHECK_RET(lyjson_ctx_next(lydctx->jsonctx, status));
        LY_CHECK_RET(*status != LYJSON_NULL, LY_EINVAL);

        LY_CHECK_RET(lyjson_ctx_next(lydctx->jsonctx, NULL));
        LY_CHECK_RET(lyjson_ctx_status(lydctx->jsonctx, 0) != LYJSON_ARRAY_CLOSED, LY_EINVAL);

        *type_hint = LYD_NODE_OPAQ_ISEMPTY;
    } else if (*status == LYJSON_STRING) {
        *type_hint = LYD_NODE_OPAQ_ISSTRING;
    } else if (*status == LYJSON_NUMBER) {
        *type_hint = LYD_NODE_OPAQ_ISNUMBER;
    } else if (*status == LYJSON_FALSE || *status == LYJSON_TRUE) {
        *type_hint = LYD_NODE_OPAQ_ISBOOLEAN;
    } else if (*status == LYJSON_NULL) {
        *type_hint = 0;
    } else {
        return LY_EINVAL;
    }

    return LY_SUCCESS;
}

/**
 * @brief Check in advance if the input data are parseable according to the provided @p snode.
 *
 * Note that the checks are done only in case the LYD_PARSE_OPAQ is allowed. Otherwise the same checking
 * is naturally done when the data are really parsed.
 *
 * @param[in] lydctx JSON data parser context. When the function returns, the context is in the same state
 * as before calling, despite it is necessary to process input data for checking.
 * @param[in] snode Schema node corresponding to the member currently being processed in the context.
 * @return LY_SUCCESS in case the data are ok for the @p snode or the LYD_PARSE_OPAQ is not enabled.
 * @return LY_ENOT in case the input data are not sufficient to fully parse the list instance
 * @return LY_EINVAL in case of invalid leaf JSON encoding
 * and they are expected to be parsed as opaq nodes.
 */
static LY_ERR
lydjson_data_check_opaq(struct lyd_json_ctx *lydctx, const struct lysc_node *snode, int *type_hint)
{
    LY_ERR ret = LY_SUCCESS;
    struct lyjson_ctx *jsonctx = lydctx->jsonctx;
    enum LYJSON_PARSER_STATUS status;

    assert(snode);
    assert(snode->nodetype & (LYD_NODE_TERM | LYS_LIST));

    if ((lydctx->parse_options & LYD_PARSE_OPAQ)) {
        /* backup parser */
        lyjson_ctx_backup(jsonctx);
        status = lyjson_ctx_status(jsonctx, 0);

        /* check if the node is parseable. if not, NULL the snode to announce that it is supposed to be parsed as an opaq node */
        switch (snode->nodetype) {
        case LYS_LEAFLIST:
        case LYS_LEAF:
            /* value may not be valid in which case we parse it as an opaque node */
            ret = lydjson_value_type_hint(lydctx, &status, type_hint);
            if (ret) {
                break;
            }

            if (_lys_value_validate(NULL, snode, jsonctx->value, jsonctx->value_len, lydjson_resolve_prefix, jsonctx, LYD_JSON)) {
                ret = LY_ENOT;
            }
            break;
        case LYS_LIST:
            /* lists may not have all its keys */
            if (lydjson_check_list(jsonctx, snode)) {
                /* invalid list, parse as opaque if it missing/has invalid some keys */
                ret = LY_ENOT;
            }
        }

        /* restore parser */
        lyjson_ctx_restore(jsonctx);
    } else if (snode->nodetype & (LYS_LEAF | LYS_LEAFLIST)) {
        status = lyjson_ctx_status(jsonctx, 0);
        ret = lydjson_value_type_hint(lydctx, &status, type_hint);
    }

    return ret;
}

/**
 * @brief Join the forward-referencing metadata with their target data nodes.
 *
 * Note that JSON encoding for YANG data allows forward-referencing metadata only for leafs/leaf-lists.
 *
 * @param[in] lydctx JSON data parser context.
 * @param[in] first The first sibling node (top-level or in a particular parent node)
 * as a starting point to search for the metadata's target data node
 * @return LY_SUCCESS on success
 * @return LY_EVALID in case there are some metadata with unresolved target data node instance
 */
static LY_ERR
lydjson_metadata_finish(struct lyd_json_ctx *lydctx, struct lyd_node **first_p)
{
    LY_ERR ret = LY_SUCCESS;
    struct lyd_node *node, *attr, *next, *start = *first_p, *meta_iter;
    unsigned int instance = 0;
    const char *prev = NULL;

    /* finish linking metadata */
    LY_LIST_FOR_SAFE(*first_p, next, attr) {
        struct lyd_node_opaq *meta_container = (struct lyd_node_opaq*)attr;
        unsigned int match = 0;
        int is_attr;
        const char *name, *prefix;
        size_t name_len, prefix_len;
        const struct lysc_node *snode;

        if (attr->schema || meta_container->name[0] != '@') {
            /* not an opaq metadata node */
            continue;
        }

        if (prev != meta_container->name) {
            /* metas' names are stored in dictionary, so checking pointers must works */
            lydict_remove(lydctx->jsonctx->ctx, prev);
            prev = lydict_insert(lydctx->jsonctx->ctx, meta_container->name, 0);
            instance = 1;
        } else {
            instance++;
        }

        /* find the correspnding data node */
        LY_LIST_FOR(start, node) {
            if (!node->schema) {
                /* opaq node - we are going to put into it just a generic attribute. */
                if (strcmp(&meta_container->name[1], ((struct lyd_node_opaq*)node)->name)) {
                    continue;
                }

                if (((struct lyd_node_opaq*)node)->hint & LYD_NODE_OPAQ_ISLIST) {
                    LOGVAL(lydctx->jsonctx->ctx, LY_VLOG_LYD, node, LYVE_SYNTAX,
                           "Metadata container references a sibling list node %s.", ((struct lyd_node_opaq*)node)->name);
                    ret = LY_EVALID;
                    goto cleanup;
                }

                /* match */
                match++;
                if (match != instance) {
                    continue;
                }

                LY_LIST_FOR(meta_container->child, meta_iter) {
                    /* convert opaq node to a attribute of the opaq node */
                    struct lyd_node_opaq *meta = (struct lyd_node_opaq*)meta_iter;
                    struct ly_prefix *val_prefs = NULL;
                    int dynamic = 0;

                    /* get value prefixes */
                    LY_CHECK_GOTO(ret = lydjson_get_value_prefixes(lydctx->jsonctx->ctx, lydctx->jsonctx->value, lydctx->jsonctx->value_len, &val_prefs), cleanup);

                    /* attr2 is always changed to the created attribute */
                    ret = lyd_create_attr(node, NULL, lydctx->jsonctx->ctx, meta->name, strlen(meta->name), meta->value, strlen(meta->value),
                                          &dynamic, meta->hint, LYD_JSON, val_prefs, meta->prefix.id, strlen(meta->prefix.id), NULL);
                    LY_CHECK_GOTO(ret, cleanup);
                }

                /* done */
                break;
            } else {
                /* this is the second time we are resolving the schema node, so it must succeed,
                 * but remember that snode can be still NULL */
                lydjson_parse_name(meta_container->name, strlen(meta_container->name), &name, &name_len, &prefix, &prefix_len, &is_attr);
                assert(is_attr);
                ret = lydjson_get_snode(lydctx, is_attr, prefix, prefix_len, name, name_len, (*first_p)->parent, &snode);
                assert(ret == LY_SUCCESS);

                if (snode != node->schema) {
                    continue;
                }

                /* match */
                match++;
                if (match != instance) {
                    continue;
                }

                LY_LIST_FOR(meta_container->child, meta_iter) {
                    /* convert opaq node to a metadata of the node */
                    struct lyd_node_opaq *meta = (struct lyd_node_opaq*)meta_iter;
                    struct lys_module *mod = NULL;
                    int dynamic = 0;

                    mod = ly_ctx_get_module_implemented(lydctx->jsonctx->ctx, meta->prefix.id);
                    if (mod) {
                        ret = lyd_parser_create_meta((struct lyd_ctx*)lydctx, node, NULL, mod,
                                                     meta->name, strlen(meta->name), meta->value, strlen(meta->value),
                                                     &dynamic, meta->hint, lydjson_resolve_prefix, NULL, LYD_JSON, snode);
                        LY_CHECK_GOTO(ret, cleanup);
                    } else if (lydctx->parse_options & LYD_PARSE_STRICT) {
                        LOGVAL(lydctx->jsonctx->ctx, LY_VLOG_LYD, node, LYVE_REFERENCE,
                               "Unknown (or not implemented) YANG module \"%s\" for metadata \"%s%s%s\".",
                               meta->prefix.id, meta->prefix.id, strlen(meta->prefix.id) ? ":" : "", meta->name);
                        ret = LY_EVALID;
                        goto cleanup;
                    }
                }
                /* add/correct flags */
                lyd_parse_set_data_flags(node, &lydctx->when_check, &node->meta, lydctx->parse_options);

                /* done */
                break;
            }
        }

        if (match != instance) {
            /* there is no corresponding data node for the metadata */
            if (instance > 1) {
                LOGVAL(lydctx->jsonctx->ctx, LY_VLOG_LYD, *first_p ? (*first_p)->parent : NULL, LYVE_REFERENCE,
                       "Missing %d%s JSON data instance to be coupled with %s metadata.", instance,
                       instance == 2 ? "nd" : (instance == 3 ? "rd" : "th"), meta_container->name);
            } else {
                LOGVAL(lydctx->jsonctx->ctx, LY_VLOG_LYD, *first_p ? (*first_p)->parent : NULL, LYVE_REFERENCE,
                       "Missing JSON data instance to be coupled with %s metadata.", meta_container->name);
            }
            ret = LY_EVALID;
        } else {
            /* remove the opaq attr */
            if (attr == (*first_p)) {
                *first_p = attr->next;
            }
            lyd_free_tree(attr);
        }
    }

cleanup:
    lydict_remove(lydctx->jsonctx->ctx, prev);

    return ret;
}

/**
 * @brief Parse a metadata member.
 *
 * @param[in] lydctx JSON data parser context.
 * @param[in] snode Schema node of the metadata parent.
 * @param[in] node Parent node in case the metadata is not forward-referencing (only LYD_NODE_TERM)
 * so the data node does not exists. In such a case the metadata is stored in the context for the later
 * processing by lydjson_metadata_finish().
 * @return LY_SUCCESS on success
 * @return Various LY_ERR values in case of failure.
 */
static LY_ERR
lydjson_metadata(struct lyd_json_ctx *lydctx, const struct lysc_node *snode, struct lyd_node *node)
{
    LY_ERR ret = LY_SUCCESS;
    enum LYJSON_PARSER_STATUS status;
    const char *expected;
    int in_parent = 0;
    const char *name, *prefix = NULL;
    size_t name_len, prefix_len = 0;
    struct lys_module *mod;
    struct lyd_meta *meta = NULL;
    const struct ly_ctx *ctx = lydctx->jsonctx->ctx;
    int is_attr = 0;
    struct lyd_node *prev = node;
    int instance = 0;
    uint16_t nodetype;

    assert(snode || node);

    nodetype = snode ? snode->nodetype : LYS_CONTAINER;

    /* move to the second item in the name/X pair */
    ret = lyjson_ctx_next(lydctx->jsonctx, &status);
    LY_CHECK_GOTO(ret, cleanup);

    /* check attribute encoding */
    switch (nodetype) {
    case LYS_LEAFLIST:
        expected = "@name/array of objects/nulls";

        LY_CHECK_GOTO(status != LYJSON_ARRAY, representation_error);

next_entry:
        instance++;

        /* move into array / next entry */
        ret = lyjson_ctx_next(lydctx->jsonctx, &status);
        LY_CHECK_GOTO(ret, cleanup);

        if (status == LYJSON_ARRAY_CLOSED) {
            /* we are done, move after the array */
            ret = lyjson_ctx_next(lydctx->jsonctx, NULL);
            goto cleanup;
        }
        LY_CHECK_GOTO(status != LYJSON_OBJECT && status != LYJSON_NULL, representation_error);

        if (!node || node->schema != prev->schema) {
            LOGVAL(lydctx->jsonctx->ctx, LY_VLOG_LYD, prev->parent, LYVE_REFERENCE,
                   "Missing JSON data instance no. %d of %s:%s to be coupled with metadata.",
                   instance, prev->schema->module->name, prev->schema->name);
            ret = LY_EVALID;
            goto cleanup;
        }

        if (status == LYJSON_NULL) {
            /* continue with the next entry in the leaf-list array */
            prev = node;
            node = node->next;
            goto next_entry;
        }
        break;
    case LYS_LEAF:
    case LYS_ANYXML:
        expected = "@name/object";

        LY_CHECK_GOTO(status != LYJSON_OBJECT && (nodetype != LYS_LEAFLIST || status != LYJSON_NULL), representation_error);
        break;
    case LYS_CONTAINER:
    case LYS_LIST:
    case LYS_ANYDATA:
    case LYS_NOTIF:
    case LYS_ACTION:
    case LYS_RPC:
        in_parent = 1;
        expected = "@/object";
        LY_CHECK_GOTO(status != LYJSON_OBJECT, representation_error);
        break;
    }

    /* process all the members inside a single metadata object */
    assert(status == LYJSON_OBJECT);

    while (status != LYJSON_OBJECT_CLOSED) {
        lydjson_parse_name(lydctx->jsonctx->value, lydctx->jsonctx->value_len, &name, &name_len, &prefix, &prefix_len, &is_attr);
        if (!prefix) {
            LOGVAL(ctx, LY_VLOG_LYD, (void*)node, LYVE_SYNTAX_JSON,
                   "Metadata in JSON must be namespace-qualified, missing prefix for \"%.*s\".",
                   lydctx->jsonctx->value_len, lydctx->jsonctx->value);
            ret = LY_EVALID;
            goto cleanup;
        } else if (is_attr) {
            LOGVAL(ctx, LY_VLOG_LYD, (void*)node, LYVE_SYNTAX_JSON,
                   "Invalid format of the Metadata identifier in JSON, unexpected '@' in \"%.*s\"",
                   lydctx->jsonctx->value_len, lydctx->jsonctx->value);
            ret = LY_EVALID;
            goto cleanup;
        }

        /* get the element module */
        mod = ly_ctx_get_module_implemented2(ctx, prefix, prefix_len);
        if (!mod) {
            if (lydctx->parse_options & LYD_PARSE_STRICT) {
                LOGVAL(ctx, LY_VLOG_LYD, (void*)node, LYVE_REFERENCE,
                       "Prefix \"%.*s\" of the metadata \"%.*s\" does not match any module in the context.",
                       prefix_len, prefix, name_len, name);
                ret = LY_EVALID;
                goto cleanup;
            }
            if (!(lydctx->parse_options & LYD_PARSE_OPAQ)) {
                /* skip element with children */
                ret = lydjson_data_skip(lydctx->jsonctx);
                LY_CHECK_GOTO(ret, cleanup);
                status = lyjson_ctx_status(lydctx->jsonctx, 0);
                /* end of the item */
                continue;
            }
        }

        /* get the value */
        ret = lyjson_ctx_next(lydctx->jsonctx, NULL);
        LY_CHECK_GOTO(ret, cleanup);

        if (node->schema) {
            /* create metadata */
            meta = NULL;
            ret = lyd_parser_create_meta((struct lyd_ctx*)lydctx, node, &meta, mod, name, name_len, lydctx->jsonctx->value, lydctx->jsonctx->value_len,
                                         &lydctx->jsonctx->dynamic, 0, lydjson_resolve_prefix, lydctx->jsonctx, LYD_JSON, snode);
            LY_CHECK_GOTO(ret, cleanup);

            /* add/correct flags */
            lyd_parse_set_data_flags(node, &lydctx->when_check, &meta, lydctx->parse_options);
        } else {
            /* create attribute */
            struct ly_prefix *val_prefs = NULL;

            /* get value prefixes */
            LY_CHECK_GOTO(ret = lydjson_get_value_prefixes(lydctx->jsonctx->ctx, lydctx->jsonctx->value, lydctx->jsonctx->value_len, &val_prefs), cleanup);

            /* attr2 is always changed to the created attribute */
            ret = lyd_create_attr(node, NULL, lydctx->jsonctx->ctx, name, name_len, lydctx->jsonctx->value, lydctx->jsonctx->value_len,
                                  &lydctx->jsonctx->dynamic, 0, LYD_JSON, val_prefs, prefix, prefix_len, NULL);
            LY_CHECK_GOTO(ret, cleanup);
        }
        /* next member */
        ret = lyjson_ctx_next(lydctx->jsonctx, &status);
        LY_CHECK_GOTO(ret, cleanup);
    }

    if (nodetype == LYS_LEAFLIST) {
        /* continue by processing another metadata object for the following
         * leaf-list instance since they are allways instantiated in JSON array */
        prev = node;
        node = node->next;
        goto next_entry;
    }

    /* move after the metadata */
    ret = lyjson_ctx_next(lydctx->jsonctx, NULL);
    LY_CHECK_GOTO(ret, cleanup);

cleanup:
    return ret;

representation_error:
    LOGVAL(ctx, LY_VLOG_LYD, (void*)node, LYVE_SYNTAX_JSON,
           "The attribute(s) of %s \"%s\" is expected to be represented as JSON %s, but input data contains @%s/%s.",
           lys_nodetype2str(nodetype), node->schema ? node->schema->name : ((struct lyd_node_opaq*)node)->name,
           expected, lyjson_token2str(status), in_parent ? "" : "name");

    return LY_EVALID;
}

/**
 * @brief Eat the node pointed by @p node_p by inserting it into @p parent and maintain the @p first_p pointing to the first child node.
 *
 * @param[in] parent Parent node to insert to, can be NULL in case of top-level (or provided first_p).
 * @param[in, out] first_p Pointer to the first sibling node in case of top-level.
 * @param[in, out] node_p pointer to the new node to insert, after the insert is done, pointer is set to NULL.
 */
static void
lydjson_maintain_children(struct lyd_node_inner *parent, struct lyd_node **first_p, struct lyd_node **node_p)
{
    if (*node_p) {
        /* insert, keep first pointer correct */
        lyd_insert_node((struct lyd_node *)parent, first_p, *node_p);
        while (!parent && (*first_p)->prev->next) {
            *first_p = (*first_p)->prev;
        }
        *node_p = NULL;
    }
}

static LY_ERR lydjson_subtree_r(struct lyd_json_ctx *lydctx, struct lyd_node_inner *parent, struct lyd_node **first);

static LY_ERR
lydjson_parse_opaq(struct lyd_json_ctx *lydctx, const char *name, size_t name_len,
                   const char *prefix, size_t prefix_len, struct lyd_node_inner *parent,
                   enum LYJSON_PARSER_STATUS *status, enum LYJSON_PARSER_STATUS *status_inner,
                   struct lyd_node **first, struct lyd_node **node)
{
    LY_ERR ret = LY_SUCCESS;
    const char *value = NULL;
    size_t value_len = 0;
    struct ly_prefix *val_prefs = NULL;
    int dynamic = 0;
    int type_hint = 0;

    if (*status_inner != LYJSON_OBJECT && *status_inner != LYJSON_OBJECT_EMPTY) {
        value = lydctx->jsonctx->value;
        value_len = lydctx->jsonctx->value_len;
        dynamic = lydctx->jsonctx->dynamic;
        lydctx->jsonctx->dynamic = 0;

        LY_CHECK_RET(lydjson_value_type_hint(lydctx, status_inner, &type_hint));

        if (value) {
            /* get value prefixes */
            LY_CHECK_RET(lydjson_get_value_prefixes(lydctx->jsonctx->ctx, value, value_len, &val_prefs));
        }
    }

    /* create node */
    ret = lyd_create_opaq(lydctx->jsonctx->ctx, name, name_len, value, value_len, &dynamic, type_hint,
                          LYD_JSON, val_prefs, prefix, prefix_len, NULL, node);
    if (dynamic) {
        free((char*)value);
        dynamic = 0;
    }
    value = NULL;
    value_len = 0;
    val_prefs = NULL;
    LY_CHECK_RET(ret);

    if (*status == LYJSON_OBJECT || *status == LYJSON_OBJECT_EMPTY) {
        /* process children */
        while (*status != LYJSON_OBJECT_CLOSED && *status != LYJSON_OBJECT_EMPTY) {
            LY_CHECK_RET(lydjson_subtree_r(lydctx, (struct lyd_node_inner *)(*node), lyd_node_children_p(*node)));
            *status = lyjson_ctx_status(lydctx->jsonctx, 0);
        }
    } else if (*status == LYJSON_ARRAY || *status == LYJSON_ARRAY_EMPTY) {
        /* process another instance of the same node */
        /* but first mark the node to be expected a list or a leaf-list */
        ((struct lyd_node_opaq*)*node)->hint |= LYD_NODE_OPAQ_ISLIST;

        if (*status_inner == LYJSON_OBJECT || *status_inner == LYJSON_OBJECT_EMPTY) {
            /* but first process children of the object in the array */
            while (*status_inner != LYJSON_OBJECT_CLOSED && *status_inner != LYJSON_OBJECT_EMPTY) {
                LY_CHECK_RET(lydjson_subtree_r(lydctx, (struct lyd_node_inner *)(*node), lyd_node_children_p(*node)));
                *status_inner = lyjson_ctx_status(lydctx->jsonctx, 0);
            }
        }

        LY_CHECK_RET(lyjson_ctx_next(lydctx->jsonctx, status_inner));

        /* continue with the next instance */
        if (*status_inner != LYJSON_ARRAY_CLOSED) {
            assert(node);
            lydjson_maintain_children(parent, first, node);
            return lydjson_parse_opaq(lydctx, name, name_len, prefix, prefix_len, parent, status, status_inner, first, node);
        }
    }

    /* finish linking metadata */
    LY_CHECK_RET(lydjson_metadata_finish(lydctx, lyd_node_children_p(*node)));

    /* move after the item */
    return lyjson_ctx_next(lydctx->jsonctx, status);
}

/**
 * @brief Parse JSON subtree.
 *
 * @param[in] lydctx JSON data parser context.
 * @param[in] parent Data parent of the subtree, must be set if @p first is not.
 * @param[in,out] first First top-level sibling, must be set if @p parent is not.
 * @return LY_ERR value.
 */
static LY_ERR
lydjson_subtree_r(struct lyd_json_ctx *lydctx, struct lyd_node_inner *parent, struct lyd_node **first)
{
    LY_ERR ret = LY_SUCCESS;
    enum LYJSON_PARSER_STATUS status = lyjson_ctx_status(lydctx->jsonctx, 0);
    enum LYJSON_PARSER_STATUS status_inner = 0;
    const char *name, *prefix = NULL;
    size_t name_len, prefix_len = 0;
    int is_attr = 0;
    const struct lysc_node *snode, *snode_backup = NULL;
    struct lyd_node *node = NULL, *attr_node = NULL, *anchor = NULL;
    const struct ly_ctx *ctx = lydctx->jsonctx->ctx;
    const char *expected = NULL;
    int type_hint = 0;
    uint32_t prev_opts;

    assert(parent || first);
    assert(status == LYJSON_OBJECT);

start:

    /* process the node name */
    lydjson_parse_name(lydctx->jsonctx->value, lydctx->jsonctx->value_len, &name, &name_len, &prefix, &prefix_len, &is_attr);

    if (is_attr && !name_len && !prefix_len) {
        /* parent's attribute without a name - skip schema node detection and get the schema from the parent */
        if (!parent) {
            LOGVAL(ctx, LY_VLOG_LYD, NULL, LYVE_SYNTAX_JSON, "Invalid metadata format - \"@\" can be used only inside anydata, container or list entries.");
            ret = LY_EVALID;
            goto cleanup;
        }
        attr_node = (struct lyd_node*)parent;
        snode = parent->schema;
        goto attribute;
    }

    /* get the schema node */
    ret = lydjson_get_snode(lydctx, is_attr, prefix, prefix_len, name, name_len, parent, &snode);
    if (ret == LY_ENOT) {
        /* skip element with children */
        ret = lydjson_data_skip(lydctx->jsonctx);
        LY_CHECK_GOTO(ret, cleanup);
        status = lyjson_ctx_status(lydctx->jsonctx, 0);
        if (status == LYJSON_OBJECT) {
            /* start over again */
            goto start;
        } else {
            /* end of the data */
            goto cleanup;
        }
    }
    LY_CHECK_GOTO(ret, cleanup);

    if (!snode) {
        /* parse as an opaq node */
        assert(lydctx->parse_options & LYD_PARSE_OPAQ);

        /* move to the second item in the name/X pair */
        ret = lyjson_ctx_next(lydctx->jsonctx, &status);
        LY_CHECK_GOTO(ret, cleanup);

        if (status == LYJSON_ARRAY) {
            /* move into the array */
            ret = lyjson_ctx_next(lydctx->jsonctx, &status_inner);
            LY_CHECK_GOTO(ret, cleanup);
        } else {
            /* just a flag to pass correct parameters into lydjson_parse_opaq() */
            status_inner = LYJSON_ERROR;
        }

        ret = lydjson_parse_opaq(lydctx, name, name_len, prefix, prefix_len,
                                 parent, &status, status_inner == LYJSON_ERROR ? &status : &status_inner, first, &node);
        LY_CHECK_GOTO(ret, cleanup);

    } else if (!is_attr) {
        /* parse as a standard lyd_node */

        /* move to the second item in the name/X pair */
        ret = lyjson_ctx_next(lydctx->jsonctx, &status);
        LY_CHECK_GOTO(ret, cleanup);

        /* first check the expected representation according to the nodetype and then continue with the content */
        switch (snode->nodetype) {
        case LYS_LEAFLIST:
            expected = "name/array of values";

            LY_CHECK_GOTO(status != LYJSON_ARRAY, representation_error);

            /* move into array */
            ret = lyjson_ctx_next(lydctx->jsonctx, &status);
            LY_CHECK_GOTO(ret, cleanup);

            /* process the value */
            goto next_term;
        case LYS_LEAF:
            if (status == LYJSON_ARRAY) {
                expected = "name/[null]";
            } else {
                expected = "name/value";
            }

next_term:
            ret = lydjson_data_check_opaq(lydctx, snode, &type_hint);
            if (ret == LY_SUCCESS) {
                /* create terminal node */
                ret = lyd_parser_create_term((struct lyd_ctx*)lydctx, snode, lydctx->jsonctx->value, lydctx->jsonctx->value_len,
                                             &lydctx->jsonctx->dynamic, type_hint, lydjson_resolve_prefix, lydctx->jsonctx, LYD_JSON, &node);
                LY_CHECK_GOTO(ret, cleanup);

                ret = lyjson_ctx_next(lydctx->jsonctx, &status);
                LY_CHECK_GOTO(ret, cleanup);
            } else if (ret == LY_ENOT) {
                /* parse it again as an opaq node */
                ret = lydjson_parse_opaq(lydctx, name, name_len, prefix, prefix_len, parent,
                                         &status, &status, first, &node);
                LY_CHECK_GOTO(ret, cleanup);

                if (snode->nodetype == LYS_LEAFLIST) {
                    ((struct lyd_node_opaq*)node)->hint |= LYD_NODE_OPAQ_ISLIST;
                }
            } else if (ret == LY_EINVAL) {
                goto representation_error;
            } else {
                goto cleanup;
            }

            if (snode->nodetype == LYS_LEAFLIST) {
                /* continue with the next instance of the leaf-list */
                if(status != LYJSON_ARRAY_CLOSED) {
                    assert(node);
                    lydjson_maintain_children(parent, first, &node);
                    goto next_term;
                }

                /* move after the array */
                ret = lyjson_ctx_next(lydctx->jsonctx, &status);
                LY_CHECK_GOTO(ret, cleanup);
            }

            break;
        case LYS_LIST:
            expected = "name/array of objects";

            LY_CHECK_GOTO(status != LYJSON_ARRAY, representation_error);

            /* move into array */
            ret = lyjson_ctx_next(lydctx->jsonctx, &status);
            LY_CHECK_GOTO(ret, cleanup);

next_list:
            if (lydjson_data_check_opaq(lydctx, snode, &type_hint)) {
                snode_backup = snode;
                snode = NULL;
                /* parse it again as an opaq node */
                ret = lydjson_parse_opaq(lydctx, name, name_len, prefix, prefix_len, parent,
                                         &status, &status, first, &node);
                LY_CHECK_GOTO(ret, cleanup);
                ((struct lyd_node_opaq*)node)->hint |= LYD_NODE_OPAQ_ISLIST;

                snode = snode_backup;
                snode_backup = NULL;
                goto list_loop;
            }

            /* process children */
            goto next_inner;
        case LYS_CONTAINER:
        case LYS_NOTIF:
        case LYS_ACTION:
        case LYS_RPC:
            expected = "name/object";

next_inner:
            LY_CHECK_GOTO(status != LYJSON_OBJECT && status != LYJSON_OBJECT_EMPTY, representation_error);

            /* create inner node */
            ret = lyd_create_inner(snode, &node);
            LY_CHECK_GOTO(ret, cleanup);

            /* process children */
            while (status != LYJSON_OBJECT_CLOSED && status != LYJSON_OBJECT_EMPTY) {
                ret = lydjson_subtree_r(lydctx, (struct lyd_node_inner *)node, lyd_node_children_p(node));
                LY_CHECK_GOTO(ret, cleanup);
                status = lyjson_ctx_status(lydctx->jsonctx, 0);
            }

            /* finish linking metadata */
            ret = lydjson_metadata_finish(lydctx, lyd_node_children_p(node));
            LY_CHECK_GOTO(ret, cleanup);

            if (snode->nodetype == LYS_LIST) {
                /* check all keys exist */
                ret = lyd_parse_check_keys(node);
                LY_CHECK_GOTO(ret, cleanup);
            }

            if (!(lydctx->parse_options & LYD_PARSE_ONLY)) {
                /* new node validation, autodelete CANNOT occur, all nodes are new */
                ret = lyd_validate_new(lyd_node_children_p(node), snode, NULL, NULL);
                LY_CHECK_GOTO(ret, cleanup);

                /* add any missing default children */
                ret = lyd_new_implicit_r(node, lyd_node_children_p(node), NULL, NULL, &lydctx->unres_node_type, &lydctx->when_check,
                                         (lydctx->validate_options & LYD_VALIDATE_NO_STATE) ? LYD_IMPLICIT_NO_STATE : 0, NULL);
                LY_CHECK_GOTO(ret, cleanup);
            }

            ret = lyjson_ctx_next(lydctx->jsonctx, &status);
            LY_CHECK_GOTO(ret, cleanup);
            if (snode->nodetype == LYS_LIST) {
list_loop:
                /* continue with the next instance of the list */
                if(status != LYJSON_ARRAY_CLOSED) {
                    assert(node);
                    lydjson_maintain_children(parent, first, &node);
                    goto next_list;
                }

                /* move after the array */
                ret = lyjson_ctx_next(lydctx->jsonctx, &status);
                LY_CHECK_GOTO(ret, cleanup);

            } else if (snode->nodetype & (LYS_RPC | LYS_ACTION | LYS_NOTIF)) {
                /* rememeber the RPC/action/notification */
                lydctx->op_node = node;
            }

            break;
        case LYS_ANYDATA:
        case LYS_ANYXML:
            expected = "name/object";
            LY_CHECK_GOTO(status != LYJSON_OBJECT && status != LYJSON_OBJECT_EMPTY, representation_error);

            /* parse any data tree with correct options */
            /* first backup the current options and then make the parser to process data as opaq nodes */
            prev_opts = lydctx->parse_options;
            lydctx->parse_options &= ~LYD_PARSE_STRICT;
            lydctx->parse_options |= LYD_PARSE_OPAQ;

            /* process the anydata content */
            while (status != LYJSON_OBJECT_CLOSED && status != LYJSON_OBJECT_EMPTY) {
                ret = lydjson_subtree_r(lydctx, NULL, &anchor);
                LY_CHECK_GOTO(ret, cleanup);
                status = lyjson_ctx_status(lydctx->jsonctx, 0);
            }

            /* reset parser options */
            lydctx->parse_options = prev_opts;
            LY_CHECK_GOTO(ret, cleanup);

            /* finish linking metadata */
            ret = lydjson_metadata_finish(lydctx, &anchor);
            LY_CHECK_GOTO(ret, cleanup);

            /* create any node */
            ret = lyd_create_any(snode, anchor, LYD_ANYDATA_DATATREE, &node);
            LY_CHECK_GOTO(ret, cleanup);

            break;
        }

    } else {
attribute:
        /* parse as an attribute to a node */
        if (!attr_node && snode) {
            /* try to find the instance */
            for (struct lyd_node *iter = *first; iter; iter = iter->next) {
                if (iter->schema == snode) {
                    attr_node = iter;
                    break;
                }
            }
        }
        if (!attr_node) {
            /* parse just as an opaq node with the name beginning with @,
             * later we have to check that it belongs to a standard node
             * and it is supposed to be converted to a metadata */

            /* move into metadata */
            ret = lyjson_ctx_next(lydctx->jsonctx, &status);
            LY_CHECK_GOTO(ret, cleanup);

            if (status == LYJSON_ARRAY) {
                /* move into the array */
                ret = lyjson_ctx_next(lydctx->jsonctx, &status_inner);
                LY_CHECK_GOTO(ret, cleanup);
            } else {
                /* just a flag to pass correct parameters into lydjson_parse_opaq() */
                status_inner = LYJSON_ERROR;
            }

            /* backup parser options to parse unknown metadata as opaq nodes and try to resolve them later */
            prev_opts = lydctx->parse_options;
            lydctx->parse_options &= ~LYD_PARSE_STRICT;
            lydctx->parse_options |= LYD_PARSE_OPAQ;

            ret = lydjson_parse_opaq(lydctx, prefix ? prefix - 1 : name - 1, prefix ? prefix_len + name_len + 2 : name_len + 1,
                                     NULL, 0, parent, &status, status_inner == LYJSON_ERROR ? &status : &status_inner, first, &node);
            LY_CHECK_ERR_GOTO(ret, lydctx->parse_options = prev_opts, cleanup);

            /* restore the parser options */
            lydctx->parse_options = prev_opts;
        } else {
            ret = lydjson_metadata(lydctx, snode, attr_node);
        }
    }

    lydjson_maintain_children(parent, first, &node);

cleanup:
    lyd_free_tree(node);
    return ret;

representation_error:
    LOGVAL(ctx, LY_VLOG_LYD, parent, LYVE_SYNTAX_JSON,
           "The %s \"%s\" is expected to be represented as JSON %s, but input data contains name/%s.",
           lys_nodetype2str(snode->nodetype), snode->name, expected, lyjson_token2str(status));

    ret = LY_EVALID;
    goto cleanup;
}

LY_ERR
lyd_parse_json_init(const struct ly_ctx *ctx, struct ly_in *in, int parse_options, int validate_options, struct lyd_json_ctx **lydctx_p)
{
    LY_ERR ret = LY_SUCCESS;
    struct lyd_json_ctx *lydctx;
    size_t i, line = 1;

    /* starting top-level */
    for (i = 0; in->current[i] != '\0' && is_jsonws(in->current[i]); i++) {
        if (in->current[i] == 0x0a) { /* new line */
            line++;
        };
    }
    if (in->current[i] == '\0') {
        /* empty data input */
        return LY_SUCCESS;
    }
    if (in->current[i] != '{') {
        LOGVAL(ctx, LY_VLOG_LINE, &line, LY_VCODE_INSTREXP, LY_VCODE_INSTREXP_len(&in->current[i]), &in->current[i],
               "a top-level JSON object ('{') holding encoded YANG data");
        return LY_EVALID;
    }

    /* init context */
    lydctx = calloc(1, sizeof *lydctx);
    LY_CHECK_ERR_RET(!lydctx, LOGMEM(ctx), LY_EMEM);
    lydctx->parse_options = parse_options;
    lydctx->validate_options = validate_options;
    lydctx->free = lyd_json_ctx_free;
    lydctx->resolve_prefix = lydjson_resolve_prefix;

    LY_CHECK_ERR_RET(ret = lyjson_ctx_new(ctx, in, &lydctx->jsonctx), free(lydctx), ret);

    *lydctx_p = lydctx;
    return LY_SUCCESS;
}

LY_ERR
lyd_parse_json_data(const struct ly_ctx *ctx, struct ly_in *in, int parse_options, int validate_options, struct lyd_node **tree, struct lyd_ctx **lydctx_p)
{
    LY_ERR ret = LY_SUCCESS;
    struct lyd_json_ctx *lydctx = NULL;
    enum LYJSON_PARSER_STATUS status;

    assert(tree);
    *tree = NULL;

    ret = lyd_parse_json_init(ctx, in, parse_options, validate_options, &lydctx);
    LY_CHECK_GOTO(ret || !lydctx, cleanup);

    status = lyjson_ctx_status(lydctx->jsonctx, 0);
    assert(status == LYJSON_OBJECT);

    /* read subtree(s) */
    while (lydctx->jsonctx->in->current[0] && status != LYJSON_OBJECT_CLOSED) {
        ret = lydjson_subtree_r(lydctx, NULL, tree);
        LY_CHECK_GOTO(ret, cleanup);

        status = lyjson_ctx_status(lydctx->jsonctx, 0);
    }

    /* finish linking metadata */
    ret = lydjson_metadata_finish(lydctx, tree);
    LY_CHECK_GOTO(ret, cleanup);

cleanup:
    /* there should be no unresolved types stored */
    assert(!(parse_options & LYD_PARSE_ONLY) || (!lydctx->unres_node_type.count && !lydctx->unres_meta_type.count
           && !lydctx->when_check.count));

    if (ret) {
        lyd_json_ctx_free((struct lyd_ctx *)lydctx);
        lyd_free_all(*tree);
        *tree = NULL;
    } else {
        *lydctx_p = (struct lyd_ctx *)lydctx;
    }

    return ret;
}

static LY_ERR
lydjson_notif_envelope(struct lyjson_ctx *jsonctx, struct lyd_node **envp)
{
    LY_ERR ret = LY_ENOT, r;
    const char *name, *prefix, *value = NULL;
    size_t name_len, prefix_len, value_len;
    int is_attr, dynamic = 0;
    enum LYJSON_PARSER_STATUS status;
    struct lyd_node *et;

    *envp = NULL;

    /* backup the context */
    lyjson_ctx_backup(jsonctx);

    /* "notification" envelope */
    lydjson_parse_name(jsonctx->value, jsonctx->value_len, &name, &name_len, &prefix, &prefix_len, &is_attr);
    LY_CHECK_GOTO(prefix_len || is_attr, cleanup);
    LY_CHECK_GOTO(name_len != 12 || strncmp(name, "notification", name_len), cleanup);

    r = lyjson_ctx_next(jsonctx, &status);
    LY_CHECK_ERR_GOTO(r, ret = r, cleanup);
    LY_CHECK_GOTO(status != LYJSON_OBJECT, cleanup);

    /* "eventTime" child */
    lydjson_parse_name(jsonctx->value, jsonctx->value_len, &name, &name_len, &prefix, &prefix_len, &is_attr);
    LY_CHECK_GOTO(prefix_len || is_attr, cleanup);
    LY_CHECK_GOTO(name_len != 9 || strncmp(name, "eventTime", name_len), cleanup);

    /* go for the data */
    r = lyjson_ctx_next(jsonctx, &status);
    LY_CHECK_ERR_GOTO(r, ret = r, cleanup);
    LY_CHECK_GOTO(status != LYJSON_STRING, cleanup);

    value = jsonctx->value;
    value_len = jsonctx->value_len;
    dynamic = jsonctx->dynamic;
    jsonctx->dynamic = 0;

    r = lyjson_ctx_next(jsonctx, &status);
    LY_CHECK_ERR_GOTO(r, ret = r, cleanup);
    LY_CHECK_GOTO(status != LYJSON_OBJECT, cleanup);
    /* now the notificationContent is expected, which will be parsed by the caller */

    /* create notification envelope */
    ret = lyd_create_opaq(jsonctx->ctx, "notification", 12, "", 0, NULL, 0, LYD_JSON, NULL, NULL, 0,
                          "urn:ietf:params:xml:ns:netconf:notification:1.0", envp);
    LY_CHECK_GOTO(ret, cleanup);
    /* create notification envelope */
    ret = lyd_create_opaq(jsonctx->ctx, "eventTime", 9, value, value_len, &dynamic, LYD_NODE_OPAQ_ISSTRING,
                          LYD_JSON, NULL, NULL, 0, "urn:ietf:params:xml:ns:netconf:notification:1.0", &et);
    LY_CHECK_GOTO(ret, cleanup);
    /* insert eventTime into notification */
    lyd_insert_node(*envp, NULL, et);

    ret = LY_SUCCESS;
cleanup:
    if (ret) {
        /* restore the context */
        lyjson_ctx_restore(jsonctx);
        if (dynamic) {
            free((char*)value);
        }
    }
    return ret;
}

LY_ERR
lyd_parse_json_notif(const struct ly_ctx *ctx, struct ly_in *in, struct lyd_node **tree, struct lyd_node **ntf)
{
    LY_ERR ret = LY_SUCCESS;
    struct lyd_json_ctx *lydctx = NULL;
    struct lyd_node *ntf_e = NULL;
    enum LYJSON_PARSER_STATUS status;

    /* init */
    ret = lyd_parse_json_init(ctx, in, LYD_PARSE_ONLY | LYD_PARSE_STRICT, 0, &lydctx);
    LY_CHECK_GOTO(ret || !lydctx, cleanup);
    lydctx->int_opts = LYD_INTOPT_NOTIF;

    status = lyjson_ctx_status(lydctx->jsonctx, 0);
    assert(status == LYJSON_OBJECT);

    /* parse "notification" and "eventTime", if present */
    lydjson_notif_envelope(lydctx->jsonctx, &ntf_e);

    /* read subtree(s) */
    while (lydctx->jsonctx->in->current[0] && status != LYJSON_OBJECT_CLOSED) {
        ret = lydjson_subtree_r(lydctx, NULL, tree);
        LY_CHECK_GOTO(ret, cleanup);

        status = lyjson_ctx_status(lydctx->jsonctx, 0);
    }

    /* finish linking metadata */
    ret = lydjson_metadata_finish(lydctx, tree);
    LY_CHECK_GOTO(ret, cleanup);

    /* make sure we have parsed some notification */
    if (!lydctx->op_node) {
        LOGVAL(ctx, LY_VLOG_NONE, NULL, LYVE_DATA, "Missing the \"notification\" node.");
        ret = LY_EVALID;
        goto cleanup;
    }

    if (ntf_e) {
        /* finish notification envelope */
        ret = lyjson_ctx_next(lydctx->jsonctx, &status);
        LY_CHECK_GOTO(ret, cleanup);
        if (status == LYJSON_END) {
            LOGVAL(ctx, LY_VLOG_LINE, &lydctx->jsonctx->line, LY_VCODE_EOF);
            ret = LY_EVALID;
            goto cleanup;
        } else if (status != LYJSON_OBJECT_CLOSED) {
            LOGVAL(ctx, LY_VLOG_LINE, &lydctx->jsonctx->line, LYVE_SYNTAX, "Unexpected sibling member \"%.*s\" of \"notification\".",
                   lydctx->jsonctx->value_len, lydctx->jsonctx->value);
            ret = LY_EVALID;
            goto cleanup;
        }
    }

    if (ntf) {
        *ntf = lydctx->op_node;
    }
    assert(*tree);
    if (ntf_e) {
        /* connect to the notification */
        lyd_insert_node(ntf_e, NULL, *tree);
        *tree = ntf_e;
    }

cleanup:
    /* we have used parse_only flag */
    assert(!lydctx || (!lydctx->unres_node_type.count && !lydctx->unres_meta_type.count && !lydctx->when_check.count));

    lyd_json_ctx_free((struct lyd_ctx *)lydctx);
    if (ret) {
        lyd_free_all(*tree);
        lyd_free_tree(ntf_e);
        *tree = NULL;
    }
    return ret;
}

static LY_ERR
lydjson_object_envelope(struct lyjson_ctx *jsonctx, const char *ns, const char *object_id, struct lyd_node **envp)
{
    LY_ERR ret = LY_ENOT, r;
    const char *name, *prefix;
    size_t name_len, prefix_len;
    int is_attr;
    enum LYJSON_PARSER_STATUS status;

    *envp = NULL;

    /* "id" envelope */
    lydjson_parse_name(jsonctx->value, jsonctx->value_len, &name, &name_len, &prefix, &prefix_len, &is_attr);
    LY_CHECK_GOTO(prefix_len || is_attr, cleanup);
    LY_CHECK_GOTO(name_len != strlen(object_id) || strncmp(name, object_id, name_len), cleanup);

    r = lyjson_ctx_next(jsonctx, &status);
    LY_CHECK_ERR_GOTO(r, ret = r, cleanup);
    LY_CHECK_GOTO(status != LYJSON_OBJECT, cleanup);

    /* create the object envelope */
    ret = lyd_create_opaq(jsonctx->ctx, object_id, strlen(object_id), "", 0, NULL, 0, LYD_JSON, NULL, NULL, 0, ns, envp);
    LY_CHECK_GOTO(ret, cleanup);

    ret = LY_SUCCESS;
cleanup:
    return ret;
}

static LY_ERR
lydjson_object_envelope_close(struct lyjson_ctx *jsonctx, const char *object_id)
{
    enum LYJSON_PARSER_STATUS status;

    LY_CHECK_RET(lyjson_ctx_next(jsonctx, &status));
    if (status == LYJSON_END) {
        LOGVAL(jsonctx->ctx, LY_VLOG_LINE, &jsonctx->line, LY_VCODE_EOF);
        return LY_EVALID;
    } else if (status != LYJSON_OBJECT_CLOSED) {
        LOGVAL(jsonctx->ctx, LY_VLOG_LINE, &jsonctx->line, LYVE_SYNTAX, "Unexpected sibling member \"%.*s\" of \"%s\".",
               jsonctx->value_len, jsonctx->value, object_id);
        return LY_EVALID;
    }
    return LY_SUCCESS;
}

LY_ERR
lyd_parse_json_rpc(const struct ly_ctx *ctx, struct ly_in *in, struct lyd_node **tree, struct lyd_node **op)
{
    LY_ERR ret = LY_SUCCESS;
    struct lyd_json_ctx *lydctx = NULL;
    struct lyd_node *rpc_e = NULL, *act_e = NULL;
    enum LYJSON_PARSER_STATUS status;

    /* init */
    ret = lyd_parse_json_init(ctx, in, LYD_PARSE_ONLY | LYD_PARSE_STRICT, 0, &lydctx);
    LY_CHECK_GOTO(ret || !lydctx, cleanup);
    lydctx->int_opts = LYD_INTOPT_RPC;

    /* process envelope(s), if present */

    /* backup the context */
    lyjson_ctx_backup(lydctx->jsonctx);
    /* process rpc */
    ret = lydjson_object_envelope(lydctx->jsonctx, "urn:ietf:params:xml:ns:netconf:base:1.0", "rpc", &rpc_e);
    if (ret == LY_ENOT) {
        ret = LY_SUCCESS;
        goto parse_content;
    } else if (ret) {
        goto cleanup;
    }
    /* process action */
    ret = lydjson_object_envelope(lydctx->jsonctx, "urn:ietf:params:xml:ns:yang:1", "action", &act_e);
    if (ret == LY_ENOT) {
        ret = LY_SUCCESS;
        goto parse_content;
    } else if (ret) {
        goto cleanup;
    }

parse_content:

    status = lyjson_ctx_status(lydctx->jsonctx, 0);
    assert(status == LYJSON_OBJECT);

    /* read subtree(s) */
    while (lydctx->jsonctx->in->current[0] && status != LYJSON_OBJECT_CLOSED) {
        ret = lydjson_subtree_r(lydctx, NULL, tree);
        LY_CHECK_GOTO(ret, cleanup);

        status = lyjson_ctx_status(lydctx->jsonctx, 0);
    }

    /* finish linking metadata */
    ret = lydjson_metadata_finish(lydctx, tree);
    LY_CHECK_GOTO(ret, cleanup);

    /* make sure we have parsed some operation */
    if (!lydctx->op_node) {
        LOGVAL(ctx, LY_VLOG_NONE, NULL, LYVE_DATA, "Missing the %s node.",
               act_e ? "action" : (rpc_e ? "rpc" : "rpc/action"));
        ret = LY_EVALID;
        goto cleanup;
    }

    if (act_e) {
        /* finish action envelope */
        ret = lydjson_object_envelope_close(lydctx->jsonctx, "action");
        LY_CHECK_GOTO(ret, cleanup);
        if (lydctx->op_node->schema->nodetype != LYS_ACTION) {
            LOGVAL(ctx, LY_VLOG_LYD, lydctx->op_node, LYVE_DATA, "Unexpected %s element, an \"action\" expected.",
                   lys_nodetype2str(lydctx->op_node->schema->nodetype));
            ret = LY_EVALID;
            goto cleanup;
        }
    }
    if (rpc_e) {
        /* finish rpc envelope */
        ret = lydjson_object_envelope_close(lydctx->jsonctx, "rpc");
        LY_CHECK_GOTO(ret, cleanup);
        if (!act_e && lydctx->op_node->schema->nodetype != LYS_RPC) {
            LOGVAL(ctx, LY_VLOG_LYD, lydctx->op_node, LYVE_DATA, "Unexpected %s element, an \"rpc\" expected.",
                   lys_nodetype2str(lydctx->op_node->schema->nodetype));
            ret = LY_EVALID;
            goto cleanup;
        }
    }

    if (op) {
        *op = lydctx->op_node;
    }
    assert(*tree);
    if (act_e) {
        /* connect to the action */
        lyd_insert_node(act_e, NULL, *tree);
        *tree = act_e;
    }
    if (rpc_e) {
        /* connect to the rpc */
        lyd_insert_node(rpc_e, NULL, *tree);
        *tree = rpc_e;
    }

cleanup:
    /* we have used parse_only flag */
    assert(!lydctx || (!lydctx->unres_node_type.count && !lydctx->unres_meta_type.count && !lydctx->when_check.count));

    lyd_json_ctx_free((struct lyd_ctx *)lydctx);
    if (ret) {
        lyd_free_all(*tree);
        lyd_free_tree(act_e);
        lyd_free_tree(rpc_e);
        *tree = NULL;
    }
    return ret;
}
