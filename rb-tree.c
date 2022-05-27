#include "rb-tree.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct rbt_tree;

struct rbt_node {
    struct rbt_node *left;
    struct rbt_node *right;
    struct rbt_node *parent;
    rbt_color color;
    void *key;
    struct rbt_tree *tree;
};

struct rbt_tree {
    struct rbt_node *root;
    struct rbt_node sentinel;
    rbt_node_destruct node_destruct;
    rbt_node_compare node_compare;
};

#define rb_sentinel(tree) &(tree)->sentinel

static void debug_verify_properties(struct rbt_tree *);
static void debug_verify_property_1(struct rbt_tree *, struct rbt_node *);
static void debug_verify_property_2(struct rbt_tree *, struct rbt_node *);
static int debug_node_color(struct rbt_tree *, struct rbt_node *n);
static void debug_verify_property_4(struct rbt_tree *, struct rbt_node *);
static void debug_verify_property_5(struct rbt_tree *, struct rbt_node *);
static void debug_verify_property_5_helper(struct rbt_tree *, struct rbt_node *,
                                           int, int *);

bool rbt_node_is_valid(const struct rbt_node *node)
{
    assert(node);
    assert(node->tree);
    return node && node != rb_sentinel(node->tree);
}

rbt_color rbt_node_get_color(const struct rbt_node *node)
{
    assert(node);
    return node->color;
}

struct rbt_node *rbt_node_get_left(const struct rbt_node *node)
{
    assert(node);
    return node->left;
}

struct rbt_node *rbt_node_get_right(const struct rbt_node *node)
{
    assert(node);
    return node->right;
}

struct rbt_node *rbt_node_get_parent(const struct rbt_node *node)
{
    assert(node);
    return node->parent;
}

const void *rbt_node_get_key(const struct rbt_node *node)
{
    assert(node);
    if (rbt_node_is_valid(node)) {
        return node->key;
    }
    return (void *)0;
}

static void _do_node_destruct(struct rbt_node *node)
{
    struct rbt_tree *tree;
    assert(node);
    tree = node->tree;
    assert(tree);
    if (rbt_node_is_valid(node)) {
        if (tree->node_destruct) {
            tree->node_destruct(node->key);
        }
    } else {
        assert(false);
    }
}

static void __left_rotate(struct rbt_tree *tree, struct rbt_node *x)
{
    struct rbt_node *y;
    y        = x->right;
    x->right = y->left;
    if (rbt_node_is_valid(y->left)) {
        y->left->parent = x;
    }
    if (rbt_node_is_valid(y)) {
        y->parent = x->parent;
    }
    if (rbt_node_is_valid(x->parent)) {
        if (x == x->parent->left) {
            x->parent->left = y;
        } else {
            x->parent->right = y;
        }
    } else {
        tree->root = y;
    }
    y->left = x;
    if (rbt_node_is_valid(x)) {
        x->parent = y;
    }
}

static void __right_rotate(struct rbt_tree *tree, struct rbt_node *x)
{
    struct rbt_node *y;
    assert(tree);
    assert(x);
    y       = x->left;
    x->left = y->right;
    if (rbt_node_is_valid(y->right)) {
        y->right->parent = x;
    }
    if (rbt_node_is_valid(y)) {
        y->parent = x->parent;
    }
    if (rbt_node_is_valid(x->parent)) {
        if (x == x->parent->right) {
            x->parent->right = y;
        } else {
            x->parent->left = y;
        }
    } else {
        tree->root = y;
    }
    y->right = x;
    if (rbt_node_is_valid(x)) {
        x->parent = y;
    }
}

struct rbt_tree *rbt_tree_create(rbt_node_compare cmp, rbt_node_destruct dest)
{
    struct rbt_tree *tree = (struct rbt_tree *)calloc(1, sizeof(*tree));
    if (tree != (struct rbt_tree *)0) {
        tree->node_compare    = cmp;
        tree->node_destruct   = dest;
        tree->root            = rb_sentinel(tree);
        tree->sentinel.left   = rb_sentinel(tree);
        tree->sentinel.right  = rb_sentinel(tree);
        tree->sentinel.parent = rb_sentinel(tree);
        tree->sentinel.tree   = tree;
        tree->sentinel.color  = rbt_black;

        /* make code checker happy */
        debug_verify_properties(tree);
    }

    return tree;
}

struct rbt_node *rbt_tree_get_root(struct rbt_tree *tree)
{
    assert(tree);
    return tree->root;
}

static void __rb_insert_fixup(struct rbt_tree *tree, struct rbt_node *x)
{
    while (x != tree->root && x->parent->color == rbt_red) {
        if (x->parent == x->parent->parent->left) {
            struct rbt_node *y = x->parent->parent->right;
            if (y->color == rbt_red) {
                x->parent->color         = rbt_black;
                y->color                 = rbt_black;
                x->parent->parent->color = rbt_red;
                x                        = x->parent->parent;
            } else {
                if (x == x->parent->right) {
                    x = x->parent;
                    __left_rotate(tree, x);
                }
                x->parent->color         = rbt_black;
                x->parent->parent->color = rbt_red;
                __right_rotate(tree, x->parent->parent);
            }
        } else {
            struct rbt_node *y = x->parent->parent->left;
            if (y->color == rbt_red) {
                x->parent->color         = rbt_black;
                y->color                 = rbt_black;
                x->parent->parent->color = rbt_red;
                x                        = x->parent->parent;
            } else {
                if (x == x->parent->left) {
                    x = x->parent;
                    __right_rotate(tree, x);
                }
                x->parent->color         = rbt_black;
                x->parent->parent->color = rbt_red;
                __left_rotate(tree, x->parent->parent);
            }
        }
    }
    tree->root->color = rbt_black;
}

struct rbt_node *rbt_tree_find(struct rbt_tree *tree, const void *key)
{
    struct rbt_node *x;
    assert(tree);
    assert(key);
    x = tree->root;
    while (rbt_node_is_valid(x)) {
        int c = tree->node_compare(key, x->key);
        if (c == 0) {
            break;
        } else {
            x = c < 0 ? x->left : x->right;
        }
    }
    return x;
}

static struct rbt_node *_create_node(struct rbt_tree *tree, void *key, size_t s)
{
    struct rbt_node *node = (struct rbt_node *)calloc(1, sizeof(*node));
    if (node) {
        node->left   = rb_sentinel(tree);
        node->right  = rb_sentinel(tree);
        node->color  = rbt_red;
        node->parent = rb_sentinel(tree);
        node->tree   = tree;

        assert(key && s);
        node->key = calloc(s, sizeof(char));
        if (node->key == NULL) {
            free(node);
            node = NULL;
        } else {
            memcpy(node->key, key, s);
        }
    }
    assert(node);
    return node;
}

static void _node_clearup(struct rbt_node *node, bool destroy)
{
    assert(node);
    if (node) {
        _do_node_destruct(node);
        free(node->key);
        node->key = NULL;
        if (destroy) {
            free(node);
        }
    }
}

static int _rb_node_compare(struct rbt_node *lhs, struct rbt_node *rhs)
{
    struct rbt_tree *tree = lhs->tree;
    assert(tree == rhs->tree);
    return tree->node_compare(lhs->key, rhs->key);
}

rbt_status rbt_tree_insert(struct rbt_tree *tree, void *key, size_t size)
{
    rbt_status rc = RBT_STATUS_SUCCESS;
    struct rbt_node *x;
    struct rbt_node *y;
    struct rbt_node *z;

    x = _create_node(tree, key, size);
    if (x == (struct rbt_node *)0) {
        return RBT_STATUS_MEMORY_OUT;
    }

    y = tree->root;
    z = rb_sentinel(tree);

    while (rbt_node_is_valid(y)) {
        int c = _rb_node_compare(x, y);
        if (c == 0) {
            _node_clearup(x, true);
            return RBT_STATUS_KEY_DUPLICATE;
        }
        z = y;
        if (c < 0) {
            y = y->left;
        } else {
            y = y->right;
        }
    }
    x->parent = z;
    if (rbt_node_is_valid(z)) {
        if (_rb_node_compare(x, z) < 0) {
            z->left = x;
        } else {
            z->right = x;
        }
    } else {
        tree->root = x;
    }
    __rb_insert_fixup(tree, x);

#ifndef NDEBUG
    debug_verify_properties(tree);
#endif
    return rc;
}

static void __rb_remove_fixup(struct rbt_tree *tree, struct rbt_node *x)
{
    while (x != tree->root && x->color == rbt_black) {
        if (x == x->parent->left) {
            struct rbt_node *w = x->parent->right;
            if (w->color == rbt_red) {
                w->color         = rbt_black;
                x->parent->color = rbt_red;
                __left_rotate(tree, x->parent);
                w = x->parent->right;
            }
            if (w->left->color == rbt_black && w->right->color == rbt_black) {
                w->color = rbt_red;
                x        = x->parent;
            } else {
                if (w->right->color == rbt_black) {
                    w->left->color = rbt_black;
                    w->color       = rbt_red;
                    __right_rotate(tree, w);
                    w = x->parent->right;
                }
                w->color         = x->parent->color;
                x->parent->color = rbt_black;
                w->right->color  = rbt_black;
                __left_rotate(tree, x->parent);
                x = tree->root;
            }
        } else {
            struct rbt_node *w = x->parent->left;
            if (w->color == rbt_red) {
                w->color         = rbt_black;
                x->parent->color = rbt_red;
                __right_rotate(tree, x->parent);
                w = x->parent->left;
            }
            if (w->right->color == rbt_black && w->left->color == rbt_black) {
                w->color = rbt_red;
                x        = x->parent;
            } else {
                if (w->left->color == rbt_black) {
                    w->right->color = rbt_black;
                    w->color        = rbt_red;
                    __left_rotate(tree, w);
                    w = x->parent->left;
                }
                w->color         = x->parent->color;
                x->parent->color = rbt_black;
                w->left->color   = rbt_black;
                __right_rotate(tree, x->parent);
                x = tree->root;
            }
        }
    }
    x->color = rbt_black;
}

static struct rbt_node *_remove_rb(struct rbt_tree *tree, struct rbt_node *node)
{
    struct rbt_node *x, *y;

    if (false == rbt_node_is_valid(node->left) ||
        false == rbt_node_is_valid(node->right)) {
        y = node;
    } else {
        y = node->right;
        while (rbt_node_is_valid(y->left)) {
            y = y->left;
        }
    }
    if (rbt_node_is_valid(y->left)) {
        x = y->left;
    } else {
        x = y->right;
    }
    x->parent = y->parent;
    if (rbt_node_is_valid(y->parent)) {
        if (y == y->parent->left) {
            y->parent->left = x;
        } else {
            y->parent->right = x;
        }
    } else {
        tree->root = x;
    }
    if (y != node) {
        void *tmp = node->key;
        node->key = y->key;
        y->key    = tmp;
    }
    if (y->color == rbt_black) {
        __rb_remove_fixup(tree, x);
    }
#ifndef NDEBUG
    debug_verify_properties(tree);
#endif
    return y;
}

rbt_status rbt_tree_remove_node(struct rbt_tree *tree, const void *key)
{
    struct rbt_node *x, *z = rbt_tree_find(tree, key);
    if (false == rbt_node_is_valid(z)) {
        return RBT_STATUS_KEY_NOT_EXIST;
    }
    x = _remove_rb(tree, z);
    _node_clearup(x, true);

    return RBT_STATUS_SUCCESS;
}

rbt_status rbt_tree_destroy(struct rbt_tree *tree)
{
    rbt_status rc      = RBT_STATUS_SUCCESS;
    struct rbt_node *z = tree->root;

    while (rbt_node_is_valid(z)) {
        if (rbt_node_is_valid(z->left)) {
            z = z->left;
        } else if (rbt_node_is_valid(z->right)) {
            z = z->right;
        } else {
            _node_clearup(z, false);
            if (rbt_node_is_valid(z->parent)) {
                z = z->parent;
                if (rbt_node_is_valid(z->left)) {
                    free(z->left);
                    z->left = rb_sentinel(tree);
                } else if (rbt_node_is_valid(z->right)) {
                    free(z->right);
                    z->right = rb_sentinel(tree);
                }
            } else {
                free(z);
                z = rb_sentinel(tree);
            }
        }
    }
    free(tree);
    return rc;
}

struct rbt_node *rbt_tree_minimum(struct rbt_tree *tree, struct rbt_node *x)
{
    assert(tree);
    assert(x);
    if (x == NULL || false == rbt_node_is_valid(x)) {
        return x;
    }
    assert(tree == x->tree);
    while (rbt_node_is_valid(x->left)) {
        x = x->left;
    }
    (void)tree;
    return x;
}

struct rbt_node *rbt_tree_maximum(struct rbt_tree *tree, struct rbt_node *x)
{
    assert(tree);
    assert(x);
    if (x == NULL || false == rbt_node_is_valid(x)) {
        return x;
    }
    while (rbt_node_is_valid(x->right)) {
        x = x->right;
    }
    (void)tree;
    return x;
}

bool rbt_tree_is_empty(struct rbt_tree *tree)
{
    assert(tree);
    if (rbt_node_is_valid(tree->root)) {
        return true;
    }
    return false;
}

struct rbt_node *rbt_tree_successor(struct rbt_tree *tree, struct rbt_node *x)
{
    struct rbt_node *y;
    assert(tree);
    assert(x);
    y = rb_sentinel(tree);
    if (rbt_node_is_valid(x->right)) {
        return rbt_tree_minimum(tree, x->right);
    }
    if (x == rbt_tree_maximum(tree, tree->root)) {
        return rb_sentinel(tree);
    }
    y = x->parent;
    while (rbt_node_is_valid(y) && x == y->right) {
        x = y;
        y = y->parent;
    }
    return y;
}

static void _inorder_tree_walk(struct rbt_node *x, rbt_node_walk_cb cb, void *p)
{
    if (rbt_node_is_valid(x)) {
        _inorder_tree_walk(x->left, cb, p);
        if (cb) {
            cb(x, p);
        }
        _inorder_tree_walk(x->right, cb, p);
    }
}

void rbt_inorder_walk(struct rbt_tree *tree, rbt_node_walk_cb cb, void *p)
{
    assert(tree);
    assert(cb);
    _inorder_tree_walk(tree->root, cb, p);
}

/*
struct rbt_node *
cstl_rb_get_next(struct rbt_tree* tree, struct rbt_node**current, struct rbt_node**pre) {
    struct rbt_node* prev_current;
    assert(tree);
    assert(current);
    assert(pre);
    while (rbt_node_is_valid((*current))) {
        if (false == rbt_node_is_valid((*current)->left)) {
            prev_current = (*current);
            (*current) = (*current)->right;
            return prev_current;
        } else {
            (*pre) = (*current)->left;
            while (rbt_node_is_valid((*pre)->right) && (*pre)->right != (*current))
                (*pre) = (*pre)->right;
            if (rbt_node_is_valid((*pre)->right)) {
                (*pre)->right = (*current);
                (*current) = (*current)->left;
            } else {
                (*pre)->right = rb_sentinel(tree);
                prev_current = (*current);
                (*current) = (*current)->right;
                return prev_current;
            }
        }
    }
    return rb_sentinel(tree);
} */

void debug_verify_properties(struct rbt_tree *t)
{
    debug_verify_property_1(t, t->root);
    debug_verify_property_2(t, t->root);
    debug_verify_property_4(t, t->root);
    debug_verify_property_5(t, t->root);
}

void debug_verify_property_1(struct rbt_tree *tree, struct rbt_node *n)
{
    if (false == rbt_node_is_valid(n)) {
        return;
    }
    assert(debug_node_color(tree, n) == rbt_red ||
           debug_node_color(tree, n) == rbt_black);
    debug_verify_property_1(tree, n->left);
    debug_verify_property_1(tree, n->right);
}

void debug_verify_property_2(struct rbt_tree *tree, struct rbt_node *root)
{
    (void)tree;
    (void)root;
    assert(debug_node_color(tree, root) == rbt_black);
}

int debug_node_color(struct rbt_tree *tree, struct rbt_node *n)
{
    (void)tree;
    return false == rbt_node_is_valid(n) ? rbt_black : n->color;
}

void debug_verify_property_4(struct rbt_tree *tree, struct rbt_node *n)
{
    if (debug_node_color(tree, n) == rbt_red) {
        assert(debug_node_color(tree, n->left) == rbt_black);
        assert(debug_node_color(tree, n->right) == rbt_black);
        assert(debug_node_color(tree, n->parent) == rbt_black);
    }
    if (false == rbt_node_is_valid(n)) {
        return;
    }
    debug_verify_property_4(tree, n->left);
    debug_verify_property_4(tree, n->right);
}

void debug_verify_property_5(struct rbt_tree *tree, struct rbt_node *root)
{
    int black_count_path = -1;
    debug_verify_property_5_helper(tree, root, 0, &black_count_path);
}

void debug_verify_property_5_helper(struct rbt_tree *tree, struct rbt_node *n,
                                    int black_count, int *_black_count)
{
    if (debug_node_color(tree, n) == rbt_black) {
        black_count++;
    }
    if (false == rbt_node_is_valid(n)) {
        if (*_black_count == -1) {
            *_black_count = black_count;
        } else {
            assert(black_count == *_black_count);
        }
        return;
    }
    debug_verify_property_5_helper(tree, n->left, black_count, _black_count);
    debug_verify_property_5_helper(tree, n->right, black_count, _black_count);
}
