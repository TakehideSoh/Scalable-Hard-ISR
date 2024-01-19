#ifndef AVLTREE_H
#define AVLTREE_H

#include "bitset.h"

typedef struct Node {
   Bitset      *key;
   struct Node *left, *right;
   struct Node *pathParent;
   uint32_t     height;
   uint16_t     from;
   uint16_t     to;
   uint32_t     refs;
} Node;

typedef struct Node_list {
   uint64_t size;
   Node    *value[];
} Node_list;

uint32_t tree_height(Node *node);
Node    *tree_rightRotate(Node *node);
Node    *tree_leftRotate(Node *node);
int16_t  tree_getBalance(Node *node);
uint64_t tree_size(Node *node);
Node    *tree_contained(Node *node, Bitset *a);
Node    *tree_insert(Node *node, Bitset *a, uint32_t *count, uint16_t from, uint16_t to,
                     Node *parent);
void     tree_free(Node *node);
Node    *tree_getLeftMost(Node *node);
Node    *tree_getNext(Node *node);
void     tree_printRefs(Node *root);
Node    *tree_delete(Node *node, Bitset *a, Node **result, uint32_t level);
Node   **tree_allNodes(Node *node, uint32_t number);

bool     node_insert(Node_list **list, Node *node);
uint64_t prune(Node_list **list);

uint32_t max(uint32_t a, uint32_t b);

#endif
