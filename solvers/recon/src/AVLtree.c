#include "AVLtree.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

uint32_t max(uint32_t a, uint32_t b) { return (a > b) ? a : b; }

uint32_t tree_height(Node *node)
{
   if (node == NULL)
      return 0;
   return node->height;
}

Node *tree_rightRotate(Node *node)
{
   Node *x = node->left;
   Node *z = x->right;

   x->right     = node;
   node->left   = z;
   node->height = max(tree_height(node->left), tree_height(node->right)) + 1;
   x->height    = max(tree_height(x->left), tree_height(x->right)) + 1;
   return x;
}

Node *tree_leftRotate(Node *node)
{
   Node *y = node->right;
   Node *z = y->left;

   y->left      = node;
   node->right  = z;
   node->height = max(tree_height(node->left), tree_height(node->right)) + 1;
   y->height    = max(tree_height(y->left), tree_height(y->right)) + 1;
   return y;
}

int16_t tree_getBalance(Node *node)
{
   if (node == NULL)
      return 0;
   return tree_height(node->left) - tree_height(node->right);
}

Node *tree_newNode(Bitset *a, uint16_t from, uint16_t to, Node *parent)
{
   Node *temp = (Node *)malloc(sizeof(Node));
   if (temp == NULL) {
      perror("Failed to alloc node");
      exit(EXIT_FAILURE);
   }
   temp->key        = bitset_copy(a);
   temp->left       = NULL;
   temp->right      = NULL;
   temp->pathParent = parent;
   temp->height     = 1;
   temp->from       = from;
   temp->to         = to;
   temp->refs       = 0;
   if (parent != NULL) {
      parent->refs++;
   }
   return temp;
}

Node *tree_minValueNode(Node *node)
{
   Node *current = node;
   while (current->left != NULL)
      current = current->left;
   return current;
}

Node **tree_inserAllNodes(Node **allNodes, Node *node, uint64_t *index)
{
   if (node == NULL)
      return allNodes;
   allNodes[*index] = node;
   (*index)++;
   tree_inserAllNodes(allNodes, node->left, index);
   tree_inserAllNodes(allNodes, node->right, index);
   return allNodes;
}

Node **tree_allNodes(Node *node, uint32_t number)
{
   Node    **allNodes = (Node **)malloc(sizeof(Node *) * number);
   uint64_t *index    = (uint64_t *)malloc(sizeof(uint64_t));
   *index             = 0;
   Node **all         = tree_inserAllNodes(allNodes, node, index);
   free(index);
   return all;
}

uint64_t tree_size(Node *node)
{
   uint32_t count = 0;
   if (node == NULL)
      return 0;
   count += tree_size(node->left);
   count += tree_size(node->right);
   return count + 1;
}

Node *tree_contained(Node *node, Bitset *a)
{
   if (node == NULL)
      return NULL;
   int8_t r = bitset_compare(a, (node)->key);
   if (r == 0)
      return node;
   if (r < 0)
      return tree_contained(node->left, a);
   else
      return tree_contained(node->right, a);
}

Node *_tree_delete(Node *node, Bitset *a)
{
   if (node == NULL)
      return node;
   if (bitset_compare(a, node->key) < 0)
      node->left = _tree_delete(node->left, a);
   else if (bitset_compare(a, node->key) > 0)
      node->right = _tree_delete(node->right, a);
   else {
      if ((node->left == NULL) || (node->right == NULL)) {
         Node *temp = node->left ? node->left : node->right;
         if (temp == NULL) {
            node = NULL;
            free(node);
         } else {
            *node = *temp;
            free(temp);
         }
      } else { // node has two children
         Node *temp       = tree_minValueNode(node->right);
         node->key        = temp->key;
         node->pathParent = temp->pathParent;
         node->refs       = temp->refs;
         node->from       = temp->from;
         node->to         = temp->to;
         node->right      = _tree_delete(node->right, temp->key);
      }
   }
   // Skipped: Update balance factor of each node and balance tree
   return node;
}

Node *tree_delete(Node *node, Bitset *a, Node **result, uint32_t level)
{
   if (node == NULL || a == NULL)
      return node;
   if (bitset_compare(a, node->key) < 0)
      node->left = tree_delete(node->left, a, result, level);
   else if (bitset_compare(a, node->key) > 0)
      node->right = tree_delete(node->right, a, result, level);
   else {
      // Recursion!
      if (node->pathParent != NULL) {
         (node->pathParent)->refs--;
         if ((node->pathParent)->refs == 0 && level > 2) {
            result[level - 1] = tree_delete(result[level - 1], (node->pathParent)->key,
                                            result, level - 1);
         }
      }

      if ((node->left == NULL) || (node->right == NULL)) {
         Node *temp = node->left ? node->left : node->right;
         if (temp == NULL) {
            temp = node;
            node = NULL;
         } else {
            node->key        = temp->key;
            node->left       = temp->left;
            node->right      = temp->right;
            node->pathParent = temp->pathParent;
            node->height     = temp->height;
            node->refs       = temp->refs;
         }
         if (temp != NULL) {
            free(temp);
         }
      } else { // node has two children
         Node *temp  = tree_minValueNode(node->right);
         node->key   = temp->key;
         node->right = _tree_delete(node->right, temp->key);
      }
   }
   // Skipped: Update balance factor of each node and balance tree
   return node;
}

Node *tree_insert(Node *node, Bitset *a, uint32_t *count, uint16_t from, uint16_t to,
                  Node *vor)
{
   if (node == NULL) {
      (*count)++;
      return tree_newNode(a, from, to, vor);
   }
   // Recur down the tree
   if (bitset_compare(a, node->key) < 0) {
      node->left = tree_insert(node->left, a, count, from, to, vor);
   } else {
      if (bitset_compare(a, node->key) > 0) {
         node->right = tree_insert(node->right, a, count, from, to, vor);
      } else
         return node;
   }
   // Update the balance factor of each node and balance the tree
   node->height    = 1 + max(tree_height(node->left), tree_height(node->right));
   int16_t balance = tree_getBalance(node);
   if (balance > 1 && (bitset_compare(a, node->left->key) < 0))
      return tree_rightRotate(node);

   if (balance < -1 && (bitset_compare(a, node->right->key) > 0))
      return tree_leftRotate(node);

   if (balance > 1 && (bitset_compare(a, node->left->key) > 0)) {
      node->left = tree_leftRotate(node->left);
      return tree_rightRotate(node);
   }

   if (balance < -1 && (bitset_compare(a, node->right->key) < 0)) {
      node->right = tree_rightRotate(node->right);
      return tree_leftRotate(node);
   }
   return node;
}

void tree_free(Node *node)
{
   if (node != NULL) {
      tree_free(node->left);
      tree_free(node->right);
      bitset_free(node->key);
      free(node);
   }
}

Node *tree_getLeftMost(Node *node)
{
   if (node == NULL)
      return NULL;
   while (node->left != NULL)
      node = node->left;
   return node;
}

bool node_insert(Node_list **list, Node *node)
{
   uint64_t x = *list ? list[0]->size : 0;
   uint64_t y = x + 1;
   if ((x & y) == 0) { // x is power of 2
      void *temp = realloc(*list, sizeof(**list) + (x + y) * sizeof list[0]->value[0]);
      if (temp == NULL)
         return false;
      *list = temp;
   }
   list[0]->value[x] = node;
   list[0]->size     = y;
   return true;
}

uint64_t prune(Node_list **list)
{
   uint64_t l = 0;
   if (*list == NULL)
      return l;
   for (uint64_t i = 0; i < (*list)->size; i++) {
      Node *node = (*list)->value[i];
      while (node != NULL && node->refs == 0) {
         Node *temp = node;
         node       = node->pathParent;
         if (node != NULL) {
            node->refs--;
         }
         bitset_free(temp->key);
         free(temp);
         temp = NULL;
         l++;
      }
   }
   free(*list);
   *list = NULL;
   return l;
}
