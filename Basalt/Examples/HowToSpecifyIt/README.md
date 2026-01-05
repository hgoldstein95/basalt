# *How to Specify It* Case Study 

This directory contains a Lean 4 port of the *How to Specify It* case study, 
originally implemented in Haskell by John Hughes.

## Overview

The case study includes:
- **BST.lean**: The base BST type definition and common utilities
- **BST0.lean**: correct BST implementation
- **BST1.lean - BST8.lean**: Eight buggy BST implementations

## Bug Descriptions

Based on John Hughes's paper [*How to Specify It* (TFP '19)](https://research.chalmers.se/publication/517894/file/517894_Fulltext.pdf):

1. **BST1**: `insert` discards the existing tree, returning a single-node tree just containing the newly inserted value
2. **BST2**: `insert` fails to recognize and update an existing key, inserting a duplicate entry instead
3. **BST3**: `insert` fails to update an existing key, leaving the tree unchanged instead
4. **BST4**: `delete` fails to rebuild the tree above the key being deleted, returning only the remainder of the tree from that point on
5. **BST5**: Key comparisons reversed in `delete`; only works correctly at the root of the tree
6. **BST6**: `union` wrongly assumes that all the keys in the first argument precede those in the second
7. **BST7**: `union` wrongly assumes that if the key at the root of the first tree is smaller than the key at the root of the second tree, then all keys in the first tree will be smaller than the root key of the second tree
8. **BST8**: `union` works correctly, except that when both trees contain the same key, the left argument does not always take priority

## Structure

All implementations follow the same interface with the following operations:
- `nil`: Empty BST
- `insert`: Insert a key-value pair
- `delete`: Delete a key
- `union`: Merge two BSTs (left has priority for duplicate keys)
- `find`: Look up a value by key (defined in BST.lean)
- `toList`: Convert to list via in-order traversal (defined in BST.lean)
- `keys`: Get all keys (defined in BST.lean)
- `size`: Get the number of keys (defined in BST.lean)

This code is based on https://github.com/rjmh/how-to-specify-it/
