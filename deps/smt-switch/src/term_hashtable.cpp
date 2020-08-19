/*********************                                                        */
/*! \file term_hashtable.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief A simple hash table for terms -- used for hash-consing in
** LoggingSolver
**
**
**/

#include "term_hashtable.h"

using namespace std;

namespace smt {

/* TermHashTable */

TermHashTable::TermHashTable() {}

TermHashTable::~TermHashTable() {}

void TermHashTable::insert(const Term & t) { table[t->hash()].insert(t); }

bool TermHashTable::lookup(Term & t)
{
  size_t hashval = t->hash();
  if (table.find(hashval) != table.end()
      && table[hashval].find(t) != table[hashval].end())
  {
    // reassign t
    // should destroy the previous Term
    // when reference counter goes to zero
    t = *(table[hashval].find(t));
    return true;
  }
  return false;
}

void TermHashTable::erase(const Term & t)
{
  size_t hashval = t->hash();
  if (table.find(hashval) != table.end()
      && table[hashval].find(t) != table[hashval].end())
  {
    table[hashval].erase(t);
  }
}

void TermHashTable::clear() { table.clear(); }

}  // namespace smt
