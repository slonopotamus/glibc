/* Sort array of link maps according to dependencies.
   Copyright (C) 2017-2019 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */

#include <ldsodefs.h>

struct double_stack
{
  int *items;
  int nitems;
  int fp;
  int bp;
};

static void
_ds_init (struct double_stack *ds, int *items, int nitems)
{
  ds->items = items;
  ds->nitems = nitems;
  ds->fp = 0;
  ds->bp = nitems;
}

static bool
_ds_is_empty_front (struct double_stack *ds)
{
  return ds->fp == 0;
}

static int
_ds_top_front (struct double_stack *ds)
{
  return ds->items[ds->fp - 1];
}

static bool
_ds_pop_front (struct double_stack *ds)
{
  return ds->items[--ds->fp];
}

static void
_ds_push_front (struct double_stack *ds, int item)
{
  ds->items[ds->fp++] = item;
}

static bool
_ds_is_empty_back (struct double_stack *ds)
{
  return ds->bp == ds->nitems;
}

static int
_ds_top_back (struct double_stack *ds)
{
  return ds->items[ds->bp];
}

static bool
_ds_pop_back (struct double_stack *ds)
{
  return ds->items[ds->bp++];
}

static void
_ds_push_back (struct double_stack *ds, int item)
{
  ds->items[--ds->bp] = item;
}

/* Performs stable counting sort of MAPS array according to indices in RINDEX.
 * Runs in O(nmaps) time, uses O(nmaps) memory on stack.
 * Reference: https://en.wikipedia.org/wiki/Counting_sort */
static void
_dl_counting_sort_maps (struct link_map **maps, unsigned int nmaps,
                        int *rindex)
{
  int count[nmaps];

  memset (count, 0, nmaps * sizeof (count[0]));

  for (int i = 0; i < nmaps; ++i)
    {
      ++count[rindex[i]];
    }

  for (int i = 1; i < nmaps; ++i)
    {
      count[i] += count[i - 1];
    }

  struct link_map *maps_copy[nmaps];
  memcpy (&maps_copy, maps, nmaps * sizeof (maps_copy[0]));

  for (int i = 0; i < nmaps; ++i)
    {
      int cindex = rindex[i];
      maps[count[cindex] - 1] = maps_copy[i];
      --count[cindex];
    }
}

static int
_dl_sort_dep_func (const void *a, const void *b)
{
  const struct link_map *const *lhs = a;
  const struct link_map *const *rhs = b;

  // Note, reverse order
  return (*lhs)->l_idx - (*rhs)->l_idx;
}

/** Reverse-sorts deps according to maps index by using qsort_r */
static void
_dl_sort_deps (struct link_map **maps, struct link_map **deps)
{
  int num_edges = 0;
  for (struct link_map **dep = deps; *dep; ++dep)
    {
      ++num_edges;
    }

  qsort (deps, num_edges, sizeof (*deps), _dl_sort_dep_func);
}

struct pea_scc
{
  struct link_map **maps;
  unsigned int nmaps;
  int *rindex;
  struct double_stack vS;
  struct double_stack iS;
  bool *root;
  int index;
  int c;

  bool with_reldeps;
};

static void
_pea_scc_begin_visiting (struct pea_scc *pea_scc, int v)
{
  // First time this node encountered
  _ds_push_front (&pea_scc->vS, v);
  _ds_push_front (&pea_scc->iS, 0);
  pea_scc->root[v] = true;
  pea_scc->rindex[v] = pea_scc->index;
  ++pea_scc->index;
}

static void
_pea_scc_finish_visiting (struct pea_scc *pea_scc, int v)
{
  // Take this vertex off the call stack
  _ds_pop_front (&pea_scc->vS);
  _ds_pop_front (&pea_scc->iS);
  // Update component information
  if (pea_scc->root[v])
    {
      --pea_scc->index;
      while (!_ds_is_empty_back (&pea_scc->vS)
             && pea_scc->rindex[v]
                    <= pea_scc->rindex[_ds_top_back (&pea_scc->vS)])
        {
          int w = _ds_pop_back (&pea_scc->vS);
          pea_scc->rindex[w] = pea_scc->c;
          --pea_scc->index;
        }
      pea_scc->rindex[v] = pea_scc->c;
      --pea_scc->c;
    }
  else
    {
      _ds_push_back (&pea_scc->vS, v);
    }
}

static bool
_pea_scc_begin_edge (struct pea_scc *pea_scc, int v, int k)
{
  /* int w = (k < graph[v].staticDependencies.size ()
               ? graph[v].staticDependencies.get (k)
               : graph[v].dynamicDependencies.get (
                     k - graph[v].staticDependencies.size ()))
              .index;
        */

  int w = pea_scc->maps[v]->l_initfini[k]->l_idx;

  if (pea_scc->rindex[w] == 0)
    {
      _ds_pop_front (&pea_scc->iS);
      _ds_push_front (&pea_scc->iS, k + 1);
      _pea_scc_begin_visiting (pea_scc, w);
      return true;
    }
  else
    {
      return false;
    }
}

static void
_pea_scc_finish_edge (struct pea_scc *pea_scc, int v, int k)
{
  /* int w = (k < graph[v].staticDependencies.size ()
               ? graph[v].staticDependencies.get (k)
               : graph[v].dynamicDependencies.get (
                     k - graph[v].staticDependencies.size ()))
              .index;
        */

  int w = pea_scc->maps[v]->l_initfini[k]->l_idx;

  if (pea_scc->rindex[w] < pea_scc->rindex[v])
    {
      pea_scc->rindex[v] = pea_scc->rindex[w];
      pea_scc->root[v] = false;
    }
}

static void
_pea_scc_visit_loop (struct pea_scc *pea_scc)
{
  int v = _ds_top_front (&pea_scc->vS);
  int i = _ds_top_front (&pea_scc->iS);

  int num_edges = 0;
  for (struct link_map **dep = pea_scc->maps[v]->l_initfini; *dep; ++dep)
    {
      ++num_edges;
    }

  /*if (pea_scc->with_reldeps)
    num_edges += graph[v].dynamicDependencies.size (); */

  // Continue traversing out-edges until none left.
  while (i <= num_edges)
    {
      // Continuation
      if (i > 0)
        {
          // Update status for previously traversed out-edge
          _pea_scc_finish_edge (pea_scc, v, i - 1);
        }
      if (i < num_edges && _pea_scc_begin_edge (pea_scc, v, i))
        {
          return;
        }
      i = i + 1;
    }

  // Finished traversing out edges, update component info
  _pea_scc_finish_visiting (pea_scc, v);
}

static void
_pea_scc_visit (struct pea_scc *pea_scc, int v)
{
  _pea_scc_begin_visiting (pea_scc, v);

  while (!_ds_is_empty_front (&pea_scc->vS))
    {
      _pea_scc_visit_loop (pea_scc);
    }
}

/* Populates RINDEX array with strongly connected component number of
 * corresponding element in MAPS array. Based on 'PEA_FIND_SCC3' algorithm from
 * "A Space-Efficient Algorithm for Finding Strongly Connected Components" by
 * David J. Pearce.
 * Algorithm itself runs in O(|V| + |e|) time but requires additional qsort on
 * both vertices and edges in order to maintain stable order. Uses O(nmaps)
 * memory on stack.
 */
static void
_pea_scc (struct link_map **maps, unsigned int nmaps, int *rindex,
          bool with_reldeps)
{
  bool root[nmaps];
  memset (root, 0, nmaps * sizeof (root[0]));

  int vS[nmaps];
  int iS[nmaps];

  struct pea_scc pea_scc;
  pea_scc.maps = maps;
  pea_scc.nmaps = nmaps;
  pea_scc.rindex = rindex;
  pea_scc.index = 1;
  pea_scc.c = nmaps - 1;

  _ds_init (&pea_scc.vS, vS, nmaps);
  _ds_init (&pea_scc.iS, iS, nmaps);
  pea_scc.root = root;

  pea_scc.with_reldeps = with_reldeps;

  // 1. Reverse maps. O(nmaps)
  for (int i = 0, mid = nmaps >> 1, j = nmaps - 1; i < mid; i++, j--)
    {
      struct link_map *tmp = maps[i];
      maps[i] = maps[j];
      maps[j] = tmp;
    }

  // 2. Assign indices for stable sort. O(nmaps)
  for (int i = 0; i < nmaps; ++i)
    {
      maps[i]->l_idx = i;
    }

  // 3.1. Sort static deps according to maps indices.
  for (int i = 0; i != nmaps; ++i)
    {
      _dl_sort_deps (maps, maps[i]->l_initfini);
    }

  // 3.2. Sort reldeps according to maps indices
  if (__glibc_unlikely (with_reldeps))
    {

      for (int i = 0; i < nmaps; ++i)
        {
          _dl_sort_deps (maps, maps[i]->l_reldeps->list);
        }
    }

  // 4. Perform PeaSCC
  for (int i = 0; i != nmaps; ++i)
    {
      if (rindex[i] == 0)
        {
          _pea_scc_visit (&pea_scc, i);
        }
    }
}

static void
_dl_sort_maps_pass (struct link_map **maps, unsigned int nmaps,
                    bool with_reldeps)
{
  int rindex[nmaps];
  memset (rindex, 0, nmaps * sizeof (rindex[0]));

  // 1. Calculate rindex
  _pea_scc (maps, nmaps, rindex, with_reldeps);

  // 2. Sort maps according to rindex. O(nmaps)
  _dl_counting_sort_maps (maps, nmaps, rindex);
}

/* Sort array MAPS according to dependencies of the contained objects.
   Array USED, if non-NULL, is permutated along MAPS.  If FOR_FINI this is
   called for finishing an object.  */
void
_dl_sort_maps (struct link_map **maps, unsigned int nmaps, char *used,
               bool for_fini)
{
  /* A list of one element need not be sorted.  */
  if (nmaps <= 1)
    return;

  if (__glibc_unlikely (for_fini))
    {
      // First pass, sort on both static and dynamic deps
      _dl_sort_maps_pass (maps, nmaps, true);
    }

  // Second pass, sort only on static deps
  _dl_sort_maps_pass (maps, nmaps, false);
}
