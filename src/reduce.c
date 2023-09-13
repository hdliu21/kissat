#include "reduce.h"
#include "allocate.h"
#include "collect.h"
#include "inline.h"
#include "print.h"
#include "rank.h"
#include "report.h"
#include "trail.h"

#include <inttypes.h>
#include <math.h>


#include "inline.h"

#include <inttypes.h>

static void dump_literal (kissat *solver, unsigned ilit) {
  const int elit = kissat_export_literal (solver, ilit);
  printf ("%d", elit);
  // const int value = VALUE (ilit);
  // if (value) {
  //   const unsigned ilit_level = LEVEL (ilit);
  //   printf ("@%u=%d", ilit_level, value);
  // }
}

static void dump_binary (kissat *solver, unsigned a, unsigned b) {
  printf ("binary clause ");
  dump_literal (solver, a);
  fputc (' ', stdout);
  dump_literal (solver, b);
  fputc ('\n', stdout);
}

void dump_clause (kissat *solver, clause *c) {
  if (c->redundant)
    printf ("redundant glue %u", c->glue);
  else
    printf ("irredundant");
  const reference ref = kissat_reference_clause (solver, c);
  if (c->garbage)
    printf (" garbage");
  printf (" clause[%u]", ref);
  printf("redundant clause: ");
  for (all_literals_in_clause (lit, c)) {
    fputc (' ', stdout);
    dump_literal (solver, lit);
  }
  fputc ('\n', stdout);
}

static void dump_ref (kissat *solver, reference ref) {
  clause *c = kissat_dereference_clause (solver, ref);
  dump_clause (solver, c);
}

static void dump_trail (kissat *solver) {
  unsigned prev = 0;
  for (unsigned level = 0; level <= solver->level; level++) {
    frame *frame = &FRAME (level);
    unsigned next;
    if (level < solver->level)
      next = frame[1].trail;
    else
      next = SIZE_ARRAY (solver->trail);
    if (next == prev)
      printf ("frame[%u] has no assignments\n", level);
    else {
      printf ("frame[%u] has %u assignments\n", level, next - prev);
      if (prev < next)
        printf ("block[%u] = trail[%u..%u]\n", level, prev, next - 1);
    }
    for (unsigned i = prev; i < next; i++) {
      printf ("trail[%u] ", i);
      const unsigned lit = PEEK_ARRAY (solver->trail, i);
      dump_literal (solver, lit);
      const unsigned lit_level = LEVEL (lit);
      assert (lit_level <= level);
      if (lit_level < level)
        printf (" out-of-order");
      assigned *a = ASSIGNED (lit);
      if (!lit_level) {
        printf (" UNIT\n");
        assert (!a->binary);
        assert (a->reason == UNIT_REASON);
      } else {
        fputc (' ', stdout);
        if (a->binary) {
          const unsigned other = a->reason;
          dump_binary (solver, lit, other);
        } else if (a->reason == DECISION_REASON)
          printf ("DECISION\n");
        else {
          assert (a->reason != UNIT_REASON);
          const reference ref = a->reason;
          dump_ref (solver, ref);
        }
      }
    }
    prev = next;
  }
}

static void dump_values (kissat *solver) {
  for (unsigned idx = 0; idx < VARS; idx++) {
    unsigned lit = LIT (idx);
    int value = solver->values[lit];
    printf ("val[%u] = ", lit);
    if (!value)
      printf ("unassigned\n");
    else
      printf ("%d\n", value);
  }
}

static void dump_queue (kissat *solver) {
  const queue *const queue = &solver->queue;
  printf ("queue: first %u, last %u, stamp %u, search %u (stamp %u)\n",
          queue->first, queue->last, queue->stamp, queue->search.idx,
          queue->search.stamp);
  const links *const links = solver->links;
  for (unsigned idx = queue->first; !DISCONNECTED (idx);
       idx = links[idx].next) {
    const struct links *l = links + idx;
    printf ("%u ( prev %u, next %u, stamp %u )\n", idx, l->prev, l->next,
            l->stamp);
  }
}

static void dump_scores (kissat *solver) {
  heap *heap = SCORES;
  printf ("scores.vars = %u\n", heap->vars);
  printf ("scores.size = %u\n", heap->size);
  for (unsigned i = 0; i < SIZE_STACK (heap->stack); i++)
    printf ("scores.stack[%u] = %u\n", i, PEEK_STACK (heap->stack, i));
  for (unsigned i = 0; i < heap->vars; i++)
    printf ("scores.score[%u] = %g\n", i, heap->score[i]);
  for (unsigned i = 0; i < heap->vars; i++)
    printf ("scores.pos[%u] = %u\n", i, heap->pos[i]);
}

static void dump_export (kissat *solver) {
  const unsigned size = SIZE_STACK (solver->export);
  for (unsigned idx = 0; idx < size; idx++)
    printf ("export[%u] = %u\n", LIT (idx),
            PEEK_STACK (solver->export, idx));
}

void dump_map (kissat *solver) {
  const unsigned size = SIZE_STACK (solver->export);
  unsigned first = INVALID_LIT;
  for (unsigned idx = 0; idx < size; idx++) {
    const unsigned ilit = LIT (idx);
    const int elit = PEEK_STACK (solver->export, idx);
    printf ("map[%u] -> %d", ilit, elit);
    if (elit) {
      const unsigned eidx = ABS (elit);
      const import *const import = &PEEK_STACK (solver->import, eidx);
      if (import->eliminated)
        printf (" -> eliminated[%u]", import->lit);
      else {
        unsigned mlit = import->lit;
        if (elit < 0)
          mlit = NOT (mlit);
        printf (" -> %u", mlit);
      }
    }
    if (!LEVEL (ilit) && VALUE (ilit)) {
      if (first == INVALID_LIT) {
        first = ilit;
        printf (" #");
      } else
        printf (" *");
    }
    fputc ('\n', stdout);
  }
}

static void dump_import (kissat *solver) {
  const unsigned size = SIZE_STACK (solver->import);
  for (unsigned idx = 1; idx < size; idx++) {
    import *import = &PEEK_STACK (solver->import, idx);
    printf ("import[%u] = ", idx);
    if (!import->imported)
      printf ("undefined\n");
    else if (import->eliminated) {
      unsigned pos = import->lit;
      printf ("eliminated[%u]", pos);
      if (pos < SIZE_STACK (solver->eliminated)) {
        int value = PEEK_STACK (solver->eliminated, pos);
        if (value)
          printf (" (assigned to %d)", value);
      }
      fputc ('\n', stdout);
    } else
      printf ("%u\n", import->lit);
  }
}

static void dump_etrail (kissat *solver) {
  for (unsigned i = 0; i < SIZE_STACK (solver->etrail); i++)
    printf ("etrail[%u] = %d\n", i, (int) PEEK_STACK (solver->etrail, i));
}

static void dump_extend (kissat *solver) {
  const extension *const begin = BEGIN_STACK (solver->extend);
  const extension *const end = END_STACK (solver->extend);
  for (const extension *p = begin, *q; p != end; p = q) {
    assert (p->blocking);
    printf ("extend[%zu] %d", (size_t) (p - begin), p->lit);
    if (!p[1].blocking)
      fputs (" :", stdout);
    for (q = p + 1; q != end && !q->blocking; q++)
      printf (" %d", q->lit);
    fputc ('\n', stdout);
  }
}

static void dump_binaries (kissat *solver) {
  for (all_literals (lit)) {
    if (solver->watching) {
      for (all_binary_blocking_watches (watch, WATCHES (lit))) {
        if (!watch.type.binary)
          continue;
        const unsigned other = watch.binary.lit;
        if (lit > other)
          continue;
        dump_binary (solver, lit, other);
      }
    } else {
      for (all_binary_large_watches (watch, WATCHES (lit))) {
        if (!watch.type.binary)
          continue;
        const unsigned other = watch.binary.lit;
        if (lit > other)
          continue;
        dump_binary (solver, lit, other);
      }
    }
  }
}

static void dump_clauses (kissat *solver) {
  for (all_clauses (c))
    dump_clause (solver, c);
}

void dump_vectors (kissat *solver) {
  vectors *vectors = &solver->vectors;
  unsigneds *stack = &vectors->stack;
  printf ("vectors.size = %zu\n", SIZE_STACK (*stack));
  printf ("vectors.capacity = %zu\n", CAPACITY_STACK (*stack));
  printf ("vectors.usable = %zu\n", vectors->usable);
  const unsigned *const begin = BEGIN_STACK (*stack);
  const unsigned *const end = END_STACK (*stack);
  if (begin == end)
    return;
  fputc ('-', stdout);
  for (const unsigned *p = begin + 1; p != end; p++)
    if (*p == INVALID_LIT)
      fputs (" -", stdout);
    else
      printf (" %u", *p);
  fputc ('\n', stdout);
}

int dump (kissat *solver) {
  if (!solver)
    return 0;
  printf ("vars = %u\n", solver->vars);
  printf ("size = %u\n", solver->size);
  printf ("level = %u\n", solver->level);
  printf ("active = %u\n", solver->active);
  printf ("assigned = %u\n", kissat_assigned (solver));
  printf ("unassigned = %u\n", solver->unassigned);
  dump_import (solver);
  dump_export (solver);
#ifdef LOGGING
  if (solver->compacting)
    dump_map (solver);
#endif
  dump_etrail (solver);
  dump_extend (solver);
  dump_trail (solver);
  printf ("stable = %u\n", (unsigned) solver->stable);
  if (solver->stable)
    dump_scores (solver);
  else
    dump_queue (solver);
  dump_values (solver);
  printf ("binary = %" PRIu64 "\n", solver->statistics.clauses_binary);
  printf ("irredundant = %" PRIu64 "\n",
          solver->statistics.clauses_irredundant);
  printf ("redundant = %" PRIu64 "\n",
          solver->statistics.clauses_redundant);
  dump_binaries (solver);
  dump_clauses (solver);
  dump_extend (solver);
  return 0;
}

bool kissat_reducing (kissat *solver) {
  if (!GET_OPTION (reduce))
    return false;
  if (!solver->statistics.clauses_redundant)
    return false;
  if (CONFLICTS < solver->limits.reduce.conflicts)
    return false;
  return true;
}
//void dump_clause (kissat *solver, clause *c);
void my_print_clause(clause* c){
  printf("reducibale clause: ");
  for(unsigned i = 0; i < c->size; ++i){
    unsigned lit = c->lits[i] ;
    bool sign = lit & 1u;
    unsigned idx = lit >> 1;
    if (idx == 0) {
      printf("lit is %u", lit);
      exit(0);
    }
    char c = sign ? '-' : '+';
    printf("%c%u ", c , idx);
  }
  printf("\n");
}

typedef struct reducible reducible;

struct reducible {
  uint64_t rank;
  unsigned ref;
};

#define RANK_REDUCIBLE(RED) (RED).rank

// clang-format off
typedef STACK (reducible) reducibles;
// clang-format on
// int myArray[] = {630, 10828, 68, 140, 980, 18610, 115116, 96010, 90101, 4581, 6185, 3359, 166, 97505, 138958, 241, 15761, 3894, 558, 120, 10271, 6267, 30563, 112, 100, 221, 3030, 8183, 165, 100, 282, 3382, 9345, 3153, 78618, 121424, 109, 570, 27856, 3819, 86739, 95655, 1659, 95341, 150402, 82156, 119311, 515, 6097, 586, 147981, 157, 117807, 13282, 2345, 389, 98846, 83824, 2841, 96219, 8496, 228, 766, 122605, 83683, 667, 9111, 5770, 485, 112947, 452, 4803, 2799, 7302, 80458, 7203, 121045, 1080, 2905, 268, 235, 7287, 8697, 17403, 3067, 306, 4804, 97849, 279, 60426, 668, 66, 120988, 88863, 309, 2184, 80, 127286, 2904};
int myArray[] = {45289,40338,38644,35790,36363,42548,42638,16637,42435,15968,40544,30744,40448,38592,14515,39534,39573,41461,40000,40036,38813,9979,42505,40122,41432,37256,43715,41894,40221,16628,41988,40595,41194,41771,37135,41736,37634,39626,38914,40811,40472,36059,44200,41243,39998,38741,39140,42825,39961,41432,45746,38243,41510,39966,36105,36874,36999,36696,38263,40424,40700,33788,41581,36762,40808,15732,40639,15985,36567,14180,38698,40986,44236,44682,41598,40997,43578,39620,37715,15138,17095,42751,40130,41723,41680,42823,34875,39893,40049,34729,37673,37955,38360,15481,34237,47434,40410,43631,39830,42485,41795,38427,44145,17265,16851,41237,40540,42167,41801,31579,37898,43062,43650,50451,16047,41519,38917,45139,39864,41786,36251,35907,40497,44759,39158,42893,16376,43157,42014,39672,15471,39960,14472,39987,40031,42730,43221,39544,36490,39464,42411,41029,40298,37023,41744,38602,34848,40363,41070,40256,33363,41542,13964,42744,37429,41626,40523,18335,43247,41949,40659,44020,15979,44082,40221,14930,40124,36511,14466,42111,37298,43005,38402,37624,38359,14425,41083,36705,17212,36735,14973,45182,39422,42647,35657,43565,41317,36734,41123,41166,36290,39842,45036,35626,35997,38434,42222,14178,39541,35693,43709,14968,45105,41911,38095,42789,39942,37066,42535,41008,39151,40352,38157,39265,40462,43398,36782,37304,36422,17180,41413,40811,45794,16143,38855,44071,41218,41574,15841,38333,39002,16176,39273,42300,35901,34523,15415,40791,42850,16970,40157,39605,15347,43791,35644,38854,39115,33656,42562,36366,38114,43309,14695,44260,42195,44050,36653,40457,37313,39893,42513,40932,42264,42531,43820,39599,38958,39062,16059,40672,40141,38341,35733,45956,44622,44548,41141,39088,38759,40200,40388,40211,37765,34781,38645,45303,43541,40489,41398,39037,38632,15647,39390,40396,42574,41057,45239,42644,43398,34816,41069,42193,37771,15484,41272,39842,40798,32442,38413,41851,31693,15585,41292,43661,38706,40209,38199,39673,17626,40599};
static bool collect_reducibles (kissat *solver, reducibles *reds,
                                reference start_ref) {
  assert (start_ref != INVALID_REF);
  assert (start_ref <= SIZE_STACK (solver->arena));
  ward *const arena = BEGIN_STACK (solver->arena);
  clause *start = (clause *) (arena + start_ref);
  const clause *const end = (clause *) END_STACK (solver->arena);
  assert (start < end);
  while (start != end && (!start->redundant || start->keep))
    start = kissat_next_clause (start);
  if (start == end) {
    solver->first_reducible = INVALID_REF;
    LOG ("no reducible clause candidate left");
    return false;
  }
  const reference redundant = (ward *) start - arena;
#ifdef LOGGING
  if (redundant < solver->first_reducible)
    LOG ("updating redundant clauses start from %zu to %zu",
         (size_t) solver->first_reducible, (size_t) redundant);
  else
    LOG ("no update to redundant clauses start %zu",
         (size_t) solver->first_reducible);
#endif
  solver->first_reducible = redundant;
  const unsigned tier2 = GET_OPTION (tier2);
  for (clause *c = start; c != end; c = kissat_next_clause (c)) {
    if (!c->redundant)
      continue;
    if (c->garbage)
      continue;
    if (c->reason)
      continue;
    if (c->keep)
      continue;
    if (c->used) {
      c->used--;
      if (c->glue <= tier2)
        continue;
    }
    assert (!c->garbage);
    assert (kissat_clause_in_arena (solver, c));
    reducible red;
    // int importance = 0;
    // for (all_literals_in_clause (lit, c)){
    //   int elit = kissat_export_literal(solver, lit);
    //   if (elit < 0) elit = -elit;
    //   importance += myArray[elit-1];
    // }
    // importance = importance / c->size;
    const uint64_t negative_size = ~c->size;
    const uint64_t negative_glue = ~c->glue;
    // red.rank = negative_size  | (negative_glue << 32) ;
    red.rank = negative_size  | (negative_glue << 32) ;
    //red.rank = importance;
    red.ref = (ward *) c - arena;
    // my_print_clause(c);
    // dump_clause(solver, c);
    PUSH_STACK (*reds, red);
  }
  if (EMPTY_STACK (*reds)) {
    LOG ("did not find any reducible redundant clause");
    return false;
  }
  return true;
}

#define USEFULNESS RANK_REDUCIBLE

static void sort_reducibles (kissat *solver, reducibles *reds) {
  RADIX_STACK (reducible, uint64_t, *reds, USEFULNESS);
}

static void mark_less_useful_clauses_as_garbage (kissat *solver,
                                                 reducibles *reds) {
  const size_t size = SIZE_STACK (*reds);
  double fraction = GET_OPTION (reducefraction) / 100.0;
  size_t target = size * fraction;
#ifndef QUIET
  statistics *statistics = &solver->statistics;
  const size_t clauses =
      statistics->clauses_irredundant + statistics->clauses_redundant;
  kissat_phase (solver, "reduce", GET (reductions),
                "reducing %zu (%.0f%%) out of %zu (%.0f%%) "
                "reducible clauses",
                target, kissat_percent (target, size), size,
                kissat_percent (size, clauses));
#endif
  unsigned reduced = 0;
  ward *arena = BEGIN_STACK (solver->arena);
  const reducible *const begin = BEGIN_STACK (*reds);
  const reducible *const end = END_STACK (*reds);
  for (const reducible *p = begin; p != end && target--; p++) {
    clause *c = (clause *) (arena + p->ref);
    assert (kissat_clause_in_arena (solver, c));
    assert (!c->garbage);
    assert (!c->keep);
    assert (!c->reason);
    assert (c->redundant);
    LOGCLS (c, "reducing");
    kissat_mark_clause_as_garbage (solver, c);
    reduced++;
  }
  ADD (clauses_reduced, reduced);
}

static bool compacting (kissat *solver) {
  if (!GET_OPTION (compact))
    return false;
  unsigned inactive = solver->vars - solver->active;
  unsigned limit = GET_OPTION (compactlim) / 1e2 * solver->vars;
  bool compact = (inactive > limit);
  LOG ("%u inactive variables %.0f%% <= limit %u %.0f%%", inactive,
       kissat_percent (inactive, solver->vars), limit,
       kissat_percent (limit, solver->vars));
  return compact;
}

int kissat_reduce (kissat *solver) {
  START (reduce);
  INC (reductions);
  kissat_phase (solver, "reduce", GET (reductions),
                "reduce limit %" PRIu64 " hit after %" PRIu64 " conflicts",
                solver->limits.reduce.conflicts, CONFLICTS);
  bool compact = compacting (solver);
  reference start = compact ? 0 : solver->first_reducible;
  if (start != INVALID_REF) {
#ifndef QUIET
    size_t arena_size = SIZE_STACK (solver->arena);
    size_t words_to_sweep = arena_size - start;
    size_t bytes_to_sweep = sizeof (word) * words_to_sweep;
    kissat_phase (solver, "reduce", GET (reductions),
                  "reducing clauses after offset %" REFERENCE_FORMAT
                  " in arena",
                  start);
    kissat_phase (solver, "reduce", GET (reductions),
                  "reducing %zu words %s %.0f%%", words_to_sweep,
                  FORMAT_BYTES (bytes_to_sweep),
                  kissat_percent (words_to_sweep, arena_size));
#endif
    if (kissat_flush_and_mark_reason_clauses (solver, start)) {
      reducibles reds;
      INIT_STACK (reds);
      if (collect_reducibles (solver, &reds, start)) {
        sort_reducibles (solver, &reds);
        mark_less_useful_clauses_as_garbage (solver, &reds);
        RELEASE_STACK (reds);
        kissat_sparse_collect (solver, compact, start);
      } else if (compact)
        kissat_sparse_collect (solver, compact, start);
      else
        kissat_unmark_reason_clauses (solver, start);
    } else
      assert (solver->inconsistent);
  } else
    kissat_phase (solver, "reduce", GET (reductions), "nothing to reduce");
  UPDATE_CONFLICT_LIMIT (reduce, reductions, SQRT, false);
  REPORT (0, '-');
  STOP (reduce);
  return solver->inconsistent ? 20 : 0;
}
