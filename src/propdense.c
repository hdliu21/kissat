#include "propdense.h"
#include "fastassign.h"
#include "global.h"

static inline bool non_watching_propagate_literal (kissat *solver,
                                                   unsigned lit) {
  assert (!solver->watching);
  LOG ("propagating %s", LOGLIT (lit));
  assert (VALUE (lit) > 0);
  const unsigned not_lit = NOT (lit);

  watches *watches = &WATCHES (not_lit);
  const size_t size_watches = SIZE_WATCHES (*watches);
  unsigned ticks = 1 + kissat_cache_lines (size_watches, sizeof (watch));

  ward *const arena = BEGIN_STACK (solver->arena);
  assigned *assigned = solver->assigned;
  value *values = solver->values;

  for (all_binary_large_watches (watch, *watches)) {
    if (watch.type.binary) {
      const unsigned other = watch.binary.lit;
      assert (VALID_INTERNAL_LITERAL (other));
      const value other_value = values[other];
      if (other_value > 0)
        continue;
      if (other_value < 0) {
        LOGBINARY (not_lit, other, "conflicting");
        return false;
      }
      assert (!solver->level);
      kissat_fast_binary_assign (solver, solver->probing, 0, values,
                                 assigned, other, not_lit);
    } else {
      const reference ref = watch.large.ref;
      assert (ref < SIZE_STACK (solver->arena));
      clause *c = (clause *) (arena + ref);
      assert (c->size > 2);
      assert (!c->redundant);
      ticks++;
      if (c->garbage)
        continue;
      unsigned non_false = 0;
      unsigned unit = INVALID_LIT;
      bool satisfied = false;
      for (all_literals_in_clause (other, c)) {
        if (other == not_lit)
          continue;
        assert (VALID_INTERNAL_LITERAL (other));
        const value other_value = values[other];
        if (other_value < 0)
          continue;
        if (other_value > 0) {
          satisfied = true;
          assert (!solver->level);
          LOGCLS (c, "%s satisfied", LOGLIT (other));
          kissat_mark_clause_as_garbage (solver, c);
          break;
        }
        if (!non_false++)
          unit = other;
        else if (non_false > 1)
          break;
      }
      if (satisfied)
        continue;
      if (!non_false) {
        LOGREF (ref, "conflicting");
        return false;
      }
      if (non_false == 1)
        kissat_fast_assign_reference (solver, values, assigned, unit, ref,
                                      c);
    }
  }

  ADD (ticks, ticks);
  ADD (dense_ticks, ticks);

  return true;
}

bool kissat_dense_propagate (kissat *solver) {
  assert (!solver->level);
  assert (!solver->watching);
  assert (!solver->inconsistent);
  START (propagate);
  unsigned *propagate = solver->propagate;
  bool res = true;
  while (res && propagate != END_ARRAY (solver->trail))
    res = non_watching_propagate_literal (solver, *propagate++);
  const unsigned propagated = propagate - solver->propagate;
  // printf("Propagating literals ");
  for(unsigned int* p= solver->propagate; p != propagate; ++p){
    // printf("%d ",kissat_export_literal(solver, *p));
    int elit = kissat_export_literal(solver, *p);
    if(elit < 0) elit = -elit;
    freq_cnt[elit]++;
  } 
  // printf("\n");
  // printf("propagated number is %d\n", propagated);
  solver->propagate = propagate;
  ADD (dense_propagations, propagated);
  ADD (propagations, propagated);
  if (!res) {
    assert (!solver->inconsistent);
    LOG ("inconsistent root propagation");
    CHECK_AND_ADD_EMPTY ();
    ADD_EMPTY_TO_PROOF ();
    solver->inconsistent = true;
  }
  STOP (propagate);
  return res;
}
