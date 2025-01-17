#include "proprobe.h"
#include "fastassign.h"
#include "trail.h"
#include "global.h"

#define PROPAGATE_LITERAL probing_propagate_literal
#define PROPAGATION_TYPE "probing"
#define PROBING_PROPAGATION

#include "proplit.h"

static void update_probing_propagation_statistics (kissat *solver,
                                                   unsigned propagated) {
  const uint64_t ticks = solver->ticks;
  LOG (PROPAGATION_TYPE " propagation took %u propagations", propagated);
  LOG (PROPAGATION_TYPE " propagation took %" PRIu64 " ticks", ticks);

  ADD (propagations, propagated);
  // printf("propagated number is %d\n", propagated);
  ADD (probing_propagations, propagated);

#if defined(METRICS)
  if (solver->backbone_computing) {
    ADD (backbone_propagations, propagated);
    ADD (backbone_ticks, ticks);
  }
  if (solver->vivifying) {
    ADD (vivify_propagations, propagated);
    ADD (vivify_ticks, ticks);
  }
#endif

  ADD (probing_ticks, ticks);
  ADD (ticks, ticks);
}

clause *kissat_probing_propagate (kissat *solver, clause *ignore,
                                  bool flush) {
  assert (solver->probing);
  assert (solver->watching);
  assert (!solver->inconsistent);

  START (propagate);

  clause *conflict = 0;
  unsigned *propagate = solver->propagate;
  solver->ticks = 0;
  while (!conflict && propagate != END_ARRAY (solver->trail)) {
    const unsigned lit = *propagate++;
    conflict = probing_propagate_literal (solver, ignore, lit);
  }

  const unsigned propagated = propagate - solver->propagate;
  // printf("Propagating literals ");
  for(unsigned int* p= solver->propagate; p != propagate; ++p){
    // printf("%d ",kissat_export_literal(solver, *p));
    int elit = kissat_export_literal(solver, *p);
    if(elit < 0) elit = -elit;
    freq_cnt[elit]++;
  } 
  // printf("\n");
  solver->propagate = propagate;
  update_probing_propagation_statistics (solver, propagated);
  kissat_update_conflicts_and_trail (solver, conflict, flush);

  STOP (propagate);

  return conflict;
}
