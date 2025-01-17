#include "propbeyond.h"
#include "fastassign.h"
#include "trail.h"
#include "global.h"

#define PROPAGATE_LITERAL propagate_literal_beyond_conflicts
#define CONTINUE_PROPAGATING_AFTER_CONFLICT
#define PROPAGATION_TYPE "beyond conflict"

#include "proplit.h"

static inline void
update_beyond_propagation_statistics (kissat *solver,
                                      const unsigned *saved_propagate) {
  assert (saved_propagate <= solver->propagate);
  const unsigned propagated = solver->propagate - saved_propagate;

  // printf("Propagating literals ");
  for(unsigned int* p= saved_propagate; p != solver->propagate; ++p){
    // printf("%d ",kissat_export_literal(solver, *p));
    int elit = kissat_export_literal(solver, *p);
    if(elit < 0) elit = -elit;
    freq_cnt[elit]++;
  } 
  // printf("\n");
  // printf("propagated number is %d\n", propagated);
  LOG ("propagated %u literals", propagated);
  LOG ("propagation took %" PRIu64 " ticks", solver->ticks);

  ADD (propagations, propagated);
  ADD (ticks, solver->ticks);
}

static void propagate_literals_beyond_conflicts (kissat *solver) {
  unsigned *propagate = solver->propagate;
  while (propagate != END_ARRAY (solver->trail))
    (void) propagate_literal_beyond_conflicts (solver, *propagate++);
  solver->propagate = propagate;
}

void kissat_propagate_beyond_conflicts (kissat *solver) {
  assert (!solver->probing);
  assert (solver->watching);
  assert (!solver->inconsistent);

  START (propagate);

  solver->ticks = 0;
  const unsigned *saved_propagate = solver->propagate;
  propagate_literals_beyond_conflicts (solver);
  update_beyond_propagation_statistics (solver, saved_propagate);

  STOP (propagate);
}
