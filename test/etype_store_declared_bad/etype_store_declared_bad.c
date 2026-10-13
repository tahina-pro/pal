#include "pal.h"
#undef assert
#include <stdint.h>

/* C11 6.5p6. A declared object keeps its declared type for its whole
   lifetime, so a store through a `double *` does *not* re-type it the way the
   same store re-types `malloc`ed storage (`etype_retype_store`). It is
   undefined behaviour.

   This is the mirror of the bug `etype_retype_store` pins, and it had the same
   shape: the emitter produced a `float64_t` write against the `int64_t`
   points-to it still held, reported nothing, and left F* to fail with a
   *tactic* error -- which aborts VC generation, so it could not even be
   pinned as a `should-fail` test. PAL refuses it instead, and the `refuse`
   file pins the reason rather than just the fact that something failed. */
void declared_object_is_not_retypable(void) {
  int64_t x = 5;
  *(double *)&x = 1.5;
}
