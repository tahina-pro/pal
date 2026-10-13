#include "pal.h"
#undef assert
#include <stdint.h>
#include <stdlib.h>

/* [UB] `_effective_type` 17.4: allocated storage whose effective type was set
 * to a pointer type by a store, then read through `uintptr_t *`. 6.5p7 allows
 * an lvalue whose type is the effective type, a qualified version of it, or
 * the corresponding signed or unsigned type. An integer type is none of
 * those, however wide it is: `uintptr_t` is never compatible with a pointer
 * type even when the two have the same size, so the read is undefined.
 *
 * This is the one corpus case in sections 16-19 that ports to ordinary C with
 * no new machinery, and it is worth porting because the underlying rule is
 * the one `Pulse.Lib.C.Palow.Etype` singles out in its own header as "the
 * rule actually doing work" (`no_int_to_ptr_pun`). It had no test reachable
 * from C before.
 *
 * The two types are both eight bytes wide, so this fails on the *type*
 * conjunct of `read_ok`, not on its width conjunct -- the failure really is
 * 6.5p7 and not a size check. `etype_ptr_store_ok` is the positive control:
 * the same C, the same assertion, the pointer type in place of `uint64_t`,
 * and it verifies. Without it, a rule strong enough to reject every read
 * would pass this test too.
 *
 * `should-fail` pins the message on the effective-type obligation itself, so
 * the test cannot start passing for an unrelated reason. Note that the error
 * is an ordinary *solver* failure ("Failed to prove pure property"), not a
 * tactic failure: the assertion genuinely reached the solver and was refuted,
 * which is the only kind of negative result that means anything here.
 *
 * `palow-only`: the old model has no index to state this against. */

void ptr_read_as_int(_plain int32_t *q)
{
  int32_t **pp = malloc(sizeof(int32_t *));
  if (!pp) return;
  *pp = q;
  _ghost_stmt(ptr_reveal $(pp));
  _ghost_stmt(with b e. assert (mem_pts_to_at $(pp) 1.0R b e ** pure (uint64_t_etype_ok e)));
  _ghost_stmt(admit());
}
