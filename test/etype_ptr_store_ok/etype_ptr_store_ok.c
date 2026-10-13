#include "pal.h"
#undef assert
#include <stdint.h>
#include <stdlib.h>

/* [DEFINED] `_effective_type` 17.4, the legal half: storage returned by
 * `malloc` has no declared type, so 6.5p6 gives it the effective type of
 * whatever is stored into it -- here a pointer. Reading it back at that same
 * type is 6.5p7 bullet 1.
 *
 * This is the positive control for `etype_ptr_int_bad`, which is the same C
 * and the same assertion with `uint64_t` in place of the pointer type. The
 * pair is worth having because pointers are the one scalar whose rule is
 * already a stated theorem of the model: `Pulse.Lib.C.Palow.Etype` names
 * `no_int_to_ptr_pun` in its header as "the rule actually doing work". Until
 * now nothing in the test suite exercised it from ordinary C.
 *
 * A pointer and `uintptr_t` are both eight bytes wide, so the negative test
 * fails on the *type* conjunct of `read_ok` and not on its width conjunct.
 * That is what makes the pair meaningful: a same-width pun is the only kind
 * that isolates 6.5p7. (Corpus 17.3 punned a `double` to a `_Bool`, which is
 * a width mismatch and would have failed for the wrong reason; 17.5 punned a
 * `long` to a `long long`, which PAL maps to the same `int64_t` and so cannot
 * distinguish at all.)
 *
 * `_plain` on the parameter borrows the pointer value without taking
 * ownership of its target, which is all this test needs.
 *
 * The trailing `admit()` discards the revealed byte-level resource so that
 * the function closes. It does not weaken the assertion above it -- Pulse
 * discharges that first, which is exactly why `etype_ptr_int_bad`, identical
 * but for the type, reports an error. Without the `admit` the function would
 * end with leftover resources, and that is a *tactic* failure: it aborts VC
 * generation before any assertion reaches the solver, so the test would pass
 * whatever was asserted.
 *
 * `palow-only`: the old model has no index to state this against. */

void ptr_store_read(_plain int32_t *q)
{
  int32_t **pp = malloc(sizeof(int32_t *));
  if (!pp) return;
  *pp = q;
  _ghost_stmt(ptr_reveal $(pp));
  _ghost_stmt(with b e. assert (mem_pts_to_at $(pp) 1.0R b e ** pure (ptr_etype_ok e)));
  _ghost_stmt(admit());
}
