#include "pal.h"
#undef assert
#include <stdint.h>
#include <stdlib.h>

/* [DEFINED] `_effective_type` 15: storage returned by `malloc` has no
 * declared type, so 6.5p6 gives it the effective type of whatever is stored
 * into it -- here `int32_t`. Reading it back at that same type is 6.5p7
 * bullet 1, and is what every correct use of `malloc` does.
 *
 * What this adds over `etype_pun_counterpart_ok` is *where the index comes
 * from*. That test takes an `int32_t *` parameter, so its obligation is
 * discharged abstractly, from the contract alone. Here the object is created
 * inside the function under test, so the index the assertion sees is the
 * concrete one the emitter actually builds for a `malloc` block. The two
 * tests check the rule against the two ways an index can reach it.
 *
 * `etype_malloc_float_bad` is the negative counterpart: the same C, the same
 * assertion, `float32_t` in place of `int32_t`, and it fails. Without this
 * test a rule strong enough to reject every read would pass that one.
 *
 * The trailing `admit()` discards the revealed byte-level resource so that
 * the function closes. It does not weaken the assertion above it -- Pulse
 * discharges that before it reaches the `admit`, which is precisely why
 * `etype_malloc_float_bad`, identical but for the type, reports an error.
 * Without the `admit` the function ends with leftover resources, and that is
 * a *tactic* failure: it aborts VC generation before any assertion is ever
 * sent to the solver, so the test would pass whatever was asserted.
 *
 * `palow-only`: the old model has no index to state this against. */

int32_t malloc_store_read(void)
{
  int32_t *i = malloc(sizeof(int32_t));
  if (!i) return 0;
  *i = 42;
  _ghost_stmt(int32_t_reveal $(i));
  _ghost_stmt(with b e. assert (mem_pts_to_at $(i) 1.0R b e ** pure (int32_t_etype_ok e)));
  _ghost_stmt(admit());
  return 0;
}
