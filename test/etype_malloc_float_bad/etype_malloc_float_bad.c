#include "pal.h"
#undef assert
#include <stdint.h>
#include <stdlib.h>

/* [UB] `_effective_type` 15: a store through an `int32_t` lvalue gives
 * `malloc`ed storage the effective type `int32_t` (6.5p6). Reading that
 * object through a `float *` is then on none of the bullets of 6.5p7 -- not
 * the effective type, not its signed or unsigned counterpart, not a character
 * type, not an aggregate containing one -- so the access is undefined.
 *
 * This is the allocated-storage half of the rule. `etype_pun_float_bad` makes
 * the same point about an object whose type arrives through a parameter's
 * contract, where the index is abstract; here the index is the concrete one
 * the emitter builds for a `malloc` block, so the test also pins that the
 * emitter does not hand out storage that stays readable at every type.
 *
 * It fails for exactly one reason. The two types are the same width, so the
 * width conjunct of `read_ok` holds and cannot be what rejects this; and the
 * obligation is asserted on its own, not as part of a step that would also
 * need a `float` representation -- which could not be produced in any case,
 * since `Float.fsti` deliberately states no surjectivity. What is left is
 * `float32_t_etype_ok`, which is 6.5p7.
 *
 * `etype_malloc_store_ok` is the positive control: this file with `int32_t`
 * in place of `float32_t`, which verifies.
 *
 * On the trailing `admit()`, see `etype_malloc_store_ok`. It is reached only
 * after the assertion has been discharged, so it cannot be what makes this
 * test fail -- and it is what makes the *passing* control meaningful.
 *
 * `palow-only`: the old model has no index to state this against. */

float malloc_store_read_float(void)
{
  int32_t *i = malloc(sizeof(int32_t));
  if (!i) return 0.0f;
  *i = 42;
  _ghost_stmt(int32_t_reveal $(i));
  _ghost_stmt(with b e. assert (mem_pts_to_at $(i) 1.0R b e ** pure (float32_t_etype_ok e)));
  _ghost_stmt(admit());
  return 0.0f;
}
