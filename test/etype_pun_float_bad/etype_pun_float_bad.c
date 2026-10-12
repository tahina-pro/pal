#include "pal.h"
#include <stdint.h>

/* [UB] `_effective_type` 13.1: an `int` object read through `float *`.
 *
 * `float` is on none of the bullets of 6.5p7 -- it is not the effective type,
 * not its signed or unsigned counterpart, not a character type, and not an
 * aggregate containing one -- so the access is undefined.
 *
 * The program under test is ordinary C, not a ghost reconstruction of one.
 * The emitter looks through the pointer-to-pointer cast when it decides what
 * `*(float *)i` reaches, so the read translates; it does not decide that the
 * read is *legal*. Legality is the bridge below, and the bridge fails.
 *
 * It fails for exactly one reason. The two types are the same width, so the
 * width conjunct of `read_ok` holds and cannot be what rejects this; and the
 * obligation is asserted on its own, before the step that would also need a
 * representation, so the failure cannot be the solver running out of a
 * `float` value to exhibit. What is left is `float32_t_etype_ok`, which is
 * 6.5p7.
 *
 * `etype_pun_counterpart_ok` is the positive control: the same C, the same
 * bridge, the same assertion, with `uint32_t` in place of `float`. It
 * verifies. Without it a rule strong enough to reject every pun would pass
 * this test.
 *
 * `palow-only`: the old model has no index to state this against. */

/* `pal.h` rewrites `assert` so that C `assert()` becomes a Pulse assertion.
   Inside an `_include_pulse` block the text is Pulse, not C. */
#undef assert

_include_pulse(Etype_pun_float_bad_include,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  module ET = Pulse.Lib.C.Palow.Etype
  module I32 = FStar.Int32

  (* Viewing an `int32_t` object as a `float32_t`. The effective-type index
     does not permit it, and there is no rule that makes it permit it. *)
  ghost fn as_float (a: ptr) (#p: perm) (#x: I32.t)
    requires int32_t_pts_to a p x
    ensures  exists* (y: float32). float32_t_pts_to a p y
  {
    int32_t_reveal a;
    with b e. assert (mem_pts_to_at a p b e);
    assert (pure (float32_t_etype_ok e));
    admit();
  }

  (* The way back, which is not reached: the assertion above fails first. It
     is here so that the two tests have the same shape. *)
  ghost fn as_int (a: ptr) (#p: perm) (#y: float32)
    requires float32_t_pts_to a p y
    ensures  exists* (x: I32.t). int32_t_pts_to a p x
  {
    admit();
  }
)

float pun_int_as_float(int32_t *i)
{
  _ghost_stmt(Etype_pun_float_bad_include.as_float $(i));
  float f = *(float *)i;
  _ghost_stmt(Etype_pun_float_bad_include.as_int $(i));
  return f;
}
