#include "pal.h"
#include <stdint.h>

/* [DEFINED] `_effective_type` 1.2: an `int` object read through `unsigned
 * int *`. 6.5p7 bullet 3 permits an access through "the signed or unsigned
 * type corresponding to the effective type of the object".
 *
 * This is the *positive control* for `etype_pun_float_bad`, and it is what
 * makes that test mean something: both run the same C through the same
 * bridge, and the only difference between them is the type being read. A
 * rule strong enough to reject every pun would pass the negative test and
 * fail this one.
 *
 * Unlike the earlier `etype_*` tests, the program under test is ordinary C.
 * The emitter looks through a pointer-to-pointer cast when it decides what a
 * dereference reaches, so `*(uint32_t *)i` translates to a `uint32_t` read of
 * `i`; what it does *not* do is decide the read is legal, which is the whole
 * point. Legality is the bridge below, and the bridge's only real obligation
 * is `uint32_t_etype_ok` -- 6.5p7 and nothing else.
 *
 * `palow-only`: the old model has no index to state this against. */

/* `pal.h` rewrites `assert` so that C `assert()` becomes a Pulse assertion.
   Inside an `_include_pulse` block the text is Pulse, not C. */
#undef assert

_include_pulse(Etype_pun_counterpart_ok_include,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  module ET = Pulse.Lib.C.Palow.Etype
  module U32 = FStar.UInt32
  module I32 = FStar.Int32
  module E = Pulse.Lib.C.Palow.Encoding

  (* Viewing an `int32_t` object as the `uint32_t` that shares its bytes.
     The value is not in question -- the bytes already *are* an encoding, and
     `int32_t_repr` says which one -- so the only thing to discharge is that
     the effective-type index permits a `uint32_t` access, which is
     `read_ok_counterpart`. *)
  ghost fn as_unsigned (a: ptr) (#p: perm) (#x: I32.t)
    requires int32_t_pts_to a p x
    ensures  exists* (y: U32.t). uint32_t_pts_to a p y
  {
    int32_t_reveal a;
    with b e. assert (mem_pts_to_at a p b e);
    let y = U32.uint_to_t (E.to_bits 32 (I32.v x));
    ET.read_ok_counterpart e ET.SInt32;
    assert (pure (uint32_t_etype_ok e));
    uint32_t_conceal a #p #b #e #y;
  }

  (* And back, so that the object leaves the function at the type it entered
     with. A read does not change the effective type of an object. *)
  ghost fn as_signed (a: ptr) (#p: perm) (#y: U32.t)
    requires uint32_t_pts_to a p y
    ensures  exists* (x: I32.t). int32_t_pts_to a p x
  {
    uint32_t_reveal a;
    with b e. assert (mem_pts_to_at a p b e);
    let x = I32.int_to_t (if U32.v y < 2147483648 then U32.v y else U32.v y - 4294967296);
    ET.read_ok_counterpart e ET.SUInt32;
    int32_t_conceal a #p #b #e #x;
  }
)

uint32_t pun_int_as_unsigned(int32_t *i)
{
  _ghost_stmt(Etype_pun_counterpart_ok_include.as_unsigned $(i));
  uint32_t u = *(uint32_t *)i;
  _ghost_stmt(Etype_pun_counterpart_ok_include.as_signed $(i));
  return u;
}
