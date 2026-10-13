#include "pal.h"
#undef assert
#include <stdint.h>

/* [UB in C, ACCEPTED by the model] `_effective_type` 13.3: two distinct
 * struct types with identical layout are *not* compatible -- 6.2.7p1 makes
 * compatibility of structs declared in one translation unit depend on the
 * tag, and layout identity is irrelevant. Reading a `struct sa` object
 * through a `struct sb *` is therefore undefined.
 *
 * The model accepts it. This test records that, rather than leaving the gap
 * only in a design note: the assertion below is the one a bridge between the
 * two types would have to discharge, and it goes through. The same convention
 * is used for the section-18 cases, which are stated as positive theorems for
 * the same reason.
 *
 * WHY it is accepted, which is the part worth keeping. A generated
 * aggregate's `{sn}_etype_ok` is a *field-wise* conjunction:
 *
 *     struct_sa_etype_ok e = elen e == 8 /\ allocated e
 *                         /\ int32_t_etype_ok (Seq.slice e 0 4)
 *                         /\ int32_t_etype_ok (Seq.slice e 4 8)
 *
 * and `struct_sb_etype_ok` is literally the same formula, so no index can
 * tell the two apart. The tag lives in `{sn}_ctype` (`ET.TStruct "struct_sa"`
 * vs `ET.TStruct "struct_sb"`), which `ET.access_ok` *does* distinguish --
 * the model has the rule, the generated layer just does not state it.
 *
 * It cannot simply be strengthened to include `ET.read_ok e {sn}_ctype`.
 * `{sn}_pts_to` is field-wise, so `{sn}_gather` folds a struct back together
 * out of the field points-tos alone; each field's index is existentially
 * bound inside its own resource, and nothing relates their join to the
 * struct's `_ctype`. Carrying the tag would mean carrying the parent's index
 * through a focus and back -- the same missing restoration token that blocks
 * cross-type union punning and the character-access bullet. One library
 * change would close all three; this test is here so that closing it is
 * observable.
 *
 * When it is closed, this file should start failing, and should then be
 * turned into a `should-fail` test pinned on `struct_sb_etype_ok`.
 *
 * `palow-only`: the old model has no index to state this against. */

struct sa { int32_t x; int32_t y; };
struct sb { int32_t x; int32_t y; };

int32_t read_as_other_tag(struct sa *p)
{
  _ghost_stmt(struct_sa_reveal $(p));
  /* The obligation a `struct sa` -> `struct sb` bridge would carry. It
     should not hold, and it does. */
  _ghost_stmt(with b e. assert (mem_pts_to_at $(p) 1.0R b e ** pure (struct_sb_etype_ok e)));
  _ghost_stmt(admit());
  return 0;
}
