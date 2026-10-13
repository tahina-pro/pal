#include "pal.h"
#undef assert
#include <stdint.h>
#include <stdlib.h>

/* Re-typing covers a whole object. `mem_retype` relates a byte range to a
   ctype of exactly that size, so the re-typing store PAL now takes
   (`etype_retype_store`) is available only when the two types agree on width.

   Storing an `int32_t` into eight bytes that hold an `int64_t` re-types *part*
   of the object. That needs `mem_split` to carve the range first, which the
   emitter does not do here, so it refuses rather than guessing. The same gap
   covers the legal-C case `*(char *)p = ...`, which does not re-type at all
   (6.5p6 exempts character types) but is still a narrower store.

   Pinning the refusal is the point: this is the boundary of what the re-typing
   store covers, and it should not move silently. */
void partial_retype_is_not_covered(void) {
  int64_t *i = malloc(sizeof(int64_t));
  if (i == NULL) return;
  *i = 5;
  *(int32_t *)i = 7;
  free(i);
}
