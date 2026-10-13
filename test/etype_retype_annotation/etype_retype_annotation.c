#include "pal.h"
#undef assert
#include <stdlib.h>

/* C11 6.5p6 again, but said rather than done.

   A store through a `double *` already re-types allocated storage by itself,
   and PAL takes that step without being asked. `_retype` is for where there is
   no such store to read it off: here the object's life as an `int64_t` ends
   and the storage goes back to the allocator at its new type, so nothing is
   ever written through a `double *`.

   The annotation is a no-op when it agrees with what the block already holds,
   so writing it where a store would have said the same thing costs nothing.
   This is all DEFINED behaviour. */
void defined_retype_without_a_store(void) {
  int64_t *i = malloc(sizeof(int64_t));
  if (i == NULL) return;
  *i = 5;
  _retype((double *)i);
  free(i);
}
