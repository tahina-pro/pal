#include "pal.h"
#undef assert
#include <stdlib.h>

/* C11 6.5p6. The storage `malloc` hands back has no declared type, so the
   effective type of the object in it is whatever was last stored through a
   typed lvalue. Storing an `int64_t` makes it an `int64_t`; storing a `double`
   through a `double *` makes it a `double`, and the `int64_t` that was there
   is gone -- not reinterpreted, gone.
   This is DEFINED behaviour, and it is the case PAL used to translate wrongly:
   it emitted the `double` store against the points-to it still held at
   `int64_t` and reported nothing. */
void defined_retype_of_allocated_storage(void) {
  int64_t *i = malloc(sizeof(int64_t));
  if (i == NULL) return;
  *i = 5;
  *(double *)i = 1.5;
  free(i);
}
