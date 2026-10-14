# Enforce C11 effective types (6.5p6/p7)

Base: `gebner_palow`. This branch takes the effective-type model from
"formalized but inert" to "enforced on generated code".

Before this branch, `Pulse.Lib.C.Palow.Etype` defined `read_ok`, `store_ok`
and friends, and nothing asked them. A typed points-to said which bytes an
object owned but not what type those bytes were at, so `int32_t_reveal`
followed by `float32_t_conceal` typechecked, and the model's theorems were
commentary. Now every typed points-to carries a per-byte **effective-type
index**, and the generated `conceal` / `claim` sites have to earn `read_ok`
of the index they actually have.

---

## 1. The corpus this is measured against

`test/_effective_type/effective_type.c` — 73 cases covering 6.5p6/p7, each
tagged `[DEFINED]`, `[UB]`, `[UNSPEC]` or `[IMPL-DEF]` and cited to N1570. It
is a standalone C program with no `pal.h` and no annotations, so it is a
*specification to work against* rather than a test; the `_` prefix keeps it
out of the test glob and out of `check-template.sh`.

Nineteen representative cases are transcribed as theorems in
`Etype.fst`, named after the case they come from. Transcribing them is what
turned up three gaps in the model, now closed:

- **`store_ok`** — `store_etypes` says how a store *moves* the index, and on a
  declared object it moves nothing. Taken alone that reads as "permitted, no
  effect", where C says undefined. `store_ok` is the missing side condition.
- **`counterpart_ok`** — 6.5p7 bullet 3, the signed/unsigned counterpart.
- **The character exception** (6.5p6, last sentence). `store_entry` now
  short-circuits at `tchar`. Load-bearing, not a nicety: without it `malloc` +
  `memset` + use-as-`int32_t` would be undefined, because clearing the buffer
  would retype every byte as `char` and no wider read could cross one.
  `store_ok` moved with it — its `not fixed` disjunct is now guarded by
  `u =!= tchar`, or `store_ok_read_ok` breaks at `tchar`.
  `store_char_identity` is the canary.

`make palow-check` translates the corpus with `--palow-permissive`. **Four**
modules fail to verify, and none of the four is about 6.5p7: a FAM fill loop
needing the `test/vec_fam` frontier invariant, an existentially-quantified
global across a call, and two the ownership analysis does not grant.

---

## 2. The index, and why it is shaped this way

### Per byte, with an offset

An index entry is a `ctype`, the byte's **offset within its object**, and a
`fixed` flag (declared vs. allocated). The offset is what makes an access
check composable: byte *k* of an access is byte `en.off` of its object, so
requiring `access_ok en.ty (en.off - k) u` forces every byte the access covers
to come from the *same* subobject.

### A store relabels a byte only if its current type does not already license it

```fstar
let store_entry (en: option etype_entry) (u: ctype) (k: nat) : option etype_entry =
  if u = tchar then en else
  match en with
  | Some e0 -> if e0.fixed || access_ok e0.ty (e0.off - k) u then Some e0
               else Some ({ ty = u; off = k; fixed = false })
  | None -> Some ({ ty = u; off = k; fixed = false })
```

This answers the obvious worry about a per-byte index: storing a `uint32_t`
through member `y` of a `struct T` does **not** demote the struct, because
`access_ok struct_T_ctype 0 uint32_t_ctype` already holds, so the store is a
no-op on the index (`member_store_keeps_object`). Writing a `struct S` over
storage that held a `struct T` *is* a relabel (`retype_allocated`) — which is
the case 6.5p6 is actually about. A declared object is never relabelled
(`retype_declared`), and fresh `None` storage always is, which keeps
`no_int_to_ptr_pun` true.

`access_ok` had to become a `bool` to be the test in that `if`. That is the
better choice anyway: descriptors are closed terms, so each instance
*computes* rather than asking the solver to reason about the recursion.

### Layer 0 is the view of allocated storage

`mem_pts_to a p b` is now *defined* as `exists* e. mem_pts_to_at a p b e **
pure (allocated e)` — an slprop **equality** (`mem_pts_to_at_eq`), not a pair
of axiomatized ghost steps. That matters: two independent predicates with
ghost steps between them could be used to discard an index and conjure a fresh
one; an equality cannot.

`Pulse.Lib.C.Palow.Index` (new, **no new axioms**) packages the two rewrites:

- `mem_hide_etypes` forgets the index.
- `mem_show_etypes` recovers one, but **existentially** — so nothing can be
  concluded about it.

The asymmetry is the whole design. Round-tripping loses information and never
gains any: bytes that came out of a declared `int` cannot be put back as a
`float`, because re-establishing a typed points-to needs `read_ok` of the
index they actually have, and after a `hide` nobody can prove that about
anything.

Two observations (`not_null`, `fits`) are lifted to the indexed form by
share / observe / gather. Two are deliberately absent: `perm_bound` survives
sharing only in its halved form, and `disjoint` needs the whole `1.0R` range,
leaving nothing behind to retain the index with.

`mem_share_at` / `mem_gather_at` **are** new layer-0 axioms, and genuinely
cannot be derived — going out to `mem_pts_to`, sharing, and coming back gives
two halves with existential indices, provably equal to each other but not to
the `e` you started with, because the resource that knew `e` was spent on the
rewrite. That inability is exactly what makes `hide` → `show` safe, so it is
not a defect to work around.

---

## 3. Threading it through `pulse/`

The index could not stop at the scalars: `uint8_t_of_elem` goes through
`elem_pts_to`, which is generic over an element representation.

**The array layer carries a predicate, not a `ctype`.** `array_pts_to` and
`elem_pts_to` take an `eok: etypes -> prop`. A `ctype` parameter would have
forced every array of unions to name a type the union does not have, and would
not have expressed a union's "carries no effective type at all". Every type
publishes its own `{t}_etype_ok` under a uniform name, so a struct or array
containing one states its condition without knowing what kind of type it is.

**`_pts_to_uninit` carries the index too**, or `forget` → `reveal_uninit` is a
laundering path around `reveal`.

### Aggregate join, and `{sn}_live_ok`

Rebuilding a struct from separated field predicates was the hard problem.
From the fields' `read_ok … field_ctype` you cannot recover
`read_ok e struct_ctype` — `read_ok (etypes_of ct_i32 false ++ etypes_of
ct_i32 false) ct_T` is simply false.

The resolution is a generated, **value-dependent** `{sn}_live_ok x e`. For a
plain struct it degenerates to the storage condition:

```fstar
let struct_mis_live_ok (x: struct_mis) (e: ET.etypes) : prop = struct_mis_etype_ok e
```

For an aggregate containing a union it names the **live member**, because a
member focus hands the client the member's own typed resource, which records
`read_ok` at the member's type and nothing else — so that is all the matching
unfocus can put back:

```fstar
let struct_context_t_anon_1_live_ok (x: struct_context_t_anon_1) (e: ET.etypes) : prop =
  ... /\ union__u_context_t_live_ok (x).fld_payload (Seq.slice e 8 64)
```

Each comes with two generated lemmas — `_live_ok_etype_ok` (a live object
still meets the storage condition) and `_live_ok_read_ok` (storage a store at
the aggregate's own type produced is live at every member) — so split and join
both work. A union's *storage* condition is `untyped`, which is not a
shortcut: 6.5.2.3p3 and its footnote permit reading any member, so the bytes
must admit a read at every member's type at once, and "carries no effective
type" says exactly that — and unlike a conjunction of per-member `read_ok`s it
splits and rejoins.

### Proof-size work

Threading an index through wide structs made some generated queries blow up.
Three changes keep them linear:

- **Carve wide structs part by part** rather than all at once.
- **`sizeof_norms`** — state each size fact once by normalisation rather than
  by SMT.
- **Per-field alignment lemmas** — in `test/dpe`'s sixty-nine-field struct the
  shared context was large enough that the last field's goal timed out. Each
  is now proved separately, as one implication with nothing else in scope.

`{sn}_claim_uninit` carries `rlimit 150`; nothing wider than `_IO_FILE` /
`profile_descriptor_t` exists today to test the margin.

---

## 4. Tests

Negative tests are the point, and they are easy to get wrong in two ways: a
test pinned on the ownership analysis passes without testing anything and
keeps passing if the rule is deleted, and a rule strong enough to reject
*everything* makes all the negatives pass too. So each negative is pinned on
the exact message, and each has a positive control.

| Test | What it pins |
|---|---|
| `etype_access_ok` | positive control for `etype_pun_bad` — the defined cases through the *identical* obligation |
| `etype_pun_bad` | `read_ok (etypes_of ct_i32 true) ct_f32` |
| `etype_store_bad` | `store_ok (etypes_of ct_i32 true) ct_f32` — a store at the wrong type into a declared object |
| `etype_memcpy_bad` | `read_ok (copy_etypes …)` — 6.5p6's third rule is "for all other accesses to an object having no declared type", so it does not apply to a declared one |
| `etype_char_store` | the character exception, through `mem_store_etypes` on a slice of a larger object |
| `etype_claim_ok` / `etype_claim_bad` | 6.5p7 on the **generated** API |
| `flex_free` | giving a flexible-array-member object back |
| `etype_pun_counterpart_ok` | 6.5p7 bullet 3 on **ordinary C**, for an object arriving through a parameter's contract |
| `etype_pun_float_bad` | `float32_t_etype_ok` — the same C, the same bridge, `float` in place of `unsigned` |
| `etype_malloc_store_ok` | the same rule where the index is the **concrete** one the emitter builds for a `malloc` block |
| `etype_malloc_float_bad` | `float32_t_etype_ok` on allocated storage |
| `etype_struct_tag_gap` | records that corpus 13.3 (a struct read at another tag with identical layout) is **accepted**, and why |
| `etype_ptr_store_ok` | 6.5p7 bullet 1 at a **pointer** type — the positive control for the next row |
| `etype_ptr_int_bad` | `uint64_t_etype_ok` on storage whose effective type is a pointer (corpus 17.4) — the first test from ordinary C for `no_int_to_ptr_pun`, the rule `Etype.fst` calls "the rule actually doing work" |

The first four reach `Etype` through a helper taking `read_ok e u` as a
*hypothesis* — which shows the predicate says the right thing, but not that
anything asks it. `etype_claim_ok` / `etype_claim_bad` close that gap: the
obligation is the `{t}_etype_ok` in `{t}_claim_uninit`'s precondition, the
same one every typed claim in generated code carries, earned from the index a
store left behind rather than assumed. The positive file claims storage a
store typed `int32_t` as a `uint32_t` (bullet 3) and a byte of it as an
`int8_t` (the character bullet); the negative claims that byte as a `bool_t`,
which is on none of the bullets, and fails on exactly

```
bool_t_etype_ok (Seq.slice (ET.store_etypes e0 int32_t_ctype) 0 1)
```

— same width, same alignment, same full ownership.

### Porting the corpus to ordinary C

The `etype_*` tests above state the rule about ghost reconstructions of C
programs. The four new tests state it about C: the program under test is
`uint32_t u = *(uint32_t *)i;`, and the only ghost code is a short bridge that
turns one typed points-to into another.

Three things had to be true for that to work.

- **The emitter has to look through a pointer-to-pointer cast** when it
  decides what a dereference reaches (`Body::strip_ptr_casts`). Before, the
  ownership analysis refused to *translate* the natural C for a pun, so 6.5p7
  was never consulted and the negative tests could not fail for the right
  reason. The cast is looked through only when both sides are pointers, so an
  integer cast to a pointer still grants nothing (`ptr_int_cast`).
- **`read_ok_counterpart`** (new, in `Etype.fst`) is bullet 3 in *open* form.
  The model already had `case_1_2_signed_unsigned_counterpart`, but only for
  the closed index `etypes_of ct_i32 true`, which the solver settles by
  computation; a read through a pointer reaches a *variable* index.
- **The bridge has to assert the etype obligation on its own, before the
  `conceal`.** `conceal` also wants a representation, and `Float.fsti`
  deliberately states no surjectivity, so a bridge that asserts both at once
  fails ambiguously. Asserting 6.5p7 first makes the negative test fail for
  exactly one reason, and the pun types are the same width so the width
  conjunct of `read_ok` cannot be what rejects it.

Each pair is the same file twice, differing only in the type asserted. The
pairs differ from each other in *where the index comes from*: through a
parameter's contract, where the obligation is discharged abstractly, and from
a `malloc` block the function allocates itself, where it is discharged against
the concrete index the emitter built.

All four end in `admit()`, which is load-bearing rather than lazy. Leftover
resources at the end of a `fn` are a **tactic** failure, and a tactic failure
aborts VC generation before any assertion in the body reaches the solver — so
without the `admit` the files would "pass" no matter what they asserted,
including `pure (1 == 2)`. This is worth stating because an earlier reading of
a probe written without it produced a confident and entirely wrong conclusion
(see *Known gaps*).

### Why the rest of the corpus is not ported

Each remaining section was probed rather than assumed. Only one case in
sections 5–19 ports with no new machinery, and it is now `etype_ptr_int_bad`.
The others divide into four kinds:

- **An unimplemented model rule.** 6.5p6's third rule — copying propagates the
  source's effective type — is not implemented at all. `memcpy` from
  `<string.h>` translates to an extern with `requires emp / ensures emp`, so a
  copy transports nothing: after `memcpy(d, &src, sizeof(double))` the
  destination is still `float64_t_pts_to_uninit` and the read fails. The only
  way to get the rule today is the hand-written `Copy_shim` in
  `memcpy_transport`, which is the ghost apparatus these ports exist to avoid.
  This blocks corpus 5.x, 11.1(1), 12.2, 14.1 and 18.x.
- **Re-typing allocated storage is not supported, and fails silently.** See
  *Known gaps*. This blocks corpus 4.x, 7.3/7.4 and all of 16.x.
- **Scalar identity is representational, not nominal.** `char` and
  `signed char` both map to `int8_t`, `long` and `long long` both to
  `int64_t`, and `size_t`, `unsigned long` and `uint64_t` all to
  `TScalar SUInt64`. Corpus 9.1, 9.2 and 17.5 ask whether two *distinct C
  types that share a representation* may alias, and the model has no name with
  which to tell them apart.
- **Nothing left to observe.** 7.1 and 7.2 verify, but each allocation gets a
  fresh claim, so no storage is shared and no index is in question. 10.2 is
  not a 6.5p7 case and the model already settles it — `{sn}_padding` holds the
  padding with its bytes unconstrained and no way to read them at a type.
  10.3's question (did `memset` install a type?) is unobservable because the
  storage is claimed at its type before the `memset` runs.

Two further cases would fail for the wrong reason and so were deliberately not
ported: 17.3 puns a `double` to a `_Bool`, and 17.1/17.2 are bounds and
alignment violations. A negative test is only worth having when the obligation
it fails on is the effective-type one, which is why 17.4 — both sides eight
bytes wide, and distinct in the model — is the only one of the five that works.

Corpus 19.x is *already* rejected, but by initialization tracking rather than
by effective types: the context shows `int32_t_pts_to_uninit` where
`int32_t_pts_to` is wanted. It could be ported cheaply, but it would be a test
of a different rule.

### Corpus plumbing

The corpus declares `printf`, `puts` and `strcmp` itself, with `_array` on
their string parameters: `<stdio.h>` says `const char *`, which PAL reads as a
pointer to a *single* `char`, while a string literal is an array. Without
those three lines, eight modules fail on their first call and hide everything
above them. (Note `_array` is a `pal.h` macro — without the include, clang
silently recovers `const _array char *` as `int` and the failure merely
changes shape.)

---

## 5. Merge: upstream packed structs

The last commit merges `gebner_palow` through `980eaf80`, which adds
unaligned fields of packed structs — a new `Pulse.Lib.C.Palow.Unaligned`
module holding a field at the byte level rather than through its typed
points-to. It was written against the pre-index API. Two decisions:

- **`bytes_uninit` takes the field type's `etype_ok`**, making it exactly
  `{t}_pts_to_uninit` less the alignment. It has to: `memcpy` preserves the
  *destination's* index, so `{t}_write_uninit_u` can only conclude the bytes
  it filled are readable at the type if the index already admitted the type
  before the write.
- **`{t}_reveal_uninit_at`** (new, 13 types) — `reveal_uninit` keeping the
  index, for the stack temporary each unaligned op copies through. The
  alternative, `mem_retype`, is unavailable at the character types
  (`~(c == tchar)`), and this is the honest statement anyway: the bytes a
  stack slot hands out already meet the type's condition.

---

## 6. The re-typing store, and `_retype`

6.5p6 says a store through an lvalue of type `T` into an object with no
declared type makes `T` that object's effective type. PAL did not take that
step, and worse, did not say it was not taking it. Given

```c
int64_t *i = malloc(sizeof *i);
*i = 5;
*(double *)i = 1.5;       /* defined: the object becomes a double */
```

the emitter produced `float64_t_write` applied straight to an
`int64_t_pts_to`, **reported no diagnostic and exited 0**, leaving F\* to
reject the generated file with a *tactic* failure. That contradicts the
promise in every generated file's own header, and it meant corpus §16 could
not even be ported as a negative test — a `should-fail` test would have been
green for entirely the wrong reason.

The store path now takes the step, inline, with no new `pulse/` code and no
new axioms:

```
int64_t_forget a;             (* only when the block holds a value *)
int64_t_reveal_uninit_at a;
mem_retype a float64_t_ctype;
float64_t_claim_uninit a;
```

Neither `aligned_divides` nor `{to}_etype_ok_read_ok_all` is needed: all
thirteen scalar types have `alignof == sizeof`, so agreeing on width is
agreeing on alignment, and `{t}_etype_ok` unfolds to exactly what
`mem_retype` ensures. `free` afterwards follows the block at its new type.

It is gated on the target being a `Block` rather than a `Slot` — that is,
on the storage having come from an allocator. The mirror case had the same
silent mis-emission and is now **refused**, naming the rule:

> a store at `float64_t` into `x`, which is declared as `int64_t`: an object
> with a declared type keeps it, so this is not a re-typing store but
> undefined behaviour (C11 6.5p6)

Width mismatches are refused too; re-typing part of an object needs
`mem_split`, and that includes the legal-C case `*(char *)p = …` into a
wider object, which does not re-type at all.

**`_retype((T *)p)`** says the same thing where no store does: storage whose
life as one type ends and which then changes hands at another. The cast is
the point — clang type-checks it, so the target type is read off the AST
rather than re-parsed out of a captured source snippet the way a predicate
is. The macro wraps `(void)(p)` in a compound statement under a *nullary*
`annotate("pal-retype")`, and the C++ side walks to the `CastExpr` and takes
its pointee. Saying it where a store would have said it anyway is accepted
and costs nothing; saying it about a declared object is refused exactly as a
store is.

`etype_retype_store` and `etype_retype_annotation` cover the two.

### Pinning a refusal: the `refuse` file

Both refusals above shipped without regression tests, because the harness had
no way to express one. When PAL cannot translate a body it says why, stubs the
body with `admit()`, and puts an `assert False` in `TranslationErrors.fst` so
F\* rejects the build — but it exits 0, and it writes that file either way,
empty when there is nothing to report. So a refusal does fail a normal test;
what it cannot do is say *which* refusal, since every untranslated body fails
identically.

A test directory may now carry a **`refuse`** file, the counterpart of
`should-fail` one stage earlier: PAL must have refused, and every line of
`refuse` must appear in what it said. `etype_store_declared_bad` pins the
6.5p6 refusal and `etype_retype_partial_bad` pins the width one — the latter
being the boundary of what the re-typing store covers, which should not move
silently.

The mechanism was checked against all three ways it could go wrong: a wrong
expected reason fails, a test that translates cleanly fails, and the two real
refusals pass.

---

## Status

`make test -j8` — **0 errors**, 10 "Failed as expected", 2 "Refused as
expected". `make -C pulse -j8` verifies. `cargo fmt --check` and
`clang-format` pass.

## Known gaps

- **A declared object cannot be re-typed in the model, only in the emitter.**
  `{t}_stack_alloc` hands back the same `{t}_pts_to_uninit` that `malloc`
  does, and `{t}_etype_ok e` is `read_ok e {t}_ctype /\ ET.allocated e`, so
  *every* typed points-to in PAL — a local's included — asserts "no byte of
  this is at a declared type". `ET.etype_entry.fixed` is set nowhere outside
  `Etype.fst`'s own case theorems. Hand-written Pulse and `_include_pulse`
  shims can therefore `mem_retype` a stack local, which is corpus 14.x
  undefined behaviour. C source cannot reach it — §6 above refuses it in the
  emitter — but the model does not state the rule, and `mem_retype`'s own
  comment ("unavailable for a declared object, which is what C says too") is
  aspirational.
  Closing this is not a local change, and layer 0 already says so. The
  cheap-looking route — require a `freeable` at `mem_retype` — is **wrong**,
  and `pool_flex` shows why: a chunk from `func_pool_alloc` carries no
  `freeable` yet is legitimately re-typed, because `freeable` deliberately
  does not split. The faithful condition is `ET.allocated`, which already
  splits and rejoins.
  But `mem_pts_to_at_eq` pins the *unindexed* view to allocated storage by
  construction — `mem_pts_to a p b == exists* e. mem_pts_to_at a p b e **
  pure (elen e == len b /\ allocated e)` — and its comment is explicit that
  this is the point: "an object with a declared type does not pass through
  this view at all; **it needs an indexed path of its own**." That path was
  never built. `{t}_stack_alloc` therefore hands back the ordinary
  `{t}_pts_to_uninit`, and `mem_stack_alloc` hands back `ET.etypes_none`
  rather than a `fixed` index.
  Building it means `{t}_pts_to` gains a declared/allocated parameter, since
  the *same* contract has to accept both — `&local` and a `malloc`ed pointer
  both flow into a callee's `int32_t_pts_to`. So it is not only ~13 scalar
  types × the full operation set plus aggregates, arrays and unions, but also
  every generated contract becoming generic in that parameter. Substantial,
  mechanical, and worth deciding deliberately rather than drifting into.
- **Scalar effective types are identified by representation, not by name.**
  `ET.scalar` is a closed set of widths and signednesses, so two distinct C
  types with the same representation are the same `ctype`. This is the scalar
  counterpart of the struct-tag gap below, but strictly worse: a struct at
  least carries its tag in `TStruct` and merely drops it in `{sn}_etype_ok`,
  whereas a scalar has no name in the model to drop. Closing it is an
  `Etype.fst` change, not an emitter change.
- **An aggregate's effective type does not carry its tag, so corpus 13.3 is
  accepted.** 6.2.7p1 makes two structs declared in one translation unit
  compatible only if their tags agree, but the generated `{sn}_etype_ok` is a
  field-wise conjunction, so `struct_sa_etype_ok` and `struct_sb_etype_ok` for
  identical layouts are *literally the same formula*. The tag is present in
  `{sn}_ctype` and `ET.access_ok` distinguishes it — the model has the rule,
  the generated layer does not state it. `etype_struct_tag_gap` pins this, and
  should be converted to a `should-fail` test when it is closed.
- **Cross-type union punning is not supported, and the reason is structural.**
  Reading `u->i` after `u->f = 1.5f` is defined C (6.5.2.3p3 and footnote 95),
  but the emitter refuses it. The obstacle is that `{un}_etype_ok` is only
  `elen /\ allocated`, dropping `read_ok e {un}_ctype`, so `live_ok_read_ok_all`
  — which would re-derive liveness at *any* member, i.e. the punning licence —
  cannot be applied. Restoring that conjunct breaks `{un}_unfocus_{m}`, because
  after a member focus only the member's own `read_ok` is in hand and the
  restoration token `{un}_rest_{m}` has nowhere to carry the parent's index.
  **This is the same missing-token problem that blocks the character bullet**
  (reading any object through `unsigned char *`, corpus 2.x), which needs a
  `char_focus` borrow combinator analogous to `array_focus` for exactly the
  same reason — and it is the same reason the struct tag is lost above, since
  `{sn}_gather` folds an aggregate back together out of the field points-tos
  alone, with each field's index existentially bound inside its own resource.
  **All three gaps are one missing library feature**: a focus that hands back a
  restoration token carrying the parent's effective-type index.
- **`*(int32_t *)pt` for a `struct point *pt` emits code that cannot verify**
  rather than being refused. The emitter resolves it to the first member's
  address but does not emit the member focus bracket, so F\* reports a
  tactic failure naming `int32_t_pts_to (var_pt +! struct_point_offsetof_x)`.
  This predates the cast work above and is reachable without it. A refusal
  would be the honest answer.
- Corpus section 14's declared-object puns are likely to stay ghost: PAL knows
  the declared type statically and would not emit the cross-type read at all.
- **`palow.md`'s "What has been built so far, and what the next domino is"
  section is stale.** It predates the threading and still says "what is *not*
  done is the threading itself", and still describes the planned `fields_ok`
  rather than the `live_ok` that shipped. It also predicts "one large change
  rather than a sequence of small ones", which turned out not to be how it
  went. **This section should be rewritten before merge.**
- A flexible struct that `finish_flex` has gathered into a value still cannot
  be freed — there is no `{sn}_forget` for one. The free path reports this
  rather than mis-translating.
- Corpus section 24 (`case_24_1`) is unmodelled: whether `u->f = x` installs
  `float` or `union upun` is a position the model will have to take, and one
  the C standard does not settle.
- Two section-18 cases are stated as *positive* theorems because the model
  accepts what C calls undefined; both carry a comment saying so.
- Sections 20–23 (`volatile`, `_Atomic`, `restrict`, lifetime, `const`) are
  not 6.5p6/p7 and belong with the features they name.
