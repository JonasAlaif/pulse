module Pulse.C.Types.Scalar
open Pulse.Lib.Pervasives
include Pulse.C.Types.Base

// To be extracted as: t
[@@noextract_to "krml"] // primitive
val scalar_t ( [@@@strictly_positive] t: Type0) : Type0
[@@noextract_to "krml"] // proof-only
val scalar (t: Type) : typedef (scalar_t t)
val mk_scalar (#t: Type) (v: t) : Ghost (scalar_t t)
  (requires True)
  (ensures (fun y ->
    fractionable (scalar t) y /\
    full (scalar t) y
  ))

val mk_scalar_fractionable
  (#t: Type)
  (v: t)
  (p: perm)
: Lemma
  (requires (fractionable (scalar t) (mk_fraction (scalar t) (mk_scalar v) p)))
  (ensures (p `lesser_equal_perm` full_perm))

val mk_scalar_inj
  (#t: Type)
  (v1 v2: t)
  (p1 p2: perm)
: Lemma
  (requires (mk_fraction (scalar t) (mk_scalar v1) p1 == mk_fraction (scalar t) (mk_scalar v2) p2))
  (ensures (v1 == v2 /\ p1 == p2))
  [SMTPat [mk_fraction (scalar t) (mk_scalar v1) p1; mk_fraction (scalar t) (mk_scalar v2) p2]]

```pulse
ghost
fn scalar_unique
  (#t: Type)
  (v1 v2: t)
  (p1 p2: perm)
  (r: ref (scalar t))
requires
    (pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1) ** pts_to r (mk_fraction (scalar t) (mk_scalar v2) p2))
ensures
    (pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1) ** pts_to r (mk_fraction (scalar t) (mk_scalar v2) p2) ** pure (
      v1 == v2 /\ (p1 `sum_perm` p2) `lesser_equal_perm` full_perm
    ))
{
  fractional_permissions_theorem (mk_scalar v1) (mk_scalar v2) p1 p2 r;
  let _ = mk_scalar_inj v1 v2 full_perm full_perm;
  ()
}
```

[@@noextract_to "krml"] // primitive
val read0 (#t: Type) (#v: Ghost.erased t) (#p: perm) (r: ref (scalar t))
: stt t
  (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
  (fun v' -> pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p) ** pure (
    v' == Ghost.reveal v
  ))

let mk_fraction_full_scalar (#t: Type) (v: t) : Lemma
  (mk_scalar v == mk_fraction (scalar t) (mk_scalar v) full_perm)
  [SMTPat (mk_scalar v)]
= ()

val get_scalar_value
  (#t: Type)
  (c: scalar_t t)
: GTot (option t)

val get_scalar_value_mk_fraction
  (#t: Type)
  (c: scalar_t t)
  (p: perm)
: Lemma
  (requires (fractionable (scalar t) c))
  (ensures (get_scalar_value (mk_fraction (scalar t) c p) == get_scalar_value c))
  [SMTPat (get_scalar_value (mk_fraction (scalar t) c p))]

val get_scalar_value_mk_scalar
  (#t: Type)
  (c: t)
: Lemma
  (get_scalar_value (mk_scalar c) == Some c)
  [SMTPat (get_scalar_value (mk_scalar c))]

val get_scalar_value_uninitialized
  (t: Type)
: Lemma
  (get_scalar_value (uninitialized (scalar t)) == None)
  [SMTPat (get_scalar_value (uninitialized (scalar t)))]

val get_scalar_value_unknown
  (t: Type)
: Lemma
  (get_scalar_value (unknown (scalar t)) == None)
  [SMTPat (get_scalar_value (unknown (scalar t)))]

val get_scalar_value_some
  (#t: Type)
  (c: scalar_t t)
: Lemma
  (requires (Some? (get_scalar_value c)))
  (ensures (
    exists v0 p . Ghost.reveal c == mk_fraction (scalar t) (mk_scalar v0) p
  ))
  [SMTPat (get_scalar_value c)]

let read_prf
  (#t: Type)
  (v0: t)
  (p: perm)
: Lemma
  (forall v0' p' . (* {:pattern (mk_fraction (scalar t) (mk_scalar v0) p)} *) mk_fraction (scalar t) (mk_scalar v0') p' == mk_fraction (scalar t) (mk_scalar v0) p ==> (
    v0' == v0 /\
    p' == p
  ))
= 
  let prf v0' p' : Lemma
    (requires (mk_fraction (scalar t) (mk_scalar v0') p' == mk_fraction (scalar t) (mk_scalar v0) p))
    (ensures (v0' == Ghost.reveal v0 /\ p' == Ghost.reveal p))
  = mk_scalar_inj (Ghost.reveal v0) v0' p p'
  in
  let prf' v0' p' : Lemma
    ((mk_fraction (scalar t) (mk_scalar v0') p' == mk_fraction (scalar t) (mk_scalar v0) p) ==> (v0' == Ghost.reveal v0 /\ p' == Ghost.reveal p))
  = Classical.move_requires (prf v0') p'
  in
  Classical.forall_intro_2 prf'

 // FIXME: FStar.IndefiniteDescription.indefinite_description_tot cannot be called directly from Pulse because of refinements on lambdas!
let indefinite_description_tot0 (a:Type) (p:(a -> prop)) (q: squash (exists x. p x))
: Tot (w:Ghost.erased a{ p w })
= FStar.IndefiniteDescription.indefinite_description_tot a p

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn read (#t: Type) (#v: Ghost.erased (scalar_t t)) (r: ref (scalar t))
requires
  (pts_to r v ** pure (
    exists v0 p . Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p
  ))
returns v1: t
ensures
  (pts_to r v ** pure (
    forall v0 p . (* {:pattern (mk_fraction (scalar t) (mk_scalar v0) p)} *) Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p ==> v0 == v1
  ))
{
  let v0 = indefinite_description_tot0 t (fun v0 -> exists p . Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p) ();
  let p = indefinite_description_tot0 perm (fun p -> Ghost.reveal v == mk_fraction (scalar t) (mk_scalar (Ghost.reveal v0)) p) ();
  let _ = read_prf #t v0 p;
  rewrite (pts_to r v) as (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v0)) p));
  let v1 = read0 r;
  rewrite (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v0)) p)) as (pts_to r v);
  v1
}
```

[@@noextract_to "krml"] // primitive
val write (#t: Type) (#v: Ghost.erased (scalar_t t)) (r: ref (scalar t)) (v': t)
: stt unit
  (pts_to r v ** pure (
    full (scalar t) v
  ))
  (fun _ -> pts_to r (mk_scalar v'))
