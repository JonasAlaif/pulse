module PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
module H2 = PulseCore.Heap2
module ST = PulseCore.HoareStateMonad
module CM = FStar.Algebra.CommMonoid
let eset (i:eqtype) = erased (Set.set i)

let non_info (t:Type u#a) : Type u#a = x:erased t -> (y:t { y == reveal x })

let core_ref: Type u#0 = H2.core_ref
let ref (a:Type u#a) (p:pcm a) = core_ref
val is_null (c:core_ref) : GTot bool

let core_ghost_ref : Type u#0 = H2.core_ghost_ref
let ghost_ref (a:Type u#a) (p:pcm a) = core_ghost_ref

noeq
type lens (mem:Type u#a) (core:Type u#b) = {
  get: mem -> core;
  put: core -> mem -> mem;
  get_put : (m:mem -> Lemma (put (get m) m == m));
  put_get : (c:core -> m:mem -> Lemma (get (put c m) == c));
  put_put : (c0:core -> c1:core -> m:mem -> Lemma (put c1 (put c0 m) == put c1 m));
}

noeq
type separable (mem:Type u#a) = {
  core: Type u#a;
  lens_core: lens mem core;
  empty : core;
  disjoint : core -> core -> prop;
  join : (
    m0:core ->
    m1:core { disjoint m0 m1 } ->
    core
  );
  disjoint_sym : (
    m0:core ->
    m1:core ->
    Lemma (disjoint m0 m1 <==> disjoint m1 m0)
  );
  join_commutative : (
    m0:core ->
    m1:core { disjoint m0 m1 } ->
    Lemma (disjoint_sym m0 m1; join m0 m1 == join m1 m0)
  );
  disjoint_join : (
    m0:core ->
    m1:core ->
    m2:core ->
    Lemma (
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) ==>
        disjoint m0 m1 /\
        disjoint m0 m2 /\
        disjoint (join m0 m1) m2 /\
        disjoint (join m0 m2) m1)
  );
  join_associative : (
    m0:core ->
    m1:core ->
    m2:core { disjoint m1 m2 /\ disjoint m0 (join m1 m2) } ->
    Lemma (disjoint m0 m1 /\
           disjoint (join m0 m1) m2 /\
           join m0 (join m1 m2) == join (join m0 m1) m2)
  );
  join_empty : (
    m0:core ->
    Lemma (disjoint m0 empty /\ join m0 empty == m0)
  );
}

let is_affine_mem_prop (#m:Type u#a) (sep:separable m) (p:sep.core -> prop)
: prop
= forall (m0 m1:sep.core). p m0 /\ sep.disjoint m0 m1 ==> p (sep.join m0 m1)

let affine_mem_prop (#m:Type u#a) (sep:separable m)
: Type u#(max 1 a)
= p:(sep.core -> prop){ is_affine_mem_prop sep p }

noeq
type heap_sig : Type u#(a + 2) = {
    mem : Type u#(a + 1);
    sep : separable mem;
    full_mem_pred : mem -> prop;
    
    is_ghost_action : mem -> mem -> prop;
    is_ghost_action_preorder : (
      unit ->
      Lemma (FStar.Preorder.preorder_rel is_ghost_action)
    );

    slprop : Type u#(a + 1);
    interp: slprop -> affine_mem_prop sep;
    as_slprop: affine_mem_prop sep -> slprop;
    interp_as : (
      p:affine_mem_prop sep ->
      Lemma (forall c. interp (as_slprop p) c == p c)
    );
    slprop_extensionality: (
      p:slprop ->
      q:slprop ->
      Lemma ((forall c. interp p c <==> interp q c) ==> p == q)
    );
    non_info_slprop: non_info slprop;

    bprop : Type u#a;
    up: bprop -> slprop;
    down: slprop -> bprop;
    non_info_bprop: non_info bprop;
    up_down: (
      p:bprop ->
      Lemma (down (up p) == p)
    );

    emp : slprop;
    pure : prop -> slprop;
    star : slprop -> slprop -> slprop;
    intro_emp: (
      c:sep.core ->
      Lemma (interp emp c)
    );
    pure_interp: (
      p:prop ->
      c:sep.core ->
      Lemma (interp (pure p) c == p)
    );
    pure_true_emp: (
      unit ->
      Lemma (pure True == emp)
    );
    emp_unit : (
      p:slprop ->
      Lemma (p == (p `star` emp))
    );
    star_commutative: (
      p:slprop ->
      q:slprop ->
      Lemma (p `star` q == q `star` p)
    );
    star_associative: (
      p:slprop ->
      q:slprop ->
      r:slprop ->
      Lemma (p `star` (q `star` r) == (p `star` q) `star` r)
    );
    star_equiv: (
      p:slprop ->
      q:slprop ->
      m:sep.core ->
      Lemma (
        interp (p `star` q) m <==> 
        (exists m0 m1. 
          sep.disjoint m0 m1 /\
          m == sep.join m0 m1 /\
          interp p m0 /\
          interp q m1))
    );
    pts_to: (
      #a:Type u#a ->
      #p:pcm a ->
      ref a p ->
      a ->
      slprop
    );

    ghost_pts_to: (
      meta:bool ->
      #a:Type u#a ->
      #p:pcm a ->
      ghost_ref a p ->
      a ->
      slprop
    );

    iname:eqtype;
    iref:Type0;
    iref_erasable: non_info iref;
    iname_of: (i:iref -> GTot iname);
    inv : iref -> slprop -> slprop;
    iname_ok: iname -> mem -> prop;
    dup_inv_equiv : (
      i:iref ->
      p:slprop ->
      Lemma (inv i p == (inv i p `star` inv i p))
    );
    mem_invariant : eset iname -> mem -> slprop;
    inv_iname_ok : (
      i:iref ->
      p:slprop ->
      m:mem ->
      Lemma 
        (requires interp (inv i p) (sep.lens_core.get m))
        (ensures iname_ok (iname_of i) m)
    );
    mem_invariant_equiv : (
      e:eset iname ->
      m:mem ->
      i:iref ->
      p:slprop ->
      Lemma 
        (requires
          not (iname_of i `Set.mem` e))
        (ensures
          mem_invariant e m `star` inv i p ==
          mem_invariant (Set.add (iname_of i) e) m `star` p `star` inv i p)
    );
}
let core_of (#h:heap_sig) (m:h.mem)
: h.sep.core
= h.sep.lens_core.get m

let interpret (#h:heap_sig u#h) (p:h.slprop) : h.mem -> prop = fun m -> h.interp p (h.sep.lens_core.get m)
let inames (hs:heap_sig u#h) = eset hs.iname
let inames_ok (#hs:heap_sig u#h) (is:inames hs) (m:hs.mem) = forall (i:hs.iname). i `Set.mem` is ==> hs.iname_ok i m
let full_mem (hs:heap_sig u#h) = m:hs.mem{ hs.full_mem_pred m }
let maybe_ghost_action (chs:heap_sig u#m) (maybe_ghost:bool) (m0 m1:chs.mem)
    = maybe_ghost ==> chs.is_ghost_action m0 m1

let step_t 
  (chs:heap_sig u#m)
  (a:Type u#a)
  (maybe_ghost:bool)
  (except:inames chs)
  (expects:chs.slprop)
  (provides: a -> GTot chs.slprop)
  (frame:chs.slprop)
= ST.st #(full_mem chs) a
    (requires fun m0 ->
        inames_ok except m0 /\
        interpret (expects `chs.star` frame `chs.star` chs.mem_invariant except m0) m0)
    (ensures fun m0 x m1 ->
        maybe_ghost_action chs maybe_ghost m0 m1 /\
        inames_ok except m1 /\
        interpret (expects `chs.star` frame `chs.star` chs.mem_invariant except m0) m0 /\  //TODO: fix the effect so as not to repeat this
        interpret (provides x `chs.star` frame `chs.star` chs.mem_invariant except m1) m1)

(** An action is just a thunked computation in [MstTot] that takes a frame as argument *)
let _action_except 
    (chs:heap_sig u#m)
    (a:Type u#a)
    (maybe_ghost:bool)
    (except:inames chs)
    (expects:chs.slprop)
    (provides: a -> GTot chs.slprop)
 : Type u#(max a (m + 1)) 
 = frame:chs.slprop -> step_t chs a maybe_ghost except expects provides frame

let action_except
    (chs:heap_sig u#m)
    (a:Type u#a)
    (except:inames chs)
    (expects:chs.slprop)
    (provides:a -> GTot chs.slprop)
= _action_except chs a false except expects provides

let ghost_action_except
      (chs:heap_sig u#m)
      (a:Type u#a)
      (except:inames chs)
      (expects:chs.slprop)
      (provides: a -> GTot chs.slprop)
= _action_except chs a true except expects provides

let exists_
    (chs:heap_sig u#m)
    (#a:Type u#a)
    (p: a -> GTot chs.slprop)
: chs.slprop
= chs.as_slprop (fun m -> exists (x:a). chs.interp (p x) m)

val cm_slprop (hs:heap_sig u#h) : CM.cm (hs.slprop)
val cm_e_slprop (hs:heap_sig u#h) : CM.cm (erased hs.slprop)