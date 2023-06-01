module Pulse.Checker.Auto.Util

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Checker.Framing
open Pulse.Checker.VPropEquiv

module VP = Pulse.Checker.VPropEquiv
module F = Pulse.Checker.Framing
module Metatheory = Pulse.Typing.Metatheory


let k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt
  = fun p r -> r

let k_elab_trans (#g0 #g1 #g2:env) (#ctxt0 #ctxt1 #ctxt2:term)
                 (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
                 (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2
   = fun post_hint res -> k0 post_hint (k1 post_hint res)

let comp_st_with_post (c:comp_st) (post:term) : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i st -> C_STAtomic i {st with post}

let ve_unit_r g (p:term) : vprop_equiv g (Tm_Star p Tm_Emp) p = 
  VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)

let st_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { freevars post `Set.subset` freevars (comp_post c)})
                  (veq: (x:var { Metatheory.fresh_wrt x g (freevars (comp_post c)) } ->
                         vprop_equiv (extend x (Inl (comp_res c)) g) 
                                     (open_term (comp_post c) x)
                                     (open_term post x)))
  : st_typing g t (comp_st_with_post c post)
  = let c' = comp_st_with_post c post in
    let (| u_of, pre_typing, x, post_typing |) = Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness d))) in
    let veq = veq x in
    let st_equiv : st_equiv g c c' =
        ST_VPropEquiv g c c' x pre_typing u_of post_typing (VE_Refl _ _) veq
    in
    T_Equiv _ _ _ _ d st_equiv

let simplify_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { comp_post c == Tm_Star post Tm_Emp})
  : st_typing g t (comp_st_with_post c post)
  = st_equiv_post d post (fun x -> ve_unit_r (extend x (Inl (comp_res c)) g) (open_term post x))

let simplify_lemma (c:comp_st) (c':comp_st) (post_hint:option post_hint_t)
  : Lemma
    (requires
        comp_post_matches_hint c post_hint /\
        comp_res c' == comp_res c /\
        comp_u c' == comp_u c /\
        comp_post c' == Tm_Star (comp_post c) Tm_Emp)
    (ensures comp_post_matches_hint (comp_st_with_post c' (comp_post c)) post_hint /\
             comp_pre (comp_st_with_post c' (comp_post c)) == comp_pre c')
  = () 

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 0"
let k_elab_equiv_continutation (#g1 #g2:env) (#ctxt #ctxt1 #ctxt2:term)
  (k:continuation_elaborator g1 ctxt g2 ctxt1)
  (d:vprop_equiv g2 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt g2 ctxt2 =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g2 ctxt1 ctxt2 =
    let d : vprop_equiv g2 (Tm_Star ctxt2 Tm_Emp) ctxt1 = 
      VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) (VE_Sym _ _ _ d)) in
      (| Tm_Emp, emp_typing, d |)
  in
  let (| st, c, st_d |) = res in
  if not (stateful_comp c) then k post_hint (| st, c, st_d |)
  else
    let (| _, pre_typing, _, _ |) =
      Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness st_d))) in
    let (| c', st_d' |) =
      Pulse.Checker.Framing.apply_frame (vprop_equiv_typing_bk pre_typing d) st_d framing_token in
    assert (comp_post c' == Tm_Star (comp_post c) Tm_Emp);
    let st_d' = simplify_post st_d' (comp_post c) in
    k post_hint (| st, _, st_d' |)
#pop-options

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 0"
let k_elab_equiv_prefix (#g1 #g2:env) (#ctxt1 #ctxt2 #ctxt:term)
  (k:continuation_elaborator g1 ctxt1 g2 ctxt)
  (d:vprop_equiv g1 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt2 g2 ctxt =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g1 ctxt2 ctxt1 = 
  let d = VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) d) in
    (| Tm_Emp, emp_typing, d |)
  in
  let res = k post_hint res in
  let (| st, c, st_d |) = res in
  if not (stateful_comp c) then (| st, c, st_d |)
  else let (| _, pre_typing, _, _ |) =
         Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness st_d))) in
       let (| c', st_d' |) =
         Pulse.Checker.Framing.apply_frame
           (vprop_equiv_typing_fwd pre_typing d)
           st_d
           framing_token in
        simplify_lemma c c' post_hint;
        let c''  = comp_st_with_post c' (comp_post c) in
        let st_d' : st_typing g1 st c'' = simplify_post st_d' (comp_post c) in
        let res : (checker_result_t g1 ctxt2 post_hint) = (| st, c'', st_d' |) in
        res
#pop-options

let k_elab_equiv (#g1 #g2:env) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)                 
                 (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
                 (d1:vprop_equiv g1 ctxt1 ctxt1')
                 (d2:vprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2' =
  
  let k : continuation_elaborator g1 ctxt1 g2 ctxt2' =
    k_elab_equiv_continutation k d2 in
  let k : continuation_elaborator g1 ctxt1' g2 ctxt2' =
    k_elab_equiv_prefix k d1 in
  k

let rec list_as_vprop' (vp:vprop) (fvps:list vprop)
  : Tot vprop (decreases fvps) =
  match fvps with
  | [] -> vp
  | hd::tl -> list_as_vprop' (Tm_Star vp hd) tl

let rec canon_right_aux (g:env) (vps:list vprop) (f:vprop -> T.Tac bool)
  : T.Tac (vps' : list vprop &
           fvps : list vprop &
           vprop_equiv g (list_as_vprop vps) (list_as_vprop' (list_as_vprop vps') fvps)) =

  match vps with
  | [] -> (| [], [], VE_Refl _ _ |)
  | hd::rest ->
    if f hd
    then begin
      let (| vps', fvps, _ |) = canon_right_aux g rest f in
      let v_eq = magic () in
      // let v_eq
      //   : vprop_equiv g (list_as_vprop vps)
      //                   (list_as_vprop (hd :: (vps' @ fvps)))
      //   = list_as_vprop_ctx g [hd] _ rest (vps' @ fvps) (VE_Refl _ _) v_eq    
      // in  
      // let v_eq
      //   : vprop_equiv g (list_as_vprop vps)
      //                   (list_as_vprop ((vps'@[hd]) @ fvps))
      //   = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (vprop_equiv_swap_equiv _ _ _ hd _ (VE_Refl _ _)))
      // in
      // let v_eq 
      //   :  vprop_equiv g (list_as_vprop vps)
      //                    (list_as_vprop (vps'@(hd::fvps)))
      //   = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (list_as_vprop_assoc _ _ _ _)) in
      (| vps', hd :: fvps, v_eq |)
    end
    else begin
      let (| vps', pures, _ |) = canon_right_aux g rest f in
      let v_eq = magic () in //list_as_vprop_ctx g [hd] _ _ _ (VE_Refl _ _) v_eq in
      (| hd::vps', pures, v_eq |)
    end

let canon_right (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
  (f:vprop -> T.Tac bool)
  : T.Tac (ctxt':term &
           tot_typing g ctxt' Tm_VProp &
           continuation_elaborator g ctxt g ctxt')
  = let (| vps', pures, veq |) = canon_right_aux g (vprop_as_list ctxt) f in
    let veq : vprop_equiv g ctxt (list_as_vprop' (list_as_vprop vps') pures)
      = magic () in
    //   VE_Trans _ _ _ _ (vprop_list_equiv g ctxt) veq
    // in
    (| _, VP.vprop_equiv_typing_fwd ctxt_typing veq, k_elab_equiv (k_elab_unit _ _) (VE_Refl _ _) veq |)

#push-options "--query_stats --fuel 2 --ifuel 2 --split_queries no --z3rlimit_factor 8"
let continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (Tm_Star ctxt (comp_pre c1)) Tm_VProp)
  : T.Tac (x:var { None? (lookup g x) } &
           continuation_elaborator
             g (Tm_Star ctxt (comp_pre c1))
             (extend x (Inl (comp_res c1)) g) (Tm_Star (open_term (comp_post c1) x) ctxt)) =

  let pre1 = comp_pre c1 in
  let res1 = comp_res c1 in
  let post1 = comp_post c1 in
  let ctxt_typing = star_typing_inversion_l ctxt_pre1_typing in
  // let p_prop = Metatheory.pure_typing_inversion pure_typing in
  let v_eq = VE_Comm g ctxt pre1 in
  let framing_token : F.frame_for_req_in_ctxt g (Tm_Star ctxt pre1) pre1 = 
    (| ctxt, ctxt_typing, VE_Comm g pre1 ctxt  |)
  in
  let (| c1, e1_typing |) =
    Pulse.Checker.Framing.apply_frame ctxt_pre1_typing e1_typing framing_token in
  let (| u_of_1, pre_typing, _, _ |) =
    Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness e1_typing))) in
  let x = fresh g in
  let b = Inl res1 in
  let g' = extend x b g in
  
  let post1_opened = open_term_nv post1 (v_as_nv x) in
  let k : continuation_elaborator g (Tm_Star ctxt pre1) g' (Tm_Star post1_opened ctxt) =
    fun post_hint res ->
    let (| e2, c2, e2_typing |) = res in
    if not (stateful_comp c2) // || None? post_hint
    then T.fail "Unexpected non-stateful comp in continuation elaborate"
    else (
      let e2_typing : st_typing g' e2 c2 = e2_typing in
      let e2_closed = close_st_term e2 x in
      assume (open_st_term e2_closed x == e2);
      assert (comp_pre c1 == (Tm_Star ctxt pre1));
      assert (comp_post c1 == Tm_Star post1 ctxt);
      assert (comp_pre c2 == Tm_Star post1_opened ctxt);
      assert (open_term (comp_post c1) x == Tm_Star post1_opened (open_term ctxt x));
      // ctxt is well-typed, hence ln
      assume (open_term ctxt x == ctxt);
      assert (open_term (comp_post c1) x == comp_pre c2);
      // we closed e2 with x
      assume (~ (x `Set.mem` freevars_st e2_closed));
      if x `Set.mem` freevars (comp_post c2)
      then T.fail "Impossible"
      else (
        let t_typing, post_typing =
          Pulse.Checker.Bind.bind_res_and_post_typing g (st_comp_of_comp c2) x post_hint in
        let (| e, c, e_typing |) =
          Pulse.Checker.Bind.mk_bind
            g (Tm_Star ctxt pre1) 
            e1 e2_closed c1 c2 (v_as_nv x) e1_typing
            u_of_1 
            e2_typing
            t_typing
            post_typing
        in
        (| e, c, e_typing |)
      )
    )

  in
  (| x, k |)
#pop-options

let elim_one (#g:env)
  (ctxt:term) (p:vprop)
  (ctxt_p_typing:tot_typing g (Tm_Star ctxt p) Tm_VProp)
  (e1:st_term) (c1:comp { stateful_comp c1 /\ comp_pre c1 == p })
  (e1_typing:st_typing g e1 c1)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' Tm_VProp &
           continuation_elaborator g (Tm_Star ctxt p) g' ctxt') =
  
  let ctxt_typing = star_typing_inversion_l ctxt_p_typing in

  let (| x, k |) = continuation_elaborator_with_bind ctxt e1_typing ctxt_p_typing in
  let g' = extend x (Inl (comp_res c1)) g in
  let ctxt_g'_typing : tot_typing g' ctxt Tm_VProp =
    Metatheory.tot_typing_weakening x (Inl (comp_res c1)) ctxt_typing in
  let ctxt' = Tm_Star (open_term_nv (comp_post c1) (v_as_nv x)) ctxt in
  let k
    : continuation_elaborator
        g (Tm_Star ctxt p)
        g' ctxt' =
    k in
  let ctxt'_typing : tot_typing g' ctxt' Tm_VProp = magic () in
  Pulse.Checker.Common.extends_extends_env g x (Inl (comp_res c1));
  (| g', ctxt', ctxt'_typing, k |)

let rec elim_all (#g:env)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (bool & 
           (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt'))
   = match ctxt with
     | Tm_Star ctxt' p ->
       let p_typing = star_typing_inversion_r #_ #ctxt' #p ctxt_typing in
       if f p
       then match mk #_ #p p_typing with
            | Some (| e1, c1, e1_typing |) ->
              let (| g', _, ctxt_typing', k |) =
                elim_one ctxt' p ctxt_typing e1 c1 e1_typing in
              let _, (| g'', ctxt'', ctxt_typing'', k' |) =
                elim_all #g' f mk ctxt_typing' in
              true, (| g'', ctxt'', ctxt_typing'', k_elab_trans k k' |)
            | None ->
              extends_env_refl g;
              false, (| g, ctxt, ctxt_typing, k_elab_unit _ _ |)
       else begin
         extends_env_refl g;
         false, (| g, ctxt, ctxt_typing, k_elab_unit _ _ |)
       end
     | _ ->
       extends_env_refl g;
       false, (| g, ctxt, ctxt_typing, k_elab_unit _ _ |)

let add_elims_aux (#g:env) (#ctxt:term)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (bool & 
           (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt'))
   = let (| ctxt', ctxt'_typing, k |) = canon_right ctxt_typing f in
     let progress, (| g', ctxt'', ctxt''_typing, k' |) =
         elim_all f mk ctxt'_typing in
      extends_env_refl g;
      progress, (| g', ctxt'', ctxt''_typing, k_elab_trans k k' |)

  let rec add_elims (#g:env) (#ctxt:term)
                    (f:vprop -> T.Tac bool)
                    (mk:mk_t)
                    (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt')
   = let progress, res = add_elims_aux f mk ctxt_typing in
     if not progress
     then res
     else (
      let (| g', ctxt', ctxt'_typing, k |) = res in
      let (| g'', ctxt'', ctxt''_typing, k' |) = add_elims f mk ctxt'_typing in
      (| g'', ctxt'', ctxt''_typing, k_elab_trans k k' |)
     )