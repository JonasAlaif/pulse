module Pulse.Checker.Auto.Prover
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Checker.VPropEquiv
open Pulse.Typing.Metatheory
open Pulse.Checker.Auto.Util
module T = FStar.Tactics
module VP = Pulse.Checker.VPropEquiv
module F = Pulse.Checker.Framing

let vprop_typing g v = tot_typing g v Tm_VProp

let ghost_comp pre post = 
  C_STGhost Tm_EmpInames { u=u_zero; res=tm_unit; pre; post }

let unit_const = magic()
let proof_steps_idem
  : st_term
  = { term = Tm_Return { ctag=STT_Ghost; insert_eq=false; term=unit_const};
      range = Range.range_0 }
let proof_steps_idem_typing (g:env) (ctxt:vprop)
  : st_typing g proof_steps_idem (ghost_comp ctxt ctxt)
  = magic()

assume
val post_with_emp (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
  : st_typing g t (comp_st_with_post c (Tm_Star (canon_vprop (comp_post c)) Tm_Emp) )

module Metatheory = Pulse.Typing.Metatheory

let init_prover_state (#g:env) (#ctxt:vprop) (ctxt_typing: vprop_typing g ctxt)
                      (#t:st_term) (#c:comp_st) (t_typing: st_typing g t c)
  : prover_state g ctxt
  = { 
        ctxt_typing;
        t; 
        c; 
        t_typing;

        matched_pre = Tm_Emp;
        unmatched_pre = vprop_as_list (comp_pre c);
        remaining_ctxt = vprop_as_list ctxt;

        pre_equiv = VE_Trans _ _ _ _ (vprop_list_equiv _ (comp_pre c))
                                     (VE_Sym _ _ _ (VP.ve_unit_r _ (canon_vprop (comp_pre c))));
        proof_steps=proof_steps_idem;
        proof_steps_typing=post_with_emp (proof_steps_idem_typing _ ctxt);
    }

open FStar.List.Tot

let is_ghost_comp (c:comp) =
  C_STGhost? c /\ comp_u c == u_zero /\ comp_res c == tm_unit

//
// result of an intro (pure, exists, rewrite) step
//   that consumes some vprop v from p.unmatched_pre
//
noeq
type intro_result (#g:env) (#ctxt:vprop) (p:prover_state g ctxt) = {
  // the vprop that intro introduced
  v : vprop;

  // new unmatched pre and remaining ctxt
  unmatched' : list vprop;
  remaining' : list vprop;

  // the term, comp, and term typing as a witness of the introduction
  t' : st_term;
  c' : c:comp { is_ghost_comp c /\ comp_post c == v };
  t'_typing : st_typing g t' c';

  // relation between new and old unmatched_pre and remaining_ctxt
  unmatched_equiv : vprop_equiv g (list_as_vprop p.unmatched_pre)
                                  (Tm_Star v (list_as_vprop unmatched'));
  remaining_equiv : vprop_equiv g (list_as_vprop p.remaining_ctxt)
                                  (Tm_Star (comp_pre c') (list_as_vprop remaining'));
}


let add_frame (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (f:vprop)
  : c':comp { c' == Pulse.Typing.add_frame c f } &
    st_typing g t c' = admit ()

let with_pre_post (c:comp_st) (pre:vprop) (post:vprop) : comp_st =
  match c with
  | C_ST s
  | C_STGhost _ s
  | C_STAtomic _ s -> with_st_comp c { s with pre; post }

let pre_equiv (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (f:vprop) (_:vprop_equiv g (comp_pre c) f)
  : c':comp { c' == with_pre_post c f (comp_post c) } &
    st_typing g t c' = admit ()

//
// note that we need post to be ln
//
let pre_post_equiv (#g:env) (#t:st_term) (#c:comp_st {ln (comp_post c)})
  (d:st_typing g t c)
  (#pre:vprop) (_:vprop_equiv g (comp_pre c) pre)
  (#post:vprop) (_:vprop_equiv g (comp_post c) post)
  : c':comp_st { c' == with_pre_post c pre post } &
    st_typing g t c' = admit ()

let st_typing_weakening (#g:env) (#t:st_term) (#c:comp)
  (d:st_typing g t c)
  (g':env { env_extends g' g })
  : st_typing g' t c = admit ()


//
// derive next prover state from an intro step
//
#push-options "--z3rlimit_factor 30 --fuel 2 --ifuel 2"
let get_next_prover_state (#g:env) (#ctxt:vprop) (#p:prover_state g ctxt)
  (r:intro_result p)
  : T.Tac (prover_state g ctxt) =
  
  let remaining'_matched = Tm_Star (list_as_vprop r.remaining') p.matched_pre in
  let (| r_c', r_t'_typing |) = add_frame r.t'_typing remaining'_matched in
  assert (comp_pre r_c' == Tm_Star (comp_pre r.c') remaining'_matched);
  assert (comp_post r_c' == Tm_Star r.v remaining'_matched);

  let (| x, bind_continuation_elaborator |) =
    continuation_elaborator_with_bind #g Tm_Emp
    #(ghost_comp ctxt (Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre))
    #p.proof_steps
    p.proof_steps_typing
    (magic () <: tot_typing g (Tm_Star Tm_Emp ctxt) Tm_VProp)
  in

  assume (open_term (Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre) x ==
                    Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre);

  let _ : vprop_equiv g (list_as_vprop p.remaining_ctxt)
                        (Tm_Star (comp_pre r.c') (list_as_vprop r.remaining')) = r.remaining_equiv in
  let d : vprop_equiv g
    (Tm_Star (comp_pre r.c') (Tm_Star (list_as_vprop r.remaining') p.matched_pre))
    (Tm_Star (Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre) Tm_Emp) = magic () in

  let (| r_c', r_t'_typing |) = pre_equiv r_t'_typing
    (Tm_Star (Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre) Tm_Emp)
    d in

  assume (env_extends (extend x (Inl tm_unit) g) g);
  let r_t'_typing = st_typing_weakening r_t'_typing (extend x (Inl tm_unit) g) in

  let post_hint = Some {
    g;
    ret_ty = tm_unit;
    u = u_zero;
    ty_typing = magic ();
    post = comp_post r_c';
    post_typing = magic ();
  } in
  assert (comp_post_matches_hint r_c' post_hint);
  assume (env_extends g g);

  let (| steps, steps_c, steps_typing |) = bind_continuation_elaborator post_hint
    (| r.t', r_c', r_t'_typing  |) in

  assume (stateful_comp steps_c);
  assert (comp_pre steps_c == Tm_Star Tm_Emp ctxt);
  assert (comp_post steps_c == comp_post r_c');
  assume (steps_c == ghost_comp (Tm_Star Tm_Emp ctxt) (comp_post r_c'));
  assume (ln (comp_post steps_c));

  let new_matched = Tm_Star p.matched_pre r.v in
  let new_unmatched = r.unmatched' in
  let new_remaining = r.remaining' in

  assert (comp_post steps_c ==
          Tm_Star r.v (Tm_Star (list_as_vprop r.remaining') p.matched_pre));
  
  let steps_pre_equiv : vprop_equiv g (Tm_Star Tm_Emp ctxt) ctxt = magic () in
  let steps_post_equiv : vprop_equiv g
    (Tm_Star r.v (Tm_Star (list_as_vprop r.remaining') p.matched_pre))
    (Tm_Star (list_as_vprop r.remaining') (Tm_Star p.matched_pre r.v)) = magic () in

  let (| steps_c, steps_typing |) = pre_post_equiv steps_typing
    steps_pre_equiv
    steps_post_equiv in

  assert (comp_pre steps_c == ctxt);
  assert (comp_post steps_c == Tm_Star (list_as_vprop r.remaining')
                                       (Tm_Star p.matched_pre r.v));
  assume (steps_c == ghost_comp ctxt (Tm_Star (list_as_vprop r.remaining')
                                              (Tm_Star p.matched_pre r.v)));

  let d1 : vprop_equiv g (comp_pre p.c)
                         (Tm_Star (list_as_vprop p.unmatched_pre) p.matched_pre) = p.pre_equiv in
  let d2 : vprop_equiv g (list_as_vprop p.unmatched_pre)
                         (Tm_Star r.v (list_as_vprop r.unmatched')) = r.unmatched_equiv in
  let d3 : vprop_equiv g (comp_pre p.c) (Tm_Star (list_as_vprop r.unmatched')
                                                 (Tm_Star p.matched_pre r.v)) = magic () in

  { p with
    matched_pre = Tm_Star p.matched_pre r.v;
    unmatched_pre = r.unmatched';
    remaining_ctxt = r.remaining';
    proof_steps = steps;
    proof_steps_typing = steps_typing;
    pre_equiv = d3 }
#pop-options

let tm_prop = Tm_FStar FStar.Reflection.Typing.tm_prop Range.range_0

type intro_step_t =
  #g:env -> #ctxt:vprop ->
  p:prover_state g ctxt ->
  T.Tac (option (intro_result p))

let get_one_pure (g:env) (l:list vprop)
  : option (v:vprop { Tm_Pure? v } &
            rest:list vprop &
            vprop_equiv g (list_as_vprop l) (Tm_Star v (list_as_vprop rest))) =
  admit ()

// let step_intro_exists : intro_step_t =
//   fun #g #ctxt p ->
//   match get_one_pure g p.unmatched_pre with
//   | None -> None
//   | Some (| v, rest, veq |) ->
//     let Tm_Pure p = v in
//     admit ()


assume val step_intro_exists : intro_step_t
assume val step_intro_pure : intro_step_t
assume val step_intro_rewrite : intro_step_t

let prover_step_intro_exists #g #o (p:prover_state g o)
  : T.Tac (option (prover_state g o)) =
  T.map_opt get_next_prover_state (step_intro_exists p)

let prover_step_intro_pure #g #o (p:prover_state g o)
  : T.Tac (option (prover_state g o)) =
  T.map_opt get_next_prover_state (step_intro_pure p)

let prover_step_intro_rewrite #g #o (p:prover_state g o)
  : T.Tac (option (prover_state g o)) =
  T.map_opt get_next_prover_state (step_intro_rewrite p)

let rec first_success (l:list prover_step_t) : prover_step_t = 
  fun #g #o p ->
    match l with
    | [] -> None
    | s :: l -> 
      match s p with
      | None -> first_success l p
      | Some p -> Some p

(* Take one step of proving, matching at least one unmatched pre, or rewriting the context.
   If neither, then returns None; and the outer loop should fail reporting unmatched preconditions *)
let step : prover_step_t
  = first_success [ Pulse.Checker.Auto.Framing.step_match <: prover_step_t;
                    prover_step_intro_exists <: prover_step_t;
                    prover_step_intro_pure <: prover_step_t;
                    prover_step_intro_rewrite <: prover_step_t ]

let finish #g #o (p:prover_state g o { p.unmatched_pre == []})
  : (t:st_term & c:comp_st { comp_pre c == o } & st_typing g t c)
  = assume (list_as_vprop [] == Tm_Emp);
    let veq1 : vprop_equiv _ (comp_pre p.c) p.matched_pre = VE_Trans _ _ _ _ p.pre_equiv (VE_Unit _ _) in
    let t_typing : st_typing g p.t (comp_st_with_pre p.c p.matched_pre) = st_typing_equiv_pre p.t_typing veq1 in
    let remaining_context_typing : vprop_typing g (list_as_vprop p.remaining_ctxt) = magic () in
    let framing_token : F.frame_for_req_in_ctxt g (proof_steps_post p) p.matched_pre =
      (| list_as_vprop p.remaining_ctxt,
         remaining_context_typing,
         VE_Comm _ _ _ |)
    in
    let ctxt_typing : vprop_typing g (proof_steps_post p) = magic () in
    let (| _, t_typing |) = F.apply_frame ctxt_typing t_typing framing_token in
    let (| t, t_typing |) = bind_proof_steps_with p _ _ t_typing in
    (| _, _, t_typing |)

let as_failure #g #o (p:prover_state g o) = {
  unmatched_preconditions = p.unmatched_pre;
  remaining_context = p.remaining_ctxt
}

let rec solve #g #o (p:prover_state g o)
  : T.Tac 
    (either 
        (t:st_term &
         c:comp_st { comp_pre c == o } &
         st_typing g t c)
        framing_failure)
  = match step p with
    | None -> Inr (as_failure p)
    | Some p ->
      match p.unmatched_pre with
      | [] -> Inl (finish p)
      | _ -> solve p

let prove_precondition (#g:env)
                       (#ctxt:term)
                       (ctxt_typing: tot_typing g ctxt Tm_VProp)
                       (#t:st_term)
                       (#c:comp_st)
                       (t_typing: st_typing g t c)
  : T.Tac 
    (either 
        (t:st_term &
         c:comp_st { comp_pre c == ctxt } &
         st_typing g t c)
        framing_failure)
   = solve (init_prover_state ctxt_typing t_typing)