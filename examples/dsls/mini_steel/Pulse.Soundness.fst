module Pulse.Soundness
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common
module Bind = Pulse.Soundness.Bind
module Lift = Pulse.Soundness.Lift
module Frame = Pulse.Soundness.Frame
module STEquiv = Pulse.Soundness.STEquiv
module Return = Pulse.Soundness.Return
module Exists = Pulse.Soundness.Exists
module LN = Pulse.Typing.LN
module FV = Pulse.Typing.FV

let lift_soundness
  (f:stt_env)
  (g:env)
  (t:term)
  (c:pure_comp)
  (d:src_typing f g t c{T_Lift? d})
  (soundness:(f:stt_env -> g:env -> t:term -> c:pure_comp ->
              d':src_typing f g t c{d' << d} ->
              GTot (RT.typing (extend_env_l f g)
                              (elab_src_typing d')
                              (elab_pure_comp c))))            
  : GTot (RT.typing (extend_env_l f g) (elab_src_typing d) (elab_pure_comp c)) =
  LN.src_typing_ln d;
  let T_Lift _ e c1 c2 e_typing lc = d in
  LN.src_typing_ln e_typing;
  match lc with
  | Lift_STAtomic_ST _ _ ->
    Lift.elab_lift_stt_atomic_typing f g
      c1 c2 _ (soundness _ _ _ _ e_typing) lc
  | Lift_STGhost_STAtomic _ _ w ->
    let (| reveal_a, reveal_a_typing |) = w in
    Lift.elab_lift_stt_ghost_typing f g
      c1 c2 _ (soundness _ _ _ _ e_typing) lc
      _ (soundness _ _ _ _ reveal_a_typing)

let frame_soundness
  (f:stt_env)
  (g:env)
  (t:term)
  (c:pure_comp)
  (d:src_typing f g t c{T_Frame? d})
  (soundness:(f:stt_env -> g:env -> t:term -> c:pure_comp ->
              d':src_typing f g t c{d' << d} ->
              GTot (RT.typing (extend_env_l f g)
                              (elab_src_typing d')
                              (elab_pure_comp c))))            
  : GTot (RT.typing (extend_env_l f g) (elab_src_typing d) (elab_pure_comp c)) =

  let T_Frame _ e c frame frame_typing e_typing = d in
  let r_e_typing = soundness _ _ _ _ e_typing in
  LN.src_typing_ln e_typing;
  Frame.elab_frame_typing f g _ _ frame frame_typing r_e_typing

let stapp_soundness
  (f:stt_env)
  (g:env)
  (t:term)
  (c:pure_comp)
  (d:src_typing f g t c{T_STApp? d})
  (soundness:(f:stt_env -> g:env -> t:term -> c:pure_comp ->
              d':src_typing f g t c{d' << d} ->
              GTot (RT.typing (extend_env_l f g)
                              (elab_src_typing d')
                              (elab_pure_comp c))))            
  : GTot (RT.typing (extend_env_l f g) (elab_src_typing d) (elab_pure_comp c)) =

  let T_STApp _ head ppname formal q res arg head_typing arg_typing = d in
  let E arg_typing = arg_typing in
  let r_head = elab_src_typing head_typing in
  let r_arg = elab_pure arg in
  elab_pure_equiv arg_typing;
  let r_head_typing
    : RT.typing _ r_head (elab_pure (Tm_Arrow {binder_ty=formal;binder_ppname=ppname} q res))
    = soundness _ _ _ _ head_typing
  in
  let r_arg_typing = soundness _ _ _ _ arg_typing in
  elab_comp_open_commute res arg;
  RT.T_App _ _ _ (binder_of_t_q_s (elab_pure formal) (elab_qual q) ppname)
                 (elab_pure_comp res)
                 r_head_typing
                 r_arg_typing

let stequiv_soundness
  (f:stt_env)
  (g:env)
  (t:term)
  (c:pure_comp)
  (d:src_typing f g t c{T_Equiv? d})
  (soundness:(f:stt_env -> g:env -> t:term -> c:pure_comp ->
              d':src_typing f g t c{d' << d} ->
              GTot (RT.typing (extend_env_l f g)
                              (elab_src_typing d')
                              (elab_pure_comp c))))            
  : GTot (RT.typing (extend_env_l f g) (elab_src_typing d) (elab_pure_comp c)) =

  let T_Equiv _ e c c' e_typing equiv = d in
  LN.src_typing_ln d;
  LN.src_typing_ln e_typing;
  let r_e_typing = soundness _ _ _ _ e_typing in 
  STEquiv.st_equiv_soundness _ _ _ _ equiv _ r_e_typing

#push-options "--z3rlimit_factor 4"
let if_soundness
  (f:stt_env)
  (g:env)
  (t:term)
  (c:pure_comp)
  (d:src_typing f g t c{T_If? d})
  (soundness:(f:stt_env -> g:env -> t:term -> c:pure_comp ->
              d':src_typing f g t c{d' << d} ->
              GTot (RT.typing (extend_env_l f g)
                              (elab_src_typing d')
                              (elab_pure_comp c))))
  : GTot (RT.typing (extend_env_l f g)
                    (elab_src_typing d)
                    (elab_pure_comp c)) =

  let T_If _ b e1 e2  _ hyp b_typing e1_typing e2_typing = d in
  let rb_typing : RT.typing (extend_env_l f g)
                            (elab_pure b)
                            RT.bool_ty =
    tot_typing_soundness b_typing in
  let g_then = (hyp, Inl (mk_eq2 U_zero tm_bool b tm_true))::g in
  let re1_typing
    : RT.typing (RT.extend_env (extend_env_l f g)
                               hyp
                               (RT.eq2 (R.pack_universe R.Uv_Zero)
                                       RT.bool_ty
                                       (elab_pure b)
                                       RT.true_bool))
                (elab_src_typing e1_typing)
                (elab_pure_comp c) =
    soundness f g_then e1 c e1_typing in
  let g_else = (hyp, Inl (mk_eq2 U_zero tm_bool b tm_false))::g in
  let re2_typing
    : RT.typing (RT.extend_env (extend_env_l f g)
                               hyp
                               (RT.eq2 (R.pack_universe R.Uv_Zero)
                                       RT.bool_ty
                                       (elab_pure b)
                                       RT.false_bool))
                (elab_src_typing e2_typing)
                (elab_pure_comp c) =
    soundness f g_else e2 c e2_typing in
  RT.T_If _ _ _ _ _ _ rb_typing re1_typing re2_typing
#pop-options

#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 30"
let bind_soundness
  (#f:stt_env)
  (#g:env)
  (#t:term)
  (#c:pure_comp)
  (d:src_typing f g t c{T_Bind? d})
  (soundness:(f:stt_env -> g:env -> t:term -> c:pure_comp ->
              d':src_typing f g t c{d' << d} ->
              GTot (RT.typing (extend_env_l f g)
                              (elab_src_typing d')
                              (elab_pure_comp c))))
  (mk_t_abs: (#u:universe ->
              #ty:pure_term ->
              q:option qualifier ->
              ppname:ppname ->
              t_typing:tot_typing f g ty (Tm_Type u) { t_typing << d } ->
              #body:term ->
              #x:var { None? (lookup g x) } ->
              #c:pure_comp ->
              body_typing:src_typing f ((x, Inl ty)::g) (open_term body x) c { body_typing << d } ->
        GTot (RT.typing (extend_env_l f g)
                        (mk_abs_with_name ppname (elab_pure ty) (elab_qual q) (RT.close_term (elab_src_typing body_typing) x))
                        (elab_pure (Tm_Arrow {binder_ty=ty;binder_ppname=ppname} q (close_pure_comp c x))))))
  : GTot (RT.typing (extend_env_l f g)
                    (elab_src_typing d)
                    (elab_pure_comp c))
  = let T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing bc = d in
    LN.src_typing_ln e1_typing;
    LN.src_typing_ln e2_typing;      
    FV.src_typing_freevars_inv e1_typing x;
    let r1_typing
      : RT.typing _ _ (elab_pure_comp c1)
      = soundness _ _ _ _ e1_typing
    in
    let r2_typing
      : RT.typing _ _ (elab_pure (Tm_Arrow (null_binder (comp_res c1)) None (close_pure_comp c2 x)))
      = mk_t_abs None _ t_typing e2_typing
    in
    match bc with
    | Bind_comp _ _ _ _ t2_typing y post2_typing ->
         Bind.elab_bind_typing f g _ _ _ x _ r1_typing _ r2_typing bc 
                               (tot_typing_soundness t2_typing)
                               (mk_t_abs_tot _ _ _ t2_typing post2_typing)
                               
    | Bind_comp_ghost_l _ _ _ _ (| reveal_a, reveal_a_typing |) t2_typing y post2_typing ->
         Bind.elab_bind_ghost_l_typing f g _ _ _ x _ r1_typing
           _ r2_typing bc
           (tot_typing_soundness t2_typing)
           (mk_t_abs_tot _ _ _ t2_typing post2_typing)
           (elab_pure reveal_a)
           (soundness _ _ _ _ reveal_a_typing)
    | Bind_comp_ghost_r _ _ _ _ (| reveal_b, reveal_b_typing |) t2_typing y post2_typing ->
         Bind.elab_bind_ghost_r_typing f g _ _ _ x _ r1_typing
           _ r2_typing bc
           (tot_typing_soundness t2_typing)
           (mk_t_abs_tot _ _ _ t2_typing post2_typing)
           (elab_pure reveal_b)
           (soundness _ _ _ _ reveal_b_typing)
#pop-options

let elim_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#t:term)
  (#c:pure_comp)
  (d:src_typing f g t c{T_ElimExists? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_src_typing d)
                    (elab_pure_comp c)) =

  let T_ElimExists _ u t p t_typing p_typing = d in
  let ru = elab_universe u in
  let rt_typing = tot_typing_soundness t_typing in
  let rp_typing
    : RT.typing (extend_env_l f g)
                (mk_exists ru (elab_pure t)
                   (mk_abs (elab_pure t) R.Q_Explicit (elab_pure p)))
                vprop_tm
    = tot_typing_soundness p_typing in
  let rp_typing = Exists.exists_inversion rp_typing in
  Exists.elim_exists_soundness rt_typing rp_typing
  
#push-options "--query_stats --fuel 4 --ifuel 4 --z3rlimit_factor 10"
let rec soundness (f:stt_env)
                  (g:env)
                  (t:term)
                  (c:pure_comp)
                  (d:src_typing f g t c)
  : GTot (RT.typing (extend_env_l f g) (elab_src_typing d) (elab_pure_comp c))
         (decreases d)
  = let mk_t_abs (#u:universe)
                 (#ty:pure_term)
                 (q:option qualifier)
                 (ppname:ppname)
                 (t_typing:tot_typing f g ty (Tm_Type u) { t_typing << d })
                 (#body:term)
                 (#x:var { None? (lookup g x) })
                 (#c:pure_comp)
                 (body_typing:src_typing f ((x, Inl ty)::g) (open_term body x) c { body_typing << d })
      : GTot (RT.typing (extend_env_l f g)
                        (mk_abs_with_name ppname (elab_pure ty) (elab_qual q) (RT.close_term (elab_src_typing body_typing) x))
                        (elab_pure (Tm_Arrow {binder_ty=ty;binder_ppname=ppname} q (close_pure_comp c x))))
      = let E t_typing = t_typing in
        let r_t_typing = soundness _ _ _ _ t_typing in
        let r_body_typing = soundness _ _ _ _ body_typing in
        mk_t_abs f g ppname r_t_typing r_body_typing
    in
    LN.src_typing_ln d;
    match d with
    | T_Lift _ _ _ _ _ _ ->
      lift_soundness _ _ _ _ d soundness
    | T_Frame _ _ _ _ _ _ ->
      frame_soundness _ _ _ _ d soundness

    | T_Tot _ _ _ d -> d

    | T_Abs _ ppname x q ty u body c t_typing body_typing ->
      mk_t_abs q ppname t_typing body_typing    

    | T_STApp _ _ _ _ _ _ _ _ _ ->
      stapp_soundness _ _ _ _ d soundness

    | T_Bind _ _e1 _e2 _c1 _c2 _x _c _e1_typing _t_typing _e2_typing _bc ->
      bind_soundness d soundness mk_t_abs

    | T_Equiv _ _ _ _ _ _ ->
      stequiv_soundness _ _ _ _ d soundness

    | T_Return _ e t u e_typing t_typing ->
      Return.elab_return_typing t_typing e_typing

    | T_ReturnNoEq _ e t u e_typing t_typing ->
      let e_typing = soundness _ _ _ _ e_typing in
      Return.elab_return_noeq_typing t_typing e_typing

    | T_If _ _ _ _ _ _ _ _ _ ->
      if_soundness _ _ _ _ d soundness

    | T_ElimExists _ _ _ _ _ _ ->
      elim_exists_soundness d
    | T_IntroExists _ _ _ _ _ _ _ _ -> admit ()

#pop-options

let soundness_lemma
  (f:stt_env)
  (g:env)
  (t:term)
  (c:pure_comp)
  (d:src_typing f g t c)
  : Lemma (ensures RT.typing (extend_env_l f g)
                             (elab_src_typing d)
                             (elab_pure_comp c))
  = FStar.Squash.bind_squash
      #(src_typing f g t c)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness f g t c d))
