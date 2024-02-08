(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Soundness.WithLocalArray

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module WT = Pulse.Steel.Wrapper.Typing

#push-options "--ifuel 1 --fuel 8 --z3rlimit_factor 10"
let withlocalarray_soundness #g #t #c d soundness =
  let T_WithLocalArray _ _ init len body init_t c x init_typing len_typing init_t_typing c_typing body_typing = d in
  let CT_ST _ st st_typing = c_typing in
  
  let rg =  elab_env g in
  let ru = comp_u c in
  let ra = elab_term init_t in
  let rinit = elab_term init in
  let rlen = elab_term len in
  let rpre = elab_term (comp_pre c) in
  let rret_t = elab_term (comp_res c) in
  let rpost = elab_term (comp_post c) in
  let rbody = elab_st_typing body_typing in

  let a_typing = tot_typing_soundness init_t_typing in
  let rinit_typing = tot_typing_soundness init_typing in
  let rlen_typing = tot_typing_soundness len_typing in
  let cres_typing, cpre_typing, cpost_typing =
    Pulse.Soundness.Comp.stc_soundness st_typing in

  let pre_typing = cpre_typing in
  let ret_t_typing = cres_typing in
  let post_typing = cpost_typing in

  elab_push_binding g x (mk_array init_t);
  let rbody_typing = soundness _ _ _ body_typing in

  WT.with_localarray_typing
    #rg
    #ru
    #ra
    #rinit
    #rlen
    #rpre
    #rret_t
    #rpost
    #rbody
    x
    a_typing
    rinit_typing
    rlen_typing
    pre_typing
    ret_t_typing
    post_typing
    rbody_typing