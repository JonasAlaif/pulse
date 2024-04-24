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

module Pulse2Rust.Env

open FStar.Compiler
open FStar.Compiler.Util
open FStar.Compiler.List
open FStar.Compiler.Effect

open FStar.Class.Setlike

open Pulse2Rust.Rust.Syntax

open RustBindings

module S = FStar.Extraction.ML.Syntax

module UEnv = FStar.Extraction.ML.UEnv

let fail (s:string) =
  failwith (format1 "Pulse to Rust extraction failed: %s" s)

let fail_nyi (s:string) =
  failwith (format1 "Pulse to Rust extraction failed: no support yet for %s" s)

let reachable_defs_to_string (d:reachable_defs) : string =
  d |> elems |> String.concat ";" |> format1 "[%s]"

let empty_env (d:dict) (all_modules:list string) (reachable_defs:reachable_defs) =
  { fns = [];
    gamma = [];
    statics = [];
    d;
    all_modules;
    reachable_defs }

let lookup_global_fn (g:env) (s:string) : option fn_signature =
  map_option (fun (_, t) -> t) (tryFind (fun (f, _) -> f = s) g.fns)

let lookup_local (g:env) (s:string) : option (typ & bool) =
  map_option (fun (_, t, b) -> t, b) (tryFind (fun (x, _, _) -> x = s) g.gamma)

let push_fn (g:env) (s:string) (t:fn_signature) : env =
  { g with fns = (s, t)::g.fns }

let push_static (g:env) (s:string) (t:typ) : env =
  { g with statics = (s, t)::g.statics }

let push_local (g:env) (s:string) (t:typ) (is_mut:bool) : env =
  { g with gamma = (s, t, is_mut)::g.gamma }
