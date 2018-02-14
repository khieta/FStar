(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
module FStar.TypeChecker.Tc
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Errors
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.Rel
open FStar.TypeChecker.Common
open FStar.TypeChecker.TcTerm
module S  = FStar.Syntax.Syntax
module SP  = FStar.Syntax.Print
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util
module BU = FStar.Util //basic util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print
module TcInductive = FStar.TypeChecker.TcInductive
module PC = FStar.Parser.Const


//set the name of the query so that we can correlate hints to source program fragments
let set_hint_correlator env se =
    match Options.reuse_hint_for () with
    | Some l ->
      let lid = Ident.lid_add_suffix (Env.current_module env) l in
      {env with qname_and_index=Some (lid, 0)}

    | None ->
      let lids = U.lids_of_sigelt se in
      let lid = match lids with
            | [] -> Ident.lid_add_suffix (Env.current_module env)
                                         (S.next_id () |> BU.string_of_int)
            | l::_ -> l in
      {env with qname_and_index=Some (lid, 0)}

let log env = (Options.log_types()) &&  not(lid_equals PC.prims_lid (Env.current_module env))

let get_tactic_fv env (tac_lid: lident) (h: term) =
  match h.n with
  | Tm_uinst (h', _) ->
    (match (SS.compress h').n with
      | Tm_fvar fv when (S.fv_eq_lid fv PC.tactic_lid) -> Some fv
      | _ -> None)
  | _ -> None

let is_builtin_tactic md =
  let path = Ident.path_of_lid md in
  if List.length(path) > 2 then
    match fst (List.splitAt 2 path) with
    | ["FStar"; "Tactics"]
    | ["FStar"; "Reflection"] -> true
    | _ -> false
  else false

(* This reference keeps a list of modules which contain user-defined tactics. It is only
   modified in tc_decl to add these modules and only read in FStar.Main (via FStar.Universal,
   in order to compile these modules when generating native tactics. *)
let user_tactics_modules: ref<list<string>> = BU.mk_ref []

(*****************Type-checking the signature of a module*****************************)

let tc_check_trivial_guard env t k =
  let t, c, g = tc_check_tot_or_gtot_term env t k in
  Rel.force_trivial_guard env g;
  t

// A helper to check that the terms elaborated by DMFF are well-typed
let recheck_debug s env t =
  if Env.debug env (Options.Other "ED") then
    BU.print2 "Term has been %s-transformed to:\n%s\n----------\n" s (Print.term_to_string t);
  let t', _, _ = tc_term env t in
  if Env.debug env (Options.Other "ED") then
    BU.print1 "Re-checked; got:\n%s\n----------\n" (Print.term_to_string t');
  // Return the original term (without universes unification variables);
  // because [tc_eff_decl] will take care of these
  t


let check_and_gen env t k =
    // BU.print1 "\x1b[01;36mcheck and gen \x1b[00m%s\n" (Print.term_to_string t);
    TcUtil.generalize_universes env (tc_check_trivial_guard env t k)

let check_nogen env t k =
    let t = tc_check_trivial_guard env t k in
    [], N.normalize [N.Beta] env t

let monad_signature env m s =
 let fail () = raise_error (Err.unexpected_signature_for_monad env m s) (range_of_lid m) in
 let s = SS.compress s in
 match s.n with
  | Tm_arrow(bs, c) ->
    let bs = SS.open_binders bs in
    begin match bs with
        | [(a, _);(wp, _)] -> a, wp.sort
        | _ -> fail()
    end
  | _ -> fail()

let tc_eff_decl env0 (ed:Syntax.eff_decl) =
//  printfn "initial eff_decl :\n\t%s\n" (FStar.Syntax.Print.eff_decl_to_string false ed);
  let open_annotated_univs, annotated_univ_names = SS.univ_var_opening ed.univs in
  let open_univs n_binders t =
      SS.subst (SS.shift_subst n_binders open_annotated_univs) t
  in
  let open_univs_binders n_binders bs =
      SS.subst_binders (SS.shift_subst n_binders open_annotated_univs) bs
  in
  let n_effect_params = List.length ed.binders in
  let effect_params_un, signature_un, opening =
      SS.open_term' (open_univs_binders 0 ed.binders)
                    (open_univs n_effect_params ed.signature) in
  let effect_params, env, _ = tc_tparams env0 effect_params_un in
  let signature, _    = tc_trivial_guard env signature_un in
  let ed = {ed with binders=effect_params;
                    signature=signature} in
  //open ed's operations with respect to the effect parameters that are already in scope
  let ed =
    match effect_params, annotated_univ_names with
    | [], [] -> ed
    | _ ->
        let op (us, t) =
            let n_us = List.length us in
            us, SS.subst (SS.shift_subst n_us opening)
                         (open_univs (n_effect_params + n_us) t)
        in
        { ed with
            univs         = annotated_univ_names;
            ret_wp        =op ed.ret_wp
            ; bind_wp     =op ed.bind_wp
            ; return_repr =op ed.return_repr
            ; bind_repr   =op ed.bind_repr
            ; if_then_else=op ed.if_then_else
            ; ite_wp      =op ed.ite_wp
            ; stronger    =op ed.stronger
            ; close_wp    =op ed.close_wp
            ; assert_p    =op ed.assert_p
            ; assume_p    =op ed.assume_p
            ; null_wp     =op ed.null_wp
            ; trivial     =op ed.trivial
            ; repr        = snd (op ([], ed.repr))
            ; actions     = List.map (fun a ->
            { a with
                action_defn = snd (op ([], a.action_defn));
                action_typ  = snd (op ([], a.action_typ)) }) ed.actions
        }
  in
//  printfn "eff_decl after opening:\n\t%s\n" (FStar.Syntax.Print.eff_decl_to_string false ed);
   //Returns (a:Type) and M.WP a, for a fresh name a
  let wp_with_fresh_result_type env mname signature =
       let fail t =
           raise_error (Err.unexpected_signature_for_monad env mname t)
                        (range_of_lid mname) in
       match (SS.compress signature).n with
       | Tm_arrow(bs, c) ->
         let bs = SS.open_binders bs in
         begin match bs with
               | [(a, _);(wp, _)] -> a, wp.sort
               | _ -> fail signature
         end
       | _ -> fail signature
  in
  let a, wp_a = wp_with_fresh_result_type env ed.mname ed.signature in
  let fresh_effect_signature ()  =
      match annotated_univ_names with
      | [] ->
        //we type-check the signature_un again, because we want a fresh universe
        let signature, _ = tc_trivial_guard env signature_un in
        wp_with_fresh_result_type env ed.mname signature
      | _ ->
        let _, signature =
            Env.inst_tscheme (annotated_univ_names,
                              Subst.close_univ_vars annotated_univ_names signature) in
        wp_with_fresh_result_type env ed.mname signature
  in

  //put the signature in the environment to prevent generalizing its free universe variables until we're done
  let env = Env.push_bv env (S.new_bv None ed.signature) in

  if Env.debug env0 <| Options.Other "ED"
  then BU.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                        (Print.lid_to_string ed.mname)
                        (Print.binders_to_string " " ed.binders)
                        (Print.term_to_string ed.signature)
                        (Print.term_to_string (S.bv_to_name a))
                        (Print.term_to_string a.sort);

  let check_and_gen' env (us,t) k =
      match annotated_univ_names with
      | [] -> check_and_gen env t k
      | _::_ ->
        let (us, t) = SS.subst_tscheme open_annotated_univs (us, t) in
        let us, t = SS.open_univ_vars us t in
        let _ = tc_check_trivial_guard env t k in
        us, SS.close_univ_vars us t
  in

  let return_wp =
    let expected_k = U.arrow [S.mk_binder a; S.null_binder (S.bv_to_name a)] (S.mk_GTotal wp_a) in
    check_and_gen' env ed.ret_wp expected_k in

  let bind_wp =
    let b, wp_b = fresh_effect_signature () in
    let a_wp_b = U.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_b) in
    let expected_k = U.arrow [S.null_binder t_range;
                                 S.mk_binder a; S.mk_binder b;
                                 S.null_binder wp_a;
                                 S.null_binder a_wp_b]
                                 (S.mk_Total wp_b) in
    check_and_gen' env ed.bind_wp expected_k in

  let if_then_else =
    let p = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let expected_k = U.arrow [S.mk_binder a; S.mk_binder p;
                                 S.null_binder wp_a;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.if_then_else expected_k in

  let ite_wp =
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.ite_wp expected_k in

  let stronger =
    let t, _ = U.type_u() in
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder wp_a;
                                 S.null_binder wp_a]
                                (S.mk_Total t) in
    check_and_gen' env ed.stronger expected_k in

  let close_wp =
    let b = S.new_bv (Some (range_of_lid ed.mname)) (U.type_u() |> fst) in
    let b_wp_a = U.arrow [S.null_binder (S.bv_to_name b)] (S.mk_Total wp_a) in
    let expected_k = U.arrow [S.mk_binder a; S.mk_binder b; S.null_binder b_wp_a]
                                (S.mk_Total wp_a) in
    check_and_gen' env ed.close_wp expected_k in

  let assert_p =
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder (U.type_u() |> fst);
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.assert_p expected_k in

  let assume_p =
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder (U.type_u() |> fst);
                                 S.null_binder wp_a]
                                 (S.mk_Total wp_a) in
    check_and_gen' env ed.assume_p expected_k in

  let null_wp =
    let expected_k = U.arrow [S.mk_binder a]
                                (S.mk_Total wp_a) in
    check_and_gen' env ed.null_wp expected_k in

  let trivial_wp =
    let t, _ = U.type_u() in
    let expected_k = U.arrow [S.mk_binder a;
                                 S.null_binder wp_a]
                                (S.mk_GTotal t) in
    check_and_gen' env ed.trivial expected_k in

  let repr, bind_repr, return_repr, actions =
      match (SS.compress ed.repr).n with
      | Tm_unknown -> //This is not a DM4F effect definition; so nothing to do
        ed.repr, ed.bind_repr, ed.return_repr, ed.actions
      | _ ->
        //This is a DM4F effect definition
        //Need to check that the repr, bind, return and actions have their expected types
        let repr =
            let t, _ = U.type_u () in
            let expected_k = U.arrow [S.mk_binder a;
                                         S.null_binder wp_a]
                                         (S.mk_GTotal t) in
            (* printfn "About to check repr=%s\nat type %s\n" (Print.term_to_string ed.repr) (Print.term_to_string expected_k); *)
            tc_check_trivial_guard env ed.repr expected_k in

        let mk_repr' t wp =
            let repr = N.normalize [N.EraseUniverses; N.AllowUnboundUniverses] env repr in
            mk (Tm_app(repr, [as_arg t; as_arg wp])) None Range.dummyRange in

        let mk_repr a wp =
            mk_repr' (S.bv_to_name a) wp in

        let destruct_repr t =
            match (SS.compress t).n with
            | Tm_app(_, [(t, _); (wp, _)]) -> t, wp
            | _ -> failwith "Unexpected repr type" in

        let bind_repr =
            let r = S.lid_as_fv PC.range_0 Delta_constant None |> S.fv_to_tm in
            let b, wp_b = fresh_effect_signature () in
            let a_wp_b = U.arrow [S.null_binder (S.bv_to_name a)] (S.mk_Total wp_b) in
            let wp_f = S.gen_bv "wp_f" None wp_a in
            let wp_g = S.gen_bv "wp_g" None a_wp_b in
            let x_a = S.gen_bv "x_a" None (S.bv_to_name a) in
            let wp_g_x = mk_Tm_app (S.bv_to_name wp_g) [as_arg <| S.bv_to_name x_a] None Range.dummyRange in
            let res =
                let wp = mk_Tm_app (Env.inst_tscheme bind_wp |> snd)
                                   (List.map as_arg [r; S.bv_to_name a;
                                                     S.bv_to_name b; S.bv_to_name wp_f;
                                                     S.bv_to_name wp_g])
                                   None Range.dummyRange in
                mk_repr b wp in

            let expected_k = U.arrow [S.mk_binder a;
                                         S.mk_binder b;
                                         S.mk_binder wp_f;
                                         S.null_binder (mk_repr a (S.bv_to_name wp_f));
                                         S.mk_binder wp_g;
                                         S.null_binder (U.arrow [S.mk_binder x_a] (S.mk_Total <| mk_repr b (wp_g_x)))]
                                        (S.mk_Total res) in
//            printfn "About to check expected_k %s\n"
//                     (Print.term_to_string expected_k);
            let expected_k, _, _ =
                tc_tot_or_gtot_term env expected_k in
//            printfn "About to check bind=%s\n\n, at type %s\n"
//                     (Print.term_to_string (snd ed.bind_repr))
//                     (Print.term_to_string expected_k);
            let env = Env.set_range env (snd (ed.bind_repr)).pos in
            let env = {env with lax=true} in //we do not expect the bind to verify, since that requires internalizing monotonicity of WPs
            let br = check_and_gen' env ed.bind_repr expected_k in
//            let _ = printfn "After checking bind_repr is %s\nexpected_k is %s\n" (Print.tscheme_to_string br) (Print.term_to_string expected_k) in
            br in

        let return_repr =
            let x_a = S.gen_bv "x_a" None (S.bv_to_name a) in
            let res =
                let wp = mk_Tm_app (Env.inst_tscheme return_wp |> snd)
                                   (List.map as_arg [S.bv_to_name a; S.bv_to_name x_a])
                                   None Range.dummyRange in
                mk_repr a wp in
            let expected_k = U.arrow [S.mk_binder a;
                                         S.mk_binder x_a]
                                       (S.mk_Total res) in
            let expected_k, _, _ =
                tc_tot_or_gtot_term env expected_k in
            (* printfn "About to check return_repr=%s, at type %s\n" *)
            (*         (Print.term_to_string (snd ed.return_repr)) *)
            (*         (Print.term_to_string expected_k); *)
            let env = Env.set_range env (snd (ed.return_repr)).pos in
            let univs, repr = check_and_gen' env ed.return_repr expected_k in
            match univs with
            | [] -> [], repr
            | _ -> raise_error (Errors.Fatal_UnexpectedUniversePolymorphicReturn, "Unexpected universe-polymorphic return for effect") repr.pos in

      let actions =
        let check_action (act:action) =
          (* We should not have action params anymore, they should have been handled by dmff below *)
          assert (match act.action_params with | [] -> true | _ -> false) ;

          // 0) The action definition has a (possibly) useless type; the
          // action cps'd type contains the "good" wp that tells us EVERYTHING
          // about what this action does. Please note that this "good" wp is
          // of the form [binders -> repr ...], i.e. is it properly curried.
          let act_typ, _, g_t = tc_tot_or_gtot_term env act.action_typ in

          // 1) Check action definition, setting its expected type to
          //    [action_typ]
          let env' = { Env.set_expected_typ env act_typ with instantiate_imp = false } in
          if Env.debug env (Options.Other "ED") then
            BU.print3 "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
              (text_of_lid act.action_name) (Print.term_to_string act.action_defn)
              (Print.term_to_string act_typ);
          let act_defn, _, g_a = tc_tot_or_gtot_term env' act.action_defn in

          let act_defn = N.normalize [ N.UnfoldUntil S.Delta_constant ] env act_defn in
          let act_typ = N.normalize [ N.UnfoldUntil S.Delta_constant; N.Eager_unfolding; N.Beta ] env act_typ in
          // 2) This implies that [action_typ] has Type(k): good for us!

          // 3) Unify [action_typ] against [expected_k], because we also need
          // to check that the action typ is of the form [binders -> repr ...]
          let expected_k, g_k =
            let act_typ = SS.compress act_typ in
            match act_typ.n with
            | Tm_arrow(bs, c) ->
              let bs, _ = SS.open_comp bs c in
              let res = mk_repr' S.tun S.tun in
              let k = U.arrow bs (S.mk_Total res) in
              let k, _, g = tc_tot_or_gtot_term env k in
              k, g
            | _ -> raise_error (Errors.Fatal_ActionMustHaveFunctionType, (BU.format2
              "Actions must have function types (not: %s, a.k.a. %s)"
                (Print.term_to_string act_typ) (Print.tag_of_term act_typ))) act_defn.pos
          in
          let g = Rel.teq env act_typ expected_k in
          Rel.force_trivial_guard env (Rel.conj_guard g_a (Rel.conj_guard g_k (Rel.conj_guard g_t g)));

          // 4) Do a bunch of plumbing to assign a type in the new monad to
          //    the action
          let act_typ = match (SS.compress expected_k).n with
              | Tm_arrow(bs, c) ->
                let bs, c = SS.open_comp bs c in
                let a, wp = destruct_repr (U.comp_result c) in
                let c = {
                  comp_univs=[env.universe_of env a];
		          effect_name = ed.mname;
                  result_typ = a;
                  effect_args = [as_arg wp];
                  flags = []
                } in
                U.arrow bs (S.mk_Comp c)
              | _ -> failwith "Impossible (expected_k is an arrow)" in

          (* printfn "Checked action %s against type %s\n" *)
          (*         (Print.term_to_string act_defn) *)
          (*         (Print.term_to_string (N.normalize [N.Beta] env act_typ)); *)

          let univs, act_defn = TcUtil.generalize_universes env act_defn in
          let act_typ = N.normalize [N.Beta] env act_typ in
          let act_typ = Subst.close_univ_vars univs act_typ in
          {act with
              action_univs=univs;
              action_defn=act_defn;
              action_typ =act_typ }
        in
        ed.actions |> List.map check_action in
      repr, bind_repr, return_repr, actions
  in

  //generalize and close
  (* QUESTION (KM) : Why do we close with ed.binders and not effect_params ?? *)
  let t0 = U.arrow ed.binders (S.mk_Total ed.signature) in
  let (univs, t) =
      let gen_univs, t = TcUtil.generalize_universes env0 t0 in
      match annotated_univ_names with
      | [] -> gen_univs, t
      | _ ->
        if List.length gen_univs = List.length annotated_univ_names
        && List.forall2 (fun u1 u2 -> FStar.Syntax.Syntax.order_univ_name u1 u2 = 0)
                         gen_univs
                         annotated_univ_names
        then gen_univs, t
        else raise_error (Errors.Fatal_UnexpectedNumberOfUniverse, (BU.format2 "Expected an effect definition with %s universes; but found %s"
                                        (BU.string_of_int (List.length annotated_univ_names))
                                        (BU.string_of_int (List.length gen_univs))))
                          ed.signature.pos
  in
  let signature = match effect_params, (SS.compress t).n with
    | [], _ -> t
    | _, Tm_arrow(_, c) -> U.comp_result c
    | _ -> failwith "Impossible : t is an arrow" in
  let close n ts =
    let ts = SS.close_univ_vars_tscheme univs (SS.close_tscheme effect_params ts) in
    // We always close [bind_repr], even though it may be [Tm_unknown]
    // (non-reifiable, non-reflectable effect)
    let m = List.length (fst ts) in
    if n >= 0 && not (is_unknown (snd ts)) && m <> n
    then begin
      let error = if m < n then "not universe-polymorphic enough" else "too universe-polymorphic" in
      let err_msg =
        BU.format4 "The effect combinator is %s (m,n=%s,%s) (%s)"
          error (string_of_int m) (string_of_int n) (Print.tscheme_to_string ts)
      in
      raise_error (Errors.Fatal_MismatchUniversePolymorphic, err_msg) (snd ts ).pos
    end ;
    ts in
  let close_action act =
    let univs, defn = close (-1) (act.action_univs, act.action_defn) in
    let univs', typ = close (-1) (act.action_univs, act.action_typ) in
    assert (List.length univs = List.length univs');
    { act with
        action_univs=univs;
        action_defn=defn;
        action_typ=typ; }
  in
  assert (List.length effect_params > 0 || List.length univs = 1);
  let ed = { ed with
      univs       = univs
    ; binders     = effect_params (* QUESTION (KM) : don't we need to close the effect params ? *)
    ; signature   = signature
    ; ret_wp      = close 0 return_wp
    ; bind_wp     = close 1 bind_wp
    ; if_then_else= close 0 if_then_else
    ; ite_wp      = close 0 ite_wp
    ; stronger    = close 0 stronger
    ; close_wp    = close 1 close_wp
    ; assert_p    = close 0 assert_p
    ; assume_p    = close 0 assume_p
    ; null_wp     = close 0 null_wp
    ; trivial     = close 0 trivial_wp
    ; repr        = (snd (close 0 ([], repr)))
    ; return_repr = close 0 return_repr
    ; bind_repr   = close 1 bind_repr
    ; actions     = List.map close_action actions} in

  if Env.debug env Options.Low
  || Env.debug env <| Options.Other "ED"
  then BU.print_string (Print.eff_decl_to_string false ed);
  ed


let cps_and_elaborate env ed =
  // Using [STInt: a:Type -> Effect] as an example...
  let effect_binders_un, signature_un = SS.open_term ed.binders ed.signature in
  // [binders] is the empty list (for [ST (h: heap)], there would be one binder)
  let effect_binders, env, _ = tc_tparams env effect_binders_un in
  // [signature] is a:Type -> effect
  let signature, _ = tc_trivial_guard env signature_un in
  // We will open binders through [open_and_check]

  let raise_error : (Errors.raw_error * string) -> 'a = fun (e, err_msg) ->
    Errors.raise_error (e, err_msg) signature.pos
  in

  let effect_binders = List.map (fun (bv, qual) ->
    { bv with sort = N.normalize [ N.EraseUniverses ] env bv.sort }, qual
  ) effect_binders in

  // Every combinator found in the effect declaration is parameterized over
  // [binders], then [a]. This is a variant of [open_effect_signature] where we
  // just extract the binder [a].
  let a, effect_marker =
    // TODO: more stringent checks on the shape of the signature; better errors
    match (SS.compress signature_un).n with
    | Tm_arrow ([(a, _)], effect_marker) ->
        a, effect_marker
    | _ ->
        raise_error (Errors.Fatal_BadSignatureShape, "bad shape for effect-for-free signature")
  in

  (* TODO : having "_" as a variable name can create a really strange shadowing
            behaviour between uu___ variables in the tcterm ; needs to be investigated *)
  let a =
      if S.is_null_bv a
      then S.gen_bv "a" (Some (S.range_of_bv a)) a.sort
      else a
  in

  let open_and_check env other_binders t =
    let subst = SS.opening_of_binders (effect_binders @ other_binders) in
    let t = SS.subst subst t in
    let t, comp, _ = tc_term env t in
    t, comp
  in
  let mk x = mk x None signature.pos in

  // TODO: check that [_comp] is [Tot Type]
  let repr, _comp = open_and_check env [] ed.repr in
  if Env.debug env (Options.Other "ED") then
    BU.print1 "Representation is: %s\n" (Print.term_to_string repr);

  let dmff_env = DMFF.empty env (tc_constant env Range.dummyRange) in
  let wp_type = DMFF.star_type dmff_env repr in
  let wp_type = recheck_debug "*" env wp_type in
  let wp_a = N.normalize [ N.Beta ] env (mk (Tm_app (wp_type, [ (S.bv_to_name a, S.as_implicit false) ]))) in

  // Building: [a -> wp a -> Effect]
  let effect_signature =
    let binders = [ (a, S.as_implicit false); S.gen_bv "dijkstra_wp" None wp_a |> S.mk_binder ] in
    let binders = close_binders binders in
    mk (Tm_arrow (binders, effect_marker))
  in
  let effect_signature = recheck_debug "turned into the effect signature" env effect_signature in

  let sigelts = BU.mk_ref [] in
  let mk_lid name : lident = U.dm4f_lid ed name in

  // TODO: we assume that reading the top-level definitions in the order that
  // they come in the effect definition is enough... probably not
  let elaborate_and_star dmff_env other_binders item =
    let env = DMFF.get_env dmff_env in
    let u_item, item = item in
    // TODO: assert no universe polymorphism
    let item, item_comp = open_and_check env other_binders item in
    if not (U.is_total_lcomp item_comp) then
      raise_err (Errors.Fatal_ComputationNotTotal, (BU.format2 "Computation for [%s] is not total : %s !" (Print.term_to_string item) (Print.lcomp_to_string item_comp)));
    let item_t, item_wp, item_elab = DMFF.star_expr dmff_env item in
    let item_wp = recheck_debug "*" env item_wp in
    let item_elab = recheck_debug "_" env item_elab in
    dmff_env, item_t, item_wp, item_elab
  in

  let dmff_env, _, bind_wp, bind_elab = elaborate_and_star dmff_env [] ed.bind_repr in
  let dmff_env, _, return_wp, return_elab = elaborate_and_star dmff_env [] ed.return_repr in
  let rc_gtot = {
            residual_effect = PC.effect_GTot_lid;
            residual_typ = None;
            residual_flags = []
  } in

  (* Starting from [return_wp (b1:Type) (b2:b1) : M.wp b1 = fun bs -> body <: Type0], we elaborate *)
  (* [lift_from_pure (b1:Type) (wp:(b1 -> Type0)-> Type0) : M.wp b1 = fun bs -> wp (fun b2 -> body)] *)
  let lift_from_pure_wp =
      match (SS.compress return_wp).n with
      | Tm_abs (b1 :: b2 :: bs, body, what) ->
        let b1,b2, body =
          match SS.open_term [b1 ; b2] (U.abs bs body None) with
          | [b1 ; b2], body -> b1, b2, body
          | _ -> failwith "Impossible : open_term not preserving binders arity"
        in
        (* WARNING : pushing b1 and b2 in env might break the well-typedness *)
        (* invariant but we need them for normalization *)
        let env0 = push_binders (DMFF.get_env dmff_env) [b1 ; b2] in
        let wp_b1 =
          let raw_wp_b1 = mk (Tm_app (wp_type, [ (S.bv_to_name (fst b1), S.as_implicit false) ])) in
          N.normalize [ N.Beta ] env0 raw_wp_b1
        in
        let bs, body, what' = U.abs_formals <| N.eta_expand_with_type env0 body (U.unascribe wp_b1) in

        (* We check that what' is Tot Type0 *)
        let fail () =
          let error_msg =
            BU.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s"
              (Print.term_to_string body)
              (match what' with
               | None -> "None"
               | Some rc -> FStar.Ident.text_of_lid rc.residual_effect)
          in raise_error (Errors.Fatal_WrongBodyTypeForReturnWP, error_msg)
        in
        begin match what' with
        | None -> fail ()
        | Some rc ->
          if not (U.is_pure_effect rc.residual_effect) then fail ();
          BU.map_opt rc.residual_typ (fun rt ->
              let g_opt = Rel.try_teq true env rt U.ktype0 in
              match g_opt with
                | Some g' -> Rel.force_trivial_guard env g'
                | None -> fail ()) |> ignore
        end ;

        let wp =
          let t2 = (fst b2).sort in
          let pure_wp_type = DMFF.double_star t2 in
          S.gen_bv "wp" None pure_wp_type
        in

        (* fun b1 wp -> (fun bs@bs'-> wp (fun b2 -> body $$ Type0) $$ Type0) $$ wp_a *)
        let body = mk_Tm_app (S.bv_to_name wp) [U.abs [b2] body what', None] None Range.dummyRange in
        U.abs ([ b1; S.mk_binder wp ])
              (U.abs (bs) body what)
              (Some rc_gtot)

      | _ ->
          raise_error (Errors.Fatal_UnexpectedReturnShape, "unexpected shape for return")
  in

  let return_wp =
    // TODO: fix [tc_eff_decl] to deal with currying
    match (SS.compress return_wp).n with
    | Tm_abs (b1 :: b2 :: bs, body, what) ->
        U.abs ([ b1; b2 ]) (U.abs bs body what) (Some rc_gtot)
    | _ ->
        raise_error (Errors.Fatal_UnexpectedReturnShape, "unexpected shape for return")
  in
  let bind_wp =
    match (SS.compress bind_wp).n with
    | Tm_abs (binders, body, what) ->
        // TODO: figure out how to deal with ranges
        let r = S.lid_as_fv PC.range_lid (S.Delta_defined_at_level 1) None in
        U.abs ([ S.null_binder (mk (Tm_fvar r)) ] @ binders) body what
    | _ ->
        raise_error (Errors.Fatal_UnexpectedBindShape, "unexpected shape for bind")
  in

  let apply_close t =
    if List.length effect_binders = 0 then
      t
    else
      close effect_binders (mk (Tm_app (t, snd (U.args_of_binders effect_binders))))
  in
  let rec apply_last f l = match l with
    | [] -> failwith "empty path.."
    | [a] -> [f a]
    | (x::xs) -> x :: (apply_last f xs)
  in
  let register name item =
    let p = path_of_lid ed.mname in
    let p' = apply_last (fun s -> "__" ^ s ^ "_eff_override_" ^ name) p in
    let l' = lid_of_path p' Range.dummyRange in
    match try_lookup_lid env l' with
    | Some (_us,_t) -> begin
      if Options.debug_any () then
          BU.print1 "DM4F: Applying override %s\n" (string_of_lid l');
      // TODO: GM: get exact delta depth, needs a change of interfaces
      fv_to_tm (lid_as_fv l' Delta_equational None)
      end
    | None ->
      let sigelt, fv = TcUtil.mk_toplevel_definition env (mk_lid name) (U.abs effect_binders item None) in
      sigelts := sigelt :: !sigelts;
      fv
  in
  let lift_from_pure_wp = register "lift_from_pure" lift_from_pure_wp in

  // we do not expect the return_elab to verify, since that may require internalizing monotonicity of WPs (i.e. continuation monad)
  let return_wp = register "return_wp" return_wp in
  Options.push ();
  sigelts := mk_sigelt (Sig_pragma (SetOptions "--admit_smt_queries true")) :: !sigelts;
  let return_elab = register "return_elab" return_elab in
  Options.pop();

  // we do not expect the bind to verify, since that requires internalizing monotonicity of WPs
  let bind_wp = register "bind_wp" bind_wp in
  Options.push ();
  sigelts := mk_sigelt (Sig_pragma (SetOptions "--admit_smt_queries true")) :: !sigelts;
  let bind_elab = register "bind_elab" bind_elab in
  Options.pop ();

  let dmff_env, actions = List.fold_left (fun (dmff_env, actions) action ->
    let params_un = SS.open_binders action.action_params in
    let action_params, env', _ = tc_tparams (DMFF.get_env dmff_env) params_un in
    let action_params = List.map (fun (bv, qual) ->
      { bv with sort = N.normalize [ N.EraseUniverses ] env' bv.sort }, qual
    ) action_params in
    let dmff_env' = DMFF.set_env dmff_env env' in
    // We need to reverse-engineer what tc_eff_decl wants here...
    let dmff_env, action_t, action_wp, action_elab =
      elaborate_and_star dmff_env' action_params (action.action_univs, action.action_defn)
    in
    let name = action.action_name.ident.idText in
    let action_typ_with_wp = DMFF.trans_F dmff_env' action_t action_wp in
    let action_params = SS.close_binders action_params in
    let action_elab = SS.close action_params action_elab in
    let action_typ_with_wp = SS.close action_params action_typ_with_wp in
    let action_elab = abs action_params action_elab None in
    let action_typ_with_wp =
      match action_params with
      | [] -> action_typ_with_wp
      | _ -> flat_arrow action_params (S.mk_Total action_typ_with_wp)
    in
    if Env.debug env <| Options.Other "ED"
    then BU.print4 "original action_params %s, end action_params %s, type %s, term %s\n"
        (Print.binders_to_string "," params_un)
        (Print.binders_to_string "," action_params)
        (Print.term_to_string action_typ_with_wp)
        (Print.term_to_string action_elab);
    let action_elab = register (name ^ "_elab") action_elab in
    let action_typ_with_wp = register (name ^ "_complete_type") action_typ_with_wp in
    (* it does not seem that dmff_env' has been modified  by elaborate_and_star so it should be okay to return the original env *)
    dmff_env,
    { action with
      action_params = [] ;
      action_defn = apply_close action_elab;
      action_typ = apply_close action_typ_with_wp
    } :: actions
  ) (dmff_env, []) ed.actions in
  let actions = List.rev actions in

  let repr =
    let wp = S.gen_bv "wp_a" None wp_a in
    let binders = [ S.mk_binder a; S.mk_binder wp ] in
    U.abs binders (DMFF.trans_F dmff_env (mk (Tm_app (repr, [ S.bv_to_name a, S.as_implicit false ]))) (S.bv_to_name wp)) None
  in
  let repr = recheck_debug "FC" env repr in
  let repr = register "repr" repr in

  (* We are still lacking a principled way to generate pre/post condition *)
  (* Current algorithm takes the type of wps : fun (a: Type) -> (t1 -> t2 ... -> tn -> Type0) *)
  (* Checks that there is exactly one ti containing the type variable a and returns that ti *)
  (* as type of postconditons, the rest as type of preconditions *)
  let pre, post =
    match (unascribe <| SS.compress wp_type).n with
    | Tm_abs (type_param :: effect_param, arrow, _) ->
        let type_param , effect_param, arrow =
            match SS.open_term (type_param :: effect_param) arrow with
                | (b :: bs), body -> b, bs, body
                | _ -> failwith "Impossible : open_term nt preserving binders arity"
        in
        begin match (unascribe <| SS.compress arrow).n with
        | Tm_arrow (wp_binders, c) ->
            let wp_binders, c = SS.open_comp wp_binders c in
            let pre_args, post_args =
                List.partition (fun (bv,_) ->
                  Free.names bv.sort |> BU.set_mem (fst type_param) |> not
                ) wp_binders
            in
            let post = match post_args with
                | [post] -> post
                | [] ->
                  let err_msg =
                    BU.format1 "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                      (Print.term_to_string arrow)
                  in
                  raise_err (Errors.Fatal_ImpossibleToGenerateDMEffect, err_msg)
                | _ ->
                  let err_msg =
                      BU.format1 "Impossible to generate DM effect: multiple post candidates %s" (Print.term_to_string arrow)
                  in
                  raise_err (Errors.Fatal_ImpossibleToGenerateDMEffect, err_msg)
            in
            // Pre-condition does not mention the return type; don't close over it
            U.arrow pre_args c,
            // Post-condition does, however!
            U.abs (type_param :: effect_param) (fst post).sort None
        | _ ->
            raise_error (Errors.Fatal_ImpossiblePrePostArrow, (BU.format1 "Impossible: pre/post arrow %s" (Print.term_to_string arrow)))
        end
    | _ ->
        raise_error (Errors.Fatal_ImpossiblePrePostAbs, (BU.format1 "Impossible: pre/post abs %s" (Print.term_to_string wp_type)))
  in
  // Desugaring is aware of these names and generates references to them when
  // the user writes something such as [STINT.repr]
  ignore (register "pre" pre);
  ignore (register "post" post);
  ignore (register "wp" wp_type);

  let ed = { ed with
    signature = close effect_binders effect_signature;
    repr = apply_close repr;
    ret_wp = [], apply_close return_wp;
    bind_wp = [], apply_close bind_wp;
    return_repr = [], apply_close return_elab;
    bind_repr = [], apply_close bind_elab;
    actions = actions; // already went through apply_close
    binders = close_binders effect_binders
  } in


  // Generate the missing combinators.
  let sigelts', ed = DMFF.gen_wps_for_free env effect_binders a wp_a ed in
  if Env.debug env (Options.Other "ED") then
    BU.print_string (Print.eff_decl_to_string true ed);

  let lift_from_pure_opt =
    if List.length effect_binders = 0 then begin
      // Won't work with parameterized effect
      let lift_from_pure = {
          source = PC.effect_PURE_lid;
          target = ed.mname ;
          lift_wp = Some ([], apply_close lift_from_pure_wp) ;
          lift = None //Some ([], apply_close return_elab)
      } in
      Some (mk_sigelt (Sig_sub_effect (lift_from_pure)))
    end else None
  in

  List.rev !sigelts @ sigelts', ed, lift_from_pure_opt


let tc_lex_t env ses quals lids =
    (* We specifically type lex_t as:

          type lex_t<u> : Type(u) =
          datacon LexTop<utop>  : lex_t<utop>
          datacon LexCons<ucons1, ucons2> : #a:Type(ucons1) -> hd:a -> tl:lex_t<ucons2> -> lex_t<max ucons1 ucons2>
    *)
    assert (quals = []);
    let err_range = (List.hd ses).sigrng in
    begin match lids with
        | [lex_t; lex_top; lex_cons] when
            (lid_equals lex_t PC.lex_t_lid
             && lid_equals lex_top PC.lextop_lid
             && lid_equals lex_cons PC.lexcons_lid) -> ()
        | _ -> Errors.raise_error (Errors.Fatal_InvalidRedefinitionOfLexT, ("Invalid (partial) redefinition of lex_t")) err_range
    end;
    begin match ses with
      | [{ sigel = Sig_inductive_typ(lex_t, [], [], t, _, _);  sigquals = []; sigrng = r };
         { sigel = Sig_datacon(lex_top, [], _t_top, _lex_t_top, 0, _); sigquals = []; sigrng = r1 };
         { sigel = Sig_datacon(lex_cons, [], _t_cons, _lex_t_cons, 0, _); sigquals = []; sigrng = r2 }]
         when (lid_equals lex_t PC.lex_t_lid
            && lid_equals lex_top PC.lextop_lid
            && lid_equals lex_cons PC.lexcons_lid) ->

        let u = S.new_univ_name (Some r) in
        let t = mk (Tm_type(U_name u)) None r in
        let t = Subst.close_univ_vars [u] t in
        let tc = { sigel = Sig_inductive_typ(lex_t, [u], [], t, [], [PC.lextop_lid; PC.lexcons_lid]);
                   sigquals = [];
                   sigrng = r;
                   sigmeta = default_sigmeta;
                   sigattrs = [] } in

        let utop = S.new_univ_name (Some r1) in
        let lex_top_t = mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r1) Delta_constant None, [U_name utop])) None r1 in
        let lex_top_t = Subst.close_univ_vars [utop] lex_top_t in
        let dc_lextop = { sigel = Sig_datacon(lex_top, [utop], lex_top_t, PC.lex_t_lid, 0, []);
                          sigquals = [];
                          sigrng = r1;
                          sigmeta = default_sigmeta;
                          sigattrs = []  } in

        let ucons1 = S.new_univ_name (Some r2) in
        let ucons2 = S.new_univ_name (Some r2) in
        let lex_cons_t =
            let a = S.new_bv (Some r2) (mk (Tm_type(U_name ucons1)) None r2) in
            let hd = S.new_bv (Some r2) (S.bv_to_name a) in
            let tl = S.new_bv (Some r2) (mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r2) Delta_constant None, [U_name ucons2])) None r2) in
            let res = mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r2) Delta_constant None, [U_max [U_name ucons1; U_name ucons2]])) None r2 in
            U.arrow [(a, Some S.imp_tag); (hd, None); (tl, None)] (S.mk_Total res) in
        let lex_cons_t = Subst.close_univ_vars [ucons1;ucons2]  lex_cons_t in
        let dc_lexcons = { sigel = Sig_datacon(lex_cons, [ucons1;ucons2], lex_cons_t, PC.lex_t_lid, 0, []);
                           sigquals = [];
                           sigrng = r2;
                           sigmeta = default_sigmeta;
                           sigattrs = []  } in
        { sigel = Sig_bundle([tc; dc_lextop; dc_lexcons], lids);
          sigquals = [];
          sigrng = Env.get_range env;
          sigmeta = default_sigmeta;
          sigattrs = []  }
      | _ ->
        let err_msg =
          BU.format1 "Invalid (re)definition of lex_t: %s\n"
            (Print.sigelt_to_string (mk_sigelt (Sig_bundle(ses, lids))))
        in
        raise_error (Errors.Fatal_InvalidRedefinitionOfLexT, err_msg) err_range
    end

let tc_assume (env:env) (lid:lident) (phi:formula) (quals:list<qualifier>) (r:Range.range) :sigelt =
    let env = Env.set_range env r in
    let k, _ = U.type_u() in
    let phi = tc_check_trivial_guard env phi k |> N.normalize [N.Beta; N.Eager_unfolding] env in
    TcUtil.check_uvars r phi;
    let us, phi = TcUtil.generalize_universes env phi in
    { sigel = Sig_assume(lid, us, phi);
      sigquals = quals;
      sigrng = r;
      sigmeta = default_sigmeta;
      sigattrs = []  }

let tc_inductive env ses quals lids =
    let env = Env.push env "tc_inductive" in
    let sig_bndle, tcs, datas = TcInductive.check_inductive_well_typedness env ses quals lids in
    (* we have a well-typed inductive;
            we still need to check whether or not it supports equality
            and whether it is strictly positive
       *)

    (* Once the datacons are generalized we can construct the projectors with the right types *)
    let data_ops_ses = List.map (TcUtil.mk_data_operations quals env tcs) datas |> List.flatten in

    //strict positivity check
    (if Options.no_positivity () || Options.lax ()  then ()  //skipping positivity check if lax mode
     else
       let env = push_sigelt env sig_bndle in
       let b = List.iter (fun ty ->
         let b = TcInductive.check_positivity ty env in
         if not b then
           let lid, r =
             match ty.sigel with
             | Sig_inductive_typ (lid, _, _, _, _, _) -> lid, ty.sigrng
             | _                                         -> failwith "Impossible!"
           in
           Errors.log_issue r (Errors.Error_InductiveTypeNotSatisfyPositivityCondition, ("Inductive type " ^ lid.str ^ " does not satisfy the positivity condition"))
         else ()
       ) tcs in
       ());

    //generate hasEq predicate for this inductive
    //skip logical connectives types in prims, tcs is bound to the inductive type, caller ensures its length is > 0
    let skip_prims_type (_:unit) :bool =
        let lid =
            let ty = List.hd tcs in
            match ty.sigel with
                | Sig_inductive_typ (lid, _, _, _, _, _) -> lid
                | _                                         -> failwith "Impossible"
        in
        //these are the prims type we are skipping
        let types_to_skip = [ "c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"; ] in
        List.existsb (fun s -> s = lid.ident.idText) types_to_skip
    in

    let is_noeq = List.existsb (fun q -> q = Noeq) quals in

    let res =
        if ((List.length tcs = 0) || ((lid_equals env.curmodule PC.prims_lid) && skip_prims_type ()) || is_noeq)
        then [sig_bndle], data_ops_ses
        else
            let is_unopteq = List.existsb (fun q -> q = Unopteq) quals in
            let ses =
              if is_unopteq then TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env tc_assume
              else TcInductive.optimized_haseq_scheme sig_bndle tcs datas env tc_assume
            in
            { sigel = Sig_bundle(tcs@datas, lids);
              sigquals = quals;
              sigrng = Env.get_range env;
              sigmeta = default_sigmeta;
              sigattrs = []  }::ses, data_ops_ses in
    ignore (Env.pop env "tc_inductive");
    res


(* [tc_decl env se] typechecks [se] in environment [env] and returns *)
(* the list of typechecked sig_elts, and a list of new sig_elts elaborated during typechecking but not yet typechecked *)
let tc_decl env se: list<sigelt> * list<sigelt> =
  let env = set_hint_correlator env se in
  TcUtil.check_sigelt_quals env se;
  let r = se.sigrng in
  match se.sigel with
  | Sig_inductive_typ _
  | Sig_datacon _ ->
    failwith "Impossible bare data-constructor"

  | Sig_bundle(ses, lids) when (lids |> BU.for_some (lid_equals PC.lex_t_lid)) ->
    //lex_t is very special; it uses a more expressive form of universe polymorphism than is allowed elsewhere
    //Instead of this special treatment, we could make use of explicit lifts, but LexCons is used pervasively
    (*
        type lex_t<u> =
          | LexTop<u>  : lex_t<u>
          | LexCons<u1, u2> : #a:Type(u1) -> a -> lex_t<u2> -> lex_t<max u1 u2>
    *)
    let env = Env.set_range env r in
    let se = tc_lex_t env ses se.sigquals lids  in
    [se], []

  | Sig_bundle(ses, lids) ->
    let env = Env.set_range env r in
    let ses, projectors_ses = tc_inductive env ses se.sigquals lids in
    ses, projectors_ses

  | Sig_pragma(p) ->
    U.process_pragma p r;
    [se], []

  | Sig_new_effect_for_free (ne) ->
      (* This is only an elaboration rule not a typechecking one *)

      // Let the power of Dijkstra generate everything "for free", then defer
      // the rest of the job to [tc_decl].
      let ses, ne, lift_from_pure_opt = cps_and_elaborate env ne in
      let effect_and_lift_ses = match lift_from_pure_opt with
          | Some lift -> [ { se with sigel = Sig_new_effect (ne) } ; lift ]
          | None -> [ { se with sigel = Sig_new_effect (ne) } ]
      in

      [], ses @ effect_and_lift_ses

  | Sig_new_effect(ne) ->
    let ne = tc_eff_decl env ne in
    let se = { se with sigel = Sig_new_effect(ne) } in
    [se], []

  | Sig_sub_effect(sub) ->
    let ed_src = Env.get_effect_decl env sub.source in
    let ed_tgt = Env.get_effect_decl env sub.target in
    let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
    let b, wp_b_tgt = monad_signature env sub.target (Env.lookup_effect_lid env sub.target) in
    let wp_a_tgt    = SS.subst [NT(b, S.bv_to_name a)] wp_b_tgt in
    let expected_k  = U.arrow [S.mk_binder a; S.null_binder wp_a_src] (S.mk_Total wp_a_tgt) in
    let repr_type eff_name a wp =
      let no_reify l = raise_error (Errors.Fatal_EffectCannotBeReified, (BU.format1 "Effect %s cannot be reified" l.str)) (Env.get_range env) in
      match Env.effect_decl_opt env eff_name with
      | None -> no_reify eff_name
      | Some (ed, qualifiers) ->
          let repr = Env.inst_effect_fun_with [U_unknown] env ed ([], ed.repr) in
          if not (qualifiers |> List.contains Reifiable) then
            no_reify eff_name
          else
            mk (Tm_app(repr, [as_arg a; as_arg wp])) None (Env.get_range env)
    in
    let lift, lift_wp =
      match sub.lift, sub.lift_wp with
      | None, None ->
        failwith "Impossible (parser)"
      | lift, Some (_, lift_wp) ->
        (* Covers both the "classic" format and the reifiable case. *)
        lift, check_and_gen env lift_wp expected_k
      (* Sub-effect for free case *)
      | Some (what, lift), None ->
        if Env.debug env (Options.Other "ED") then
            BU.print1 "Lift for free : %s\n" (Print.term_to_string lift) ;
        let dmff_env = DMFF.empty env (tc_constant env Range.dummyRange) in
        let lift, comp, _ = tc_term env lift in
        (* TODO : Check that comp is pure ? *)
        let _, lift_wp, lift_elab = DMFF.star_expr dmff_env lift in
        let _ = recheck_debug "lift-wp" env lift_wp in
        let _ = recheck_debug "lift-elab" env lift_elab in
        Some ([], lift_elab), ([], lift_wp)
    in
    let lax = env.lax in
    (* we do not expect the lift to verify, *)
    (* since that requires internalizing monotonicity of WPs *)
    let env = {env with lax=true} in
    let lift = match lift with
    | None -> None
    | Some (_, lift) ->
      let a, wp_a_src = monad_signature env sub.source (Env.lookup_effect_lid env sub.source) in
      let wp_a = S.new_bv None wp_a_src in
      let a_typ = S.bv_to_name a in
      let wp_a_typ = S.bv_to_name wp_a in
      let repr_f = repr_type sub.source a_typ wp_a_typ in
      let repr_result =
        let lift_wp = N.normalize [N.EraseUniverses; N.AllowUnboundUniverses] env (snd lift_wp) in
        let lift_wp_a = mk (Tm_app(lift_wp, [as_arg a_typ; as_arg wp_a_typ])) None (Env.get_range env) in
        repr_type sub.target a_typ lift_wp_a in
      let expected_k =
        U.arrow [S.mk_binder a; S.mk_binder wp_a; S.null_binder repr_f]
                    (S.mk_Total repr_result) in
//          printfn "LIFT: Expected type for lift = %s\n" (Print.term_to_string expected_k);
        let expected_k, _, _ =
          tc_tot_or_gtot_term env expected_k in
//          printfn "LIFT: Checking %s against expected type %s\n" (Print.term_to_string lift) (Print.term_to_string expected_k);
        let lift = check_and_gen env lift expected_k in
//          printfn "LIFT: Checked %s against expected type %s\n" (Print.tscheme_to_string lift) (Print.term_to_string expected_k);
        Some lift
    in
    let sub = {sub with lift_wp=Some lift_wp; lift=lift} in
    let se = { se with sigel = Sig_sub_effect(sub) } in
    [se], []

  | Sig_effect_abbrev(lid, uvs, tps, c, flags) ->
    assert (uvs = []);
    let env0 = env in
    let env = Env.set_range env r in
    let tps, c = SS.open_comp tps c in
    let tps, env, us = tc_tparams env tps in
    let c, u, g = tc_comp env c in
    Rel.force_trivial_guard env g;
    let tps = SS.close_binders tps in
    let c = SS.close_comp tps c in
    let uvs, t = TcUtil.generalize_universes env0 (mk (Tm_arrow(tps, c)) None r) in
    let tps, c = match tps, (SS.compress t).n with
      | [], Tm_arrow(_, c) -> [], c
      | _,  Tm_arrow(tps, c) -> tps, c
      | _ -> failwith "Impossible (t is an arrow)" in
    if List.length uvs <> 1
    then (let _, t = Subst.open_univ_vars uvs t in
          raise_error (Errors.Fatal_TooManyUniverse, (BU.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                  (Print.lid_to_string lid)
                                  (List.length uvs |> BU.string_of_int)
                                  (Print.term_to_string t))) r);
    let se = { se with sigel = Sig_effect_abbrev(lid, uvs, tps, c, flags) } in
    [se], []

  | Sig_declare_typ (_, _, _)
  | Sig_let (_, _)
      when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) ->
      (* Dummy declaration which must be erased since it has been elaborated somewhere else *)
      [], []

  | Sig_declare_typ(lid, uvs, t) -> //NS: No checks on the qualifiers?
    let env = Env.set_range env r in

    if lid_exists env lid
    then raise_error (Errors.Fatal_AlreadyDefinedTopLevelDeclaration, (BU.format1 "Top-level declaration %s for a name that is already used in this module; \
                                   top-level declarations must be unique in their module"
                                   (Ident.text_of_lid lid))) r;

    let uvs, t =
        if uvs = []
        then check_and_gen env t (fst (U.type_u()))
        else
            let uvs, t = SS.open_univ_vars uvs t in
            let t = tc_check_trivial_guard env t (fst (U.type_u())) in
            let t = N.normalize [N.NoFullNorm; N.Beta] env t in
            uvs, SS.close_univ_vars uvs t
    in
    let se = { se with sigel = Sig_declare_typ(lid, uvs, t) } in
    [se], []

  | Sig_assume(lid, us, phi) ->
    let _, phi = SS.open_univ_vars us phi in
    let se = tc_assume env lid phi se.sigquals r in
    [se], []

  | Sig_main(e) ->
    let env = Env.set_range env r in
    let env = Env.set_expected_typ env t_unit in
    let e, c, g1 = tc_term env e in
    let e, _, g = check_expected_effect env (Some (U.ml_comp t_unit r)) (e, lcomp_comp c) in
    Rel.force_trivial_guard env (Rel.conj_guard g1 g);
    let se = { se with sigel = Sig_main(e) } in
    [se], []

  | Sig_let(lbs, lids) ->
    let env = Env.set_range env r in
    let check_quals_eq l qopt q = match qopt with
      | None -> Some q
      | Some q' ->
        if List.length q = List.length q'
        && List.forall2 U.qualifier_equal q q'
        then Some q
        else raise_error (Errors.Fatal_InconsistentQualifierAnnotation, (BU.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              (Print.lid_to_string l)
                              (Print.quals_to_string q)
                              (Print.quals_to_string q'))) r
    in

    let rename_parameters lb =
      let rename_in_typ def typ =
        let typ = Subst.compress typ in
        let def_bs = match (Subst.compress def).n with
                     | Tm_abs (binders, _, _) -> binders
                     | _ -> [] in
        match typ with
        | { n = Tm_arrow(val_bs, c); pos = r } -> begin
          let has_auto_name bv =
            BU.starts_with bv.ppname.idText Ident.reserved_prefix in
          let rec rename_binders def_bs val_bs =
            match def_bs, val_bs with
            | [], _ | _, [] -> val_bs
            | (body_bv, _) :: bt, (val_bv, aqual) :: vt ->
              (match has_auto_name body_bv, has_auto_name val_bv with
               | true, _ -> (val_bv, aqual)
               | false, true -> ({ val_bv with
                                   ppname = { val_bv.ppname with
                                              idText = body_bv.ppname.idText } }, aqual)
               | false, false ->
                 // if body_bv.ppname.idText <> val_bv.ppname.idText then
                 //   Errors.warn body_bv.ppname.idRange
                 //     (BU.format2 "Parameter name %s doesn't match name %s used in val declaration"
                 //                  body_bv.ppname.idText val_bv.ppname.idText);
                 (val_bv, aqual)) :: rename_binders bt vt in
          Syntax.mk (Tm_arrow(rename_binders def_bs val_bs, c)) None r end
        | _ -> typ in
      { lb with lbtyp = rename_in_typ lb.lbdef lb.lbtyp } in

    (* 1. (a) Annotate each lb in lbs with a type from the corresponding val decl, if there is one
          (b) Generalize the type of lb only if none of the lbs have val decls nor explicit universes
      *)
    let should_generalize, lbs', quals_opt =
       snd lbs |> List.fold_left (fun (gen, lbs, quals_opt) lb ->
          let lbname = right lb.lbname in //this is definitely not a local let binding
          let gen, lb, quals_opt = match Env.try_lookup_val_decl env lbname.fv_name.v with
            | None ->
                if lb.lbunivs <> []
                then false, lb, quals_opt // we already have generalized universes (e.g. elaborated term)
                else gen, lb, quals_opt //no annotation found; use whatever was in the let binding

            | Some ((uvs,tval), quals) ->
              let quals_opt = check_quals_eq lbname.fv_name.v quals_opt quals in
              let def = match lb.lbtyp.n with
                | Tm_unknown -> lb.lbdef
                | _ ->
                  (* If there are two type ascriptions we check that they are compatible *)
                  mk (Tm_ascribed (lb.lbdef, (Inl lb.lbtyp, None), None)) None lb.lbdef.pos
              in
              if lb.lbunivs <> [] && List.length lb.lbunivs <> List.length uvs
              then raise_error (Errors.Fatal_IncoherentInlineUniverse, ("Inline universes are incoherent with annotation from val declaration")) r;
              false, //explicit annotation provided; do not generalize
              mk_lb (Inr lbname, uvs, PC.effect_ALL_lid, tval, def),
              quals_opt
          in
          gen, lb::lbs, quals_opt)
          (true, [], (if se.sigquals=[] then None else Some se.sigquals))
    in

    let quals = match quals_opt with
      | None -> [Visible_default]
      | Some q ->
        if q |> BU.for_some (function Irreducible | Visible_default | Unfold_for_unification_and_vcgen -> true | _ -> false)
        then q
        else Visible_default::q //the default visibility for a let binding is Unfoldable
    in

    let lbs' = List.rev lbs' in

    (* 2. Turn the top-level lb into a Tm_let with a unit body *)
    let e = mk (Tm_let((fst lbs, lbs'), mk (Tm_constant (Const_unit)) None r)) None r in

    (* 3. Type-check the Tm_let and then convert it back to a Sig_let *)
    let se, lbs = match tc_maybe_toplevel_term ({env with top_level=true; generalize=should_generalize}) e with
      | {n=Tm_let(lbs, e)}, _, g when Rel.is_trivial g ->
        // Propagate binder names into signature
        let lbs = (fst lbs, (snd lbs) |> List.map rename_parameters) in

        //propagate the MaskedEffect tag to the qualifiers
        let quals = match e.n with
            | Tm_meta(_, Meta_desugared Masked_effect) -> HasMaskedEffect::quals
            | _ -> quals
        in
        { se with sigel = Sig_let(lbs, lids);
                  sigquals =  quals },
        lbs
      | _ -> failwith "impossible (typechecking should preserve Tm_let)"
    in

    (* 4. Record the type of top-level lets, and log if requested *)
    snd lbs |> List.iter (fun lb ->
        let fv = right lb.lbname in
        Env.insert_fv_info env fv lb.lbtyp);

    if log env
    then BU.print1 "%s\n" (snd lbs |> List.map (fun lb ->
          let should_log = match Env.try_lookup_val_decl env (right lb.lbname).fv_name.v with
              | None -> true
              | _ -> false in
          if should_log
          then BU.format2 "let %s : %s" (Print.lbname_to_string lb.lbname) (Print.term_to_string (*env*) lb.lbtyp)
          else "") |> String.concat "\n");

    (* 5. If top-level let is a user-defined tactic, check if it has been dynamically loaded as a native tactic.
          If so, don't add its definition to the environment, instead add the reified tactic as an assumption and
          replace its definition by the reflection of this assumed tactic. *)
    let reified_tactic_type (l: lident) (t: typ): typ =
      (* transform computations of type tactic to type __tac *)
      let t = Subst.compress t in
      match t.n with
        | Tm_arrow(bs, c) ->
            let bs, c = Subst.open_comp bs c in
            if is_total_comp c
            then begin
              let c' =
              (match c.n with
                | Total (t', u) ->
                  (match (Subst.compress t').n with
                  | Tm_app (h, args) ->
                      (match (Subst.compress h).n with
                       | Tm_uinst (h', u') ->
                          let h'' = fv_to_tm <| lid_as_fv PC.u_tac_lid Delta_constant None in
                          mk_Total' (mk_Tm_app (mk_Tm_uinst h'' u') args None t'.pos) u
                       | _ -> c)
                  | _ -> c)
                | _ -> c) in
              {t with n=Tm_arrow(bs, Subst.close_comp bs c')}
            end else t
        | Tm_app(h, args) ->
          (* tactics which take no arguments *)
            (match (Subst.compress h).n with
              | Tm_uinst (h', u') ->
                let h'' = fv_to_tm <| lid_as_fv PC.u_tac_lid Delta_constant None in
                mk_Tm_app (mk_Tm_uinst h'' u') args None t.pos
              | _ -> t)
        | _ -> t in

    (* makes `assume val __native_tac: 'a -> __tac 'b` *)
    let reified_tactic_decl (assm_lid: lident) (lb: letbinding): sigelt =
      let t = reified_tactic_type assm_lid lb.lbtyp in
      { sigel = Sig_declare_typ(assm_lid, lb.lbunivs, t);
        sigquals =[Assumption];
        sigrng = Ident.range_of_lid assm_lid;
        sigmeta = default_sigmeta;
        sigattrs = [] } in

    (* makes `let native_tac (x: 'a): tactic 'b = fun () -> TAC?.reflect (__native_tac x)` *)
    let reflected_tactic_decl (b: bool) (lb: letbinding) (bs: binders) (assm_lid: lident) comp: sigelt =
      let reified_tac = fv_to_tm <| lid_as_fv assm_lid Delta_constant None in
      let tac_args: args = List.map (fun x -> bv_to_name (fst x), snd x) bs in
      (* __native_tac x *)

      let reflect_head = mk (Tm_constant (Const_reflect PC.tac_effect_lid)) None Range.dummyRange in
      let refl_arg = mk_Tm_app reified_tac tac_args None Range.dummyRange in
      let app = mk_Tm_app reflect_head [(refl_arg, None)] None Range.dummyRange in
      (* TAC?. reflect (__native_tac x) *)

      let unit_binder = mk_binder <| new_bv None t_unit in
      let body = abs [unit_binder] app <| Some (U.residual_comp_of_comp comp) in
      let func = abs bs body <| Some (U.residual_comp_of_comp comp) in
      {se with sigel=Sig_let((b, [{lb with lbdef=func}]), lids)} in

    let tactic_decls =
      (match (snd lbs) with
        | [hd] ->
          let bs, comp = U.arrow_formals_comp hd.lbtyp in
          let t = comp_result comp in
          (match (SS.compress t).n with
            | Tm_app(h, args) ->
                let h = SS.compress h in
                let tac_lid = (right hd.lbname).fv_name.v in
                let assm_lid = lid_of_ns_and_id tac_lid.ns (id_of_text <| "__" ^ tac_lid.ident.idText) in
                (match get_tactic_fv env assm_lid h with
                 | Some fv ->
                    (* check if the tactic has already been typechecked *)
                    if not (is_some <| Env.try_lookup_val_decl env tac_lid) then begin
                      (* if it's a user tactic, add the name of the module to the list of modules which contain user tactics,
                         if the module has not already been added *)
                      if (not (is_builtin_tactic env.curmodule)) then
                        let added_modules = !user_tactics_modules in
                        let module_name = Ident.ml_path_of_lid env.curmodule in
                        if not (List.contains module_name added_modules) then
                          user_tactics_modules := added_modules @ [module_name]
                         else ()
                      else ();
                      (* check if tactic has been dynamically loaded *)
                      if env.is_native_tactic assm_lid then begin
                        let se_assm = reified_tactic_decl assm_lid hd in
                        let se_refl = reflected_tactic_decl (fst lbs) hd bs assm_lid comp in
                        Some (se_assm, se_refl)
                      end else None
                    end else None
                 | None -> None)
            | _ -> None)
        | _ -> None
      ) in

    match tactic_decls with
    | Some (se_assm, se_refl) ->
        if Env.debug env (Options.Other "NativeTactics") then
          BU.print2 "Native tactic declarations: \n%s\n%s\n"
            (Print.sigelt_to_string se_assm) (Print.sigelt_to_string se_refl)
        else ();
        [se_assm; se_refl], []
    | None -> [se], []

(* adds the typechecked sigelt to the env, also performs any processing required in the env (such as reset options) *)
(* this was earlier part of tc_decl, but separating it might help if and when we cache type checked modules *)
let add_sigelt_to_env (env:Env.env) (se:sigelt) :Env.env =
  match se.sigel with
  | Sig_inductive_typ _ -> failwith "add_sigelt_to_env: Impossible, bare data constructor"
  | Sig_datacon _ -> failwith "add_sigelt_to_env: Impossible, bare data constructor"
  | Sig_pragma (ResetOptions _) ->
    let env = Env.set_proof_ns (Options.using_facts_from ()) env in
    env.solver.refresh();
    env
  | Sig_pragma _
  | Sig_new_effect_for_free _ -> env
  | Sig_new_effect ne ->
    let env = Env.push_sigelt env se in
    ne.actions |> List.fold_left (fun env a -> Env.push_sigelt env (U.action_as_lb ne.mname a)) env
  | Sig_declare_typ (_, _, _)
  | Sig_let (_, _) when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) -> env
  | _ -> Env.push_sigelt env se


let tc_decls env ses =
  let rec process_one_decl (ses, env) se =
    if Env.debug env Options.Low
    then BU.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" (Print.sigelt_to_string se);

    let ses', ses_elaborated = tc_decl env se in
    let ses' = ses' |> List.map (fun se ->
        if Env.debug env (Options.Other "UF")
        then BU.print1 "About to elim vars from %s" (Print.sigelt_to_string se);
        N.elim_uvars env se) in
    let ses_elaborated = ses_elaborated |> List.map (fun se ->
        (* if Env.debug env (Options.Other "UF") *)
        (* then printfn "About to elim vars from %s" (Print.sigelt_to_string se); *)
        N.elim_uvars env se) in

    Env.promote_id_info env (fun t ->
        N.normalize
               [N.AllowUnboundUniverses; //this is allowed, since we're reducing types that appear deep within some arbitrary context
                N.CheckNoUvars;
                N.Beta; N.NoDeltaSteps; N.CompressUvars;
                N.Exclude N.Zeta; N.Exclude N.Iota; N.NoFullNorm]
              env
              t); //update the id_info table after having removed their uvars
    let env = ses' |> List.fold_left (fun env se -> add_sigelt_to_env env se) env in
    FStar.Syntax.Unionfind.reset();

    if Options.log_types() || Env.debug env <| Options.Other "LogTypes"
    then begin
      BU.print1 "Checked: %s\n" (List.fold_left (fun s se -> s ^ Print.sigelt_to_string se ^ "\n") "" ses')
    end;

    List.iter (fun se -> env.solver.encode_sig env se) ses';

    let ses' = List.map (fun s -> { s with sigattrs = se.sigattrs }) ses' in

    (List.rev_append ses' ses, env), ses_elaborated
  in
  // A wrapper to (maybe) print the time taken for each sigelt
  let process_one_decl_timed acc se =
    let (_, env) = acc in
    let r, ms_elapsed = BU.record_time (fun () -> process_one_decl acc se) in
    if Env.debug env (Options.Other "TCDeclTime")
    then BU.print2 "Checked %s in %s milliseconds\n" (Print.sigelt_to_string_short se) (string_of_int ms_elapsed);
    r
  in

  let ses, env = BU.fold_flatten process_one_decl_timed ([], env) ses in
  List.rev_append ses [], env

let tc_partial_modul env modul push_before_typechecking =
  let verify = Options.should_verify modul.name.str in
  let action = if verify then "Verifying" else "Lax-checking" in
  let label = if modul.is_interface then "interface" else "implementation" in
  if Options.debug_any () then
    BU.print3 "%s %s of %s\n" action label modul.name.str;

  let name = BU.format2 "%s %s"  (if modul.is_interface then "interface" else "module") modul.name.str in
  let msg = "Internals for " ^name in
  let env = {env with Env.is_iface=modul.is_interface; admit=not verify} in
  if push_before_typechecking then env.solver.push msg;
  let env = Env.set_current_module env modul.name in
  let ses, env = tc_decls env modul.declarations in
  {modul with declarations=ses}, env

let tc_more_partial_modul env modul decls =
  let ses, env = tc_decls env decls in
  let modul = {modul with declarations=modul.declarations@ses} in
  modul, env

let finish_partial_modul env modul =
  let env = Env.finish_module env modul in
  env.solver.pop ("Ending modul " ^ modul.name.str);
  env.solver.encode_modul env modul;
  env.solver.refresh();
  //interactive mode manages it itself
  let _ = if not (Options.interactive ()) then Options.restore_cmd_line_options true |> ignore else () in
  modul, env

let load_checked_module env modul =
  //This function tries to very carefully mimic the effect of the environment
  //of having checked the module from scratch, i.e., using tc_module below
  let env = Env.set_current_module env modul.name in
  env.solver.push ("Internals for " ^ Ident.string_of_lid modul.name);
  let env = List.fold_left (fun env se ->
             //push every sigelt in the environment
             let env = Env.push_sigelt env se in
             //and then query it back immediately to populate the environment's internal cache
             //this is important for extraction to work correctly,
             //in particular, when extracting a module we want the module's internal symbols
             //that may be marked "abstract" externally to be visible internally
             //populating the cache enables this behavior, rather indirectly, sadly : (
             let lids = Util.lids_of_sigelt se in
             lids |> List.iter (fun lid -> ignore (Env.try_lookup_lid env lid));
             env)
             env
             modul.declarations in
  //And then call finish_partial_modul, which is the normal workflow of tc_modul below
  //except with the flag `must_check_exports` set to false, since this is already a checked module
  snd (finish_partial_modul env modul)

let tc_modul env modul =
  let modul, env = tc_partial_modul env modul true in
  finish_partial_modul env modul

let extract_interface (env:env) (m:modul) :modul =  //env is only used when calling extract_let_rec_annotation, so we don't update it at at all
  let is_abstract = List.contains Abstract in
  let is_irreducible = List.contains Irreducible in
  let is_assume = List.contains Assumption in
  let filter_out_abstract = List.filter (fun q -> not (q = Abstract || q = Irreducible)) in
  let filter_out_abstract_and_noeq = List.filter (fun q -> not (q = Abstract || q = Noeq || q = Unopteq || q = Irreducible)) in  //abstract inductive should not have noeq and unopteq
  let filter_out_abstract_and_inline = List.filter (fun q -> not (q = Abstract || q = Irreducible || q = Inline_for_extraction || q = Unfold_for_unification_and_vcgen)) in
  let add_assume_if_needed quals = if List.contains Assumption quals then quals else Assumption::quals in
  let is_unfold_or_inline = List.existsb (fun q -> q = Unfold_for_unification_and_vcgen || q = Inline_for_extraction) in
  let is_lemma = List.existsML (fun (_, t) -> U.is_lemma t) in

  //if the module contains both a val and a let, we will only keep the val
  let added_vals = BU.mk_ref [] in

  //in case we need to drop val, keep let, carry over the types from val
  let val_typs = BU.mk_ref [] in

  //we need to filter out projectors and discriminators of abstract inductive datacons, so keep track of such datacons
  let abstract_inductive_datacons = BU.mk_ref [] in

  let is_projector_or_discriminator_of_an_abstract_inductive (quals:list<qualifier>) :bool =
    List.existsML (fun q ->
      match q with
      | Discriminator l
      | Projector (l, _) -> List.existsb (fun l' -> lid_equals l l') !abstract_inductive_datacons
      | _ -> false
    ) quals
  in

  let mk_typ_for_abstract_inductive (bs:binders) (t:typ) (r:Range.range) :typ =
    match bs with
    | [] -> t
    | _  ->
      (match t.n with
       | Tm_arrow (bs', c ) -> mk (Tm_arrow (bs@bs', c)) None r  //flattening arrows?
       | _ -> mk (Tm_arrow (bs, mk_Total t)) None r)  //Total ok?
  in

  let val_has_already_been_added (lids:list<lident>) :bool =
    List.existsML (fun lid ->
      List.existsML (fun lid' -> lid_equals lid lid') !added_vals  //TODO: check for a let rec, do we allow vals only for some of the bindings?
    ) lids
  in

  //extract the type of the letbinding, boolean indicates whether we were successful
  let extract_lbs_annotations (lbs:list<letbinding>) (lids:list<lident>) (r:Range.range) :(list<(univ_names * typ)> * bool) =
    List.fold_left2 (fun (l, b) lb lid ->
      let opt = List.tryFind (fun (l', _) -> lid_equals lid l') !val_typs in
      if opt <> None then ((snd (opt |> must))::l, b)
      else
        match lb.lbtyp.n with
        | Tm_unknown ->
          (match lb.lbdef.n with
           | Tm_ascribed (_, (Inr c, _), _) ->  //top-level term, NOTE: possibly with effect
             (lb.lbunivs, U.comp_result c)::l, b  //it's fine to not keep the body as we have the type
           | Tm_ascribed (_, (Inl t, _), _) -> (lb.lbunivs, t)::l, b
           | Tm_abs (bs, e, _) ->
             (match e.n with
              | Tm_ascribed (_, (Inr c, _), _) -> (lb.lbunivs, (mk (Tm_arrow (bs, c)) None r))::l, b
              | Tm_ascribed (_, (Inl t, _), _) ->
                let c = if Options.ml_ish () then U.ml_comp t r else S.mk_Total t in  //taking care of top-level effects here, is there a utility?
                (lb.lbunivs, (mk (Tm_arrow (bs, c)) None r))::l, b
              | _ -> (lb.lbunivs, lb.lbtyp)::l, true)  //can't get the type of the letbinding, so must keep the body
           | _ -> (lb.lbunivs, lb.lbtyp)::l, true)  //can't get the type, so must keep the body
        | _ -> (lb.lbunivs, lb.lbtyp)::l, b  //take whatever is annotated
    ) ([], false) lbs lids
  in

  //TODO: calling extract_let_rec_annotation multiple times, can call it just once in the main body, and then pass it around
  let is_pure_or_ghost_function_with_non_unit_type (typs:list<(univ_names * typ)>) :bool = List.existsML (fun (_, t) -> is_pure_or_ghost_function t && not (is_unit t)) typs in
  let is_unit (typs:list<(univ_names * typ)>) = List.for_all (fun (_, t) -> is_unit t) typs in

  let vals_of_lbs (s:sigelt) (lbs:list<letbinding>) (lids:list<lident>) (typs:list<(univ_names * typ)>) (quals:list<qualifier>) :list<sigelt> =
    List.map3 (fun lb lid typ ->
      { s with sigel = Sig_declare_typ (lid, fst typ, snd typ); sigquals = Assumption::(filter_out_abstract_and_inline quals) }
    ) lbs lids typs
  in

  let annotate_with_typs (typs:list<(univ_names * typ)>) (s:sigelt) :sigelt =
    { s with sigel = match s.sigel with
        | Sig_let (lbs, lids) -> Sig_let ((fst lbs, List.map2 (fun lb (uvs, t) -> { lb with lbunivs = uvs; lbtyp = t }) (snd lbs) typs), lids)
        | _ -> failwith "Impossible!" }
  in

  let extract_sigelt (s:sigelt) :list<sigelt> =
    match s.sigel with
    | Sig_inductive_typ _
    | Sig_datacon _ -> failwith "Impossible! Bare data constructor"
    
    | Sig_bundle (sigelts, lidents) ->
      if is_abstract s.sigquals then
        //for an abstract inductive type, we will only retain the type declarations, in an unbundled form
        List.fold_left (fun sigelts s -> 
          match s.sigel with
          | Sig_inductive_typ (lid, uvs, bs, t, _, _) ->  //add a val declaration for the type
            let s' = Sig_declare_typ (lid, uvs, mk_typ_for_abstract_inductive bs t s.sigrng) in  //we need to make an Tm_arrow to account for inductive type parameters
            (*
             * AR: Assumption qualifier seems necessary, else smt encoding waits for the definition for the symbol to be encoded
             *)
            ({ s with sigel = s'; sigquals = Assumption::(filter_out_abstract_and_noeq s.sigquals) })::sigelts  //filter out the abstract qualifier
          | Sig_datacon (lid, _, _, _, _, _) ->
            abstract_inductive_datacons := lid::!abstract_inductive_datacons;
            sigelts  //nothing to do for datacons
          | _ -> failwith "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon"
        ) [] sigelts
      else [s]  //if it is not abstract, retain as is
    | Sig_declare_typ (lid, uvs, t) ->
      //val remains as val, except we filter out the abstract qualifier
      if is_projector_or_discriminator_of_an_abstract_inductive s.sigquals then []
      else if (not (is_assume s.sigquals)) then begin  //|| (is_unfold_or_inline s.sigquals && not (is_abstract s.sigquals)) then begin
        val_typs := (lid, (uvs, t))::!val_typs;
        []
      end
      else begin
        added_vals := lid::!added_vals;
        [{ s with sigquals = add_assume_if_needed (filter_out_abstract s.sigquals) }]
      end
    | Sig_let (lbs, lids) ->
      if val_has_already_been_added lids then []
      else if is_projector_or_discriminator_of_an_abstract_inductive s.sigquals then []
      else
        let typs, b = extract_lbs_annotations (snd lbs) lids s.sigrng in
        if (is_abstract s.sigquals || is_irreducible s.sigquals || is_lemma typs) then
          if b then failwith ("Abstract and irreducible defns must be annotated at the top-level: " ^ (List.hd lids).str ^ "\n\n")
          else vals_of_lbs s (snd lbs) lids typs s.sigquals
        else if b then [annotate_with_typs typs s]  //if top level annotation is missing, retain as is
        else if is_pure_or_ghost_function_with_non_unit_type typs then [annotate_with_typs typs s]  //pure or ghost functions with non-unit types are retained as is
        else if not (is_unit typs) then [annotate_with_typs typs s]  //non-unit types are retained as is
        else vals_of_lbs s (snd lbs) lids typs s.sigquals  //TODO: add case for functions with reifiable effects
    | Sig_main t -> failwith "Did not anticipate this would arise"
    | Sig_assume (lids, uvs, t) -> [ { s with sigquals = filter_out_abstract s.sigquals } ]  //should we not permit abstract with assumes anyway?
    | Sig_new_effect _
    | Sig_new_effect_for_free _
    | Sig_sub_effect _
    | Sig_effect_abbrev _
    | Sig_pragma _ -> [s]
  in
  
  { m with declarations = List.flatten (List.map extract_sigelt m.declarations); is_interface = true }

let check_module env m =
  if Options.debug_any()
  then BU.print2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (Print.lid_to_string m.name);

  let env = {env with lax=not (Options.should_verify m.name.str)} in
  let m, env = tc_modul env m in

  (* Debug information for level Normalize : normalizes all toplevel declarations an dump the current module *)
  if Options.dump_module m.name.str
  then BU.print1 "Module after type checking:\n%s\n" (Print.modul_to_string m);
  if Options.dump_module m.name.str && Options.debug_at_level m.name.str (Options.Other "Normalize")
  then begin
    let normalize_toplevel_lets = fun se -> match se.sigel with
        | Sig_let ((b, lbs), ids) ->
            let n = N.normalize [N.Beta ; N.Eager_unfolding; N.Reify ; N.Inlining ; N.Primops ; N.UnfoldUntil S.Delta_constant ; N.AllowUnboundUniverses ] in
            let update lb =
                let univnames, e = SS.open_univ_vars lb.lbunivs lb.lbdef in
                { lb with lbdef = n (Env.push_univ_vars env univnames) e }
            in
            { se with sigel = Sig_let ((b, List.map update lbs), ids) }
        | _ -> se
    in
    let normalized_module = { m with declarations = List.map normalize_toplevel_lets m.declarations } in
    BU.print1 "%s\n" (Print.modul_to_string normalized_module)
  end;

  m, env