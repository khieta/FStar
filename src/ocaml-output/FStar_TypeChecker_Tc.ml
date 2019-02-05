open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      let tbl =
        FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index
          FStar_Pervasives_Native.fst
         in
      let get_n lid =
        let n_opt = FStar_Util.smap_try_find tbl lid.FStar_Ident.str  in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else (Prims.parse_int "0")  in
      let uu____65 = FStar_Options.reuse_hint_for ()  in
      match uu____65 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____73 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____73 l  in
          let uu___380_74 = env  in
          let uu____75 =
            let uu____90 =
              let uu____98 = let uu____104 = get_n lid  in (lid, uu____104)
                 in
              FStar_Pervasives_Native.Some uu____98  in
            (tbl, uu____90)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___380_74.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___380_74.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___380_74.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___380_74.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___380_74.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___380_74.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___380_74.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___380_74.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___380_74.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___380_74.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___380_74.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___380_74.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___380_74.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___380_74.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___380_74.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___380_74.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___380_74.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___380_74.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___380_74.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___380_74.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___380_74.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___380_74.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___380_74.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___380_74.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___380_74.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___380_74.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___380_74.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___380_74.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___380_74.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___380_74.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___380_74.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____75;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___380_74.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___380_74.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___380_74.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___380_74.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___380_74.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___380_74.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___380_74.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___380_74.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___380_74.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___380_74.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___380_74.FStar_TypeChecker_Env.nbe)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____127 = FStar_TypeChecker_Env.current_module env  in
                let uu____128 =
                  let uu____130 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____130 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____127 uu____128
            | l::uu____135 -> l  in
          let uu___381_138 = env  in
          let uu____139 =
            let uu____154 =
              let uu____162 = let uu____168 = get_n lid  in (lid, uu____168)
                 in
              FStar_Pervasives_Native.Some uu____162  in
            (tbl, uu____154)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___381_138.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___381_138.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___381_138.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___381_138.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___381_138.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___381_138.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___381_138.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___381_138.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___381_138.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___381_138.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___381_138.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___381_138.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___381_138.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___381_138.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___381_138.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___381_138.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___381_138.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___381_138.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___381_138.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___381_138.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___381_138.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___381_138.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___381_138.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___381_138.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___381_138.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___381_138.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___381_138.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___381_138.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___381_138.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___381_138.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___381_138.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____139;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___381_138.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___381_138.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___381_138.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___381_138.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___381_138.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___381_138.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___381_138.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___381_138.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___381_138.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___381_138.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___381_138.FStar_TypeChecker_Env.nbe)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____194 =
         let uu____196 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____196  in
       Prims.op_Negation uu____194)
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____213 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____213 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____243 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____243
         then
           let uu____247 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____247
         else ());
        (let uu____252 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____252 with
         | (t',uu____260,uu____261) ->
             ((let uu____263 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____263
               then
                 let uu____267 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____267
               else ());
              t'))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____288 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____288
  
let check_nogen :
  'Auu____298 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____298 Prims.list * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____321 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t1
           in
        ([], uu____321)
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail1 uu____357 =
          let uu____358 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____364 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____358 uu____364  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____408)::(wp,uu____410)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____439 -> fail1 ())
        | uu____440 -> fail1 ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____452 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____452 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____484 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____484 t  in
          let open_univs_binders n_binders bs =
            let uu____500 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____500 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____510 =
            let uu____517 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____519 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____517 uu____519  in
          (match uu____510 with
           | (effect_params_un,signature_un,opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____530 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____530 with
                | (effect_params,env1,uu____539) ->
                    let uu____540 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____540 with
                     | (signature,uu____546) ->
                         let ed1 =
                           let uu___382_548 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___382_548.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___382_548.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___382_548.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___382_548.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___382_548.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___382_548.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___382_548.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___382_548.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___382_548.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___382_548.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___382_548.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___382_548.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___382_548.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___382_548.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___382_548.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___382_548.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___382_548.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___382_548.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____576 ->
                               let op uu____608 =
                                 match uu____608 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____628 =
                                       let uu____629 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____638 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____629
                                         uu____638
                                        in
                                     (us, uu____628)
                                  in
                               let uu___383_647 = ed1  in
                               let uu____648 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____649 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____650 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____651 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____652 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____653 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____654 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____655 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____656 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____657 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____658 =
                                 let uu____659 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____659  in
                               let uu____670 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____671 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____672 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___384_680 = a  in
                                      let uu____681 =
                                        let uu____682 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____682
                                         in
                                      let uu____693 =
                                        let uu____694 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____694
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___384_680.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___384_680.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___384_680.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___384_680.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____681;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____693
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___383_647.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___383_647.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___383_647.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___383_647.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____648;
                                 FStar_Syntax_Syntax.bind_wp = uu____649;
                                 FStar_Syntax_Syntax.if_then_else = uu____650;
                                 FStar_Syntax_Syntax.ite_wp = uu____651;
                                 FStar_Syntax_Syntax.stronger = uu____652;
                                 FStar_Syntax_Syntax.close_wp = uu____653;
                                 FStar_Syntax_Syntax.assert_p = uu____654;
                                 FStar_Syntax_Syntax.assume_p = uu____655;
                                 FStar_Syntax_Syntax.null_wp = uu____656;
                                 FStar_Syntax_Syntax.trivial = uu____657;
                                 FStar_Syntax_Syntax.repr = uu____658;
                                 FStar_Syntax_Syntax.return_repr = uu____670;
                                 FStar_Syntax_Syntax.bind_repr = uu____671;
                                 FStar_Syntax_Syntax.actions = uu____672;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___383_647.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____739 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____745 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____739 uu____745  in
                           let uu____752 =
                             let uu____753 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____753.FStar_Syntax_Syntax.n  in
                           match uu____752 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____792)::(wp,uu____794)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____823 -> fail1 signature1)
                           | uu____824 -> fail1 signature1  in
                         let uu____825 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____825 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____849 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____856 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____856 with
                                     | (signature1,uu____868) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____869 ->
                                    let uu____872 =
                                      let uu____877 =
                                        let uu____878 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____878)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____877
                                       in
                                    (match uu____872 with
                                     | (uu____891,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____894 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____894
                                 in
                              ((let uu____896 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____896
                                then
                                  let uu____901 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____903 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____906 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____908 =
                                    let uu____910 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____910
                                     in
                                  let uu____911 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____901 uu____903 uu____906 uu____908
                                    uu____911
                                else ());
                               (let check_and_gen' env3 uu____946 k =
                                  match uu____946 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____982::uu____983 ->
                                           let uu____986 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____986 with
                                            | (us1,t1) ->
                                                let uu____1009 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____1009 with
                                                 | (us2,t2) ->
                                                     let uu____1024 =
                                                       let uu____1025 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____1025 t2 k
                                                        in
                                                     let uu____1026 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____1026))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____1045 =
                                      let uu____1054 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1061 =
                                        let uu____1070 =
                                          let uu____1077 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1077
                                           in
                                        [uu____1070]  in
                                      uu____1054 :: uu____1061  in
                                    let uu____1096 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____1045
                                      uu____1096
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____1100 = fresh_effect_signature ()
                                     in
                                  match uu____1100 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____1116 =
                                          let uu____1125 =
                                            let uu____1132 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____1132
                                             in
                                          [uu____1125]  in
                                        let uu____1145 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____1116
                                          uu____1145
                                         in
                                      let expected_k =
                                        let uu____1151 =
                                          let uu____1160 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____1167 =
                                            let uu____1176 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1183 =
                                              let uu____1192 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____1199 =
                                                let uu____1208 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____1215 =
                                                  let uu____1224 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____1224]  in
                                                uu____1208 :: uu____1215  in
                                              uu____1192 :: uu____1199  in
                                            uu____1176 :: uu____1183  in
                                          uu____1160 :: uu____1167  in
                                        let uu____1267 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____1151
                                          uu____1267
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____1280 =
                                      let uu____1283 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____1283
                                       in
                                    let uu____1284 =
                                      let uu____1285 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____1285
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____1280
                                      uu____1284
                                     in
                                  let expected_k =
                                    let uu____1297 =
                                      let uu____1306 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1313 =
                                        let uu____1322 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____1329 =
                                          let uu____1338 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____1345 =
                                            let uu____1354 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1354]  in
                                          uu____1338 :: uu____1345  in
                                        uu____1322 :: uu____1329  in
                                      uu____1306 :: uu____1313  in
                                    let uu____1391 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1297
                                      uu____1391
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____1406 =
                                      let uu____1415 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1422 =
                                        let uu____1431 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____1431]  in
                                      uu____1415 :: uu____1422  in
                                    let uu____1456 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1406
                                      uu____1456
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____1460 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1460 with
                                  | (t,uu____1466) ->
                                      let expected_k =
                                        let uu____1470 =
                                          let uu____1479 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1486 =
                                            let uu____1495 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____1502 =
                                              let uu____1511 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____1511]  in
                                            uu____1495 :: uu____1502  in
                                          uu____1479 :: uu____1486  in
                                        let uu____1542 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____1470
                                          uu____1542
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____1555 =
                                      let uu____1558 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____1558
                                       in
                                    let uu____1559 =
                                      let uu____1560 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____1560
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____1555
                                      uu____1559
                                     in
                                  let b_wp_a =
                                    let uu____1572 =
                                      let uu____1581 =
                                        let uu____1588 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1588
                                         in
                                      [uu____1581]  in
                                    let uu____1601 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1572
                                      uu____1601
                                     in
                                  let expected_k =
                                    let uu____1607 =
                                      let uu____1616 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1623 =
                                        let uu____1632 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____1639 =
                                          let uu____1648 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____1648]  in
                                        uu____1632 :: uu____1639  in
                                      uu____1616 :: uu____1623  in
                                    let uu____1679 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1607
                                      uu____1679
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____1694 =
                                      let uu____1703 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1710 =
                                        let uu____1719 =
                                          let uu____1726 =
                                            let uu____1727 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1727
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1726
                                           in
                                        let uu____1736 =
                                          let uu____1745 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1745]  in
                                        uu____1719 :: uu____1736  in
                                      uu____1703 :: uu____1710  in
                                    let uu____1776 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1694
                                      uu____1776
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1791 =
                                      let uu____1800 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1807 =
                                        let uu____1816 =
                                          let uu____1823 =
                                            let uu____1824 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1824
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1823
                                           in
                                        let uu____1833 =
                                          let uu____1842 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1842]  in
                                        uu____1816 :: uu____1833  in
                                      uu____1800 :: uu____1807  in
                                    let uu____1873 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1791
                                      uu____1873
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1888 =
                                      let uu____1897 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1897]  in
                                    let uu____1916 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1888
                                      uu____1916
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1920 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1920 with
                                  | (t,uu____1926) ->
                                      let expected_k =
                                        let uu____1930 =
                                          let uu____1939 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1946 =
                                            let uu____1955 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1955]  in
                                          uu____1939 :: uu____1946  in
                                        let uu____1980 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1930
                                          uu____1980
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1983 =
                                  let uu____1996 =
                                    let uu____1997 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1997.FStar_Syntax_Syntax.n  in
                                  match uu____1996 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____2016 ->
                                      let repr =
                                        let uu____2018 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____2018 with
                                        | (t,uu____2024) ->
                                            let expected_k =
                                              let uu____2028 =
                                                let uu____2037 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____2044 =
                                                  let uu____2053 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____2053]  in
                                                uu____2037 :: uu____2044  in
                                              let uu____2078 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2028 uu____2078
                                               in
                                            tc_check_trivial_guard env2
                                              ed2.FStar_Syntax_Syntax.repr
                                              expected_k
                                         in
                                      let mk_repr' t wp =
                                        let repr1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.EraseUniverses;
                                            FStar_TypeChecker_Env.AllowUnboundUniverses]
                                            env2 repr
                                           in
                                        let uu____2095 =
                                          let uu____2102 =
                                            let uu____2103 =
                                              let uu____2120 =
                                                let uu____2131 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____2140 =
                                                  let uu____2151 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____2151]  in
                                                uu____2131 :: uu____2140  in
                                              (repr1, uu____2120)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____2103
                                             in
                                          FStar_Syntax_Syntax.mk uu____2102
                                           in
                                        uu____2095
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____2212 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____2212 wp  in
                                      let destruct_repr t =
                                        let uu____2227 =
                                          let uu____2228 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____2228.FStar_Syntax_Syntax.n
                                           in
                                        match uu____2227 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____2239,(t1,uu____2241)::
                                             (wp,uu____2243)::[])
                                            -> (t1, wp)
                                        | uu____2302 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____2314 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____2314
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____2315 =
                                          fresh_effect_signature ()  in
                                        match uu____2315 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____2331 =
                                                let uu____2340 =
                                                  let uu____2347 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____2347
                                                   in
                                                [uu____2340]  in
                                              let uu____2360 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2331 uu____2360
                                               in
                                            let wp_f =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_f"
                                                FStar_Pervasives_Native.None
                                                wp_a
                                               in
                                            let wp_g =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_g"
                                                FStar_Pervasives_Native.None
                                                a_wp_b
                                               in
                                            let x_a =
                                              let uu____2368 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____2368
                                               in
                                            let wp_g_x =
                                              let uu____2373 =
                                                let uu____2378 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____2379 =
                                                  let uu____2380 =
                                                    let uu____2389 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2389
                                                     in
                                                  [uu____2380]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____2378 uu____2379
                                                 in
                                              uu____2373
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____2422 =
                                                  let uu____2427 =
                                                    let uu____2428 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2428
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____2437 =
                                                    let uu____2438 =
                                                      let uu____2441 =
                                                        let uu____2444 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____2445 =
                                                          let uu____2448 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____2449 =
                                                            let uu____2452 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____2453 =
                                                              let uu____2456
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____2456]
                                                               in
                                                            uu____2452 ::
                                                              uu____2453
                                                             in
                                                          uu____2448 ::
                                                            uu____2449
                                                           in
                                                        uu____2444 ::
                                                          uu____2445
                                                         in
                                                      r :: uu____2441  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2438
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____2427 uu____2437
                                                   in
                                                uu____2422
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let maybe_range_arg =
                                              let uu____2476 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs
                                                 in
                                              if uu____2476
                                              then
                                                let uu____2487 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                let uu____2494 =
                                                  let uu____2503 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  [uu____2503]  in
                                                uu____2487 :: uu____2494
                                              else []  in
                                            let expected_k =
                                              let uu____2539 =
                                                let uu____2548 =
                                                  let uu____2557 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____2564 =
                                                    let uu____2573 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b
                                                       in
                                                    [uu____2573]  in
                                                  uu____2557 :: uu____2564
                                                   in
                                                let uu____2598 =
                                                  let uu____2607 =
                                                    let uu____2616 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____2623 =
                                                      let uu____2632 =
                                                        let uu____2639 =
                                                          let uu____2640 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____2640
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____2639
                                                         in
                                                      let uu____2641 =
                                                        let uu____2650 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____2657 =
                                                          let uu____2666 =
                                                            let uu____2673 =
                                                              let uu____2674
                                                                =
                                                                let uu____2683
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____2683]
                                                                 in
                                                              let uu____2702
                                                                =
                                                                let uu____2705
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____2705
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____2674
                                                                uu____2702
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____2673
                                                             in
                                                          [uu____2666]  in
                                                        uu____2650 ::
                                                          uu____2657
                                                         in
                                                      uu____2632 ::
                                                        uu____2641
                                                       in
                                                    uu____2616 :: uu____2623
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____2607
                                                   in
                                                FStar_List.append uu____2548
                                                  uu____2598
                                                 in
                                              let uu____2750 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2539 uu____2750
                                               in
                                            let uu____2753 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            (match uu____2753 with
                                             | (expected_k1,uu____2761,uu____2762)
                                                 ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env4 =
                                                   let uu___385_2769 = env3
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_sig
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.gamma_sig);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.attrtab
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.attrtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.phase1
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.phase1);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.uvar_subtyping
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.uvar_subtyping);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.normalized_eff_names
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.normalized_eff_names);
                                                     FStar_TypeChecker_Env.fv_delta_depths
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.fv_delta_depths);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.postprocess
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.postprocess);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.nbe
                                                       =
                                                       (uu___385_2769.FStar_TypeChecker_Env.nbe)
                                                   }  in
                                                 let br =
                                                   check_and_gen' env4
                                                     ed2.FStar_Syntax_Syntax.bind_repr
                                                     expected_k1
                                                    in
                                                 br)
                                         in
                                      let return_repr =
                                        let x_a =
                                          let uu____2782 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____2782
                                           in
                                        let res =
                                          let wp =
                                            let uu____2790 =
                                              let uu____2795 =
                                                let uu____2796 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2796
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____2805 =
                                                let uu____2806 =
                                                  let uu____2809 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____2810 =
                                                    let uu____2813 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____2813]  in
                                                  uu____2809 :: uu____2810
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____2806
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____2795 uu____2805
                                               in
                                            uu____2790
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____2827 =
                                            let uu____2836 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____2843 =
                                              let uu____2852 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____2852]  in
                                            uu____2836 :: uu____2843  in
                                          let uu____2877 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____2827
                                            uu____2877
                                           in
                                        let uu____2880 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env2 expected_k
                                           in
                                        match uu____2880 with
                                        | (expected_k1,uu____2888,uu____2889)
                                            ->
                                            let env3 =
                                              FStar_TypeChecker_Env.set_range
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____2895 =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____2895 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____2918 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let uu____2933 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env2, act)
                                            else
                                              (let uu____2947 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____2947 with
                                               | (usubst,uvs) ->
                                                   let uu____2970 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env2 uvs
                                                      in
                                                   let uu____2971 =
                                                     let uu___386_2972 = act
                                                        in
                                                     let uu____2973 =
                                                       FStar_Syntax_Subst.subst_binders
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_params
                                                        in
                                                     let uu____2974 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____2975 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___386_2972.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___386_2972.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         = uu____2973;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____2974;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____2975
                                                     }  in
                                                   (uu____2970, uu____2971))
                                             in
                                          match uu____2933 with
                                          | (env3,act1) ->
                                              let act_typ =
                                                let uu____2979 =
                                                  let uu____2980 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____2980.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____2979 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____3006 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____3006
                                                    then
                                                      let uu____3009 =
                                                        let uu____3012 =
                                                          let uu____3013 =
                                                            let uu____3014 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3014
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____3013
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____3012
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs uu____3009
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____3037 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____3038 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env3 act_typ
                                                 in
                                              (match uu____3038 with
                                               | (act_typ1,uu____3046,g_t) ->
                                                   let env' =
                                                     let uu___387_3049 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env3 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___387_3049.FStar_TypeChecker_Env.nbe)
                                                     }  in
                                                   ((let uu____3052 =
                                                       FStar_TypeChecker_Env.debug
                                                         env3
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____3052
                                                     then
                                                       let uu____3056 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____3058 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____3060 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____3056
                                                         uu____3058
                                                         uu____3060
                                                     else ());
                                                    (let uu____3065 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____3065 with
                                                     | (act_defn,uu____3073,g_a)
                                                         ->
                                                         let act_defn1 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Env.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant]
                                                             env3 act_defn
                                                            in
                                                         let act_typ2 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Env.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant;
                                                             FStar_TypeChecker_Env.Eager_unfolding;
                                                             FStar_TypeChecker_Env.Beta]
                                                             env3 act_typ1
                                                            in
                                                         let uu____3077 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs,c) ->
                                                               let uu____3113
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs c
                                                                  in
                                                               (match uu____3113
                                                                with
                                                                | (bs1,uu____3125)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____3132
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____3132
                                                                     in
                                                                    let uu____3135
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____3135
                                                                    with
                                                                    | 
                                                                    (k1,uu____3149,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____3153 ->
                                                               let uu____3154
                                                                 =
                                                                 let uu____3160
                                                                   =
                                                                   let uu____3162
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____3164
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____3162
                                                                    uu____3164
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____3160)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____3154
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____3077
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env3
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____3182
                                                                  =
                                                                  let uu____3183
                                                                    =
                                                                    let uu____3184
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____3184
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____3183
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env3
                                                                  uu____3182);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____3186
                                                                    =
                                                                    let uu____3187
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____3187.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____3186
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____3212
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____3212
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____3219
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____3219
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____3239
                                                                    =
                                                                    let uu____3240
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____3240]
                                                                     in
                                                                    let uu____3241
                                                                    =
                                                                    let uu____3252
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____3252]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____3239;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____3241;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____3277
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____3277))
                                                                  | uu____3280
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____3282
                                                                  =
                                                                  if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                  then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                  else
                                                                    (
                                                                    let uu____3304
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____3304))
                                                                   in
                                                                match uu____3282
                                                                with
                                                                | (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env3
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___388_3323
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___388_3323.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___388_3323.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___388_3323.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    }))))))
                                           in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action)
                                         in
                                      (repr, bind_repr, return_repr, actions)
                                   in
                                match uu____1983 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____3347 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____3347
                                       in
                                    let uu____3350 =
                                      let uu____3355 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____3355 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____3374 ->
                                               let uu____3377 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____3384 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____3384 =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____3377
                                               then (gen_univs, t)
                                               else
                                                 (let uu____3395 =
                                                    let uu____3401 =
                                                      let uu____3403 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____3405 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____3403 uu____3405
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____3401)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____3395
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____3350 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____3416 =
                                             let uu____3429 =
                                               let uu____3430 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____3430.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____3429)  in
                                           match uu____3416 with
                                           | ([],uu____3441) -> t
                                           | (uu____3456,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____3457,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____3495 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____3523 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____3523
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____3530 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____3534 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____3534))
                                                && (m <> n1)
                                               in
                                            if uu____3530
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____3562 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____3570 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____3572 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____3562 uu____3570
                                                  uu____3572
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____3588 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____3588 with
                                           | (univs2,defn) ->
                                               let uu____3604 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____3604 with
                                                | (univs',typ) ->
                                                    let uu___389_3621 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___389_3621.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___389_3621.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___389_3621.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___390_3624 = ed2  in
                                           let uu____3625 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____3627 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____3629 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____3631 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____3633 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____3635 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____3637 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____3639 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____3641 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____3643 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____3645 =
                                             let uu____3646 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____3646
                                              in
                                           let uu____3664 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____3666 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____3668 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___390_3624.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___390_3624.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____3625;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____3627;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____3629;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____3631;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____3633;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____3635;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____3637;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____3639;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____3641;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____3643;
                                             FStar_Syntax_Syntax.repr =
                                               uu____3645;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____3664;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____3666;
                                             FStar_Syntax_Syntax.actions =
                                               uu____3668;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___390_3624.FStar_Syntax_Syntax.eff_attrs)
                                           }  in
                                         ((let uu____3672 =
                                             (FStar_TypeChecker_Env.debug
                                                env2 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env2)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____3672
                                           then
                                             let uu____3677 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____3677
                                           else ());
                                          ed3))))))))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let uu____3703 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____3703 with
      | (effect_binders_un,signature_un) ->
          let uu____3720 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____3720 with
           | (effect_binders,env1,uu____3739) ->
               let uu____3740 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____3740 with
                | (signature,uu____3756) ->
                    let raise_error1 uu____3772 =
                      match uu____3772 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____3808  ->
                           match uu____3808 with
                           | (bv,qual) ->
                               let uu____3827 =
                                 let uu___391_3828 = bv  in
                                 let uu____3829 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___391_3828.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___391_3828.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____3829
                                 }  in
                               (uu____3827, qual)) effect_binders
                       in
                    let uu____3834 =
                      let uu____3841 =
                        let uu____3842 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____3842.FStar_Syntax_Syntax.n  in
                      match uu____3841 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____3852)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____3884 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____3834 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____3910 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____3910
                           then
                             let uu____3913 =
                               let uu____3916 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____3916  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____3913
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____3964 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____3964 with
                           | (t2,comp,uu____3977) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____3986 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____3986 with
                          | (repr,_comp) ->
                              ((let uu____4010 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____4010
                                then
                                  let uu____4014 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____4014
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange)
                                   in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr
                                   in
                                let uu____4021 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____4024 =
                                    let uu____4025 =
                                      let uu____4026 =
                                        let uu____4043 =
                                          let uu____4054 =
                                            let uu____4063 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____4066 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____4063, uu____4066)  in
                                          [uu____4054]  in
                                        (wp_type, uu____4043)  in
                                      FStar_Syntax_Syntax.Tm_app uu____4026
                                       in
                                    mk1 uu____4025  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____4024
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____4114 =
                                      let uu____4121 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____4121)  in
                                    let uu____4127 =
                                      let uu____4136 =
                                        let uu____4143 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____4143
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____4136]  in
                                    uu____4114 :: uu____4127  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____4180 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature
                                   in
                                let sigelts = FStar_Util.mk_ref []  in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name  in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 =
                                    FStar_TypeChecker_DMFF.get_env dmff_env1
                                     in
                                  let uu____4246 = item  in
                                  match uu____4246 with
                                  | (u_item,item1) ->
                                      let uu____4261 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____4261 with
                                       | (item2,item_comp) ->
                                           ((let uu____4277 =
                                               let uu____4279 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____4279
                                                in
                                             if uu____4277
                                             then
                                               let uu____4282 =
                                                 let uu____4288 =
                                                   let uu____4290 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____4292 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____4290 uu____4292
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____4288)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____4282
                                             else ());
                                            (let uu____4298 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____4298 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____4316 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____4318 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____4320 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____4320 with
                                | (dmff_env1,uu____4346,bind_wp,bind_elab) ->
                                    let uu____4349 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____4349 with
                                     | (dmff_env2,uu____4375,return_wp,return_elab)
                                         ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           }  in
                                         let lift_from_pure_wp =
                                           let uu____4384 =
                                             let uu____4385 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4385.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4384 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4443 =
                                                 let uu____4462 =
                                                   let uu____4467 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____4467
                                                    in
                                                 match uu____4462 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____4549 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____4443 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____4603 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____4603 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____4626 =
                                                          let uu____4627 =
                                                            let uu____4644 =
                                                              let uu____4655
                                                                =
                                                                let uu____4664
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____4669
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____4664,
                                                                  uu____4669)
                                                                 in
                                                              [uu____4655]
                                                               in
                                                            (wp_type,
                                                              uu____4644)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4627
                                                           in
                                                        mk1 uu____4626  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____4705 =
                                                      let uu____4714 =
                                                        let uu____4715 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____4715
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____4714
                                                       in
                                                    (match uu____4705 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____4738
                                                           =
                                                           let error_msg =
                                                             let uu____4741 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____4743 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                    -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____4741
                                                               uu____4743
                                                              in
                                                           raise_error1
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg)
                                                            in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                                -> fail1 ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu____4753
                                                                   =
                                                                   let uu____4755
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____4755
                                                                    in
                                                                 if
                                                                   uu____4753
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____4760
                                                                   =
                                                                   FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0
                                                                     in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail1 ())
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4760
                                                                   (fun a1 
                                                                    -> ()))));
                                                          (let wp =
                                                             let t2 =
                                                               (FStar_Pervasives_Native.fst
                                                                  b21).FStar_Syntax_Syntax.sort
                                                                in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2
                                                                in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type
                                                              in
                                                           let body3 =
                                                             let uu____4789 =
                                                               let uu____4794
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____4795
                                                                 =
                                                                 let uu____4796
                                                                   =
                                                                   let uu____4805
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____4805,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____4796]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____4794
                                                                 uu____4795
                                                                in
                                                             uu____4789
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____4842 =
                                                             let uu____4843 =
                                                               let uu____4852
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____4852]
                                                                in
                                                             b11 ::
                                                               uu____4843
                                                              in
                                                           let uu____4877 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____4842
                                                             uu____4877
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____4880 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____4888 =
                                             let uu____4889 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4889.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4888 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4947 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____4947
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____4968 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____4976 =
                                             let uu____4977 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____4977.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4976 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____5011 =
                                                 let uu____5012 =
                                                   let uu____5021 =
                                                     let uu____5028 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____5028
                                                      in
                                                   [uu____5021]  in
                                                 FStar_List.append uu____5012
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____5011 body what
                                           | uu____5047 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind")
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____5077 =
                                                let uu____5078 =
                                                  let uu____5079 =
                                                    let uu____5096 =
                                                      let uu____5107 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____5107
                                                       in
                                                    (t, uu____5096)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____5079
                                                   in
                                                mk1 uu____5078  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____5077)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____5165 = f a2  in
                                               [uu____5165]
                                           | x::xs ->
                                               let uu____5176 =
                                                 apply_last1 f xs  in
                                               x :: uu____5176
                                            in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname
                                              in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p
                                              in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange
                                              in
                                           let uu____5210 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____5210 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____5240 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____5240
                                                 then
                                                   let uu____5243 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____5243
                                                 else ());
                                                (let uu____5248 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____5248))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____5257 =
                                                 let uu____5262 = mk_lid name
                                                    in
                                                 let uu____5263 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____5262 uu____5263
                                                  in
                                               (match uu____5257 with
                                                | (sigelt,fv) ->
                                                    ((let uu____5267 =
                                                        let uu____5270 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____5270
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____5267);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____5368 =
                                             let uu____5371 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____5374 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____5371 :: uu____5374  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____5368);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____5470 =
                                              let uu____5473 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____5474 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____5473 :: uu____5474  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____5470);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____5570 =
                                               let uu____5573 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____5576 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____5573 :: uu____5576  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____5570);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____5672 =
                                                let uu____5675 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____5676 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____5675 :: uu____5676  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____5672);
                                             (let uu____5769 =
                                                FStar_List.fold_left
                                                  (fun uu____5809  ->
                                                     fun action  ->
                                                       match uu____5809 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____5830 =
                                                             let uu____5837 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____5837
                                                               params_un
                                                              in
                                                           (match uu____5830
                                                            with
                                                            | (action_params,env',uu____5846)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____5872
                                                                     ->
                                                                    match uu____5872
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____5891
                                                                    =
                                                                    let uu___392_5892
                                                                    = bv  in
                                                                    let uu____5893
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___392_5892.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___392_5892.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____5893
                                                                    }  in
                                                                    (uu____5891,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____5899
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____5899
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
                                                                     in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp
                                                                     in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1
                                                                     in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab
                                                                     in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp
                                                                     in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____5938
                                                                    ->
                                                                    let uu____5939
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____5939
                                                                     in
                                                                    ((
                                                                    let uu____5943
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____5943
                                                                    then
                                                                    let uu____5948
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____5951
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____5954
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____5956
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____5948
                                                                    uu____5951
                                                                    uu____5954
                                                                    uu____5956
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2
                                                                     in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____5965
                                                                    =
                                                                    let uu____5968
                                                                    =
                                                                    let uu___393_5969
                                                                    = action
                                                                     in
                                                                    let uu____5970
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____5971
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___393_5969.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___393_5969.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___393_5969.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____5970;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____5971
                                                                    }  in
                                                                    uu____5968
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____5965))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____5769 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions
                                                     in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a
                                                       in
                                                    let binders =
                                                      let uu____6015 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____6022 =
                                                        let uu____6031 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____6031]  in
                                                      uu____6015 ::
                                                        uu____6022
                                                       in
                                                    let uu____6056 =
                                                      let uu____6059 =
                                                        let uu____6060 =
                                                          let uu____6061 =
                                                            let uu____6078 =
                                                              let uu____6089
                                                                =
                                                                let uu____6098
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____6101
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____6098,
                                                                  uu____6101)
                                                                 in
                                                              [uu____6089]
                                                               in
                                                            (repr,
                                                              uu____6078)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____6061
                                                           in
                                                        mk1 uu____6060  in
                                                      let uu____6137 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____6059
                                                        uu____6137
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____6056
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____6138 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____6142 =
                                                    let uu____6151 =
                                                      let uu____6152 =
                                                        let uu____6155 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____6155
                                                         in
                                                      uu____6152.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6151 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____6169)
                                                        ->
                                                        let uu____6206 =
                                                          let uu____6227 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____6227
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____6295 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____6206
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____6360 =
                                                               let uu____6361
                                                                 =
                                                                 let uu____6364
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____6364
                                                                  in
                                                               uu____6361.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____6360
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____6397
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____6397
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____6412
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____6443
                                                                     ->
                                                                    match uu____6443
                                                                    with
                                                                    | 
                                                                    (bv,uu____6452)
                                                                    ->
                                                                    let uu____6457
                                                                    =
                                                                    let uu____6459
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____6459
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____6457
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____6412
                                                                    with
                                                                    | 
                                                                    (pre_args,post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____6551
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____6551
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____6561
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____6572
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____6572
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____6582
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____6585
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____6582,
                                                                    uu____6585)))
                                                              | uu____6600 ->
                                                                  let uu____6601
                                                                    =
                                                                    let uu____6607
                                                                    =
                                                                    let uu____6609
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____6609
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____6607)
                                                                     in
                                                                  raise_error1
                                                                    uu____6601))
                                                    | uu____6621 ->
                                                        let uu____6622 =
                                                          let uu____6628 =
                                                            let uu____6630 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____6630
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____6628)
                                                           in
                                                        raise_error1
                                                          uu____6622
                                                     in
                                                  (match uu____6142 with
                                                   | (pre,post) ->
                                                       ((let uu____6663 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____6666 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____6669 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___394_6672
                                                             = ed  in
                                                           let uu____6673 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____6674 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____6675 =
                                                             let uu____6676 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____6676)
                                                              in
                                                           let uu____6683 =
                                                             let uu____6684 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____6684)
                                                              in
                                                           let uu____6691 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____6692 =
                                                             let uu____6693 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____6693)
                                                              in
                                                           let uu____6700 =
                                                             let uu____6701 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____6701)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____6673;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____6674;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____6675;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____6683;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____6691;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____6692;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____6700;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___394_6672.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____6708 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____6708
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____6726
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____6726
                                                               then
                                                                 let uu____6730
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____6730
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____6750
                                                                    =
                                                                    let uu____6753
                                                                    =
                                                                    let uu____6754
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____6754)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____6753
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____6750;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____6761
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____6761
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____6764
                                                                 =
                                                                 let uu____6767
                                                                   =
                                                                   let uu____6770
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____6770
                                                                    in
                                                                 FStar_List.append
                                                                   uu____6767
                                                                   sigelts'
                                                                  in
                                                               (uu____6764,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____6833 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6833 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6868 = FStar_List.hd ses  in
            uu____6868.FStar_Syntax_Syntax.sigrng  in
          (match lids with
           | lex_t1::lex_top1::lex_cons::[] when
               ((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                  &&
                  (FStar_Ident.lid_equals lex_top1
                     FStar_Parser_Const.lextop_lid))
                 &&
                 (FStar_Ident.lid_equals lex_cons
                    FStar_Parser_Const.lexcons_lid)
               -> ()
           | uu____6873 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6879,[],t,uu____6881,uu____6882);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6884;
               FStar_Syntax_Syntax.sigattrs = uu____6885;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6887,_t_top,_lex_t_top,_0_1,uu____6890);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6892;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6893;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6895,_t_cons,_lex_t_cons,_0_2,uu____6898);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6900;
                 FStar_Syntax_Syntax.sigattrs = uu____6901;_}::[]
               when
               ((_0_1 = (Prims.parse_int "0")) &&
                  (_0_2 = (Prims.parse_int "0")))
                 &&
                 (((FStar_Ident.lid_equals lex_t1
                      FStar_Parser_Const.lex_t_lid)
                     &&
                     (FStar_Ident.lid_equals lex_top1
                        FStar_Parser_Const.lextop_lid))
                    &&
                    (FStar_Ident.lid_equals lex_cons
                       FStar_Parser_Const.lexcons_lid))
               ->
               let u =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r)
                  in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u))
                   FStar_Pervasives_Native.None r
                  in
               let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1  in
               let tc =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_inductive_typ
                        (lex_t1, [u], [], t2, [],
                          [FStar_Parser_Const.lextop_lid;
                          FStar_Parser_Const.lexcons_lid]));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1)
                  in
               let lex_top_t =
                 let uu____6952 =
                   let uu____6959 =
                     let uu____6960 =
                       let uu____6967 =
                         let uu____6970 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6970
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6967, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6960  in
                   FStar_Syntax_Syntax.mk uu____6959  in
                 uu____6952 FStar_Pervasives_Native.None r1  in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r1;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2)
                  in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2)
                  in
               let lex_cons_t =
                 let a =
                   let uu____6988 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6988
                    in
                 let hd1 =
                   let uu____6990 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6990
                    in
                 let tl1 =
                   let uu____6992 =
                     let uu____6993 =
                       let uu____7000 =
                         let uu____7001 =
                           let uu____7008 =
                             let uu____7011 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7011
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7008, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7001  in
                       FStar_Syntax_Syntax.mk uu____7000  in
                     uu____6993 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6992
                    in
                 let res =
                   let uu____7020 =
                     let uu____7027 =
                       let uu____7028 =
                         let uu____7035 =
                           let uu____7038 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____7038
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____7035,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____7028  in
                     FStar_Syntax_Syntax.mk uu____7027  in
                   uu____7020 FStar_Pervasives_Native.None r2  in
                 let uu____7044 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____7044
                  in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t
                  in
               let dc_lexcons =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_cons, [ucons1; ucons2], lex_cons_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let uu____7083 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____7083;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____7088 ->
               let err_msg =
                 let uu____7093 =
                   let uu____7095 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____7095  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____7093
                  in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
  
let (tc_type_common :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Syntax_Syntax.typ ->
        FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun uu____7120  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7120 with
          | (uvs,t) ->
              let uu____7133 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7133 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7145 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7145 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7163 =
                        let uu____7166 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7166
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7163)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7189 =
          let uu____7190 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7190 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7189 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7215 =
          let uu____7216 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7216 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7215 r
  
let (tc_inductive' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          (let uu____7265 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7265
           then
             let uu____7268 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7268
           else ());
          (let uu____7273 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7273 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7304 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7304 FStar_List.flatten  in
               ((let uu____7318 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7321 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7321)
                    in
                 if uu____7318
                 then ()
                 else
                   (let env1 =
                      FStar_TypeChecker_Env.push_sigelt env sig_bndle  in
                    FStar_List.iter
                      (fun ty  ->
                         let b =
                           FStar_TypeChecker_TcInductive.check_positivity ty
                             env1
                            in
                         if Prims.op_Negation b
                         then
                           let uu____7337 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7347,uu____7348,uu____7349,uu____7350,uu____7351)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7360 -> failwith "Impossible!"  in
                           match uu____7337 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Inductive type "
                                      (Prims.strcat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7379 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7389,uu____7390,ty_lid,uu____7392,uu____7393)
                               -> (data_lid, ty_lid)
                           | uu____7400 -> failwith "Impossible"  in
                         match uu____7379 with
                         | (data_lid,ty_lid) ->
                             let uu____7408 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7411 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7411)
                                in
                             if uu____7408
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Exception "
                                      (Prims.strcat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7425 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7430,uu____7431,uu____7432,uu____7433,uu____7434)
                         -> lid
                     | uu____7443 -> failwith "Impossible"  in
                   FStar_List.existsb
                     (fun s  ->
                        s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                     FStar_TypeChecker_TcInductive.early_prims_inductives
                    in
                 let is_noeq =
                   FStar_List.existsb
                     (fun q  -> q = FStar_Syntax_Syntax.Noeq) quals
                    in
                 let res =
                   let uu____7461 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7461
                   then (sig_bndle, data_ops_ses)
                   else
                     (let is_unopteq =
                        FStar_List.existsb
                          (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals
                         in
                      let ses1 =
                        if is_unopteq
                        then
                          FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                            sig_bndle tcs datas env
                        else
                          FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                            sig_bndle tcs datas env
                         in
                      (sig_bndle, (FStar_List.append ses1 data_ops_ses)))
                    in
                 res)))
  
let (tc_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive"  in
          let pop1 uu____7536 =
            let uu____7537 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___396_7547  ->
               match () with
               | () ->
                   let uu____7554 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7554 (fun r  -> pop1 (); r)) ()
          with | uu___395_7585 -> (pop1 (); FStar_Exn.raise uu___395_7585)
  
let (get_fail_se :
  FStar_Syntax_Syntax.sigelt ->
    (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun se  ->
    let comb f1 f2 =
      match (f1, f2) with
      | (FStar_Pervasives_Native.Some (e1,l1),FStar_Pervasives_Native.Some
         (e2,l2)) ->
          FStar_Pervasives_Native.Some
            ((FStar_List.append e1 e2), (l1 || l2))
      | (FStar_Pervasives_Native.Some (e,l),FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.Some (e, l)
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some (e,l)) ->
          FStar_Pervasives_Native.Some (e, l)
      | uu____7901 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7959 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7959 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7984 .
    'Auu____7984 FStar_Pervasives_Native.option -> 'Auu____7984 Prims.list
  =
  fun uu___374_7993  ->
    match uu___374_7993 with
    | FStar_Pervasives_Native.None  -> []
    | FStar_Pervasives_Native.Some x -> [x]
  
let (check_multi_contained :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  =
  fun l1  ->
    fun l2  ->
      let rec collect1 l =
        match l with
        | [] -> []
        | hd1::tl1 ->
            let uu____8073 = collect1 tl1  in
            (match uu____8073 with
             | [] -> [(hd1, (Prims.parse_int "1"))]
             | (h,n1)::t ->
                 if h = hd1
                 then (h, (n1 + (Prims.parse_int "1"))) :: t
                 else (hd1, (Prims.parse_int "1")) :: (h, n1) :: t)
         in
      let summ l = collect1 l  in
      let l11 = summ l1  in
      let l21 = summ l2  in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([],[]) -> FStar_Pervasives_Native.None
        | ((e,n1)::uu____8311,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ([],(e,n1)::uu____8367) ->
            FStar_Pervasives_Native.Some (e, (Prims.parse_int "0"), n1)
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) when hd1 <> hd2 ->
            FStar_Pervasives_Native.Some (hd1, n1, (Prims.parse_int "0"))
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) ->
            if n1 <> n2
            then FStar_Pervasives_Native.Some (hd1, n1, n2)
            else aux tl1 tl2
         in
      aux l11 l21
  
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____8595 =
            let uu____8597 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8597  in
          if uu____8595
          then
            let uu____8600 =
              let uu____8605 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8606 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8605 uu____8606  in
            (match uu____8600 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some iface_decls1 ->
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb  ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                         let has_iface_val =
                           FStar_All.pipe_right iface_decls1
                             (FStar_Util.for_some
                                (FStar_Parser_AST.decl_is_val
                                   ((lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident))
                            in
                         if has_iface_val
                         then
                           let must_erase =
                             FStar_TypeChecker_Util.must_erase_for_extraction
                               env lb.FStar_Syntax_Syntax.lbdef
                              in
                           let has_attr =
                             FStar_TypeChecker_Env.fv_has_attr env lbname
                               FStar_Parser_Const.must_erase_for_extraction_attr
                              in
                           (if must_erase && (Prims.op_Negation has_attr)
                            then
                              let uu____8639 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8640 =
                                let uu____8646 =
                                  let uu____8648 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8650 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8648 uu____8650
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8646)
                                 in
                              FStar_Errors.log_issue uu____8639 uu____8640
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8657 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8658 =
                                   let uu____8664 =
                                     let uu____8666 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8666
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8664)
                                    in
                                 FStar_Errors.log_issue uu____8657 uu____8658)
                              else ())
                         else ())))
          else ()
      | uu____8676 -> ()
  
let (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env0  ->
    fun se  ->
      let env = env0  in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      (let r = se.FStar_Syntax_Syntax.sigrng  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8721 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8749 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let se1 = tc_lex_t env1 ses se.FStar_Syntax_Syntax.sigquals lids
              in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let ses1 =
             let uu____8809 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8809
             then
               let ses1 =
                 let uu____8817 =
                   let uu____8818 =
                     let uu____8819 =
                       tc_inductive
                         (let uu___397_8828 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___397_8828.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___397_8828.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___397_8828.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___397_8828.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___397_8828.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___397_8828.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___397_8828.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___397_8828.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___397_8828.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___397_8828.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___397_8828.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___397_8828.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___397_8828.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___397_8828.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___397_8828.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___397_8828.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___397_8828.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___397_8828.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___397_8828.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___397_8828.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___397_8828.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___397_8828.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___397_8828.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___397_8828.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___397_8828.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___397_8828.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___397_8828.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___397_8828.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___397_8828.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___397_8828.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___397_8828.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___397_8828.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___397_8828.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___397_8828.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___397_8828.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___397_8828.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___397_8828.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___397_8828.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___397_8828.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___397_8828.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___397_8828.FStar_TypeChecker_Env.nbe)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8819
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8818
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8817
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8842 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8842
                 then
                   let uu____8847 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___398_8851 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___398_8851.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___398_8851.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___398_8851.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___398_8851.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8847
                 else ());
                ses1)
             else ses  in
           let uu____8861 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8861 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___399_8885 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___399_8885.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___399_8885.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___399_8885.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___399_8885.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____8897 = cps_and_elaborate env ne  in
           (match uu____8897 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___400_8936 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___400_8936.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___400_8936.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___400_8936.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___400_8936.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___401_8938 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___401_8938.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___401_8938.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___401_8938.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___401_8938.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____8945 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env)
                in
             if uu____8945
             then
               let ne1 =
                 let uu____8949 =
                   let uu____8950 =
                     let uu____8951 =
                       tc_eff_decl
                         (let uu___402_8954 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___402_8954.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___402_8954.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___402_8954.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___402_8954.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___402_8954.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___402_8954.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___402_8954.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___402_8954.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___402_8954.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___402_8954.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___402_8954.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___402_8954.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___402_8954.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___402_8954.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___402_8954.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___402_8954.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___402_8954.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___402_8954.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___402_8954.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___402_8954.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___402_8954.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___402_8954.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___402_8954.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___402_8954.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___402_8954.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___402_8954.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___402_8954.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___402_8954.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___402_8954.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___402_8954.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___402_8954.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___402_8954.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___402_8954.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___402_8954.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___402_8954.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___402_8954.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___402_8954.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___402_8954.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___402_8954.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___402_8954.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___402_8954.FStar_TypeChecker_Env.nbe)
                          }) ne
                        in
                     FStar_All.pipe_right uu____8951
                       (fun ne1  ->
                          let uu___403_8960 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___403_8960.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___403_8960.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___403_8960.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___403_8960.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____8950
                     (FStar_TypeChecker_Normalize.elim_uvars env)
                    in
                 FStar_All.pipe_right uu____8949
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____8962 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8962
                 then
                   let uu____8967 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___404_8971 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___404_8971.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___404_8971.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___404_8971.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___404_8971.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____8967
                 else ());
                ne1)
             else ne  in
           let ne2 = tc_eff_decl env ne1  in
           let se1 =
             let uu___405_8979 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___405_8979.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___405_8979.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___405_8979.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___405_8979.FStar_Syntax_Syntax.sigattrs)
             }  in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.source
              in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.target
              in
           let uu____8987 =
             let uu____8994 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8994
              in
           (match uu____8987 with
            | (a,wp_a_src) ->
                let uu____9011 =
                  let uu____9018 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____9018
                   in
                (match uu____9011 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____9036 =
                         let uu____9039 =
                           let uu____9040 =
                             let uu____9047 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____9047)  in
                           FStar_Syntax_Syntax.NT uu____9040  in
                         [uu____9039]  in
                       FStar_Syntax_Subst.subst uu____9036 wp_b_tgt  in
                     let expected_k =
                       let uu____9055 =
                         let uu____9064 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____9071 =
                           let uu____9080 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____9080]  in
                         uu____9064 :: uu____9071  in
                       let uu____9105 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____9055 uu____9105  in
                     let repr_type eff_name a1 wp =
                       (let uu____9127 =
                          let uu____9129 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____9129  in
                        if uu____9127
                        then
                          let uu____9132 =
                            let uu____9138 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____9138)
                             in
                          let uu____9142 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____9132 uu____9142
                        else ());
                       (let uu____9145 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____9145 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ([], (ed.FStar_Syntax_Syntax.repr))
                               in
                            let uu____9182 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____9183 =
                              let uu____9190 =
                                let uu____9191 =
                                  let uu____9208 =
                                    let uu____9219 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____9228 =
                                      let uu____9239 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9239]  in
                                    uu____9219 :: uu____9228  in
                                  (repr, uu____9208)  in
                                FStar_Syntax_Syntax.Tm_app uu____9191  in
                              FStar_Syntax_Syntax.mk uu____9190  in
                            uu____9183 FStar_Pervasives_Native.None
                              uu____9182)
                        in
                     let uu____9287 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9460 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9471 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9471 with
                               | (usubst,uvs1) ->
                                   let uu____9494 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9495 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9494, uu____9495)
                             else (env, lift_wp)  in
                           (match uu____9460 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if
                                    (FStar_List.length uvs) =
                                      (Prims.parse_int "0")
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____9545 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9545))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9616 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9631 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9631 with
                               | (usubst,uvs) ->
                                   let uu____9656 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9656)
                             else ([], lift)  in
                           (match uu____9616 with
                            | (uvs,lift1) ->
                                ((let uu____9692 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9692
                                  then
                                    let uu____9696 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9696
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9702 =
                                    let uu____9709 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9709 lift1
                                     in
                                  match uu____9702 with
                                  | (lift2,comp,uu____9734) ->
                                      let uu____9735 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9735 with
                                       | (uu____9764,lift_wp,lift_elab) ->
                                           let lift_wp1 =
                                             recheck_debug "lift-wp" env
                                               lift_wp
                                              in
                                           let lift_elab1 =
                                             recheck_debug "lift-elab" env
                                               lift_elab
                                              in
                                           if
                                             (FStar_List.length uvs) =
                                               (Prims.parse_int "0")
                                           then
                                             let uu____9796 =
                                               let uu____9807 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9807
                                                in
                                             let uu____9824 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9796, uu____9824)
                                           else
                                             (let uu____9853 =
                                                let uu____9864 =
                                                  let uu____9873 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____9873)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9864
                                                 in
                                              let uu____9888 =
                                                let uu____9897 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____9897)  in
                                              (uu____9853, uu____9888))))))
                        in
                     (match uu____9287 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___406_9971 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___406_9971.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___406_9971.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___406_9971.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___406_9971.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___406_9971.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___406_9971.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___406_9971.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___406_9971.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___406_9971.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___406_9971.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___406_9971.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___406_9971.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___406_9971.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___406_9971.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___406_9971.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___406_9971.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___406_9971.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___406_9971.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___406_9971.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___406_9971.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___406_9971.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___406_9971.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___406_9971.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___406_9971.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___406_9971.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___406_9971.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___406_9971.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___406_9971.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___406_9971.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___406_9971.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___406_9971.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___406_9971.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___406_9971.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___406_9971.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___406_9971.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___406_9971.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___406_9971.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___406_9971.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___406_9971.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___406_9971.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___406_9971.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___406_9971.FStar_TypeChecker_Env.nbe)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____10004 =
                                  let uu____10009 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____10009 with
                                  | (usubst,uvs1) ->
                                      let uu____10032 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____10033 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____10032, uu____10033)
                                   in
                                (match uu____10004 with
                                 | (env2,lift2) ->
                                     let uu____10038 =
                                       let uu____10045 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____10045
                                        in
                                     (match uu____10038 with
                                      | (a1,wp_a_src1) ->
                                          let wp_a =
                                            FStar_Syntax_Syntax.new_bv
                                              FStar_Pervasives_Native.None
                                              wp_a_src1
                                             in
                                          let a_typ =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          let wp_a_typ =
                                            FStar_Syntax_Syntax.bv_to_name
                                              wp_a
                                             in
                                          let repr_f =
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.source
                                              a_typ wp_a_typ
                                             in
                                          let repr_result =
                                            let lift_wp1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Env.EraseUniverses;
                                                FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   lift_wp)
                                               in
                                            let lift_wp_a =
                                              let uu____10071 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____10072 =
                                                let uu____10079 =
                                                  let uu____10080 =
                                                    let uu____10097 =
                                                      let uu____10108 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____10117 =
                                                        let uu____10128 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____10128]  in
                                                      uu____10108 ::
                                                        uu____10117
                                                       in
                                                    (lift_wp1, uu____10097)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10080
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____10079
                                                 in
                                              uu____10072
                                                FStar_Pervasives_Native.None
                                                uu____10071
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____10179 =
                                              let uu____10188 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____10195 =
                                                let uu____10204 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____10211 =
                                                  let uu____10220 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____10220]  in
                                                uu____10204 :: uu____10211
                                                 in
                                              uu____10188 :: uu____10195  in
                                            let uu____10251 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____10179 uu____10251
                                             in
                                          let uu____10254 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____10254 with
                                           | (expected_k2,uu____10264,uu____10265)
                                               ->
                                               let lift3 =
                                                 if
                                                   (FStar_List.length uvs) =
                                                     (Prims.parse_int "0")
                                                 then
                                                   check_and_gen env2 lift2
                                                     expected_k2
                                                 else
                                                   (let lift3 =
                                                      tc_check_trivial_guard
                                                        env2 lift2
                                                        expected_k2
                                                       in
                                                    let uu____10273 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____10273))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____10281 =
                              let uu____10283 =
                                let uu____10285 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____10285
                                  FStar_List.length
                                 in
                              uu____10283 <> (Prims.parse_int "1")  in
                            if uu____10281
                            then
                              let uu____10308 =
                                let uu____10314 =
                                  let uu____10316 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10318 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10320 =
                                    let uu____10322 =
                                      let uu____10324 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10324
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10322
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10316 uu____10318 uu____10320
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10314)
                                 in
                              FStar_Errors.raise_error uu____10308 r
                            else ());
                           (let uu____10351 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10354 =
                                   let uu____10356 =
                                     let uu____10359 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10359
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10356
                                     FStar_List.length
                                    in
                                 uu____10354 <> (Prims.parse_int "1"))
                               in
                            if uu____10351
                            then
                              let uu____10398 =
                                let uu____10404 =
                                  let uu____10406 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10408 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10410 =
                                    let uu____10412 =
                                      let uu____10414 =
                                        let uu____10417 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10417
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10414
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10412
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10406 uu____10408 uu____10410
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10404)
                                 in
                              FStar_Errors.raise_error uu____10398 r
                            else ());
                           (let sub2 =
                              let uu___407_10460 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___407_10460.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___407_10460.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___408_10462 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___408_10462.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___408_10462.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___408_10462.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___408_10462.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let uu____10476 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____10504 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10504 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10535 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10535 c  in
                    let uu____10544 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10544, uvs1, tps1, c1))
              in
           (match uu____10476 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10566 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10566 with
                 | (tps2,c2) ->
                     let uu____10583 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10583 with
                      | (tps3,env3,us) ->
                          let uu____10603 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10603 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10631)::uu____10632 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10651 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10659 =
                                   let uu____10661 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10661  in
                                 if uu____10659
                                 then
                                   let uu____10664 =
                                     let uu____10670 =
                                       let uu____10672 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10674 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10672 uu____10674
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10670)
                                      in
                                   FStar_Errors.raise_error uu____10664 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10682 =
                                   let uu____10683 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10683
                                    in
                                 match uu____10682 with
                                 | (uvs2,t) ->
                                     let uu____10714 =
                                       let uu____10719 =
                                         let uu____10732 =
                                           let uu____10733 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10733.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10732)  in
                                       match uu____10719 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10748,c5)) -> ([], c5)
                                       | (uu____10790,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10829 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10714 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____10863 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10863 with
                                              | (uu____10868,t1) ->
                                                  let uu____10870 =
                                                    let uu____10876 =
                                                      let uu____10878 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____10880 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____10884 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10878
                                                        uu____10880
                                                        uu____10884
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10876)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____10870 r)
                                           else ();
                                           (let se1 =
                                              let uu___409_10891 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___409_10891.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___409_10891.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___409_10891.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___409_10891.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10898,uu____10899,uu____10900) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10905  ->
                   match uu___375_10905 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10908 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10914,uu____10915) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10924  ->
                   match uu___375_10924 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10927 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____10938 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____10938
             then
               let uu____10941 =
                 let uu____10947 =
                   let uu____10949 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____10949
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____10947)
                  in
               FStar_Errors.raise_error uu____10941 r
             else ());
            (let uu____10955 =
               let uu____10964 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____10964
               then
                 let uu____10975 =
                   tc_declare_typ
                     (let uu___410_10978 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___410_10978.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___410_10978.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___410_10978.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___410_10978.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___410_10978.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___410_10978.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___410_10978.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___410_10978.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___410_10978.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___410_10978.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___410_10978.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___410_10978.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___410_10978.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___410_10978.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___410_10978.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___410_10978.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___410_10978.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___410_10978.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___410_10978.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___410_10978.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___410_10978.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___410_10978.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___410_10978.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___410_10978.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___410_10978.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___410_10978.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___410_10978.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___410_10978.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___410_10978.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___410_10978.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___410_10978.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___410_10978.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___410_10978.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___410_10978.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___410_10978.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___410_10978.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___410_10978.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___410_10978.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___410_10978.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___410_10978.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___410_10978.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___410_10978.FStar_TypeChecker_Env.nbe)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____10975 with
                 | (uvs1,t1) ->
                     ((let uu____11003 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____11003
                       then
                         let uu____11008 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____11010 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____11008 uu____11010
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____10955 with
             | (uvs1,t1) ->
                 let uu____11045 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____11045 with
                  | (uvs2,t2) ->
                      ([(let uu___411_11075 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___411_11075.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___411_11075.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___411_11075.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___411_11075.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____11080 =
             let uu____11089 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11089
             then
               let uu____11100 =
                 tc_assume
                   (let uu___412_11103 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___412_11103.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___412_11103.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___412_11103.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___412_11103.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___412_11103.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___412_11103.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___412_11103.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___412_11103.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___412_11103.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___412_11103.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___412_11103.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___412_11103.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___412_11103.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___412_11103.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___412_11103.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___412_11103.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___412_11103.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___412_11103.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___412_11103.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___412_11103.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___412_11103.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___412_11103.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___412_11103.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___412_11103.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___412_11103.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___412_11103.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___412_11103.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___412_11103.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___412_11103.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___412_11103.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___412_11103.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___412_11103.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___412_11103.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___412_11103.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___412_11103.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___412_11103.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___412_11103.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___412_11103.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___412_11103.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___412_11103.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___412_11103.FStar_TypeChecker_Env.nbe)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11100 with
               | (uvs1,t1) ->
                   ((let uu____11129 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11129
                     then
                       let uu____11134 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11136 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11134
                         uu____11136
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____11080 with
            | (uvs1,t1) ->
                let uu____11171 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11171 with
                 | (uvs2,t2) ->
                     ([(let uu___413_11201 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___413_11201.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___413_11201.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___413_11201.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___413_11201.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11205 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11205 with
            | (e1,c,g1) ->
                let uu____11225 =
                  let uu____11232 =
                    let uu____11235 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____11235  in
                  let uu____11236 =
                    let uu____11241 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____11241)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____11232 uu____11236
                   in
                (match uu____11225 with
                 | (e2,uu____11253,g) ->
                     ((let uu____11256 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11256);
                      (let se1 =
                         let uu___414_11258 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___414_11258.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___414_11258.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___414_11258.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___414_11258.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11270 = FStar_Options.debug_any ()  in
             if uu____11270
             then
               let uu____11273 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11275 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11273
                 uu____11275
             else ());
            (let uu____11280 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11280 with
             | (t1,uu____11298,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11312 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11312 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11315 =
                              let uu____11321 =
                                let uu____11323 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11325 =
                                  let uu____11327 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11327
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11323 uu____11325
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11321)
                               in
                            FStar_Errors.raise_error uu____11315 r
                        | uu____11339 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___415_11344 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___415_11344.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___415_11344.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___415_11344.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___415_11344.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___415_11344.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___415_11344.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___415_11344.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___415_11344.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___415_11344.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___415_11344.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___415_11344.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___415_11344.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___415_11344.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___415_11344.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___415_11344.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___415_11344.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___415_11344.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___415_11344.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___415_11344.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___415_11344.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___415_11344.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___415_11344.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___415_11344.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___415_11344.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___415_11344.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___415_11344.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___415_11344.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___415_11344.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___415_11344.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___415_11344.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___415_11344.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___415_11344.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___415_11344.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___415_11344.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___415_11344.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___415_11344.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___415_11344.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___415_11344.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___415_11344.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___415_11344.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___415_11344.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___415_11344.FStar_TypeChecker_Env.nbe)
                      }  in
                    ([], ses, env1))))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let check_quals_eq l qopt val_q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some val_q
             | FStar_Pervasives_Native.Some q' ->
                 let drop_logic =
                   FStar_List.filter
                     (fun x  ->
                        Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))
                    in
                 let uu____11412 =
                   let uu____11414 =
                     let uu____11423 = drop_logic val_q  in
                     let uu____11426 = drop_logic q'  in
                     (uu____11423, uu____11426)  in
                   match uu____11414 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11412
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11453 =
                      let uu____11459 =
                        let uu____11461 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11463 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11465 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11461 uu____11463 uu____11465
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11459)
                       in
                    FStar_Errors.raise_error uu____11453 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11502 =
                   let uu____11503 = FStar_Syntax_Subst.compress def  in
                   uu____11503.FStar_Syntax_Syntax.n  in
                 match uu____11502 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11515,uu____11516) -> binders
                 | uu____11541 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11553;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11658) -> val_bs1
                     | (uu____11689,[]) -> val_bs1
                     | ((body_bv,uu____11721)::bt,(val_bv,aqual)::vt) ->
                         let uu____11778 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11802) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___416_11816 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___417_11819 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___417_11819.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___416_11816.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___416_11816.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11778
                      in
                   let uu____11826 =
                     let uu____11833 =
                       let uu____11834 =
                         let uu____11849 = rename_binders1 def_bs val_bs  in
                         (uu____11849, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11834  in
                     FStar_Syntax_Syntax.mk uu____11833  in
                   uu____11826 FStar_Pervasives_Native.None r1
               | uu____11871 -> typ1  in
             let uu___418_11872 = lb  in
             let uu____11873 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___418_11872.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___418_11872.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11873;
               FStar_Syntax_Syntax.lbeff =
                 (uu___418_11872.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___418_11872.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___418_11872.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___418_11872.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____11876 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____11931  ->
                     fun lb  ->
                       match uu____11931 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____11977 =
                             let uu____11989 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____11989 with
                             | FStar_Pervasives_Native.None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | FStar_Pervasives_Native.Some
                                 ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals
                                    in
                                 let def =
                                   match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  ->
                                       lb.FStar_Syntax_Syntax.lbdef
                                   | uu____12069 ->
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_ascribed
                                            ((lb.FStar_Syntax_Syntax.lbdef),
                                              ((FStar_Util.Inl
                                                  (lb.FStar_Syntax_Syntax.lbtyp)),
                                                FStar_Pervasives_Native.None),
                                              FStar_Pervasives_Native.None))
                                         FStar_Pervasives_Native.None
                                         (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos
                                    in
                                 (if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                        "Inline universes are incoherent with annotation from val declaration")
                                      r
                                  else ();
                                  (let uu____12116 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12116, quals_opt1)))
                              in
                           (match uu____11977 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____11876 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12220 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___376_12226  ->
                                match uu___376_12226 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12231 -> false))
                         in
                      if uu____12220
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12244 =
                    let uu____12251 =
                      let uu____12252 =
                        let uu____12266 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12266)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12252  in
                    FStar_Syntax_Syntax.mk uu____12251  in
                  uu____12244 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___419_12288 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___419_12288.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___419_12288.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___419_12288.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___419_12288.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___419_12288.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___419_12288.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___419_12288.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___419_12288.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___419_12288.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___419_12288.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___419_12288.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___419_12288.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___419_12288.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___419_12288.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___419_12288.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___419_12288.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___419_12288.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___419_12288.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___419_12288.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___419_12288.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___419_12288.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___419_12288.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___419_12288.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___419_12288.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___419_12288.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___419_12288.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___419_12288.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___419_12288.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___419_12288.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___419_12288.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___419_12288.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___419_12288.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___419_12288.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___419_12288.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___419_12288.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___419_12288.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___419_12288.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___419_12288.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___419_12288.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___419_12288.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___419_12288.FStar_TypeChecker_Env.nbe)
                  }  in
                let e1 =
                  let uu____12291 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12291
                  then
                    let drop_lbtyp e_lax =
                      let uu____12300 =
                        let uu____12301 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12301.FStar_Syntax_Syntax.n  in
                      match uu____12300 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12323 =
                              let uu____12324 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12324.FStar_Syntax_Syntax.n  in
                            match uu____12323 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12328,lb1::[]),uu____12330) ->
                                let uu____12346 =
                                  let uu____12347 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12347.FStar_Syntax_Syntax.n  in
                                (match uu____12346 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12352 -> false)
                            | uu____12354 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___420_12358 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___421_12373 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___421_12373.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___421_12373.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___421_12373.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___421_12373.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___421_12373.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___421_12373.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___420_12358.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___420_12358.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12376 -> e_lax  in
                    let e1 =
                      let uu____12378 =
                        let uu____12379 =
                          let uu____12380 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___422_12389 = env'  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___422_12389.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___422_12389.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___422_12389.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___422_12389.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___422_12389.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___422_12389.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___422_12389.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___422_12389.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___422_12389.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___422_12389.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___422_12389.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___422_12389.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___422_12389.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___422_12389.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___422_12389.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___422_12389.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___422_12389.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___422_12389.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___422_12389.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___422_12389.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___422_12389.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___422_12389.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___422_12389.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___422_12389.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___422_12389.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___422_12389.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___422_12389.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___422_12389.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___422_12389.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___422_12389.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___422_12389.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___422_12389.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___422_12389.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___422_12389.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___422_12389.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___422_12389.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___422_12389.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___422_12389.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___422_12389.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___422_12389.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___422_12389.FStar_TypeChecker_Env.nbe)
                               }) e
                             in
                          FStar_All.pipe_right uu____12380
                            (fun uu____12402  ->
                               match uu____12402 with
                               | (e1,uu____12410,uu____12411) -> e1)
                           in
                        FStar_All.pipe_right uu____12379
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env')
                         in
                      FStar_All.pipe_right uu____12378 drop_lbtyp  in
                    ((let uu____12413 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____12413
                      then
                        let uu____12418 =
                          FStar_Syntax_Print.term_to_string e1  in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____12418
                      else ());
                     e1)
                  else e  in
                let uu____12425 =
                  let uu____12434 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12434 with
                  | FStar_Pervasives_Native.None  ->
                      ((se.FStar_Syntax_Syntax.sigattrs),
                        FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some
                      (ats,(tau,FStar_Pervasives_Native.None )::[]) ->
                      (ats, (FStar_Pervasives_Native.Some tau))
                  | FStar_Pervasives_Native.Some (ats,args) ->
                      (FStar_Errors.log_issue r
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `postprocess_with`");
                       ((se.FStar_Syntax_Syntax.sigattrs),
                         FStar_Pervasives_Native.None))
                   in
                (match uu____12425 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___423_12539 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___423_12539.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___423_12539.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___423_12539.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___423_12539.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___424_12552 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___424_12552.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___424_12552.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___424_12552.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___424_12552.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___424_12552.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___424_12552.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12553 =
                       let uu____12565 =
                         FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env'
                           e1
                          in
                       match uu____12565 with
                       | ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                            FStar_Syntax_Syntax.pos = uu____12585;
                            FStar_Syntax_Syntax.vars = uu____12586;_},uu____12587,g)
                           when FStar_TypeChecker_Env.is_trivial g ->
                           let lbs2 =
                             let uu____12617 =
                               FStar_All.pipe_right
                                 (FStar_Pervasives_Native.snd lbs1)
                                 (FStar_List.map rename_parameters)
                                in
                             ((FStar_Pervasives_Native.fst lbs1),
                               uu____12617)
                              in
                           let lbs3 =
                             let uu____12641 =
                               match post_tau with
                               | FStar_Pervasives_Native.Some tau ->
                                   FStar_List.map (postprocess_lb tau)
                                     (FStar_Pervasives_Native.snd lbs2)
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.snd lbs2
                                in
                             ((FStar_Pervasives_Native.fst lbs2),
                               uu____12641)
                              in
                           let quals1 =
                             match e2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_meta
                                 (uu____12664,FStar_Syntax_Syntax.Meta_desugared
                                  (FStar_Syntax_Syntax.Masked_effect ))
                                 -> FStar_Syntax_Syntax.HasMaskedEffect ::
                                 quals
                             | uu____12669 -> quals  in
                           ((let uu___425_12678 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_let (lbs3, lids));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___425_12678.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals = quals1;
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___425_12678.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___425_12678.FStar_Syntax_Syntax.sigattrs)
                             }), lbs3)
                       | uu____12681 ->
                           failwith
                             "impossible (typechecking should preserve Tm_let)"
                        in
                     (match uu____12553 with
                      | (se2,lbs1) ->
                          (FStar_All.pipe_right
                             (FStar_Pervasives_Native.snd lbs1)
                             (FStar_List.iter
                                (fun lb  ->
                                   let fv =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_TypeChecker_Env.insert_fv_info env1
                                     fv lb.FStar_Syntax_Syntax.lbtyp));
                           (let uu____12737 = log env1  in
                            if uu____12737
                            then
                              let uu____12740 =
                                let uu____12742 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs1)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let should_log =
                                            let uu____12762 =
                                              let uu____12771 =
                                                let uu____12772 =
                                                  let uu____12775 =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  uu____12775.FStar_Syntax_Syntax.fv_name
                                                   in
                                                uu____12772.FStar_Syntax_Syntax.v
                                                 in
                                              FStar_TypeChecker_Env.try_lookup_val_decl
                                                env1 uu____12771
                                               in
                                            match uu____12762 with
                                            | FStar_Pervasives_Native.None 
                                                -> true
                                            | uu____12784 -> false  in
                                          if should_log
                                          then
                                            let uu____12796 =
                                              FStar_Syntax_Print.lbname_to_string
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            let uu____12798 =
                                              FStar_Syntax_Print.term_to_string
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            FStar_Util.format2 "let %s : %s"
                                              uu____12796 uu____12798
                                          else ""))
                                   in
                                FStar_All.pipe_right uu____12742
                                  (FStar_String.concat "\n")
                                 in
                              FStar_Util.print1 "%s\n" uu____12740
                            else ());
                           check_must_erase_attribute env0 se2;
                           ([se2], [], env0))))))
  
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      (let uu____12850 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12850
       then
         let uu____12853 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12853
       else ());
      (let uu____12858 = get_fail_se se  in
       match uu____12858 with
       | FStar_Pervasives_Native.Some (uu____12879,false ) when
           let uu____12896 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12896 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___426_12922 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___426_12922.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___426_12922.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___426_12922.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___426_12922.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___426_12922.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___426_12922.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___426_12922.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___426_12922.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___426_12922.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___426_12922.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___426_12922.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___426_12922.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___426_12922.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___426_12922.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___426_12922.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___426_12922.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___426_12922.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___426_12922.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___426_12922.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___426_12922.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___426_12922.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___426_12922.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___426_12922.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___426_12922.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___426_12922.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___426_12922.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___426_12922.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___426_12922.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___426_12922.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___426_12922.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___426_12922.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___426_12922.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___426_12922.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___426_12922.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___426_12922.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___426_12922.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___426_12922.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___426_12922.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___426_12922.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___426_12922.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___426_12922.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___426_12922.FStar_TypeChecker_Env.nbe)
               }
             else env1  in
           ((let uu____12927 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____12927
             then
               let uu____12930 =
                 let uu____12932 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12932
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12930
             else ());
            (let uu____12946 =
               FStar_Errors.catch_errors
                 (fun uu____12976  ->
                    FStar_Options.with_saved_options
                      (fun uu____12988  -> tc_decl' env' se))
                in
             match uu____12946 with
             | (errs,uu____13000) ->
                 ((let uu____13030 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____13030
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____13065 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____13065  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____13077 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13088 =
                            let uu____13098 =
                              check_multi_contained errnos1 actual  in
                            match uu____13098 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")))
                             in
                          (match uu____13088 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13163 =
                                   let uu____13169 =
                                     let uu____13171 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13174 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13177 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13179 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13181 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13171 uu____13174 uu____13177
                                       uu____13179 uu____13181
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13169)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13163)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13208 .
    'Auu____13208 ->
      FStar_Ident.lident Prims.list ->
        FStar_Syntax_Syntax.sigelt ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident
            Prims.list)
  =
  fun env  ->
    fun hidden  ->
      fun se  ->
        let is_abstract quals =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___377_13251  ->
                  match uu___377_13251 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13254 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13265) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13273 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13283 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13288 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13304 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13330 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13356) ->
            let uu____13365 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13365
            then
              let for_export_bundle se1 uu____13402 =
                match uu____13402 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13441,uu____13442) ->
                         let dec =
                           let uu___427_13452 = se1  in
                           let uu____13453 =
                             let uu____13454 =
                               let uu____13461 =
                                 let uu____13462 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13462  in
                               (l, us, uu____13461)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13454
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13453;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___427_13452.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___427_13452.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___427_13452.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13472,uu____13473,uu____13474) ->
                         let dec =
                           let uu___428_13482 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___428_13482.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___428_13482.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___428_13482.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13487 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13510,uu____13511,uu____13512) ->
            let uu____13513 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13513 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13537 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13537
            then
              ([(let uu___429_13556 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___429_13556.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___429_13556.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___429_13556.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13559 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___378_13565  ->
                         match uu___378_13565 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13568 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13574 ->
                             true
                         | uu____13576 -> false))
                  in
               if uu____13559 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13597 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13602 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13607 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13612 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13617 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13635) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13649 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13649
            then ([], hidden)
            else
              (let dec =
                 let uu____13670 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13670;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13681 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13681
            then
              let uu____13692 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___430_13706 = se  in
                        let uu____13707 =
                          let uu____13708 =
                            let uu____13715 =
                              let uu____13716 =
                                let uu____13719 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13719.FStar_Syntax_Syntax.fv_name  in
                              uu____13716.FStar_Syntax_Syntax.v  in
                            (uu____13715, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13708  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13707;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___430_13706.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___430_13706.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___430_13706.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13692, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13742 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13742
       then
         let uu____13745 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13745
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13750 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13768 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____13785) -> env
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           env
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____13789) -> env
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13791) -> env
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____13796 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13797 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13807 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13807) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13808,uu____13809,uu____13810) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13815  ->
                   match uu___379_13815 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13818 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13820,uu____13821) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13830  ->
                   match uu___379_13830 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13833 -> false))
           -> env
       | uu____13835 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13904 se =
        match uu____13904 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____13957 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____13957
              then
                let uu____13960 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13960
              else ());
             (let uu____13965 = tc_decl env1 se  in
              match uu____13965 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14018 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14018
                             then
                               let uu____14022 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____14022
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14038 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14038
                             then
                               let uu____14042 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____14042
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  (FStar_TypeChecker_Env.promote_id_info env2
                     (fun t  ->
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.AllowUnboundUniverses;
                          FStar_TypeChecker_Env.CheckNoUvars;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                          FStar_TypeChecker_Env.CompressUvars;
                          FStar_TypeChecker_Env.Exclude
                            FStar_TypeChecker_Env.Zeta;
                          FStar_TypeChecker_Env.Exclude
                            FStar_TypeChecker_Env.Iota;
                          FStar_TypeChecker_Env.NoFullNorm] env2 t);
                   (let env3 =
                      FStar_All.pipe_right ses'1
                        (FStar_List.fold_left
                           (fun env3  ->
                              fun se1  -> add_sigelt_to_env env3 se1) env2)
                       in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____14059 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____14059
                     then
                       let uu____14064 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____14073 =
                                  let uu____14075 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____14075 "\n"  in
                                Prims.strcat s uu____14073) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____14064
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____14085 =
                       let uu____14094 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____14094
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14136 se1 =
                            match uu____14136 with
                            | (exports1,hidden1) ->
                                let uu____14164 = for_export env3 hidden1 se1
                                   in
                                (match uu____14164 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____14085 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14318 = acc  in
        match uu____14318 with
        | (uu____14353,uu____14354,env1,uu____14356) ->
            let uu____14369 =
              FStar_Util.record_time
                (fun uu____14416  -> process_one_decl acc se)
               in
            (match uu____14369 with
             | (r,ms_elapsed) ->
                 ((let uu____14482 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14482
                   then
                     let uu____14486 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14488 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14486 uu____14488
                   else ());
                  r))
         in
      let uu____14493 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14493 with
      | (ses1,exports,env1,uu____14541) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> unit)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___431_14579 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___431_14579.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___431_14579.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___431_14579.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___431_14579.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___431_14579.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___431_14579.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___431_14579.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___431_14579.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___431_14579.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___431_14579.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___431_14579.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___431_14579.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___431_14579.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___431_14579.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___431_14579.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___431_14579.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___431_14579.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___431_14579.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___431_14579.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___431_14579.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___431_14579.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___431_14579.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___431_14579.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___431_14579.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___431_14579.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___431_14579.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___431_14579.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___431_14579.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___431_14579.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___431_14579.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___431_14579.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___431_14579.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___431_14579.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___431_14579.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___431_14579.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___431_14579.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___431_14579.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___431_14579.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___431_14579.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___431_14579.FStar_TypeChecker_Env.nbe)
          }  in
        let check_term lid univs1 t =
          let uu____14599 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14599 with
          | (univs2,t1) ->
              ((let uu____14607 =
                  let uu____14609 =
                    let uu____14615 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14615  in
                  FStar_All.pipe_left uu____14609
                    (FStar_Options.Other "Exports")
                   in
                if uu____14607
                then
                  let uu____14619 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14621 =
                    let uu____14623 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14623
                      (FStar_String.concat ", ")
                     in
                  let uu____14640 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14619 uu____14621 uu____14640
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14646 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14646 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14672 =
             let uu____14674 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14676 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14674 uu____14676
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14672);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14687) ->
              let uu____14696 =
                let uu____14698 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14698  in
              if uu____14696
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14712,uu____14713) ->
              let t =
                let uu____14725 =
                  let uu____14732 =
                    let uu____14733 =
                      let uu____14748 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14748)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14733  in
                  FStar_Syntax_Syntax.mk uu____14732  in
                uu____14725 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14767,uu____14768,uu____14769) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14779 =
                let uu____14781 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14781  in
              if uu____14779 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14789,lbs),uu____14791) ->
              let uu____14802 =
                let uu____14804 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14804  in
              if uu____14802
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags1) ->
              let uu____14827 =
                let uu____14829 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14829  in
              if uu____14827
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14850 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14851 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14858 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14859 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14860 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14861 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14868 -> ()  in
        let uu____14869 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14869 then () else FStar_List.iter check_sigelt exports
  
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun en  ->
    fun m  ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract  in
      let is_irreducible1 =
        FStar_List.contains FStar_Syntax_Syntax.Irreducible  in
      let is_assume = FStar_List.contains FStar_Syntax_Syntax.Assumption  in
      let filter_out_abstract =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((q = FStar_Syntax_Syntax.Abstract) ||
                   (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default)))
         in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Noeq))
                    || (q = FStar_Syntax_Syntax.Unopteq))
                   || (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default)))
         in
      let filter_out_abstract_and_inline =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Irreducible))
                    || (q = FStar_Syntax_Syntax.Visible_default))
                   || (q = FStar_Syntax_Syntax.Inline_for_extraction))
                  ||
                  (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
         in
      let abstract_inductive_tycons = FStar_Util.mk_ref []  in
      let abstract_inductive_datacons = FStar_Util.mk_ref []  in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q  ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l -> true
             | FStar_Syntax_Syntax.Projector (l,uu____14975) -> true
             | uu____14977 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____15007 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____15046 ->
                   let uu____15047 =
                     let uu____15054 =
                       let uu____15055 =
                         let uu____15070 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____15070)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15055  in
                     FStar_Syntax_Syntax.mk uu____15054  in
                   uu____15047 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____15090,uu____15091) ->
            let s1 =
              let uu___432_15101 = s  in
              let uu____15102 =
                let uu____15103 =
                  let uu____15110 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15110)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15103  in
              let uu____15111 =
                let uu____15114 =
                  let uu____15117 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15117  in
                FStar_Syntax_Syntax.Assumption :: uu____15114  in
              {
                FStar_Syntax_Syntax.sigel = uu____15102;
                FStar_Syntax_Syntax.sigrng =
                  (uu___432_15101.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15111;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___432_15101.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___432_15101.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15120 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15145 lbdef =
        match uu____15145 with
        | (uvs,t) ->
            let attrs =
              let uu____15156 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15156
              then
                let uu____15161 =
                  let uu____15162 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15162
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15161 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___433_15165 = s  in
            let uu____15166 =
              let uu____15169 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15169  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___433_15165.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15166;
              FStar_Syntax_Syntax.sigmeta =
                (uu___433_15165.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15187 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15194 = FStar_Syntax_Util.is_unit t  in
          if uu____15194
          then
            let uu____15201 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15201
          else
            (let uu____15208 =
               let uu____15209 = FStar_Syntax_Subst.compress t  in
               uu____15209.FStar_Syntax_Syntax.n  in
             match uu____15208 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15216,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15240 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15252 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15252
            then false
            else
              (let uu____15259 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15259
               then true
               else
                 (let uu____15266 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15266))
         in
      let extract_sigelt s =
        (let uu____15278 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15278
         then
           let uu____15281 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15281
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15288 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15308 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15327 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
             if is_abstract s.FStar_Syntax_Syntax.sigquals
             then
               FStar_All.pipe_right sigelts
                 (FStar_List.fold_left
                    (fun sigelts1  ->
                       fun s1  ->
                         match s1.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid,uu____15373,uu____15374,uu____15375,uu____15376,uu____15377)
                             ->
                             ((let uu____15387 =
                                 let uu____15390 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15390  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15387);
                              (let uu____15483 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15483 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15487,uu____15488,uu____15489,uu____15490,uu____15491)
                             ->
                             ((let uu____15499 =
                                 let uu____15502 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15502  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15499);
                              sigelts1)
                         | uu____15595 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15604 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15604
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15614 =
                    let uu___434_15615 = s  in
                    let uu____15616 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___434_15615.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___434_15615.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15616;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___434_15615.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___434_15615.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15614])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15627 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15627
             then []
             else
               (let uu____15634 = lbs  in
                match uu____15634 with
                | (flbs,slbs) ->
                    let typs_and_defs =
                      FStar_All.pipe_right slbs
                        (FStar_List.map
                           (fun lb  ->
                              ((lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp),
                                (lb.FStar_Syntax_Syntax.lbdef))))
                       in
                    let is_lemma1 =
                      FStar_List.existsML
                        (fun uu____15696  ->
                           match uu____15696 with
                           | (uu____15704,t,uu____15706) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15723  ->
                             match uu____15723 with
                             | (u,t,d) -> val_of_lb s lid (u, t) d) lids
                        typs_and_defs
                       in
                    if
                      ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                         (is_irreducible1 s.FStar_Syntax_Syntax.sigquals))
                        || is_lemma1
                    then vals
                    else
                      (let should_keep_defs =
                         FStar_List.existsML
                           (fun uu____15750  ->
                              match uu____15750 with
                              | (uu____15758,t,uu____15760) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15772,uu____15773) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15781 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15832 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15832) uu____15781
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15836 =
                    let uu___435_15837 = s  in
                    let uu____15838 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___435_15837.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___435_15837.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15838;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___435_15837.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___435_15837.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15836]
                else [])
             else
               (let uu____15845 =
                  let uu___436_15846 = s  in
                  let uu____15847 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___436_15846.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___436_15846.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15847;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___436_15846.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___436_15846.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15845])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15850 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15851 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15852 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15853 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15866 -> [s])
         in
      let uu___437_15867 = m  in
      let uu____15868 =
        let uu____15869 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15869 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___437_15867.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15868;
        FStar_Syntax_Syntax.exports =
          (uu___437_15867.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15920  -> FStar_TypeChecker_Env.snapshot env msg)
  
let (rollback_context :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15968  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____15984 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15984
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      rollback_context env.FStar_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
  
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let action = if verify then "Verifying" else "Lax-checking"  in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation"  in
      (let uu____16073 = FStar_Options.debug_any ()  in
       if uu____16073
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
          in
       let env1 =
         let uu___438_16089 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___438_16089.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___438_16089.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___438_16089.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___438_16089.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___438_16089.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___438_16089.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___438_16089.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___438_16089.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___438_16089.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___438_16089.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___438_16089.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___438_16089.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___438_16089.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___438_16089.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___438_16089.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___438_16089.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___438_16089.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___438_16089.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___438_16089.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___438_16089.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___438_16089.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___438_16089.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___438_16089.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___438_16089.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___438_16089.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___438_16089.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___438_16089.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___438_16089.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___438_16089.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___438_16089.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___438_16089.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___438_16089.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___438_16089.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___438_16089.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___438_16089.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___438_16089.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___438_16089.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___438_16089.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___438_16089.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___438_16089.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___438_16089.FStar_TypeChecker_Env.nbe)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____16091 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____16091 with
       | (ses,exports,env3) ->
           ((let uu___439_16124 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___439_16124.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___439_16124.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___439_16124.FStar_Syntax_Syntax.is_interface)
             }), exports, env3))
  
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____16153 = tc_decls env decls  in
        match uu____16153 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___440_16184 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___440_16184.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___440_16184.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___440_16184.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env0  ->
    fun m  ->
      fun iface_exists  ->
        let msg =
          Prims.strcat "Internals for "
            (m.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        let env01 = push_context env0 msg  in
        let uu____16245 = tc_partial_modul env01 m  in
        match uu____16245 with
        | (modul,non_private_decls,env) ->
            finish_partial_modul false iface_exists env modul
              non_private_decls

and (finish_partial_modul :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.modul ->
          FStar_Syntax_Syntax.sigelt Prims.list ->
            (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun loading_from_cache  ->
    fun iface_exists  ->
      fun en  ->
        fun m  ->
          fun exports  ->
            let should_extract_interface =
              ((((Prims.op_Negation loading_from_cache) &&
                   (Prims.op_Negation iface_exists))
                  && (FStar_Options.use_extracted_interfaces ()))
                 && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                &&
                (let uu____16282 = FStar_Errors.get_err_count ()  in
                 uu____16282 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16293 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16293
                then
                  let uu____16297 =
                    let uu____16299 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16299 then "" else " (in lax mode) "  in
                  let uu____16307 =
                    let uu____16309 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16309
                    then
                      let uu____16313 =
                        let uu____16315 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____16315 "\n"  in
                      Prims.strcat "\nfrom: " uu____16313
                    else ""  in
                  let uu____16322 =
                    let uu____16324 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16324
                    then
                      let uu____16328 =
                        let uu____16330 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____16330 "\n"  in
                      Prims.strcat "\nto: " uu____16328
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16297
                    uu____16307 uu____16322
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___441_16344 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___441_16344.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___441_16344.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___441_16344.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___441_16344.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___441_16344.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___441_16344.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___441_16344.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___441_16344.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___441_16344.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___441_16344.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___441_16344.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___441_16344.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___441_16344.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___441_16344.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___441_16344.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___441_16344.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___441_16344.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___441_16344.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___441_16344.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___441_16344.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___441_16344.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___441_16344.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___441_16344.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___441_16344.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___441_16344.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___441_16344.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___441_16344.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___441_16344.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___441_16344.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___441_16344.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___441_16344.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___441_16344.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___441_16344.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___441_16344.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___441_16344.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___441_16344.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___441_16344.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___441_16344.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___441_16344.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___441_16344.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___441_16344.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___441_16344.FStar_TypeChecker_Env.nbe)
                    }  in
                  let en02 =
                    let uu___442_16346 = en01  in
                    let uu____16347 =
                      let uu____16362 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16362, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___442_16346.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___442_16346.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___442_16346.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___442_16346.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___442_16346.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___442_16346.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___442_16346.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___442_16346.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___442_16346.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___442_16346.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___442_16346.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___442_16346.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___442_16346.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___442_16346.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___442_16346.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___442_16346.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___442_16346.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___442_16346.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___442_16346.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___442_16346.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___442_16346.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___442_16346.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___442_16346.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___442_16346.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___442_16346.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___442_16346.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___442_16346.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___442_16346.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___442_16346.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___442_16346.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___442_16346.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16347;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___442_16346.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___442_16346.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___442_16346.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___442_16346.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___442_16346.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___442_16346.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___442_16346.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___442_16346.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___442_16346.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___442_16346.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___442_16346.FStar_TypeChecker_Env.nbe)
                    }  in
                  let uu____16408 =
                    let uu____16410 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16410  in
                  if uu____16408
                  then
                    ((let uu____16414 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16414 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____16418 = tc_modul en0 modul_iface true  in
                match uu____16418 with
                | (modul_iface1,env) ->
                    ((let uu___443_16431 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___443_16431.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___443_16431.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___443_16431.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___444_16435 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___444_16435.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___444_16435.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___444_16435.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16438 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16438 FStar_Util.smap_clear);
               (let uu____16474 =
                  ((let uu____16478 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16478) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16481 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16481)
                   in
                if uu____16474 then check_exports env modul exports else ());
               (let uu____16487 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16487 (fun a4  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____16492 =
                  let uu____16494 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____16494  in
                if uu____16492
                then
                  let uu____16497 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____16497 (fun a5  -> ())
                else ());
               (modul, env))

let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun en  ->
    fun m  ->
      let env =
        FStar_TypeChecker_Env.set_current_module en
          m.FStar_Syntax_Syntax.name
         in
      let env1 =
        let uu____16514 =
          let uu____16516 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____16516  in
        push_context env uu____16514  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16537 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16548 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16548 with | (uu____16555,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16580 = FStar_Options.debug_any ()  in
         if uu____16580
         then
           let uu____16583 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16583
         else ());
        (let uu____16595 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16595
         then
           let uu____16598 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16598
         else ());
        (let env1 =
           let uu___445_16604 = env  in
           let uu____16605 =
             let uu____16607 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16607  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___445_16604.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___445_16604.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___445_16604.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___445_16604.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___445_16604.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___445_16604.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___445_16604.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___445_16604.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___445_16604.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___445_16604.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___445_16604.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___445_16604.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___445_16604.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___445_16604.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___445_16604.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___445_16604.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___445_16604.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___445_16604.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___445_16604.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___445_16604.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16605;
             FStar_TypeChecker_Env.lax_universes =
               (uu___445_16604.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___445_16604.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___445_16604.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___445_16604.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___445_16604.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___445_16604.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___445_16604.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___445_16604.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___445_16604.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___445_16604.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___445_16604.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___445_16604.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___445_16604.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___445_16604.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___445_16604.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___445_16604.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___445_16604.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___445_16604.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___445_16604.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___445_16604.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___445_16604.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___445_16604.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____16609 = tc_modul env1 m b  in
         match uu____16609 with
         | (m1,env2) ->
             ((let uu____16621 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16621
               then
                 let uu____16624 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16624
               else ());
              (let uu____16630 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16630
               then
                 let normalize_toplevel_lets se =
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_let ((b1,lbs),ids) ->
                       let n1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Reify;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.AllowUnboundUniverses]
                          in
                       let update lb =
                         let uu____16668 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16668 with
                         | (univnames1,e) ->
                             let uu___446_16675 = lb  in
                             let uu____16676 =
                               let uu____16679 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16679 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___446_16675.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___446_16675.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___446_16675.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___446_16675.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16676;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___446_16675.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___446_16675.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___447_16680 = se  in
                       let uu____16681 =
                         let uu____16682 =
                           let uu____16689 =
                             let uu____16690 = FStar_List.map update lbs  in
                             (b1, uu____16690)  in
                           (uu____16689, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16682  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16681;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___447_16680.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___447_16680.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___447_16680.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___447_16680.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16698 -> se  in
                 let normalized_module =
                   let uu___448_16700 = m1  in
                   let uu____16701 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___448_16700.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16701;
                     FStar_Syntax_Syntax.exports =
                       (uu___448_16700.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___448_16700.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16702 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16702
               else ());
              (m1, env2)))
  