open Prims
let (debug_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (eager_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____71 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____82 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____93 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____104 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____117 -> false
  
let (__proj__Other__item___0 : debug_level_t -> Prims.string) =
  fun projectee  -> match projectee with | Other _0 -> _0 
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset 
let (uu___is_Bool : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____172 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____196 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____220 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____244 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____269 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____294 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _0_1  -> Bool _0_1 
let (mk_string : Prims.string -> option_val) = fun _0_2  -> String _0_2 
let (mk_path : Prims.string -> option_val) = fun _0_3  -> Path _0_3 
let (mk_int : Prims.int -> option_val) = fun _0_4  -> Int _0_4 
let (mk_list : option_val Prims.list -> option_val) = fun _0_5  -> List _0_5 
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____350  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____377  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____405  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___80_434  ->
    match uu___80_434 with
    | Bool b -> b
    | uu____438 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___81_447  ->
    match uu___81_447 with
    | Int b -> b
    | uu____451 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___82_460  ->
    match uu___82_460 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____466 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___83_476  ->
    match uu___83_476 with
    | List ts -> ts
    | uu____482 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____493 .
    (option_val -> 'Auu____493) -> option_val -> 'Auu____493 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____511 = as_list' x  in
      FStar_All.pipe_right uu____511 (FStar_List.map as_t)
  
let as_option :
  'Auu____525 .
    (option_val -> 'Auu____525) ->
      option_val -> 'Auu____525 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___84_540  ->
      match uu___84_540 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____544 = as_t v1  in FStar_Pervasives_Native.Some uu____544
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___85_553  ->
    match uu___85_553 with
    | List ls ->
        let uu____560 =
          FStar_List.map
            (fun l  ->
               let uu____572 = as_string l  in FStar_Util.split uu____572 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____560
    | uu____584 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____620  ->
    let uu____621 =
      let uu____624 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____624  in
    FStar_List.hd uu____621
  
let (pop : unit -> unit) =
  fun uu____663  ->
    let uu____664 = FStar_ST.op_Bang fstar_options  in
    match uu____664 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____699::[] -> failwith "TOO MANY POPS!"
    | uu____707::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____749  ->
    let uu____750 =
      let uu____755 =
        let uu____758 =
          let uu____761 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____761  in
        FStar_List.map FStar_Util.smap_copy uu____758  in
      let uu____795 = FStar_ST.op_Bang fstar_options  in uu____755 ::
        uu____795
       in
    FStar_ST.op_Colon_Equals fstar_options uu____750
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____862  ->
    let curstack =
      let uu____866 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____866  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____903::[] -> false
    | uu____905::tl1 ->
        ((let uu____910 =
            let uu____915 =
              let uu____920 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____920  in
            tl1 :: uu____915  in
          FStar_ST.op_Colon_Equals fstar_options uu____910);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____989  ->
    let curstack =
      let uu____993 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____993  in
    let stack' =
      let uu____1030 =
        let uu____1031 = FStar_List.hd curstack  in
        FStar_Util.smap_copy uu____1031  in
      uu____1030 :: curstack  in
    let uu____1034 =
      let uu____1039 =
        let uu____1044 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____1044  in
      stack' :: uu____1039  in
    FStar_ST.op_Colon_Equals fstar_options uu____1034
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____1113 = FStar_ST.op_Bang fstar_options  in
    match uu____1113 with
    | [] -> failwith "set on empty option stack"
    | []::uu____1148 -> failwith "set on empty current option stack"
    | (uu____1156::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____1206  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1236 = peek ()  in FStar_Util.smap_add uu____1236 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____1249  -> match uu____1249 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____1288 =
      let uu____1292 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____1292
       in
    FStar_ST.op_Colon_Equals light_off_files uu____1288
  
let (defaults : (Prims.string * option_val) Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("abort_on", (Int (Prims.parse_int "0")));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("already_cached", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
  ("cache_off", (Bool false));
  ("cmi", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("defensive", (String "no"));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("doc", (Bool false));
  ("dump_module", (List []));
  ("eager_inference", (Bool false));
  ("eager_subtyping", (Bool false));
  ("expose_interfaces", (Bool false));
  ("extract", Unset);
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
  ("full_context_dependency", (Bool true));
  ("hide_uvar_nums", (Bool false));
  ("hint_info", (Bool false));
  ("hint_file", Unset);
  ("in", (Bool false));
  ("ide", (Bool false));
  ("include", (List []));
  ("print", (Bool false));
  ("print_in_place", (Bool false));
  ("profile", (Bool false));
  ("initial_fuel", (Int (Prims.parse_int "2")));
  ("initial_ifuel", (Int (Prims.parse_int "1")));
  ("keep_query_captions", (Bool true));
  ("lax", (Bool false));
  ("load", (List []));
  ("log_queries", (Bool false));
  ("log_types", (Bool false));
  ("max_fuel", (Int (Prims.parse_int "8")));
  ("max_ifuel", (Int (Prims.parse_int "2")));
  ("min_fuel", (Int (Prims.parse_int "1")));
  ("MLish", (Bool false));
  ("n_cores", (Int (Prims.parse_int "1")));
  ("no_default_includes", (Bool false));
  ("no_extract", (List []));
  ("no_location_info", (Bool false));
  ("no_smt", (Bool false));
  ("no_plugins", (Bool false));
  ("no_tactics", (Bool false));
  ("normalize_pure_terms_for_extraction", (Bool false));
  ("odir", Unset);
  ("prims", Unset);
  ("pretype", (Bool true));
  ("prims_ref", Unset);
  ("print_bound_var_types", (Bool false));
  ("print_effect_args", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("query_stats", (Bool false));
  ("record_hints", (Bool false));
  ("reuse_hint_for", Unset);
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("tactics_failhard", (Bool false));
  ("tactics_info", (Bool false));
  ("tactic_raw_binders", (Bool false));
  ("tactic_trace", (Bool false));
  ("tactic_trace_d", (Int (Prims.parse_int "0")));
  ("tcnorm", (Bool true));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("ugly", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("unsafe_tactic_exec", (Bool false));
  ("use_native_tactics", Unset);
  ("use_eq_at_higher_order", (Bool false));
  ("use_hints", (Bool false));
  ("use_hint_hashes", (Bool false));
  ("using_facts_from", Unset);
  ("vcgen.optimize_bind_as_seq", Unset);
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.parse_int "5")));
  ("z3rlimit_factor", (Int (Prims.parse_int "1")));
  ("z3seed", (Int (Prims.parse_int "0")));
  ("z3cliopt", (List []));
  ("use_two_phase_tc", (Bool true));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false));
  ("__tactics_nbe", (Bool false));
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false));
  ("use_nbe", (Bool false))] 
let (init : unit -> unit) =
  fun uu____2194  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2214  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2287 =
      let uu____2290 = peek ()  in FStar_Util.smap_try_find uu____2290 s  in
    match uu____2287 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2303 . Prims.string -> (option_val -> 'Auu____2303) -> 'Auu____2303
  = fun s  -> fun c  -> let uu____2321 = get_option s  in c uu____2321 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2328  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2337  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2348  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2364  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2381  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2392  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2404  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2413  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2424  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2438  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2452  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2466  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____2477  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2488  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____2500  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____2509  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____2518  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____2529  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____2541  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____2550  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2563  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____2582  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____2596  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____2608  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____2617  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____2626  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2637  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____2649  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____2658  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____2669  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____2681  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____2690  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____2699  -> lookup_opt "profile" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____2708  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____2717  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____2726  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____2735  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____2746  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____2758  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____2767  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____2776  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____2785  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____2794  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____2803  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____2812  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____2821  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____2832  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____2844  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____2853  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____2862  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____2871  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2882  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____2894  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2905  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2917  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2926  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2935  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2944  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2953  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2962  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____2971  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2980  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____2989  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3000  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____3012  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3023  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____3035  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____3044  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3053  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3062  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3071  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3080  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3089  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3098  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3107  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3116  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3125  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3134  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3143  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3152  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3161  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3170  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3179  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3190  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3202  ->
    let uu____3203 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3203
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3217  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3236  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3250  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3264  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3276  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3285  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3296  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3308  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3317  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3326  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3335  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3344  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3353  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3362  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____3371  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3380  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3389  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___86_3398  ->
    match uu___86_3398 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3419 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3428 = get_debug_level ()  in
    FStar_All.pipe_right uu____3428
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____3594  ->
    let uu____3595 =
      let uu____3597 = FStar_ST.op_Bang _version  in
      let uu____3620 = FStar_ST.op_Bang _platform  in
      let uu____3643 = FStar_ST.op_Bang _compiler  in
      let uu____3666 = FStar_ST.op_Bang _date  in
      let uu____3689 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3597
        uu____3620 uu____3643 uu____3666 uu____3689
       in
    FStar_Util.print_string uu____3595
  
let display_usage_aux :
  'Auu____3720 'Auu____3721 .
    ('Auu____3720 * Prims.string * 'Auu____3721 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____3776  ->
         match uu____3776 with
         | (uu____3789,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____3808 =
                      let uu____3810 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____3810  in
                    FStar_Util.print_string uu____3808
                  else
                    (let uu____3815 =
                       let uu____3817 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____3817 doc  in
                     FStar_Util.print_string uu____3815)
              | FStar_Getopt.OneArg (uu____3820,argname) ->
                  if doc = ""
                  then
                    let uu____3835 =
                      let uu____3837 = FStar_Util.colorize_bold flag  in
                      let uu____3839 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____3837 uu____3839
                       in
                    FStar_Util.print_string uu____3835
                  else
                    (let uu____3844 =
                       let uu____3846 = FStar_Util.colorize_bold flag  in
                       let uu____3848 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____3846
                         uu____3848 doc
                        in
                     FStar_Util.print_string uu____3844))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____3883 = o  in
    match uu____3883 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____3925 =
                let uu____3926 = f ()  in set_option name uu____3926  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____3947 = f x  in set_option name uu____3947
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____3974 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____3974  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____4003 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____4003  in
      mk_list (FStar_List.append prev_values [value])
  
let accumulate_string :
  'Auu____4025 .
    Prims.string -> ('Auu____4025 -> Prims.string) -> 'Auu____4025 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____4050 =
          let uu____4051 =
            let uu____4052 = post_processor value  in mk_string uu____4052
             in
          accumulated_option name uu____4051  in
        set_option name uu____4050
  
let (add_extract_module : Prims.string -> unit) =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s 
let (add_extract_namespace : Prims.string -> unit) =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s 
let (add_verify_module : Prims.string -> unit) =
  fun s  -> accumulate_string "verify_module" FStar_String.lowercase s 
type opt_type =
  | Const of option_val 
  | IntStr of Prims.string 
  | BoolStr 
  | PathStr of Prims.string 
  | SimpleStr of Prims.string 
  | EnumStr of Prims.string Prims.list 
  | OpenEnumStr of (Prims.string Prims.list * Prims.string) 
  | PostProcessed of ((option_val -> option_val) * opt_type) 
  | Accumulated of opt_type 
  | ReverseAccumulated of opt_type 
  | WithSideEffect of ((unit -> unit) * opt_type) 
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____4174 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4195 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4217 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4230 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4254 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4280 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4317 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4368 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4409 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4429 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4456 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____4500 -> true
    | uu____4503 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____4514 -> uu____4514
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___91_4538  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____4540 ->
                      let uu____4542 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____4542 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____4550 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____4550
                  | PathStr uu____4567 -> mk_path str_val
                  | SimpleStr uu____4569 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____4579 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____4596 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____4596
                  | Accumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val  in
                      accumulated_option opt_name v1
                  | ReverseAccumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val  in
                      reverse_accumulated_option opt_name v1
                  | WithSideEffect (side_effect,elem_spec) ->
                      (side_effect ();
                       parse_opt_val opt_name elem_spec str_val))) ()
        with
        | InvalidArgument opt_name1 ->
            let uu____4616 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____4616
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      FStar_Pervasives_Native.Some
        (Prims.strcat "[" (Prims.strcat (FStar_String.concat "|" cases) "]"))
       in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____4686,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____4696,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____4727 = desc_of_opt_type typ  in
      match uu____4727 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____4735  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____4761 =
      let uu____4763 = as_string s  in FStar_String.lowercase uu____4763  in
    mk_string uu____4761
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____4820  ->
    let uu____4834 =
      let uu____4848 =
        let uu____4862 =
          let uu____4876 =
            let uu____4890 =
              let uu____4902 =
                let uu____4903 = mk_bool true  in Const uu____4903  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____4902,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____4910 =
              let uu____4924 =
                let uu____4938 =
                  let uu____4950 =
                    let uu____4951 = mk_bool true  in Const uu____4951  in
                  (FStar_Getopt.noshort, "cache_off", uu____4950,
                    "Do not read or write any .checked files")
                   in
                let uu____4958 =
                  let uu____4972 =
                    let uu____4984 =
                      let uu____4985 = mk_bool true  in Const uu____4985  in
                    (FStar_Getopt.noshort, "cmi", uu____4984,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____4992 =
                    let uu____5006 =
                      let uu____5020 =
                        let uu____5034 =
                          let uu____5048 =
                            let uu____5062 =
                              let uu____5076 =
                                let uu____5090 =
                                  let uu____5102 =
                                    let uu____5103 = mk_bool true  in
                                    Const uu____5103  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____5102,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____5110 =
                                  let uu____5124 =
                                    let uu____5136 =
                                      let uu____5137 = mk_bool true  in
                                      Const uu____5137  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____5136,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____5144 =
                                    let uu____5158 =
                                      let uu____5170 =
                                        let uu____5171 = mk_bool true  in
                                        Const uu____5171  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____5170,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____5178 =
                                      let uu____5192 =
                                        let uu____5206 =
                                          let uu____5218 =
                                            let uu____5219 = mk_bool true  in
                                            Const uu____5219  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____5218,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____5226 =
                                          let uu____5240 =
                                            let uu____5252 =
                                              let uu____5253 = mk_bool true
                                                 in
                                              Const uu____5253  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____5252,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____5260 =
                                            let uu____5274 =
                                              let uu____5288 =
                                                let uu____5302 =
                                                  let uu____5316 =
                                                    let uu____5328 =
                                                      let uu____5329 =
                                                        mk_bool true  in
                                                      Const uu____5329  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____5328,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____5336 =
                                                    let uu____5350 =
                                                      let uu____5362 =
                                                        let uu____5363 =
                                                          mk_bool true  in
                                                        Const uu____5363  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____5362,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____5370 =
                                                      let uu____5384 =
                                                        let uu____5398 =
                                                          let uu____5410 =
                                                            let uu____5411 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5411
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____5410,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____5418 =
                                                          let uu____5432 =
                                                            let uu____5444 =
                                                              let uu____5445
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5445
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____5444,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____5452 =
                                                            let uu____5466 =
                                                              let uu____5478
                                                                =
                                                                let uu____5479
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____5479
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____5478,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____5486 =
                                                              let uu____5500
                                                                =
                                                                let uu____5514
                                                                  =
                                                                  let uu____5526
                                                                    =
                                                                    let uu____5527
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5527
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____5526,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____5534
                                                                  =
                                                                  let uu____5548
                                                                    =
                                                                    let uu____5560
                                                                    =
                                                                    let uu____5561
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5561
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____5560,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____5568
                                                                    =
                                                                    let uu____5582
                                                                    =
                                                                    let uu____5594
                                                                    =
                                                                    let uu____5595
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5595
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____5594,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____5602
                                                                    =
                                                                    let uu____5616
                                                                    =
                                                                    let uu____5630
                                                                    =
                                                                    let uu____5644
                                                                    =
                                                                    let uu____5658
                                                                    =
                                                                    let uu____5670
                                                                    =
                                                                    let uu____5671
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____5670,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____5678
                                                                    =
                                                                    let uu____5692
                                                                    =
                                                                    let uu____5706
                                                                    =
                                                                    let uu____5718
                                                                    =
                                                                    let uu____5719
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5719
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____5718,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____5726
                                                                    =
                                                                    let uu____5740
                                                                    =
                                                                    let uu____5752
                                                                    =
                                                                    let uu____5753
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5753
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____5752,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____5760
                                                                    =
                                                                    let uu____5774
                                                                    =
                                                                    let uu____5788
                                                                    =
                                                                    let uu____5802
                                                                    =
                                                                    let uu____5816
                                                                    =
                                                                    let uu____5828
                                                                    =
                                                                    let uu____5829
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5829
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____5828,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____5836
                                                                    =
                                                                    let uu____5850
                                                                    =
                                                                    let uu____5864
                                                                    =
                                                                    let uu____5876
                                                                    =
                                                                    let uu____5877
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5877
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____5876,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____5884
                                                                    =
                                                                    let uu____5898
                                                                    =
                                                                    let uu____5912
                                                                    =
                                                                    let uu____5924
                                                                    =
                                                                    let uu____5925
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5925
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____5924,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____5932
                                                                    =
                                                                    let uu____5946
                                                                    =
                                                                    let uu____5958
                                                                    =
                                                                    let uu____5959
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5959
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____5958,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____5966
                                                                    =
                                                                    let uu____5980
                                                                    =
                                                                    let uu____5992
                                                                    =
                                                                    let uu____5993
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5993
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____5992,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____6000
                                                                    =
                                                                    let uu____6014
                                                                    =
                                                                    let uu____6028
                                                                    =
                                                                    let uu____6042
                                                                    =
                                                                    let uu____6054
                                                                    =
                                                                    let uu____6055
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6055
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____6054,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____6062
                                                                    =
                                                                    let uu____6076
                                                                    =
                                                                    let uu____6088
                                                                    =
                                                                    let uu____6089
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6089
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____6088,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____6096
                                                                    =
                                                                    let uu____6110
                                                                    =
                                                                    let uu____6122
                                                                    =
                                                                    let uu____6123
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6123
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____6122,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____6130
                                                                    =
                                                                    let uu____6144
                                                                    =
                                                                    let uu____6156
                                                                    =
                                                                    let uu____6157
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6157
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6156,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6164
                                                                    =
                                                                    let uu____6178
                                                                    =
                                                                    let uu____6190
                                                                    =
                                                                    let uu____6191
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6191
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6190,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6198
                                                                    =
                                                                    let uu____6212
                                                                    =
                                                                    let uu____6224
                                                                    =
                                                                    let uu____6225
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6225
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6224,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____6232
                                                                    =
                                                                    let uu____6246
                                                                    =
                                                                    let uu____6258
                                                                    =
                                                                    let uu____6259
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6259
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6258,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____6266
                                                                    =
                                                                    let uu____6280
                                                                    =
                                                                    let uu____6292
                                                                    =
                                                                    let uu____6293
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6293
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____6292,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____6300
                                                                    =
                                                                    let uu____6314
                                                                    =
                                                                    let uu____6326
                                                                    =
                                                                    let uu____6327
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6327
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____6326,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____6334
                                                                    =
                                                                    let uu____6348
                                                                    =
                                                                    let uu____6362
                                                                    =
                                                                    let uu____6374
                                                                    =
                                                                    let uu____6375
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6375
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____6374,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____6382
                                                                    =
                                                                    let uu____6396
                                                                    =
                                                                    let uu____6410
                                                                    =
                                                                    let uu____6424
                                                                    =
                                                                    let uu____6438
                                                                    =
                                                                    let uu____6452
                                                                    =
                                                                    let uu____6464
                                                                    =
                                                                    let uu____6465
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6465
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____6464,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____6472
                                                                    =
                                                                    let uu____6486
                                                                    =
                                                                    let uu____6498
                                                                    =
                                                                    let uu____6499
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6499
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____6498,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____6506
                                                                    =
                                                                    let uu____6520
                                                                    =
                                                                    let uu____6532
                                                                    =
                                                                    let uu____6533
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6533
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____6532,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____6540
                                                                    =
                                                                    let uu____6554
                                                                    =
                                                                    let uu____6566
                                                                    =
                                                                    let uu____6567
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6567
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____6566,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____6574
                                                                    =
                                                                    let uu____6588
                                                                    =
                                                                    let uu____6602
                                                                    =
                                                                    let uu____6614
                                                                    =
                                                                    let uu____6615
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6615
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____6614,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____6622
                                                                    =
                                                                    let uu____6636
                                                                    =
                                                                    let uu____6650
                                                                    =
                                                                    let uu____6662
                                                                    =
                                                                    let uu____6663
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6663
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____6662,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____6670
                                                                    =
                                                                    let uu____6684
                                                                    =
                                                                    let uu____6696
                                                                    =
                                                                    let uu____6697
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6697
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____6696,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____6704
                                                                    =
                                                                    let uu____6718
                                                                    =
                                                                    let uu____6730
                                                                    =
                                                                    let uu____6731
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6731
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____6730,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____6738
                                                                    =
                                                                    let uu____6752
                                                                    =
                                                                    let uu____6764
                                                                    =
                                                                    let uu____6765
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6765
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____6764,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____6772
                                                                    =
                                                                    let uu____6786
                                                                    =
                                                                    let uu____6798
                                                                    =
                                                                    let uu____6799
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6799
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____6798,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____6806
                                                                    =
                                                                    let uu____6820
                                                                    =
                                                                    let uu____6832
                                                                    =
                                                                    let uu____6833
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6833
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____6832,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____6840
                                                                    =
                                                                    let uu____6854
                                                                    =
                                                                    let uu____6866
                                                                    =
                                                                    let uu____6867
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6867
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____6866,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____6874
                                                                    =
                                                                    let uu____6888
                                                                    =
                                                                    let uu____6900
                                                                    =
                                                                    let uu____6901
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6901
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____6900,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____6908
                                                                    =
                                                                    let uu____6922
                                                                    =
                                                                    let uu____6936
                                                                    =
                                                                    let uu____6948
                                                                    =
                                                                    let uu____6949
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6949
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____6948,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____6956
                                                                    =
                                                                    let uu____6970
                                                                    =
                                                                    let uu____6982
                                                                    =
                                                                    let uu____6983
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6983
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____6982,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____6990
                                                                    =
                                                                    let uu____7004
                                                                    =
                                                                    let uu____7018
                                                                    =
                                                                    let uu____7032
                                                                    =
                                                                    let uu____7046
                                                                    =
                                                                    let uu____7058
                                                                    =
                                                                    let uu____7059
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7059
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____7058,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____7066
                                                                    =
                                                                    let uu____7080
                                                                    =
                                                                    let uu____7092
                                                                    =
                                                                    let uu____7093
                                                                    =
                                                                    let uu____7101
                                                                    =
                                                                    let uu____7102
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7102
                                                                     in
                                                                    ((fun
                                                                    uu____7109
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7101)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7093
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____7092,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____7118
                                                                    =
                                                                    let uu____7132
                                                                    =
                                                                    let uu____7144
                                                                    =
                                                                    let uu____7145
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7145
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____7144,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7152
                                                                    =
                                                                    let uu____7166
                                                                    =
                                                                    let uu____7180
                                                                    =
                                                                    let uu____7192
                                                                    =
                                                                    let uu____7193
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7193
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____7192,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____7200
                                                                    =
                                                                    let uu____7214
                                                                    =
                                                                    let uu____7228
                                                                    =
                                                                    let uu____7242
                                                                    =
                                                                    let uu____7256
                                                                    =
                                                                    let uu____7270
                                                                    =
                                                                    let uu____7282
                                                                    =
                                                                    let uu____7283
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7283
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7282,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7290
                                                                    =
                                                                    let uu____7304
                                                                    =
                                                                    let uu____7316
                                                                    =
                                                                    let uu____7317
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7317
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7316,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7324
                                                                    =
                                                                    let uu____7338
                                                                    =
                                                                    let uu____7352
                                                                    =
                                                                    let uu____7366
                                                                    =
                                                                    let uu____7380
                                                                    =
                                                                    let uu____7392
                                                                    =
                                                                    let uu____7393
                                                                    =
                                                                    let uu____7401
                                                                    =
                                                                    let uu____7402
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7402
                                                                     in
                                                                    ((fun
                                                                    uu____7408
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7401)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7393
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7392,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7436
                                                                    =
                                                                    let uu____7450
                                                                    =
                                                                    let uu____7462
                                                                    =
                                                                    let uu____7463
                                                                    =
                                                                    let uu____7471
                                                                    =
                                                                    let uu____7472
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7472
                                                                     in
                                                                    ((fun
                                                                    uu____7478
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____7471)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7463
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____7462,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____7506
                                                                    =
                                                                    let uu____7520
                                                                    =
                                                                    let uu____7532
                                                                    =
                                                                    let uu____7533
                                                                    =
                                                                    let uu____7541
                                                                    =
                                                                    let uu____7542
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7542
                                                                     in
                                                                    ((fun
                                                                    uu____7549
                                                                     ->
                                                                    (
                                                                    let uu____7551
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____7551);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7541)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7533
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____7532,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____7520]
                                                                     in
                                                                    uu____7450
                                                                    ::
                                                                    uu____7506
                                                                     in
                                                                    uu____7380
                                                                    ::
                                                                    uu____7436
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7366
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7352
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7338
                                                                     in
                                                                    uu____7304
                                                                    ::
                                                                    uu____7324
                                                                     in
                                                                    uu____7270
                                                                    ::
                                                                    uu____7290
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7256
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7242
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7228
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7214
                                                                     in
                                                                    uu____7180
                                                                    ::
                                                                    uu____7200
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7166
                                                                     in
                                                                    uu____7132
                                                                    ::
                                                                    uu____7152
                                                                     in
                                                                    uu____7080
                                                                    ::
                                                                    uu____7118
                                                                     in
                                                                    uu____7046
                                                                    ::
                                                                    uu____7066
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____7032
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____7018
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____7004
                                                                     in
                                                                    uu____6970
                                                                    ::
                                                                    uu____6990
                                                                     in
                                                                    uu____6936
                                                                    ::
                                                                    uu____6956
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____6922
                                                                     in
                                                                    uu____6888
                                                                    ::
                                                                    uu____6908
                                                                     in
                                                                    uu____6854
                                                                    ::
                                                                    uu____6874
                                                                     in
                                                                    uu____6820
                                                                    ::
                                                                    uu____6840
                                                                     in
                                                                    uu____6786
                                                                    ::
                                                                    uu____6806
                                                                     in
                                                                    uu____6752
                                                                    ::
                                                                    uu____6772
                                                                     in
                                                                    uu____6718
                                                                    ::
                                                                    uu____6738
                                                                     in
                                                                    uu____6684
                                                                    ::
                                                                    uu____6704
                                                                     in
                                                                    uu____6650
                                                                    ::
                                                                    uu____6670
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____6636
                                                                     in
                                                                    uu____6602
                                                                    ::
                                                                    uu____6622
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____6588
                                                                     in
                                                                    uu____6554
                                                                    ::
                                                                    uu____6574
                                                                     in
                                                                    uu____6520
                                                                    ::
                                                                    uu____6540
                                                                     in
                                                                    uu____6486
                                                                    ::
                                                                    uu____6506
                                                                     in
                                                                    uu____6452
                                                                    ::
                                                                    uu____6472
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6438
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6424
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6410
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6396
                                                                     in
                                                                    uu____6362
                                                                    ::
                                                                    uu____6382
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6348
                                                                     in
                                                                    uu____6314
                                                                    ::
                                                                    uu____6334
                                                                     in
                                                                    uu____6280
                                                                    ::
                                                                    uu____6300
                                                                     in
                                                                    uu____6246
                                                                    ::
                                                                    uu____6266
                                                                     in
                                                                    uu____6212
                                                                    ::
                                                                    uu____6232
                                                                     in
                                                                    uu____6178
                                                                    ::
                                                                    uu____6198
                                                                     in
                                                                    uu____6144
                                                                    ::
                                                                    uu____6164
                                                                     in
                                                                    uu____6110
                                                                    ::
                                                                    uu____6130
                                                                     in
                                                                    uu____6076
                                                                    ::
                                                                    uu____6096
                                                                     in
                                                                    uu____6042
                                                                    ::
                                                                    uu____6062
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____6028
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____6014
                                                                     in
                                                                    uu____5980
                                                                    ::
                                                                    uu____6000
                                                                     in
                                                                    uu____5946
                                                                    ::
                                                                    uu____5966
                                                                     in
                                                                    uu____5912
                                                                    ::
                                                                    uu____5932
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____5898
                                                                     in
                                                                    uu____5864
                                                                    ::
                                                                    uu____5884
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____5850
                                                                     in
                                                                    uu____5816
                                                                    ::
                                                                    uu____5836
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____5802
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____5788
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____5774
                                                                     in
                                                                    uu____5740
                                                                    ::
                                                                    uu____5760
                                                                     in
                                                                    uu____5706
                                                                    ::
                                                                    uu____5726
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____5692
                                                                     in
                                                                    uu____5658
                                                                    ::
                                                                    uu____5678
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____5644
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____5630
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____5616
                                                                     in
                                                                    uu____5582
                                                                    ::
                                                                    uu____5602
                                                                     in
                                                                  uu____5548
                                                                    ::
                                                                    uu____5568
                                                                   in
                                                                uu____5514 ::
                                                                  uu____5534
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                :: uu____5500
                                                               in
                                                            uu____5466 ::
                                                              uu____5486
                                                             in
                                                          uu____5432 ::
                                                            uu____5452
                                                           in
                                                        uu____5398 ::
                                                          uu____5418
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____5384
                                                       in
                                                    uu____5350 :: uu____5370
                                                     in
                                                  uu____5316 :: uu____5336
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____5302
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____5288
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____5274
                                             in
                                          uu____5240 :: uu____5260  in
                                        uu____5206 :: uu____5226  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____5192
                                       in
                                    uu____5158 :: uu____5178  in
                                  uu____5124 :: uu____5144  in
                                uu____5090 :: uu____5110  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____5076
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____5062
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____5048
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____5034
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____5020
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____5006
                     in
                  uu____4972 :: uu____4992  in
                uu____4938 :: uu____4958  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____4924
               in
            uu____4890 :: uu____4910  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____4876
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____4862
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____4848
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___87_9083  ->
             match uu___87_9083 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____4834

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____9112  ->
    let uu____9115 = specs_with_types ()  in
    FStar_List.map
      (fun uu____9146  ->
         match uu____9146 with
         | (short,long,typ,doc) ->
             let uu____9168 =
               let uu____9182 = arg_spec_of_opt_type long typ  in
               (short, long, uu____9182, doc)  in
             mk_spec uu____9168) uu____9115

let (settable : Prims.string -> Prims.bool) =
  fun uu___88_9197  ->
    match uu___88_9197 with
    | "abort_on" -> true
    | "admit_except" -> true
    | "admit_smt_queries" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "defensive" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
    | "eager_subtyping" -> true
    | "hide_uvar_nums" -> true
    | "hint_file" -> true
    | "hint_info" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "lax" -> true
    | "load" -> true
    | "log_queries" -> true
    | "log_types" -> true
    | "max_fuel" -> true
    | "max_ifuel" -> true
    | "min_fuel" -> true
    | "no_plugins" -> true
    | "__no_positivity" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "no_smt" -> true
    | "no_tactics" -> true
    | "print_bound_var_types" -> true
    | "print_effect_args" -> true
    | "print_full_names" -> true
    | "print_implicits" -> true
    | "print_universes" -> true
    | "print_z3_statistics" -> true
    | "prn" -> true
    | "query_stats" -> true
    | "reuse_hint_for" -> true
    | "silent" -> true
    | "smtencoding.elim_box" -> true
    | "smtencoding.l_arith_repr" -> true
    | "smtencoding.nl_arith_repr" -> true
    | "tactic_raw_binders" -> true
    | "tactics_failhard" -> true
    | "tactics_info" -> true
    | "__tactics_nbe" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "tcnorm" -> true
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "ugly" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "use_two_phase_tc" -> true
    | "using_facts_from" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | "warn_error" -> true
    | "z3cliopt" -> true
    | "z3refresh" -> true
    | "z3rlimit" -> true
    | "z3rlimit_factor" -> true
    | "z3seed" -> true
    | uu____9326 -> false
  
let (all_specs : FStar_Getopt.opt Prims.list) = specs () 
let (all_specs_with_types :
  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list)
  = specs_with_types () 
let (settable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9410  ->
          match uu____9410 with
          | (uu____9425,x,uu____9427,uu____9428) -> settable x))
  
let (display_usage : unit -> unit) =
  fun uu____9444  ->
    let uu____9445 = specs ()  in display_usage_aux uu____9445
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____9477 -> true
    | uu____9480 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____9491 -> uu____9491
  
let (set_options : Prims.string -> FStar_Getopt.parse_cmdline_res) =
  fun s  ->
    try
      (fun uu___93_9502  ->
         match () with
         | () ->
             if s = ""
             then FStar_Getopt.Success
             else
               FStar_Getopt.parse_string settable_specs
                 (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
    with
    | File_argument s1 ->
        let uu____9519 =
          FStar_Util.format1 "File %s is not a valid option" s1  in
        FStar_Getopt.Error uu____9519
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____9555  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____9561 =
             let uu____9565 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____9565 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____9561)
       in
    let uu____9622 =
      let uu____9626 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____9626
       in
    (res, uu____9622)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____9668  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____9711 = specs ()  in
       FStar_Getopt.parse_cmdline uu____9711 (fun x  -> ())  in
     (let uu____9718 =
        let uu____9724 =
          let uu____9725 = FStar_List.map mk_string old_verify_module  in
          List uu____9725  in
        ("verify_module", uu____9724)  in
      set_option' uu____9718);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____9744 =
        let uu____9746 =
          let uu____9748 =
            let uu____9750 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____9750  in
          (FStar_String.length f1) - uu____9748  in
        uu____9746 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____9744  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9763 = get_lax ()  in
    if uu____9763
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____9784 = module_name_of_file_name fn  in should_verify uu____9784
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9795 = get___temp_no_proj ()  in
    FStar_List.contains m uu____9795
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9809 = should_verify m  in
    if uu____9809 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____9826  ->
    let cache_dir =
      let uu____9831 = get_cache_dir ()  in
      match uu____9831 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____9845 = get_no_default_includes ()  in
    if uu____9845
    then
      let uu____9851 = get_include ()  in
      FStar_List.append cache_dir uu____9851
    else
      (let lib_paths =
         let uu____9862 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____9862 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____9878 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____9878
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____9905 =
         let uu____9909 =
           let uu____9913 = get_include ()  in
           FStar_List.append uu____9913 ["."]  in
         FStar_List.append lib_paths uu____9909  in
       FStar_List.append cache_dir uu____9905)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____9940 = FStar_Util.smap_try_find file_map filename  in
    match uu____9940 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___95_9962  ->
               match () with
               | () ->
                   let uu____9966 = FStar_Util.is_path_absolute filename  in
                   if uu____9966
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____9982 =
                        let uu____9986 = include_path ()  in
                        FStar_List.rev uu____9986  in
                      FStar_Util.find_map uu____9982
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___94_10014 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____10034  ->
    let uu____10035 = get_prims ()  in
    match uu____10035 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____10044 = find_file filename  in
        (match uu____10044 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____10053 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____10053)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____10066  ->
    let uu____10067 = prims ()  in FStar_Util.basename uu____10067
  
let (pervasives : unit -> Prims.string) =
  fun uu____10075  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____10079 = find_file filename  in
    match uu____10079 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____10088 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10088
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____10098  ->
    let uu____10099 = pervasives ()  in FStar_Util.basename uu____10099
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____10107  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____10111 = find_file filename  in
    match uu____10111 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____10120 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10120
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10133 = get_odir ()  in
    match uu____10133 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10151 = get_cache_dir ()  in
    match uu____10151 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10160 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10160
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____10282 = FStar_Util.smap_try_find cache s  in
      match uu____10282 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let res = f s  in (FStar_Util.smap_add cache s res; res)
       in
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if s = "-*"
        then ([], false)
        else
          if FStar_Util.starts_with s "-"
          then
            (let path =
               let uu____10436 =
                 FStar_Util.substring_from s (Prims.parse_int "1")  in
               path_of_text uu____10436  in
             (path, false))
          else
            (let s1 =
               if FStar_Util.starts_with s "+"
               then FStar_Util.substring_from s (Prims.parse_int "1")
               else s  in
             ((path_of_text s1), true))
       in
    let uu____10459 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____10527 =
                       FStar_All.pipe_right (FStar_Util.split s2 " ")
                         (FStar_List.filter (fun s3  -> s3 <> ""))
                        in
                     FStar_All.pipe_right uu____10527
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____10459 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10603 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10603 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____10618  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____10627  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10636  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____10643  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____10650  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____10657  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____10667 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____10678 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____10689 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____10700 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____10709  ->
    let uu____10710 = get_codegen ()  in
    FStar_Util.map_opt uu____10710
      (fun uu___89_10716  ->
         match uu___89_10716 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____10722 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____10735  ->
    let uu____10736 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____10736
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____10762  -> let uu____10763 = get_debug ()  in uu____10763 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____10780 = get_debug ()  in
    FStar_All.pipe_right uu____10780 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____10805 = get_debug ()  in
       FStar_All.pipe_right uu____10805 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____10820  ->
    let uu____10821 = get_defensive ()  in uu____10821 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____10831  ->
    let uu____10832 = get_defensive ()  in uu____10832 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10844  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____10851  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____10858  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____10865  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10875 = get_dump_module ()  in
    FStar_All.pipe_right uu____10875 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____10890  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____10897  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____10907 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____10907
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____10943  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____10951  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____10958  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10967  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____10974  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____10981  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____10988  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____11019 = get_profile ()  in
      if uu____11019
      then
        let uu____11022 = FStar_Util.record_time f  in
        match uu____11022 with
        | (a,time) ->
            ((let uu____11033 = FStar_Util.string_of_int time  in
              let uu____11035 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____11033
                uu____11035);
             a)
      else f ()
  
let (initial_fuel : unit -> Prims.int) =
  fun uu____11046  ->
    let uu____11047 = get_initial_fuel ()  in
    let uu____11049 = get_max_fuel ()  in Prims.min uu____11047 uu____11049
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____11057  ->
    let uu____11058 = get_initial_ifuel ()  in
    let uu____11060 = get_max_ifuel ()  in Prims.min uu____11058 uu____11060
  
let (interactive : unit -> Prims.bool) =
  fun uu____11068  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____11075  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____11084  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____11091  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____11098  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____11105  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____11112  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____11119  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____11126  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____11133  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____11140  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____11146  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____11155  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____11162  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____11174 = get_no_extract ()  in
    FStar_All.pipe_right uu____11174
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____11193  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____11200  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____11207  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____11214  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11223  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____11230  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____11237  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____11244  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____11251  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____11258  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____11265  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____11272  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____11279  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____11286  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11295  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____11302  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____11309  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____11316  ->
    let uu____11317 = get_smtencoding_nl_arith_repr ()  in
    uu____11317 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____11327  ->
    let uu____11328 = get_smtencoding_nl_arith_repr ()  in
    uu____11328 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____11338  ->
    let uu____11339 = get_smtencoding_nl_arith_repr ()  in
    uu____11339 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____11349  ->
    let uu____11350 = get_smtencoding_l_arith_repr ()  in
    uu____11350 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____11360  ->
    let uu____11361 = get_smtencoding_l_arith_repr ()  in
    uu____11361 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____11371  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____11378  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____11385  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____11392  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____11399  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____11406  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____11413  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____11420  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____11427  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____11434  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____11441  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____11448  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____11455  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____11462  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11471  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____11478  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____11494  ->
    let uu____11495 = get_using_facts_from ()  in
    match uu____11495 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____11549  ->
    let uu____11550 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____11550
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____11561  ->
    let uu____11562 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____11562 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____11570 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____11581  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____11588  ->
    let uu____11589 = get_smt ()  in
    match uu____11589 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____11607  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____11614  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____11621  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____11628  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____11635  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____11642  ->
    (get_use_two_phase_tc ()) &&
      (let uu____11644 = lax ()  in Prims.op_Negation uu____11644)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____11652  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____11659  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____11666  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____11673  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____11680  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____11697 =
      let uu____11699 = trace_error ()  in Prims.op_Negation uu____11699  in
    if uu____11697
    then
      (push ();
       (let r =
          try
            (fun uu___97_11714  ->
               match () with
               | () -> let uu____11719 = f ()  in FStar_Util.Inr uu____11719)
              ()
          with | uu___96_11721 -> FStar_Util.Inl uu___96_11721  in
        pop ();
        (match r with
         | FStar_Util.Inr v1 -> v1
         | FStar_Util.Inl ex -> FStar_Exn.raise ex)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (module_matches_namespace_filter :
  Prims.string -> Prims.string Prims.list -> Prims.bool) =
  fun m  ->
    fun filter1  ->
      let m1 = FStar_String.lowercase m  in
      let setting = parse_settings filter1  in
      let m_components = path_of_text m1  in
      let rec matches_path m_components1 path =
        match (m_components1, path) with
        | (uu____11802,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____11835 -> false  in
      let uu____11847 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____11889  ->
                match uu____11889 with
                | (path,uu____11900) -> matches_path m_components path))
         in
      match uu____11847 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____11919,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____11948 = get_extract ()  in
    match uu____11948 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____11963 =
            let uu____11979 = get_no_extract ()  in
            let uu____11983 = get_extract_namespace ()  in
            let uu____11987 = get_extract_module ()  in
            (uu____11979, uu____11983, uu____11987)  in
          match uu____11963 with
          | ([],[],[]) -> ()
          | uu____12012 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____12041 = get_extract_namespace ()  in
          match uu____12041 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____12069 = get_extract_module ()  in
          match uu____12069 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____12091 = no_extract m1  in Prims.op_Negation uu____12091)
          &&
          (let uu____12094 =
             let uu____12105 = get_extract_namespace ()  in
             let uu____12109 = get_extract_module ()  in
             (uu____12105, uu____12109)  in
           (match uu____12094 with
            | ([],[]) -> true
            | uu____12129 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____12149 = get_already_cached ()  in
    match uu____12149 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  