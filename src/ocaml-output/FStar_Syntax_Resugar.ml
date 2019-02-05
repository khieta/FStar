open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____16 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____16
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____24 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____24
  
let map_opt :
  'Auu____34 'Auu____35 .
    unit ->
      ('Auu____34 -> 'Auu____35 FStar_Pervasives_Native.option) ->
        'Auu____34 Prims.list -> 'Auu____35 Prims.list
  = fun uu____51  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____60 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____60
      then
        let uu____64 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____64
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____74 .
    ('Auu____74 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____74 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___199_129  ->
            match uu___199_129 with
            | (uu____137,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____144,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____145)) -> false
            | (uu____150,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____151)) -> false
            | uu____157 -> true))
  
let filter_pattern_imp :
  'Auu____170 .
    ('Auu____170 * Prims.bool) Prims.list ->
      ('Auu____170 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____205  ->
         match uu____205 with
         | (uu____212,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s  ->
    fun t  ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
  
let rec (universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe))
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____262 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____275 = FStar_Options.print_universes ()  in
    if uu____275
    then
      let uu____279 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____279 (FStar_String.concat ", ")
    else ""
  
let rec (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env  -> fun u  -> fun r  -> resugar_universe u r

and (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____343 ->
          let uu____344 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____344 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____355 =
                      let uu____356 =
                        let uu____357 =
                          let uu____369 = FStar_Util.string_of_int n1  in
                          (uu____369, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____357  in
                      FStar_Parser_AST.Const uu____356  in
                    mk1 uu____355 r
                | uu____382 ->
                    let e1 =
                      let uu____384 =
                        let uu____385 =
                          let uu____386 =
                            let uu____398 = FStar_Util.string_of_int n1  in
                            (uu____398, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____386  in
                        FStar_Parser_AST.Const uu____385  in
                      mk1 uu____384 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____412 =
                      let uu____413 =
                        let uu____420 = FStar_Ident.id_of_text "+"  in
                        (uu____420, [e1; e2])  in
                      FStar_Parser_AST.Op uu____413  in
                    mk1 uu____412 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____428 ->
               let t =
                 let uu____432 =
                   let uu____433 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____433  in
                 mk1 uu____432 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____442 =
                        let uu____443 =
                          let uu____450 = resugar_universe x r  in
                          (acc, uu____450, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____443  in
                      mk1 uu____442 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____452 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____464 =
              let uu____470 =
                let uu____472 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____472  in
              (uu____470, r)  in
            FStar_Ident.mk_ident uu____464  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___200_510 =
      match uu___200_510 with
      | "Amp" ->
          FStar_Pervasives_Native.Some ("&", FStar_Pervasives_Native.None)
      | "At" ->
          FStar_Pervasives_Native.Some ("@", FStar_Pervasives_Native.None)
      | "Plus" ->
          FStar_Pervasives_Native.Some ("+", FStar_Pervasives_Native.None)
      | "Minus" ->
          FStar_Pervasives_Native.Some ("-", FStar_Pervasives_Native.None)
      | "Subtraction" ->
          FStar_Pervasives_Native.Some
            ("-", (FStar_Pervasives_Native.Some (Prims.parse_int "2")))
      | "Tilde" ->
          FStar_Pervasives_Native.Some ("~", FStar_Pervasives_Native.None)
      | "Slash" ->
          FStar_Pervasives_Native.Some ("/", FStar_Pervasives_Native.None)
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", FStar_Pervasives_Native.None)
      | "Less" ->
          FStar_Pervasives_Native.Some ("<", FStar_Pervasives_Native.None)
      | "Equals" ->
          FStar_Pervasives_Native.Some ("=", FStar_Pervasives_Native.None)
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", FStar_Pervasives_Native.None)
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", FStar_Pervasives_Native.None)
      | "Bar" ->
          FStar_Pervasives_Native.Some ("|", FStar_Pervasives_Native.None)
      | "Bang" ->
          FStar_Pervasives_Native.Some ("!", FStar_Pervasives_Native.None)
      | "Hat" ->
          FStar_Pervasives_Native.Some ("^", FStar_Pervasives_Native.None)
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", FStar_Pervasives_Native.None)
      | "Star" ->
          FStar_Pervasives_Native.Some ("*", FStar_Pervasives_Native.None)
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", FStar_Pervasives_Native.None)
      | "Colon" ->
          FStar_Pervasives_Native.Some (":", FStar_Pervasives_Native.None)
      | "Dollar" ->
          FStar_Pervasives_Native.Some ("$", FStar_Pervasives_Native.None)
      | "Dot" ->
          FStar_Pervasives_Native.Some (".", FStar_Pervasives_Native.None)
      | uu____838 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".[||]<-", FStar_Pervasives_Native.None)
    | "op_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".(||)<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Access" ->
        FStar_Pervasives_Native.Some (".[||]", FStar_Pervasives_Native.None)
    | "op_Lens_Access" ->
        FStar_Pervasives_Native.Some (".(||)", FStar_Pervasives_Native.None)
    | uu____978 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____996 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____996 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1014 ->
               let op =
                 let uu____1020 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____1074) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____1020
                  in
               FStar_Pervasives_Native.Some
                 (op, FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
  
type expected_arity = Prims.int FStar_Pervasives_Native.option
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string * expected_arity) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Parser_Const.op_Addition, "+");
      (FStar_Parser_Const.op_Subtraction, "-");
      (FStar_Parser_Const.op_Minus, "-");
      (FStar_Parser_Const.op_Multiply, "*");
      (FStar_Parser_Const.op_Division, "/");
      (FStar_Parser_Const.op_Modulus, "%");
      (FStar_Parser_Const.read_lid, "!");
      (FStar_Parser_Const.list_append_lid, "@");
      (FStar_Parser_Const.list_tot_append_lid, "@");
      (FStar_Parser_Const.strcat_lid, "^");
      (FStar_Parser_Const.pipe_right_lid, "|>");
      (FStar_Parser_Const.pipe_left_lid, "<|");
      (FStar_Parser_Const.op_Eq, "=");
      (FStar_Parser_Const.op_ColonEq, ":=");
      (FStar_Parser_Const.op_notEq, "<>");
      (FStar_Parser_Const.not_lid, "~");
      (FStar_Parser_Const.op_And, "&&");
      (FStar_Parser_Const.op_Or, "||");
      (FStar_Parser_Const.op_LTE, "<=");
      (FStar_Parser_Const.op_GTE, ">=");
      (FStar_Parser_Const.op_LT, "<");
      (FStar_Parser_Const.op_GT, ">");
      (FStar_Parser_Const.op_Modulus, "mod");
      (FStar_Parser_Const.and_lid, "/\\");
      (FStar_Parser_Const.or_lid, "\\/");
      (FStar_Parser_Const.imp_lid, "==>");
      (FStar_Parser_Const.iff_lid, "<==>");
      (FStar_Parser_Const.precedes_lid, "<<");
      (FStar_Parser_Const.eq2_lid, "==");
      (FStar_Parser_Const.eq3_lid, "===");
      (FStar_Parser_Const.forall_lid, "forall");
      (FStar_Parser_Const.exists_lid, "exists");
      (FStar_Parser_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____1408 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1408 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1478 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          if FStar_Util.starts_with str "dtuple"
          then
            FStar_Pervasives_Native.Some
              ("dtuple", FStar_Pervasives_Native.None)
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some
                ("tuple", FStar_Pervasives_Native.None)
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", FStar_Pervasives_Native.None)
              else
                (let uu____1590 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1590
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1626 =
      let uu____1627 = FStar_Syntax_Subst.compress t  in
      uu____1627.FStar_Syntax_Syntax.n  in
    match uu____1626 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1"))
           in
        let uu____1658 = string_to_op s  in
        (match uu____1658 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1698 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1715 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1732 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1743 -> true
    | uu____1745 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1766 ->
        let uu____1768 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1768
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1782 = may_shorten lid  in
      if uu____1782 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun t  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let name a r =
        let uu____1927 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1927  in
      let uu____1930 =
        let uu____1931 = FStar_Syntax_Subst.compress t  in
        uu____1931.FStar_Syntax_Syntax.n  in
      match uu____1930 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1934 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1959 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1959
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1962 =
              let uu____1965 = bv_as_unique_ident x  in [uu____1965]  in
            FStar_Ident.lid_of_ids uu____1962  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1968 =
              let uu____1971 = bv_as_unique_ident x  in [uu____1971]  in
            FStar_Ident.lid_of_ids uu____1968  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let s =
            if length1 = (Prims.parse_int "0")
            then a.FStar_Ident.str
            else
              FStar_Util.substring_from a.FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          let is_prefix = Prims.strcat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____2000 =
              let uu____2001 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____2001  in
            mk1 uu____2000
          else
            if
              FStar_Util.starts_with s
                FStar_Syntax_Util.field_projector_prefix
            then
              (let rest =
                 FStar_Util.substring_from s
                   (FStar_String.length
                      FStar_Syntax_Util.field_projector_prefix)
                  in
               let r =
                 FStar_Util.split rest FStar_Syntax_Util.field_projector_sep
                  in
               match r with
               | fst1::snd1::[] ->
                   let l =
                     FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos
                      in
                   let r1 =
                     FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos))
                      in
                   mk1 (FStar_Parser_AST.Projector (l, r1))
               | uu____2025 -> failwith "wrong projector format")
            else
              (let uu____2032 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____2036 =
                      let uu____2038 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____2038  in
                    let uu____2041 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____2036 <> uu____2041)
                  in
               if uu____2032
               then
                 let uu____2046 =
                   let uu____2047 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____2047  in
                 mk1 uu____2046
               else
                 (let uu____2050 =
                    let uu____2051 =
                      let uu____2062 = maybe_shorten_fv env fv  in
                      (uu____2062, [])  in
                    FStar_Parser_AST.Construct uu____2051  in
                  mk1 uu____2050))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2080 = FStar_Options.print_universes ()  in
          if uu____2080
          then
            let univs1 =
              FStar_List.map
                (fun x  -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes
               in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1,args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____2111 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2111  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2134 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2142 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2142
          then
            let uu____2145 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2145
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2150 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2171 -> ("Type", true)  in
          (match uu____2150 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2183 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2183  in
               let uu____2184 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2184
               then
                 let uu____2187 =
                   let uu____2188 =
                     let uu____2195 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2195, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2188  in
                 mk1 uu____2187
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2200) ->
          let uu____2225 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2225 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2241 = FStar_Options.print_implicits ()  in
                 if uu____2241 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2279  ->
                         match uu____2279 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2319 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2319 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2329 = FStar_Options.print_implicits ()  in
                 if uu____2329 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2340 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2340 FStar_List.rev  in
               let rec aux body3 uu___201_2365 =
                 match uu___201_2365 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2381 =
            let uu____2386 =
              let uu____2387 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2387]  in
            FStar_Syntax_Subst.open_term uu____2386 phi  in
          (match uu____2381 with
           | (x1,phi1) ->
               let b =
                 let uu____2409 =
                   let uu____2412 = FStar_List.hd x1  in
                   resugar_binder' env uu____2412 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2409  in
               let uu____2419 =
                 let uu____2420 =
                   let uu____2425 = resugar_term' env phi1  in
                   (b, uu____2425)  in
                 FStar_Parser_AST.Refine uu____2420  in
               mk1 uu____2419)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2427;
             FStar_Syntax_Syntax.vars = uu____2428;_},(e,uu____2430)::[])
          when
          (let uu____2471 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2471) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___202_2520 =
            match uu___202_2520 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2590 -> failwith "last of an empty list"  in
          let rec last_two uu___203_2629 =
            match uu___203_2629 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____2661::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2739::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2810  ->
                   match uu____2810 with
                   | (e2,qual) ->
                       let uu____2827 = resugar_term' env e2  in
                       let uu____2828 = resugar_imp env qual  in
                       (uu____2827, uu____2828)) args1
               in
            let uu____2829 = resugar_term' env e1  in
            match uu____2829 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd1,previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd1, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc  ->
                     fun uu____2866  ->
                       match uu____2866 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2882 = FStar_Options.print_implicits ()  in
            if uu____2882 then args else filter_imp args  in
          let uu____2897 = resugar_term_as_op e  in
          (match uu____2897 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2910) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2935  ->
                        match uu____2935 with
                        | (x,uu____2947) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____2956 =
                                   let uu____2957 =
                                     let uu____2958 =
                                       let uu____2965 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____2965, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____2958  in
                                   mk1 uu____2957  in
                                 FStar_Pervasives_Native.Some uu____2956))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____2969) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2995)::[] -> b
                 | uu____3012 -> failwith "wrong arguments to dtuple"  in
               let uu____3022 =
                 let uu____3023 = FStar_Syntax_Subst.compress body  in
                 uu____3023.FStar_Syntax_Syntax.n  in
               (match uu____3022 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3028) ->
                    let uu____3053 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3053 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3063 = FStar_Options.print_implicits ()
                              in
                           if uu____3063 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3080 =
                           let uu____3081 =
                             let uu____3092 =
                               FStar_List.map
                                 (fun _0_1  -> FStar_Util.Inl _0_1) xs3
                                in
                             (uu____3092, body3)  in
                           FStar_Parser_AST.Sum uu____3081  in
                         mk1 uu____3080)
                | uu____3109 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3132  ->
                              match uu____3132 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3150) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3159) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3168 = FStar_List.hd args1  in
               (match uu____3168 with
                | (t1,uu____3182) ->
                    let uu____3187 =
                      let uu____3188 = FStar_Syntax_Subst.compress t1  in
                      uu____3188.FStar_Syntax_Syntax.n  in
                    (match uu____3187 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3195 =
                           let uu____3196 =
                             let uu____3201 = resugar_term' env t1  in
                             (uu____3201, f)  in
                           FStar_Parser_AST.Project uu____3196  in
                         mk1 uu____3195
                     | uu____3202 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3203) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____3227 =
                 match new_args with
                 | (a1,uu____3237)::(a2,uu____3239)::[] -> (a1, a2)
                 | uu____3266 -> failwith "wrong arguments to try_with"  in
               (match uu____3227 with
                | (body,handler) ->
                    let decomp term =
                      let uu____3288 =
                        let uu____3289 = FStar_Syntax_Subst.compress term  in
                        uu____3289.FStar_Syntax_Syntax.n  in
                      match uu____3288 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____3294) ->
                          let uu____3319 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____3319 with | (x1,e2) -> e2)
                      | uu____3326 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____3329 = decomp body  in
                      resugar_term' env uu____3329  in
                    let handler1 =
                      let uu____3331 = decomp handler  in
                      resugar_term' env uu____3331  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____3339,uu____3340,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____3372,uu____3373,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____3410 =
                            let uu____3411 =
                              let uu____3420 = resugar_body t11  in
                              (uu____3420, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____3411  in
                          mk1 uu____3410
                      | uu____3423 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____3481 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____3511) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3520) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3541) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____3639 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____3652 =
                   let uu____3653 = FStar_Syntax_Subst.compress body  in
                   uu____3653.FStar_Syntax_Syntax.n  in
                 match uu____3652 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3658) ->
                     let uu____3683 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3683 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3693 = FStar_Options.print_implicits ()
                               in
                            if uu____3693 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3709 =
                            let uu____3718 =
                              let uu____3719 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3719.FStar_Syntax_Syntax.n  in
                            match uu____3718 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3737 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____3767 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3811  ->
                                                     match uu____3811 with
                                                     | (e2,uu____3819) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3767, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3835 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3835)
                                  | uu____3844 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3737 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3876 ->
                                let uu____3877 = resugar_term' env body2  in
                                ([], uu____3877)
                             in
                          (match uu____3709 with
                           | (pats,body3) ->
                               let uu____3894 = uncurry xs3 pats body3  in
                               (match uu____3894 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      mk1
                                        (FStar_Parser_AST.QForall
                                           (xs5, pats1, body4))
                                    else
                                      mk1
                                        (FStar_Parser_AST.QExists
                                           (xs5, pats1, body4)))))
                 | uu____3946 ->
                     if op = "forall"
                     then
                       let uu____3950 =
                         let uu____3951 =
                           let uu____3964 = resugar_term' env body  in
                           ([], [[]], uu____3964)  in
                         FStar_Parser_AST.QForall uu____3951  in
                       mk1 uu____3950
                     else
                       (let uu____3977 =
                          let uu____3978 =
                            let uu____3991 = resugar_term' env body  in
                            ([], [[]], uu____3991)  in
                          FStar_Parser_AST.QExists uu____3978  in
                        mk1 uu____3977)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4020)::[] -> resugar b
                  | uu____4037 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4049) ->
               let uu____4057 = FStar_List.hd args1  in
               (match uu____4057 with
                | (e1,uu____4071) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4143  ->
                         match uu____4143 with
                         | (e1,qual) ->
                             let uu____4160 = resugar_term' env e1  in
                             let uu____4161 = resugar_imp env qual  in
                             (uu____4160, uu____4161)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4177 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4177 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4225 =
                               let uu____4226 =
                                 let uu____4233 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4233)  in
                               FStar_Parser_AST.Op uu____4226  in
                             mk1 uu____4225  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4251  ->
                                  match uu____4251 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4270 =
                      let uu____4271 =
                        let uu____4278 =
                          let uu____4281 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4281
                           in
                        (op1, uu____4278)  in
                      FStar_Parser_AST.Op uu____4271  in
                    mk1 uu____4270
                | uu____4294 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4363 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4363 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4409 =
                   let uu____4422 =
                     let uu____4427 = resugar_pat' env pat1 branch_bv  in
                     let uu____4428 = resugar_term' env e  in
                     (uu____4427, uu____4428)  in
                   (FStar_Pervasives_Native.None, uu____4422)  in
                 [uu____4409]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4480,t1)::(pat2,uu____4483,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4579 =
            let uu____4580 =
              let uu____4587 = resugar_term' env e  in
              let uu____4588 = resugar_term' env t1  in
              let uu____4589 = resugar_term' env t2  in
              (uu____4587, uu____4588, uu____4589)  in
            FStar_Parser_AST.If uu____4580  in
          mk1 uu____4579
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4655 =
            match uu____4655 with
            | (pat,wopt,b) ->
                let uu____4697 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4697 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4749 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____4749
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4753 =
            let uu____4754 =
              let uu____4769 = resugar_term' env e  in
              let uu____4770 = FStar_List.map resugar_branch branches  in
              (uu____4769, uu____4770)  in
            FStar_Parser_AST.Match uu____4754  in
          mk1 uu____4753
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____4816) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4885 =
            let uu____4886 =
              let uu____4895 = resugar_term' env e  in
              (uu____4895, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4886  in
          mk1 uu____4885
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4924 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4924 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4978 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4978
                    in
                 let uu____4985 =
                   let uu____4990 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4990
                    in
                 match uu____4985 with
                 | (univs1,td) ->
                     let uu____5010 =
                       let uu____5017 =
                         let uu____5018 = FStar_Syntax_Subst.compress td  in
                         uu____5018.FStar_Syntax_Syntax.n  in
                       match uu____5017 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5027,(t1,uu____5029)::(d,uu____5031)::[])
                           -> (t1, d)
                       | uu____5088 -> failwith "wrong let binding format"
                        in
                     (match uu____5010 with
                      | (typ,def) ->
                          let uu____5119 =
                            let uu____5135 =
                              let uu____5136 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5136.FStar_Syntax_Syntax.n  in
                            match uu____5135 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5156) ->
                                let uu____5181 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5181 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5212 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5212
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5235 -> ([], def, false)  in
                          (match uu____5119 with
                           | (binders,term,is_pat_app) ->
                               let uu____5290 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5301 =
                                       let uu____5302 =
                                         let uu____5303 =
                                           let uu____5310 =
                                             bv_as_unique_ident bv  in
                                           (uu____5310,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5303
                                          in
                                       mk_pat uu____5302  in
                                     (uu____5301, term)
                                  in
                               (match uu____5290 with
                                | (pat,term1) ->
                                    let uu____5332 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5375  ->
                                                  match uu____5375 with
                                                  | (bv,q) ->
                                                      let uu____5390 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5390
                                                        (fun q1  ->
                                                           let uu____5402 =
                                                             let uu____5403 =
                                                               let uu____5410
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5410,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5403
                                                              in
                                                           mk_pat uu____5402)))
                                           in
                                        let uu____5413 =
                                          let uu____5418 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5418)
                                           in
                                        let uu____5421 =
                                          universe_to_string univs1  in
                                        (uu____5413, uu____5421)
                                      else
                                        (let uu____5430 =
                                           let uu____5435 =
                                             resugar_term' env term1  in
                                           (pat, uu____5435)  in
                                         let uu____5436 =
                                           universe_to_string univs1  in
                                         (uu____5430, uu____5436))
                                       in
                                    (attrs_opt, uu____5332))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5542 =
                   match uu____5542 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5602 =
                         let uu____5604 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5604  in
                       if uu____5602
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs1 (FStar_Pervasives_Native.snd pb))))
                    in
                 FStar_List.map f r  in
               let body2 = resugar_term' env body1  in
               mk1
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5685) ->
          let s =
            let uu____5704 =
              let uu____5706 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5706 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____5704  in
          let uu____5711 = mk1 FStar_Parser_AST.Wild  in label s uu____5711
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5719 =
            let uu____5720 =
              let uu____5725 = resugar_term' env tm  in (uu____5725, qi1)  in
            FStar_Parser_AST.Quote uu____5720  in
          mk1 uu____5719
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___204_5737 =
            match uu___204_5737 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5745,(uu____5746,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____5807 =
                        let uu____5808 =
                          let uu____5817 = resugar_seq t11  in
                          (uu____5817, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____5808  in
                      mk1 uu____5807
                  | uu____5820 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5864  ->
                         match uu____5864 with
                         | (x,uu____5872) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____5877 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5895,t1) ->
               resugar_term' env e)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun c  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____5935 = FStar_Options.print_universes ()  in
               if uu____5935
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.GTotal (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____5999 = FStar_Options.print_universes ()  in
               if uu____5999
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.Comp c1 ->
          let result =
            let uu____6043 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6043, FStar_Parser_AST.Nothing)  in
          let uu____6044 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6044
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6067 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6067
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6152 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6152, (FStar_Pervasives_Native.snd post))  in
                    let uu____6163 =
                      let uu____6172 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6172 then [] else [pre]  in
                    let uu____6207 =
                      let uu____6216 =
                        let uu____6225 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6225 then [] else [pats]  in
                      FStar_List.append [post1] uu____6216  in
                    FStar_List.append uu____6163 uu____6207
                | uu____6284 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6318  ->
                   match uu____6318 with
                   | (e,uu____6330) ->
                       let uu____6335 = resugar_term' env e  in
                       (uu____6335, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___205_6360 =
              match uu___205_6360 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6393 = resugar_term' env e  in
                         (uu____6393, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6398 -> aux l tl1)
               in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name),
                   (FStar_List.append (result :: decrease) args1)))
          else
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name), [result]))

and (resugar_binder' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Range.range ->
        FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun b  ->
      fun r  ->
        let uu____6445 = b  in
        match uu____6445 with
        | (x,aq) ->
            let uu____6454 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6454
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6468 =
                       let uu____6469 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6469  in
                     FStar_Parser_AST.mk_binder uu____6468 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6470 ->
                     let uu____6471 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6471
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6476 =
                          let uu____6477 =
                            let uu____6482 = bv_as_unique_ident x  in
                            (uu____6482, e)  in
                          FStar_Parser_AST.Annotated uu____6477  in
                        FStar_Parser_AST.mk_binder uu____6476 r
                          FStar_Parser_AST.Type_level imp))

and (resugar_bv_as_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun v1  ->
      fun aqual  ->
        fun body_bv  ->
          fun typ_opt  ->
            let mk1 a =
              let uu____6502 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6502  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6506 =
                if used
                then
                  let uu____6508 =
                    let uu____6515 = bv_as_unique_ident v1  in
                    (uu____6515, aqual)  in
                  FStar_Parser_AST.PatVar uu____6508
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6506  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6522;
                  FStar_Syntax_Syntax.vars = uu____6523;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6533 = FStar_Options.print_bound_var_types ()  in
                if uu____6533
                then
                  let uu____6536 =
                    let uu____6537 =
                      let uu____6548 =
                        let uu____6555 = resugar_term' env typ  in
                        (uu____6555, FStar_Pervasives_Native.None)  in
                      (pat, uu____6548)  in
                    FStar_Parser_AST.PatAscribed uu____6537  in
                  mk1 uu____6536
                else pat

and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun x  ->
      fun qual  ->
        fun body_bv  ->
          let uu____6576 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6576
            (fun aqual  ->
               let uu____6588 =
                 let uu____6593 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                   uu____6593
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6588)

and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun p  ->
      fun branch_bv  ->
        let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b  ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None)
           in
        let may_drop_implicits args =
          (let uu____6665 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6665) &&
            (let uu____6668 =
               FStar_List.existsML
                 (fun uu____6681  ->
                    match uu____6681 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6703)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6708 -> false
                          | uu____6710 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6668)
           in
        let resugar_plain_pat_cons' fv args =
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args))
           in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____6778 = may_drop_implicits args  in
            if uu____6778 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____6803  ->
                 match uu____6803 with
                 | (p1,b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1
             in
          resugar_plain_pat_cons' fv args2
        
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk1 (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
              mk1
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____6858 =
                  let uu____6860 =
                    let uu____6862 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____6862  in
                  Prims.op_Negation uu____6860  in
                if uu____6858
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk1 (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____6906 = filter_pattern_imp args  in
              (match uu____6906 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____6956 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____6956 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____6975 =
                       let uu____6981 =
                         let uu____6983 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6983
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6981)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6975);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7036  ->
                        match uu____7036 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7053 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7053)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7061;
                 FStar_Syntax_Syntax.fv_delta = uu____7062;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7091 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7091 FStar_List.rev  in
              let args1 =
                let uu____7107 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7127  ->
                          match uu____7127 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7107 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7205 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7205
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7228 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7228
                 in
              let args2 =
                let uu____7246 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7246 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7290 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7290 with
               | FStar_Pervasives_Native.Some (op,uu____7302) ->
                   let uu____7319 =
                     let uu____7320 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7320  in
                   mk1 uu____7319
               | FStar_Pervasives_Native.None  ->
                   let uu____7330 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7330 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7335 ->
              let uu____7336 =
                let uu____7337 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7337  in
              mk1 uu____7336
          | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term)
         in aux p FStar_Pervasives_Native.None

and (resugar_arg_qual :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
          if b
          then FStar_Pervasives_Native.None
          else
            FStar_Pervasives_Native.Some
              (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____7377 =
            let uu____7380 =
              let uu____7381 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7381  in
            FStar_Pervasives_Native.Some uu____7380  in
          FStar_Pervasives_Native.Some uu____7377

and (resugar_imp :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.imp)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> FStar_Parser_AST.Hash
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____7393 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7393

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___206_7401  ->
    match uu___206_7401 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Irreducible  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____7408 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7409 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7410 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7415 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7424 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7433 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___207_7439  ->
    match uu___207_7439 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.PushOptions s -> FStar_Parser_AST.PushOptions s
    | FStar_Syntax_Syntax.PopOptions  -> FStar_Parser_AST.PopOptions
    | FStar_Syntax_Syntax.RestartSolver  -> FStar_Parser_AST.RestartSolver
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon))
  =
  fun env  ->
    fun datacon_ses  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid,uvs,bs,t,uu____7482,datacons) ->
            let uu____7492 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7520,uu____7521,uu____7522,inductive_lid,uu____7524,uu____7525)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7532 -> failwith "unexpected"))
               in
            (match uu____7492 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7553 = FStar_Options.print_implicits ()  in
                   if uu____7553 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7570 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___208_7577  ->
                             match uu___208_7577 with
                             | FStar_Syntax_Syntax.RecordType uu____7579 ->
                                 true
                             | uu____7589 -> false))
                      in
                   if uu____7570
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7643,univs1,term,uu____7646,num,uu____7648)
                           ->
                           let uu____7655 =
                             let uu____7656 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7656.FStar_Syntax_Syntax.n  in
                           (match uu____7655 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7670)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7739  ->
                                          match uu____7739 with
                                          | (b,qual) ->
                                              let uu____7760 =
                                                bv_as_unique_ident b  in
                                              let uu____7761 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____7760, uu____7761,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____7772 -> failwith "unexpected")
                       | uu____7784 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     FStar_Parser_AST.TyconRecord
                       ((tylid.FStar_Ident.ident), bs2,
                         FStar_Pervasives_Native.None, fields)
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs1,term,uu____7915,num,uu____7917) ->
                            let c =
                              let uu____7938 =
                                let uu____7941 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____7941  in
                              ((l.FStar_Ident.ident), uu____7938,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____7961 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8041 ->
            failwith
              "Impossible : only Sig_inductive_typ can be resugared as types"
  
let (mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____8067 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8067;
          FStar_Parser_AST.attrs = []
        }
  
let (decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
  
let (resugar_tscheme'' :
  FStar_Syntax_DsEnv.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun name  ->
      fun ts  ->
        let uu____8097 = ts  in
        match uu____8097 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8110 =
              let uu____8111 =
                let uu____8128 =
                  let uu____8137 =
                    let uu____8144 =
                      let uu____8145 =
                        let uu____8158 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8158)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8145  in
                    (uu____8144, FStar_Pervasives_Native.None)  in
                  [uu____8137]  in
                (false, false, uu____8128)  in
              FStar_Parser_AST.Tycon uu____8111  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8110
  
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tscheme" ts 
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun for_free  ->
      fun r  ->
        fun q  ->
          fun ed  ->
            let resugar_action d for_free1 =
              let action_params =
                FStar_Syntax_Subst.open_binders
                  d.FStar_Syntax_Syntax.action_params
                 in
              let uu____8247 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____8247 with
              | (bs,action_defn) ->
                  let uu____8254 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____8254 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____8264 = FStar_Options.print_implicits ()
                            in
                         if uu____8264
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____8274 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____8274 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____8291 =
                             let uu____8302 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____8302,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____8291  in
                         let t =
                           FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un
                            in
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false, false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None, t)),
                                   FStar_Pervasives_Native.None)]))
                       else
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false, false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None,
                                       action_defn1)),
                                   FStar_Pervasives_Native.None)])))
               in
            let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident
               in
            let uu____8386 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____8386 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____8396 = FStar_Options.print_implicits ()  in
                  if uu____8396 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____8406 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____8406 FStar_List.rev  in
                let eff_typ1 = resugar_term' env eff_typ  in
                let ret_wp =
                  resugar_tscheme'' env "ret_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
                   in
                let bind_wp =
                  resugar_tscheme'' env "bind_wp"
                    ed.FStar_Syntax_Syntax.bind_wp
                   in
                let if_then_else1 =
                  resugar_tscheme'' env "if_then_else"
                    ed.FStar_Syntax_Syntax.if_then_else
                   in
                let ite_wp =
                  resugar_tscheme'' env "ite_wp"
                    ed.FStar_Syntax_Syntax.ite_wp
                   in
                let stronger =
                  resugar_tscheme'' env "stronger"
                    ed.FStar_Syntax_Syntax.stronger
                   in
                let close_wp =
                  resugar_tscheme'' env "close_wp"
                    ed.FStar_Syntax_Syntax.close_wp
                   in
                let assert_p =
                  resugar_tscheme'' env "assert_p"
                    ed.FStar_Syntax_Syntax.assert_p
                   in
                let assume_p =
                  resugar_tscheme'' env "assume_p"
                    ed.FStar_Syntax_Syntax.assume_p
                   in
                let null_wp =
                  resugar_tscheme'' env "null_wp"
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let trivial =
                  resugar_tscheme'' env "trivial"
                    ed.FStar_Syntax_Syntax.trivial
                   in
                let repr =
                  resugar_tscheme'' env "repr"
                    ([], (ed.FStar_Syntax_Syntax.repr))
                   in
                let return_repr =
                  resugar_tscheme'' env "return_repr"
                    ed.FStar_Syntax_Syntax.return_repr
                   in
                let bind_repr =
                  resugar_tscheme'' env "bind_repr"
                    ed.FStar_Syntax_Syntax.bind_repr
                   in
                let mandatory_members_decls =
                  if for_free
                  then [repr; return_repr; bind_repr]
                  else
                    [repr;
                    return_repr;
                    bind_repr;
                    ret_wp;
                    bind_wp;
                    if_then_else1;
                    ite_wp;
                    stronger;
                    close_wp;
                    assert_p;
                    assume_p;
                    null_wp;
                    trivial]
                   in
                let actions =
                  FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                    (FStar_List.map (fun a  -> resugar_action a false))
                   in
                let decls = FStar_List.append mandatory_members_decls actions
                   in
                mk_decl r q
                  (FStar_Parser_AST.NewEffect
                     (FStar_Parser_AST.DefineEffect
                        (eff_name, eff_binders2, eff_typ1, decls)))
  
let (resugar_sigelt' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8491) ->
          let uu____8500 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8523 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8541 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8549 -> false
                    | uu____8566 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8500 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8604 se1 =
                 match uu____8604 with
                 | (datacon_ses1,tycons) ->
                     let uu____8630 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8630 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8645 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8645 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8680 =
                           let uu____8681 =
                             let uu____8682 =
                               let uu____8699 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____8699)  in
                             FStar_Parser_AST.Tycon uu____8682  in
                           decl'_to_decl se uu____8681  in
                         FStar_Pervasives_Native.Some uu____8680
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8734,uu____8735,uu____8736,uu____8737,uu____8738)
                              ->
                              let uu____8745 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8745
                          | uu____8748 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8752 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8759) ->
          let uu____8764 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___209_8772  ->
                    match uu___209_8772 with
                    | FStar_Syntax_Syntax.Projector (uu____8774,uu____8775)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8777 -> true
                    | uu____8779 -> false))
             in
          if uu____8764
          then FStar_Pervasives_Native.None
          else
            (let mk1 e =
               FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
                 se.FStar_Syntax_Syntax.sigrng
                in
             let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown  in
             let desugared_let =
               mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy))  in
             let t = resugar_term' env desugared_let  in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec,lets,uu____8814) ->
                 let uu____8843 =
                   let uu____8844 =
                     let uu____8845 =
                       let uu____8856 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____8856)  in
                     FStar_Parser_AST.TopLevelLet uu____8845  in
                   decl'_to_decl se uu____8844  in
                 FStar_Pervasives_Native.Some uu____8843
             | uu____8893 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____8898,fml) ->
          let uu____8900 =
            let uu____8901 =
              let uu____8902 =
                let uu____8907 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____8907)  in
              FStar_Parser_AST.Assume uu____8902  in
            decl'_to_decl se uu____8901  in
          FStar_Pervasives_Native.Some uu____8900
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____8909 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____8909
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____8912 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____8912
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____8922,t) ->
                let uu____8932 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____8932
            | uu____8933 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____8941,t) ->
                let uu____8951 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____8951
            | uu____8952 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____8976 -> failwith "Should not happen hopefully"  in
          let uu____8986 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____8986
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____8996 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8996 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9008 = FStar_Options.print_implicits ()  in
                 if uu____9008 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9024 =
                 let uu____9025 =
                   let uu____9026 =
                     let uu____9043 =
                       let uu____9052 =
                         let uu____9059 =
                           let uu____9060 =
                             let uu____9073 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9073)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9060  in
                         (uu____9059, FStar_Pervasives_Native.None)  in
                       [uu____9052]  in
                     (false, false, uu____9043)  in
                   FStar_Parser_AST.Tycon uu____9026  in
                 decl'_to_decl se uu____9025  in
               FStar_Pervasives_Native.Some uu____9024)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9105 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9105
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9109 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___210_9117  ->
                    match uu___210_9117 with
                    | FStar_Syntax_Syntax.Projector (uu____9119,uu____9120)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9122 -> true
                    | uu____9124 -> false))
             in
          if uu____9109
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9132 =
                 (let uu____9136 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9136) || (FStar_List.isEmpty uvs)
                  in
               if uu____9132
               then resugar_term' env t
               else
                 (let uu____9141 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9141 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9150 = resugar_term' env t1  in
                      label universes uu____9150)
                in
             let uu____9151 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9151)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9158 =
            let uu____9159 =
              let uu____9160 =
                let uu____9167 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9172 = resugar_term' env t  in
                (uu____9167, uu____9172)  in
              FStar_Parser_AST.Splice uu____9160  in
            decl'_to_decl se uu____9159  in
          FStar_Pervasives_Native.Some uu____9158
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9175 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9192 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9208 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9232 = noenv resugar_term'  in uu____9232 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9250 = noenv resugar_sigelt'  in uu____9250 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9268 = noenv resugar_comp'  in uu____9268 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9291 = noenv resugar_pat'  in uu____9291 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9325 = noenv resugar_binder'  in uu____9325 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9350 = noenv resugar_tscheme'  in uu____9350 ts 
let (resugar_eff_decl :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____9385 = noenv resugar_eff_decl'  in
          uu____9385 for_free r q ed
  