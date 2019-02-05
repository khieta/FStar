open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___213_6  ->
    match uu___213_6 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____10 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_constant_at_level " uu____10
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____15 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_equational_at_level " uu____15
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____19 =
          let uu____21 = delta_depth_to_string d  in
          Prims.strcat uu____21 ")"  in
        Prims.strcat "Delta_abstract (" uu____19
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____33 = FStar_Options.print_real_names ()  in
    if uu____33
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____60 =
      let uu____62 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____62  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____60
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____72 = FStar_Options.print_real_names ()  in
    if uu____72
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____85 =
      let uu____87 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____87  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____85
  
let (infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list) =
  [(FStar_Parser_Const.op_Addition, "+");
  (FStar_Parser_Const.op_Subtraction, "-");
  (FStar_Parser_Const.op_Multiply, "*");
  (FStar_Parser_Const.op_Division, "/");
  (FStar_Parser_Const.op_Eq, "=");
  (FStar_Parser_Const.op_ColonEq, ":=");
  (FStar_Parser_Const.op_notEq, "<>");
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
  (FStar_Parser_Const.eq3_lid, "===")] 
let (unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list) =
  [(FStar_Parser_Const.op_Negation, "not");
  (FStar_Parser_Const.op_Minus, "-");
  (FStar_Parser_Const.not_lid, "~")] 
let (is_prim_op :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun ps  ->
    fun f  ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____309 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____322 -> failwith "get_lid"
  
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
  
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
  
let (quants : (FStar_Ident.lident * Prims.string) Prims.list) =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")] 
type exp = FStar_Syntax_Syntax.term
let (is_b2t : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  -> is_prim_op [FStar_Parser_Const.b2t_lid] t 
let (is_quant : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
  
let (is_ite : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  -> is_prim_op [FStar_Parser_Const.ite_lid] t 
let (is_lex_cons : exp -> Prims.bool) =
  fun f  -> is_prim_op [FStar_Parser_Const.lexcons_lid] f 
let (is_lex_top : exp -> Prims.bool) =
  fun f  -> is_prim_op [FStar_Parser_Const.lextop_lid] f 
let is_inr :
  'Auu____425 'Auu____426 .
    ('Auu____425,'Auu____426) FStar_Util.either -> Prims.bool
  =
  fun uu___214_436  ->
    match uu___214_436 with
    | FStar_Util.Inl uu____441 -> false
    | FStar_Util.Inr uu____443 -> true
  
let filter_imp :
  'Auu____450 .
    ('Auu____450 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____450 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___215_505  ->
            match uu___215_505 with
            | (uu____513,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____520,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____521)) -> false
            | (uu____526,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____527)) -> false
            | uu____533 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____551 =
      let uu____552 = FStar_Syntax_Subst.compress e  in
      uu____552.FStar_Syntax_Syntax.n  in
    match uu____551 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____613 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____613
        then
          let uu____622 =
            let uu____627 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____627  in
          (match uu____622 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____638 =
                 let uu____641 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____641 :: xs  in
               FStar_Pervasives_Native.Some uu____638
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____653 ->
        let uu____654 = is_lex_top e  in
        if uu____654
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____702 = f hd1  in if uu____702 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____734 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____734
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____765 = get_lid e  in find_lid uu____765 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____777 = get_lid e  in find_lid uu____777 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____789 = get_lid t  in find_lid uu____789 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___216_803  ->
    match uu___216_803 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____814 = FStar_Options.hide_uvar_nums ()  in
    if uu____814
    then "?"
    else
      (let uu____821 =
         let uu____823 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____823 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____821)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____835 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____837 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____835 uu____837
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____863 = FStar_Options.hide_uvar_nums ()  in
    if uu____863
    then "?"
    else
      (let uu____870 =
         let uu____872 =
           let uu____874 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____874 FStar_Util.string_of_int  in
         let uu____878 =
           let uu____880 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____880  in
         Prims.strcat uu____872 uu____878  in
       Prims.strcat "?" uu____870)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____908 = FStar_Syntax_Subst.compress_univ u  in
      match uu____908 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____921 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____932 = FStar_Syntax_Subst.compress_univ u  in
    match uu____932 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____943 = univ_uvar_to_string u1  in
        Prims.strcat "U_unif " uu____943
    | FStar_Syntax_Syntax.U_name x ->
        Prims.strcat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____950 = FStar_Util.string_of_int x  in
        Prims.strcat "@" uu____950
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____955 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____955 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____976 = univ_to_string u2  in
             let uu____978 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____976 uu____978)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____984 =
          let uu____986 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____986 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____984
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____1005 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____1005 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____1022 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____1022 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___217_1040  ->
    match uu___217_1040 with
    | FStar_Syntax_Syntax.Assumption  -> "assume"
    | FStar_Syntax_Syntax.New  -> "new"
    | FStar_Syntax_Syntax.Private  -> "private"
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> "unfold"
    | FStar_Syntax_Syntax.Inline_for_extraction  -> "inline"
    | FStar_Syntax_Syntax.NoExtract  -> "noextract"
    | FStar_Syntax_Syntax.Visible_default  -> "visible"
    | FStar_Syntax_Syntax.Irreducible  -> "irreducible"
    | FStar_Syntax_Syntax.Abstract  -> "abstract"
    | FStar_Syntax_Syntax.Noeq  -> "noeq"
    | FStar_Syntax_Syntax.Unopteq  -> "unopteq"
    | FStar_Syntax_Syntax.Logic  -> "logic"
    | FStar_Syntax_Syntax.TotalEffect  -> "total"
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu____1056 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____1056
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1061 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____1061
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1074 =
          let uu____1076 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1076  in
        let uu____1077 =
          let uu____1079 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1079 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____1074 uu____1077
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1105 =
          let uu____1107 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1107  in
        let uu____1108 =
          let uu____1110 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1110 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1105 uu____1108
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1127 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____1127
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
  
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1150 ->
        let uu____1153 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____1153 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1181 ->
        let uu____1184 = quals_to_string quals  in
        Prims.strcat uu____1184 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1380 = db_to_string x  in
        Prims.strcat "Tm_bvar: " uu____1380
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1384 = nm_to_string x  in
        Prims.strcat "Tm_name: " uu____1384
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1388 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____1388
    | FStar_Syntax_Syntax.Tm_uinst uu____1391 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1399 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1401 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1403,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1404;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1418,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1419;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1433 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1453 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1469 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1477 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1495 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1519 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1547 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1562 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1576,m) ->
        let uu____1614 = FStar_ST.op_Bang m  in
        (match uu____1614 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1672 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1678,m) ->
        let uu____1684 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1684
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1688 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1691 =
      let uu____1693 = FStar_Options.ugly ()  in Prims.op_Negation uu____1693
       in
    if uu____1691
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1707 = FStar_Options.print_implicits ()  in
         if uu____1707 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1715 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1740,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1766,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____1768;
             FStar_Syntax_Syntax.rng = uu____1769;_}
           ->
           let uu____1780 =
             let uu____1782 =
               let uu____1784 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____1784  in
             Prims.strcat uu____1782 "]"  in
           Prims.strcat "[LAZYEMB:" uu____1780
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1830 =
             let uu____1832 =
               let uu____1834 =
                 let uu____1835 =
                   let uu____1844 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1844  in
                 uu____1835 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1834  in
             Prims.strcat uu____1832 "]"  in
           Prims.strcat "[lazy:" uu____1830
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1913 =
                  match uu____1913 with
                  | (bv,t) ->
                      let uu____1921 = bv_to_string bv  in
                      let uu____1923 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1921 uu____1923
                   in
                let uu____1926 = term_to_string tm  in
                let uu____1928 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1926 uu____1928
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1937 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1937)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1960 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1997 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____2022  ->
                                 match uu____2022 with
                                 | (t1,uu____2031) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1997
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1960 (FStar_String.concat "\\/")  in
           let uu____2046 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____2046
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____2060 = tag_of_term t  in
           let uu____2062 = sli m  in
           let uu____2064 = term_to_string t'  in
           let uu____2066 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____2060 uu____2062
             uu____2064 uu____2066
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____2081 = tag_of_term t  in
           let uu____2083 = term_to_string t'  in
           let uu____2085 = sli m0  in
           let uu____2087 = sli m1  in
           let uu____2089 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2081
             uu____2083 uu____2085 uu____2087 uu____2089
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____2104 = FStar_Range.string_of_range r  in
           let uu____2106 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2104
             uu____2106
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2115 = lid_to_string l  in
           let uu____2117 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2119 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2115 uu____2117
             uu____2119
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2123) ->
           let uu____2128 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2128
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2132 = db_to_string x3  in
           let uu____2134 =
             let uu____2136 =
               let uu____2138 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____2138 ")"  in
             Prims.strcat ":(" uu____2136  in
           Prims.strcat uu____2132 uu____2134
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2145)) ->
           let uu____2160 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2160
           then ctx_uvar_to_string u
           else
             (let uu____2166 =
                let uu____2168 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2168  in
              Prims.strcat "?" uu____2166)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2191 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2191
           then
             let uu____2195 = ctx_uvar_to_string u  in
             let uu____2197 =
               let uu____2199 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2199 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2195 uu____2197
           else
             (let uu____2218 =
                let uu____2220 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2220  in
              Prims.strcat "?" uu____2218)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2227 = FStar_Options.print_universes ()  in
           if uu____2227
           then
             let uu____2231 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2231
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2259 = binders_to_string " -> " bs  in
           let uu____2262 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2259 uu____2262
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2294 = binders_to_string " " bs  in
                let uu____2297 = term_to_string t2  in
                let uu____2299 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2308 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2308)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2294 uu____2297
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____2299
            | uu____2312 ->
                let uu____2315 = binders_to_string " " bs  in
                let uu____2318 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2315 uu____2318)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2327 = bv_to_string xt  in
           let uu____2329 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2332 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2327 uu____2329 uu____2332
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2364 = term_to_string t  in
           let uu____2366 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2364 uu____2366
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2389 = lbs_to_string [] lbs  in
           let uu____2391 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2389 uu____2391
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2456 =
                   let uu____2458 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____2458
                     (FStar_Util.dflt "default")
                    in
                 let uu____2469 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2456 uu____2469
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2490 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2490
              in
           let uu____2493 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2493 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____2534 = term_to_string head1  in
           let uu____2536 =
             let uu____2538 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____2571  ->
                       match uu____2571 with
                       | (p,wopt,e) ->
                           let uu____2588 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____2591 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____2596 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____2596
                              in
                           let uu____2600 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____2588
                             uu____2591 uu____2600))
                in
             FStar_Util.concat_l "\n\t|" uu____2538  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2534 uu____2536
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2612 = FStar_Options.print_universes ()  in
           if uu____2612
           then
             let uu____2616 = term_to_string t  in
             let uu____2618 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2616 uu____2618
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2625 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2628 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2630 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2625 uu____2628
      uu____2630

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___218_2633  ->
    match uu___218_2633 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2639 = FStar_Util.string_of_int i  in
        let uu____2641 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2639 uu____2641
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2648 = bv_to_string x  in
        let uu____2650 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2648 uu____2650
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2659 = bv_to_string x  in
        let uu____2661 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2659 uu____2661
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2668 = FStar_Util.string_of_int i  in
        let uu____2670 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2668 uu____2670
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2677 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2677

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2681 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2681 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2697 =
      let uu____2699 = FStar_Options.ugly ()  in Prims.op_Negation uu____2699
       in
    if uu____2697
    then
      let e =
        let uu____2704 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2704  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2733 = fv_to_string l  in
           let uu____2735 =
             let uu____2737 =
               FStar_List.map
                 (fun uu____2751  ->
                    match uu____2751 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2737 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2733 uu____2735
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2776) ->
           let uu____2781 = FStar_Options.print_bound_var_types ()  in
           if uu____2781
           then
             let uu____2785 = bv_to_string x1  in
             let uu____2787 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2785 uu____2787
           else
             (let uu____2792 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2792)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2796 = FStar_Options.print_bound_var_types ()  in
           if uu____2796
           then
             let uu____2800 = bv_to_string x1  in
             let uu____2802 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2800 uu____2802
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2809 = FStar_Options.print_bound_var_types ()  in
           if uu____2809
           then
             let uu____2813 = bv_to_string x1  in
             let uu____2815 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2813 uu____2815
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2824 = quals_to_string' quals  in
      let uu____2826 =
        let uu____2828 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2848 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2850 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2852 =
                    let uu____2854 = FStar_Options.print_universes ()  in
                    if uu____2854
                    then
                      let uu____2858 =
                        let uu____2860 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2860 ">"  in
                      Prims.strcat "<" uu____2858
                    else ""  in
                  let uu____2867 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2869 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2848
                    uu____2850 uu____2852 uu____2867 uu____2869))
           in
        FStar_Util.concat_l "\n and " uu____2828  in
      FStar_Util.format3 "%slet %s %s" uu____2824
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2826

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___219_2884  ->
    match uu___219_2884 with
    | [] -> ""
    | tms ->
        let uu____2892 =
          let uu____2894 =
            FStar_List.map
              (fun t  ->
                 let uu____2902 = term_to_string t  in paren uu____2902) tms
             in
          FStar_All.pipe_right uu____2894 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2892

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2911 = FStar_Options.print_effect_args ()  in
    if uu____2911
    then
      let uu____2915 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2915
    else
      (let uu____2918 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2920 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2918 uu____2920)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___220_2924  ->
      match uu___220_2924 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.strcat "[|" (Prims.strcat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____2942 =
            let uu____2944 = term_to_string t  in
            Prims.strcat uu____2944 (Prims.strcat "]" s)  in
          Prims.strcat "#[" uu____2942
      | FStar_Pervasives_Native.None  -> s

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq  -> aqual_to_string' "" aq

and (imp_to_string :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  = fun s  -> fun aq  -> aqual_to_string' s aq

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2964 =
        let uu____2966 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2966  in
      if uu____2964
      then
        let uu____2970 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2970 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2981 = b  in
         match uu____2981 with
         | (a,imp) ->
             let uu____2995 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2995
             then
               let uu____2999 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2999
             else
               (let uu____3004 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____3007 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____3007)
                   in
                if uu____3004
                then
                  let uu____3011 = nm_to_string a  in
                  imp_to_string uu____3011 imp
                else
                  (let uu____3015 =
                     let uu____3017 = nm_to_string a  in
                     let uu____3019 =
                       let uu____3021 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____3021  in
                     Prims.strcat uu____3017 uu____3019  in
                   imp_to_string uu____3015 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  = fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____3040 = FStar_Options.print_implicits ()  in
        if uu____3040 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____3051 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____3051 (FStar_String.concat sep)
      else
        (let uu____3079 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____3079 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___221_3093  ->
    match uu___221_3093 with
    | (a,imp) ->
        let uu____3107 = term_to_string a  in imp_to_string uu____3107 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____3119 = FStar_Options.print_implicits ()  in
      if uu____3119 then args else filter_imp args  in
    let uu____3134 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3134 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____3163 = FStar_Options.ugly ()  in
      if uu____3163
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____3174 =
      let uu____3176 = FStar_Options.ugly ()  in Prims.op_Negation uu____3176
       in
    if uu____3174
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____3197 =
             let uu____3198 = FStar_Syntax_Subst.compress t  in
             uu____3198.FStar_Syntax_Syntax.n  in
           (match uu____3197 with
            | FStar_Syntax_Syntax.Tm_type uu____3202 when
                let uu____3203 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3203 -> term_to_string t
            | uu____3205 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3208 = univ_to_string u  in
                     let uu____3210 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3208 uu____3210
                 | uu____3213 ->
                     let uu____3216 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3216))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3229 =
             let uu____3230 = FStar_Syntax_Subst.compress t  in
             uu____3230.FStar_Syntax_Syntax.n  in
           (match uu____3229 with
            | FStar_Syntax_Syntax.Tm_type uu____3234 when
                let uu____3235 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3235 -> term_to_string t
            | uu____3237 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3240 = univ_to_string u  in
                     let uu____3242 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3240 uu____3242
                 | uu____3245 ->
                     let uu____3248 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3248))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3254 = FStar_Options.print_effect_args ()  in
             if uu____3254
             then
               let uu____3258 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3260 =
                 let uu____3262 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3262 (FStar_String.concat ", ")
                  in
               let uu____3277 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3279 =
                 let uu____3281 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3281 (FStar_String.concat ", ")
                  in
               let uu____3308 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3258
                 uu____3260 uu____3277 uu____3279 uu____3308
             else
               (let uu____3313 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___222_3319  ->
                           match uu___222_3319 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3322 -> false)))
                    &&
                    (let uu____3325 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3325)
                   in
                if uu____3313
                then
                  let uu____3329 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3329
                else
                  (let uu____3334 =
                     ((let uu____3338 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3338) &&
                        (let uu____3341 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3341))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____3334
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3347 =
                        (let uu____3351 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3351) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___223_3357  ->
                                   match uu___223_3357 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3360 -> false)))
                         in
                      if uu____3347
                      then
                        let uu____3364 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3364
                      else
                        (let uu____3369 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3371 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3369 uu____3371))))
              in
           let dec =
             let uu____3376 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___224_3389  ->
                       match uu___224_3389 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3396 =
                             let uu____3398 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3398
                              in
                           [uu____3396]
                       | uu____3403 -> []))
                in
             FStar_All.pipe_right uu____3376 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and (cflag_to_string : FStar_Syntax_Syntax.cflag -> Prims.string) =
  fun c  ->
    match c with
    | FStar_Syntax_Syntax.TOTAL  -> "total"
    | FStar_Syntax_Syntax.MLEFFECT  -> "ml"
    | FStar_Syntax_Syntax.RETURN  -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN  -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL  -> "sometrivial"
    | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> "trivial_postcondition"
    | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> "should_not_inline"
    | FStar_Syntax_Syntax.LEMMA  -> "lemma"
    | FStar_Syntax_Syntax.CPS  -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____3422 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___225_3432  ->
    match uu___225_3432 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____3449 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3486 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3511  ->
                              match uu____3511 with
                              | (t,uu____3520) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3486
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3449 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3537 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3537
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3542) ->
        let uu____3547 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3547
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3558 = sli m  in
        let uu____3560 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3558 uu____3560
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3570 = sli m  in
        let uu____3572 = sli m'  in
        let uu____3574 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3570
          uu____3572 uu____3574

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____3589 = FStar_Options.ugly ()  in
      if uu____3589
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)
  
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env  ->
    fun b  ->
      let uu____3610 = b  in
      match uu____3610 with
      | (a,imp) ->
          let n1 =
            let uu____3618 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3618
            then FStar_Util.JsonNull
            else
              (let uu____3623 =
                 let uu____3625 = nm_to_string a  in
                 imp_to_string uu____3625 imp  in
               FStar_Util.JsonStr uu____3623)
             in
          let t =
            let uu____3628 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3628  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____3660 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3660
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3678 = FStar_Options.print_universes ()  in
    if uu____3678 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3694 =
      let uu____3696 = FStar_Options.ugly ()  in Prims.op_Negation uu____3696
       in
    if uu____3694
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____3706 = s  in
       match uu____3706 with
       | (us,t) ->
           let uu____3718 =
             let uu____3720 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3720  in
           let uu____3724 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3718 uu____3724)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3734 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3736 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3739 =
      let uu____3741 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3741  in
    let uu____3745 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3747 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3734 uu____3736 uu____3739
      uu____3745 uu____3747
  
let (eff_decl_to_string' :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____3778 =
            let uu____3780 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3780  in
          if uu____3778
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____3801 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3801 (FStar_String.concat ",\n\t")
                in
             let uu____3816 =
               let uu____3820 =
                 let uu____3824 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____3826 =
                   let uu____3830 =
                     let uu____3832 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____3832  in
                   let uu____3836 =
                     let uu____3840 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____3843 =
                       let uu____3847 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____3849 =
                         let uu____3853 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____3855 =
                           let uu____3859 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____3861 =
                             let uu____3865 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____3867 =
                               let uu____3871 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____3873 =
                                 let uu____3877 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____3879 =
                                   let uu____3883 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____3885 =
                                     let uu____3889 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____3891 =
                                       let uu____3895 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____3897 =
                                         let uu____3901 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____3903 =
                                           let uu____3907 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____3909 =
                                             let uu____3913 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____3915 =
                                               let uu____3919 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____3921 =
                                                 let uu____3925 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____3927 =
                                                   let uu____3931 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____3931]  in
                                                 uu____3925 :: uu____3927  in
                                               uu____3919 :: uu____3921  in
                                             uu____3913 :: uu____3915  in
                                           uu____3907 :: uu____3909  in
                                         uu____3901 :: uu____3903  in
                                       uu____3895 :: uu____3897  in
                                     uu____3889 :: uu____3891  in
                                   uu____3883 :: uu____3885  in
                                 uu____3877 :: uu____3879  in
                               uu____3871 :: uu____3873  in
                             uu____3865 :: uu____3867  in
                           uu____3859 :: uu____3861  in
                         uu____3853 :: uu____3855  in
                       uu____3847 :: uu____3849  in
                     uu____3840 :: uu____3843  in
                   uu____3830 :: uu____3836  in
                 uu____3824 :: uu____3826  in
               (if for_free then "_for_free " else "") :: uu____3820  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____3816)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let basic =
      match x.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
          "#light \"off\""
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          (FStar_Pervasives_Native.None )) -> "#reset-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#reset-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
          FStar_Util.format1 "#set-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.None )) -> "#push-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#push-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
          -> "#restart-solver"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
          "#pop-options"
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univs1,tps,k,uu____4006,uu____4007) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4023 = FStar_Options.print_universes ()  in
          if uu____4023
          then
            let uu____4027 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____4027 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____4036,uu____4037,uu____4038) ->
          let uu____4045 = FStar_Options.print_universes ()  in
          if uu____4045
          then
            let uu____4049 = univ_names_to_string univs1  in
            let uu____4051 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4049
              lid.FStar_Ident.str uu____4051
          else
            (let uu____4056 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____4056)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____4062 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4064 =
            let uu____4066 = FStar_Options.print_universes ()  in
            if uu____4066
            then
              let uu____4070 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____4070
            else ""  in
          let uu____4076 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4062
            lid.FStar_Ident.str uu____4064 uu____4076
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4082 = FStar_Options.print_universes ()  in
          if uu____4082
          then
            let uu____4086 = univ_names_to_string us  in
            let uu____4088 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4086 uu____4088
          else
            (let uu____4093 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4093)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4097) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4103 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4103
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4107) ->
          let uu____4116 =
            let uu____4118 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4118 (FStar_String.concat "\n")  in
          Prims.strcat "(* Sig_bundle *)" uu____4116
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          eff_decl_to_string' false x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          eff_decl_to_string' true x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se ->
          let lift_wp =
            match ((se.FStar_Syntax_Syntax.lift_wp),
                    (se.FStar_Syntax_Syntax.lift))
            with
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                -> failwith "impossible"
            | (FStar_Pervasives_Native.Some lift_wp,uu____4163) -> lift_wp
            | (uu____4170,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____4178 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____4178 with
           | (us,t) ->
               let uu____4190 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____4192 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____4194 = univ_names_to_string us  in
               let uu____4196 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____4190
                 uu____4192 uu____4194 uu____4196)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
          let uu____4208 = FStar_Options.print_universes ()  in
          if uu____4208
          then
            let uu____4212 =
              let uu____4217 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4217  in
            (match uu____4212 with
             | (univs2,t) ->
                 let uu____4231 =
                   let uu____4236 =
                     let uu____4237 = FStar_Syntax_Subst.compress t  in
                     uu____4237.FStar_Syntax_Syntax.n  in
                   match uu____4236 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4266 -> failwith "impossible"  in
                 (match uu____4231 with
                  | (tps1,c1) ->
                      let uu____4275 = sli l  in
                      let uu____4277 = univ_names_to_string univs2  in
                      let uu____4279 = binders_to_string " " tps1  in
                      let uu____4282 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4275
                        uu____4277 uu____4279 uu____4282))
          else
            (let uu____4287 = sli l  in
             let uu____4289 = binders_to_string " " tps  in
             let uu____4292 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4287 uu____4289
               uu____4292)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4301 =
            let uu____4303 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4303  in
          let uu____4313 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4301 uu____4313
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____4317 ->
        let uu____4320 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.strcat uu____4320 (Prims.strcat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____4337 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4337 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4348,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4350;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4352;
                       FStar_Syntax_Syntax.lbdef = uu____4353;
                       FStar_Syntax_Syntax.lbattrs = uu____4354;
                       FStar_Syntax_Syntax.lbpos = uu____4355;_}::[]),uu____4356)
        ->
        let uu____4379 = lbname_to_string lb  in
        let uu____4381 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4379 uu____4381
    | uu____4384 ->
        let uu____4385 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____4385 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4409 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4411 =
      let uu____4413 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4413 (FStar_String.concat "\n")  in
    let uu____4423 =
      let uu____4425 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4425 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4409
      uu____4411 uu____4423
  
let (abs_ascription_to_string :
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    FStar_Pervasives_Native.option -> Prims.string)
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder ()  in
    (match ascription with
     | FStar_Pervasives_Native.None  ->
         FStar_Util.string_builder_append strb "None"
     | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____4469 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____4469))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____4478 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____4478)));
    FStar_Util.string_of_string_builder strb
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____4519 = f x  in
            FStar_Util.string_builder_append strb uu____4519);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4528 = f x1  in
                 FStar_Util.string_builder_append strb uu____4528)) xs;
           FStar_Util.string_builder_append strb "]";
           FStar_Util.string_of_string_builder strb)
  
let set_to_string :
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string =
  fun f  ->
    fun s  ->
      let elts = FStar_Util.set_elements s  in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "{";
           (let uu____4575 = f x  in
            FStar_Util.string_builder_append strb uu____4575);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4584 = f x1  in
                 FStar_Util.string_builder_append strb uu____4584)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____4606 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4606
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___226_4619  ->
    match uu___226_4619 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4635 =
          let uu____4637 =
            let uu____4639 =
              let uu____4641 =
                let uu____4643 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4643 (FStar_String.concat " ")  in
              Prims.strcat uu____4641 ")"  in
            Prims.strcat " " uu____4639  in
          Prims.strcat h uu____4637  in
        Prims.strcat "(" uu____4635
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4658 =
          let uu____4660 = emb_typ_to_string a  in
          let uu____4662 =
            let uu____4664 = emb_typ_to_string b  in
            Prims.strcat ") -> " uu____4664  in
          Prims.strcat uu____4660 uu____4662  in
        Prims.strcat "(" uu____4658
  