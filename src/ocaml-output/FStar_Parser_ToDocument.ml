open Prims
let (min : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then y else x 
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then x else y 
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____99 = let uu____102 = f x  in uu____102 :: acc  in
            aux xs uu____99
         in
      aux l []
  
let rec map_if_all :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____169 = f x  in
            (match uu____169 with
             | FStar_Pervasives_Native.Some r -> aux xs (r :: acc)
             | FStar_Pervasives_Native.None  -> [])
         in
      let r = aux l []  in
      if (FStar_List.length l) = (FStar_List.length r)
      then FStar_Pervasives_Native.Some r
      else FStar_Pervasives_Native.None
  
let rec all : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f  ->
    fun l  ->
      match l with
      | [] -> true
      | x::xs ->
          let uu____225 = f x  in if uu____225 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___110_258  ->
         match uu___110_258 with
         | (uu____264,FStar_Parser_AST.Nothing ) -> true
         | uu____266 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____317 'Auu____318 .
    Prims.bool -> ('Auu____317 -> 'Auu____318) -> 'Auu____317 -> 'Auu____318
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app  in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t  in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
  
let (str : Prims.string -> FStar_Pprint.document) =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____428 'Auu____429 .
    'Auu____428 ->
      ('Auu____429 -> 'Auu____428) ->
        'Auu____429 FStar_Pervasives_Native.option -> 'Auu____428
  =
  fun n1  ->
    fun f  ->
      fun x  ->
        match x with
        | FStar_Pervasives_Native.None  -> n1
        | FStar_Pervasives_Native.Some x' -> f x'
  
let (prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
  
let (prefix2_nonempty :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      if body = FStar_Pprint.empty then prefix_ else prefix2 prefix_ body
  
let (op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  -> fun body  -> prefix2 prefix_ body 
let (jump2 : FStar_Pprint.document -> FStar_Pprint.document) =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
  
let (infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1") 
let (infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1") 
let (break1 : FStar_Pprint.document) =
  FStar_Pprint.break_ (Prims.parse_int "1") 
let separate_break_map :
  'Auu____542 .
    FStar_Pprint.document ->
      ('Auu____542 -> FStar_Pprint.document) ->
        'Auu____542 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____567 =
          let uu____568 =
            let uu____569 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____569  in
          FStar_Pprint.separate_map uu____568 f l  in
        FStar_Pprint.group uu____567
  
let precede_break_separate_map :
  'Auu____581 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____581 -> FStar_Pprint.document) ->
          'Auu____581 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____611 =
            let uu____612 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____613 =
              let uu____614 = FStar_List.hd l  in
              FStar_All.pipe_right uu____614 f  in
            FStar_Pprint.precede uu____612 uu____613  in
          let uu____615 =
            let uu____616 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____622 =
                   let uu____623 =
                     let uu____624 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____624  in
                   FStar_Pprint.op_Hat_Hat sep uu____623  in
                 FStar_Pprint.op_Hat_Hat break1 uu____622) uu____616
             in
          FStar_Pprint.op_Hat_Hat uu____611 uu____615
  
let concat_break_map :
  'Auu____632 .
    ('Auu____632 -> FStar_Pprint.document) ->
      'Auu____632 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____652 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____656 = f x  in FStar_Pprint.op_Hat_Hat uu____656 break1)
          l
         in
      FStar_Pprint.group uu____652
  
let (parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (soft_parens_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting_tight :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    let uu____719 = str "begin"  in
    let uu____721 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____719 contents uu____721
  
let separate_map_last :
  'Auu____734 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____734 -> FStar_Pprint.document) ->
        'Auu____734 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun es  ->
        let l = FStar_List.length es  in
        let es1 =
          FStar_List.mapi
            (fun i  -> fun e  -> f (i <> (l - (Prims.parse_int "1"))) e) es
           in
        FStar_Pprint.separate sep es1
  
let separate_break_map_last :
  'Auu____792 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____792 -> FStar_Pprint.document) ->
        'Auu____792 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____824 =
          let uu____825 =
            let uu____826 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____826  in
          separate_map_last uu____825 f l  in
        FStar_Pprint.group uu____824
  
let separate_map_or_flow :
  'Auu____836 .
    FStar_Pprint.document ->
      ('Auu____836 -> FStar_Pprint.document) ->
        'Auu____836 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____874 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____874 -> FStar_Pprint.document) ->
        'Auu____874 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun es  ->
        let l = FStar_List.length es  in
        let es1 =
          FStar_List.mapi
            (fun i  -> fun e  -> f (i <> (l - (Prims.parse_int "1"))) e) es
           in
        FStar_Pprint.flow sep es1
  
let separate_map_or_flow_last :
  'Auu____932 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____932 -> FStar_Pprint.document) ->
        'Auu____932 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then separate_map_last sep f l
        else flow_map_last sep f l
  
let (separate_or_flow :
  FStar_Pprint.document ->
    FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  = fun sep  -> fun l  -> separate_map_or_flow sep FStar_Pervasives.id l 
let (surround_maybe_empty :
  Prims.int ->
    Prims.int ->
      FStar_Pprint.document ->
        FStar_Pprint.document ->
          FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun n1  ->
    fun b  ->
      fun doc1  ->
        fun doc2  ->
          fun doc3  ->
            if doc2 = FStar_Pprint.empty
            then
              let uu____1014 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____1014
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____1036 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1036 -> FStar_Pprint.document) ->
                  'Auu____1036 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____1095 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1095
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____1115 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1115 -> FStar_Pprint.document) ->
                  'Auu____1115 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____1174 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1174
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____1193  ->
    match uu____1193 with
    | (comment,keywords) ->
        let uu____1227 =
          let uu____1228 =
            let uu____1231 = str comment  in
            let uu____1232 =
              let uu____1235 =
                let uu____1238 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1249  ->
                       match uu____1249 with
                       | (k,v1) ->
                           let uu____1262 =
                             let uu____1265 = str k  in
                             let uu____1266 =
                               let uu____1269 =
                                 let uu____1272 = str v1  in [uu____1272]  in
                               FStar_Pprint.rarrow :: uu____1269  in
                             uu____1265 :: uu____1266  in
                           FStar_Pprint.concat uu____1262) keywords
                   in
                [uu____1238]  in
              FStar_Pprint.space :: uu____1235  in
            uu____1231 :: uu____1232  in
          FStar_Pprint.concat uu____1228  in
        FStar_Pprint.group uu____1227
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1282 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1298 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1298
      | uu____1301 -> false
  
let (is_tuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_tuple_data_lid' 
let (is_dtuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_dtuple_data_lid' 
let (is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool)
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____1352::(e2,uu____1354)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1377 -> false  in
      aux
  
let (is_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let (is_lex_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec (extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (uu____1401,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1412,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1433 = extract_from_list e2  in e1 :: uu____1433
    | uu____1436 ->
        let uu____1437 =
          let uu____1439 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1439  in
        failwith uu____1437
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1453;
           FStar_Parser_AST.level = uu____1454;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1456 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1468;
           FStar_Parser_AST.level = uu____1469;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1471;
                                                         FStar_Parser_AST.level
                                                           = uu____1472;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1474;
                                                    FStar_Parser_AST.level =
                                                      uu____1475;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Parser_Const.set_singleton)
          &&
          (FStar_Ident.lid_equals maybe_addr_of_lid
             FStar_Parser_Const.heap_addr_of_lid)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____1477;
                FStar_Parser_AST.level = uu____1478;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1480;
           FStar_Parser_AST.level = uu____1481;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1483 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1495 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1496;
           FStar_Parser_AST.range = uu____1497;
           FStar_Parser_AST.level = uu____1498;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1499;
                                                         FStar_Parser_AST.range
                                                           = uu____1500;
                                                         FStar_Parser_AST.level
                                                           = uu____1501;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1503;
                                                    FStar_Parser_AST.level =
                                                      uu____1504;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1505;
                FStar_Parser_AST.range = uu____1506;
                FStar_Parser_AST.level = uu____1507;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1509;
           FStar_Parser_AST.level = uu____1510;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1512 = extract_from_ref_set e1  in
        let uu____1515 = extract_from_ref_set e2  in
        FStar_List.append uu____1512 uu____1515
    | uu____1518 ->
        let uu____1519 =
          let uu____1521 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1521  in
        failwith uu____1519
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1533 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1533
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1542 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1542
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1553 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1553 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1563 = FStar_Ident.text_of_id op  in uu____1563 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1633 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1653 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1664 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1675 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___111_1701  ->
    match uu___111_1701 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___112_1736  ->
      match uu___112_1736 with
      | FStar_Util.Inl c ->
          let uu____1749 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1749 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1765 .
    Prims.string ->
      ('Auu____1765 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1789  ->
      match uu____1789 with
      | (assoc_levels,tokens) ->
          let uu____1821 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1821 <> FStar_Pervasives_Native.None
  
let (opinfix4 : associativity_level) = (Right, [FStar_Util.Inr "**"]) 
let (opinfix3 : associativity_level) =
  (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37]) 
let (opinfix2 : associativity_level) =
  (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let (minus_lvl : associativity_level) = (Left, [FStar_Util.Inr "-"]) 
let (opinfix1 : associativity_level) =
  (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let (pipe_right : associativity_level) = (Left, [FStar_Util.Inr "|>"]) 
let (opinfix0d : associativity_level) = (Left, [FStar_Util.Inl 36]) 
let (opinfix0c : associativity_level) =
  (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62]) 
let (equal : associativity_level) = (Left, [FStar_Util.Inr "="]) 
let (opinfix0b : associativity_level) = (Left, [FStar_Util.Inl 38]) 
let (opinfix0a : associativity_level) = (Left, [FStar_Util.Inl 124]) 
let (colon_equals : associativity_level) = (NonAssoc, [FStar_Util.Inr ":="]) 
let (amp : associativity_level) = (Right, [FStar_Util.Inr "&"]) 
let (colon_colon : associativity_level) = (Right, [FStar_Util.Inr "::"]) 
let (level_associativity_spec : associativity_level Prims.list) =
  [opinfix4;
  opinfix3;
  opinfix2;
  opinfix1;
  pipe_right;
  opinfix0d;
  opinfix0c;
  opinfix0b;
  opinfix0a;
  colon_equals;
  amp;
  colon_colon] 
let (level_table :
  ((Prims.int * Prims.int * Prims.int) * token Prims.list) Prims.list) =
  let levels_from_associativity l uu___113_1993 =
    match uu___113_1993 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____2043  ->
         match uu____2043 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2118 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2118 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2170) ->
          assoc_levels
      | uu____2208 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max_level :
  'Auu____2241 . ('Auu____2241 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2290 =
        FStar_List.tryFind
          (fun uu____2326  ->
             match uu____2326 with
             | (uu____2343,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2290 with
      | FStar_Pervasives_Native.Some ((uu____2372,l1,uu____2374),uu____2375)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2425 =
            let uu____2427 =
              let uu____2429 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2429  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2427
             in
          failwith uu____2425
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2464 = assign_levels level_associativity_spec op  in
    match uu____2464 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2523 =
      let uu____2526 =
        let uu____2532 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2532  in
      FStar_List.tryFind uu____2526 operatorInfix0ad12  in
    uu____2523 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2599 =
      let uu____2614 =
        let uu____2632 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2632  in
      FStar_List.tryFind uu____2614 opinfix34  in
    uu____2599 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2698 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2698
    then (Prims.parse_int "1")
    else
      (let uu____2711 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2711
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2757 . FStar_Ident.ident -> 'Auu____2757 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_1 when _0_1 = (Prims.parse_int "0") -> true
      | _0_2 when _0_2 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2775 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2775 ["-"; "~"])
      | _0_3 when _0_3 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2784 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2784
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_4 when _0_4 = (Prims.parse_int "3") ->
          let uu____2806 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2806 [".()<-"; ".[]<-"]
      | uu____2814 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2860 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2913 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2956 -> true
      | uu____2962 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2995 = FStar_List.for_all is_binder_annot bs  in
          if uu____2995
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____3010 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____3015 = all_binders e (Prims.parse_int "0")  in
    match uu____3015 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____3054 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____3054
  
let (comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
type decl_meta =
  {
  r: FStar_Range.range ;
  has_qs: Prims.bool ;
  has_attrs: Prims.bool ;
  has_fsdoc: Prims.bool ;
  is_fsdoc: Prims.bool }
let (__proj__Mkdecl_meta__item__r : decl_meta -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> r
  
let (__proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_qs
  
let (__proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_attrs
  
let (__proj__Mkdecl_meta__item__has_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_fsdoc
  
let (__proj__Mkdecl_meta__item__is_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> is_fsdoc
  
let (dummy_meta : decl_meta) =
  {
    r = FStar_Range.dummyRange;
    has_qs = false;
    has_attrs = false;
    has_fsdoc = false;
    is_fsdoc = false
  } 
let with_comment :
  'Auu____3214 .
    ('Auu____3214 -> FStar_Pprint.document) ->
      'Auu____3214 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3256 = FStar_ST.op_Bang comment_stack  in
          match uu____3256 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3327 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3327 FStar_Pprint.hardline  in
              let uu____3328 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3328
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3370 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3370 print_pos lookahead_pos))
              else
                (let uu____3373 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3373))
           in
        let uu____3376 =
          let uu____3382 =
            let uu____3383 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3383  in
          let uu____3384 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3382 uu____3384  in
        match uu____3376 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3393 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3393
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3405 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3405)
  
let with_comment_sep :
  'Auu____3417 'Auu____3418 .
    ('Auu____3417 -> 'Auu____3418) ->
      'Auu____3417 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3418)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3464 = FStar_ST.op_Bang comment_stack  in
          match uu____3464 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3535 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3535
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3577 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3581 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3581)
                     in
                  comments_before_pos uu____3577 print_pos lookahead_pos))
              else
                (let uu____3584 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3584))
           in
        let uu____3587 =
          let uu____3593 =
            let uu____3594 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3594  in
          let uu____3595 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3593 uu____3595  in
        match uu____3587 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3608 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3608
              else comments  in
            (comments1, printed_e)
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos ->
        decl_meta ->
          FStar_Pprint.document ->
            Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos  ->
        fun meta_decl  ->
          fun doc1  ->
            fun r  ->
              fun init1  ->
                let uu____3661 = FStar_ST.op_Bang comment_stack  in
                match uu____3661 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3755 =
                          let uu____3757 =
                            let uu____3759 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3759  in
                          uu____3757 - lbegin  in
                        max k uu____3755  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____3764 =
                          let uu____3765 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3766 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3765 uu____3766  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3764  in
                      let uu____3767 =
                        let uu____3769 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3769  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____3767 pos meta_decl doc2 true init1))
                | uu____3772 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3785 = FStar_Range.line_of_pos pos  in
                         uu____3785 - lbegin  in
                       let lnum1 = min (Prims.parse_int "3") lnum  in
                       let lnum2 =
                         if meta_decl.has_qs || meta_decl.has_attrs
                         then lnum1 - (Prims.parse_int "1")
                         else lnum1  in
                       let lnum3 = max k lnum2  in
                       let lnum4 =
                         if meta_decl.has_qs && meta_decl.has_attrs
                         then (Prims.parse_int "2")
                         else lnum3  in
                       let lnum5 =
                         if (Prims.op_Negation r) && meta_decl.has_fsdoc
                         then min (Prims.parse_int "2") lnum4
                         else lnum4  in
                       let lnum6 =
                         if r && (meta_decl.is_fsdoc || meta_decl.has_fsdoc)
                         then (Prims.parse_int "1")
                         else lnum5  in
                       let lnum7 =
                         if init1 then (Prims.parse_int "2") else lnum6  in
                       let uu____3827 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3827)
  
let separate_map_with_comments :
  'Auu____3841 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3841 -> FStar_Pprint.document) ->
          'Auu____3841 Prims.list ->
            ('Auu____3841 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3900 x =
              match uu____3900 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3919 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3919 meta_decl doc1 false false
                     in
                  let uu____3923 =
                    let uu____3925 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3925  in
                  let uu____3926 =
                    let uu____3927 =
                      let uu____3928 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3928  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3927  in
                  (uu____3923, uu____3926)
               in
            let uu____3930 =
              let uu____3937 = FStar_List.hd xs  in
              let uu____3938 = FStar_List.tl xs  in (uu____3937, uu____3938)
               in
            match uu____3930 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3956 =
                    let uu____3958 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3958  in
                  let uu____3959 =
                    let uu____3960 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3960  in
                  (uu____3956, uu____3959)  in
                let uu____3962 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3962
  
let separate_map_with_comments_kw :
  'Auu____3989 'Auu____3990 .
    'Auu____3989 ->
      'Auu____3989 ->
        ('Auu____3989 -> 'Auu____3990 -> FStar_Pprint.document) ->
          'Auu____3990 Prims.list ->
            ('Auu____3990 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4054 x =
              match uu____4054 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4073 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____4073 meta_decl doc1 false false
                     in
                  let uu____4077 =
                    let uu____4079 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4079  in
                  let uu____4080 =
                    let uu____4081 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4081  in
                  (uu____4077, uu____4080)
               in
            let uu____4083 =
              let uu____4090 = FStar_List.hd xs  in
              let uu____4091 = FStar_List.tl xs  in (uu____4090, uu____4091)
               in
            match uu____4083 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4109 =
                    let uu____4111 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4111  in
                  let uu____4112 = f prefix1 x  in (uu____4109, uu____4112)
                   in
                let uu____4114 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4114
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____5100)) ->
          let uu____5103 =
            let uu____5105 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5105 FStar_Util.is_upper  in
          if uu____5103
          then
            let uu____5111 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5111 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5114 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5121 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5124 =
      let uu____5125 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5126 =
        let uu____5127 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5127  in
      FStar_Pprint.op_Hat_Hat uu____5125 uu____5126  in
    FStar_Pprint.op_Hat_Hat uu____5121 uu____5124

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5129 ->
        let uu____5130 =
          let uu____5131 = str "@ "  in
          let uu____5133 =
            let uu____5134 =
              let uu____5135 =
                let uu____5136 =
                  let uu____5137 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5137  in
                FStar_Pprint.op_Hat_Hat uu____5136 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5135  in
            FStar_Pprint.op_Hat_Hat uu____5134 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5131 uu____5133  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5130

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5140  ->
    match uu____5140 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5188 =
                match uu____5188 with
                | (kwd,arg) ->
                    let uu____5201 = str "@"  in
                    let uu____5203 =
                      let uu____5204 = str kwd  in
                      let uu____5205 =
                        let uu____5206 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5206
                         in
                      FStar_Pprint.op_Hat_Hat uu____5204 uu____5205  in
                    FStar_Pprint.op_Hat_Hat uu____5201 uu____5203
                 in
              let uu____5207 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5207 FStar_Pprint.hardline
           in
        let uu____5214 =
          let uu____5215 =
            let uu____5216 =
              let uu____5217 = str doc1  in
              let uu____5218 =
                let uu____5219 =
                  let uu____5220 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5220  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5219  in
              FStar_Pprint.op_Hat_Hat uu____5217 uu____5218  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5216  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5215  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5214

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5224 =
          let uu____5225 = str "val"  in
          let uu____5227 =
            let uu____5228 =
              let uu____5229 = p_lident lid  in
              let uu____5230 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5229 uu____5230  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5228  in
          FStar_Pprint.op_Hat_Hat uu____5225 uu____5227  in
        let uu____5231 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5224 uu____5231
    | FStar_Parser_AST.TopLevelLet (uu____5234,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5259 =
               let uu____5260 = str "let"  in p_letlhs uu____5260 lb false
                in
             FStar_Pprint.group uu____5259) lbs
    | uu____5263 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___114_5278 =
          match uu___114_5278 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5286 = f x  in
              let uu____5287 =
                let uu____5288 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5288  in
              FStar_Pprint.op_Hat_Hat uu____5286 uu____5287
           in
        let uu____5289 = str "["  in
        let uu____5291 =
          let uu____5292 = p_list' l  in
          let uu____5293 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5292 uu____5293  in
        FStar_Pprint.op_Hat_Hat uu____5289 uu____5291

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5297 =
          let uu____5298 = str "open"  in
          let uu____5300 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5298 uu____5300  in
        FStar_Pprint.group uu____5297
    | FStar_Parser_AST.Include uid ->
        let uu____5302 =
          let uu____5303 = str "include"  in
          let uu____5305 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5303 uu____5305  in
        FStar_Pprint.group uu____5302
    | FStar_Parser_AST.Friend uid ->
        let uu____5307 =
          let uu____5308 = str "friend"  in
          let uu____5310 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5308 uu____5310  in
        FStar_Pprint.group uu____5307
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5313 =
          let uu____5314 = str "module"  in
          let uu____5316 =
            let uu____5317 =
              let uu____5318 = p_uident uid1  in
              let uu____5319 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5318 uu____5319  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5317  in
          FStar_Pprint.op_Hat_Hat uu____5314 uu____5316  in
        let uu____5320 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5313 uu____5320
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5322 =
          let uu____5323 = str "module"  in
          let uu____5325 =
            let uu____5326 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5326  in
          FStar_Pprint.op_Hat_Hat uu____5323 uu____5325  in
        FStar_Pprint.group uu____5322
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5327,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5364 = str "effect"  in
          let uu____5366 =
            let uu____5367 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5367  in
          FStar_Pprint.op_Hat_Hat uu____5364 uu____5366  in
        let uu____5368 =
          let uu____5369 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5369 FStar_Pprint.equals
           in
        let uu____5372 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5368 uu____5372
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5403 =
          let uu____5404 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5404  in
        let uu____5417 =
          let uu____5418 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5456 =
                    let uu____5457 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5457 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5456)) uu____5418
           in
        FStar_Pprint.op_Hat_Hat uu____5403 uu____5417
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5474 = str "let"  in
          let uu____5476 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5474 uu____5476  in
        let uu____5477 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5477 p_letbinding lbs
          (fun uu____5487  ->
             match uu____5487 with
             | (p,t) ->
                 let uu____5494 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5494;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5500 =
          let uu____5501 = str "val"  in
          let uu____5503 =
            let uu____5504 =
              let uu____5505 = p_lident lid  in
              let uu____5506 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5505 uu____5506  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5504  in
          FStar_Pprint.op_Hat_Hat uu____5501 uu____5503  in
        FStar_All.pipe_left FStar_Pprint.group uu____5500
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5511 =
            let uu____5513 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5513 FStar_Util.is_upper  in
          if uu____5511
          then FStar_Pprint.empty
          else
            (let uu____5521 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5521 FStar_Pprint.space)
           in
        let uu____5523 =
          let uu____5524 = p_ident id1  in
          let uu____5525 =
            let uu____5526 =
              let uu____5527 =
                let uu____5528 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5528  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5527  in
            FStar_Pprint.group uu____5526  in
          FStar_Pprint.op_Hat_Hat uu____5524 uu____5525  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5523
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5537 = str "exception"  in
        let uu____5539 =
          let uu____5540 =
            let uu____5541 = p_uident uid  in
            let uu____5542 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5546 =
                     let uu____5547 = str "of"  in
                     let uu____5549 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5547 uu____5549  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5546) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5541 uu____5542  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5540  in
        FStar_Pprint.op_Hat_Hat uu____5537 uu____5539
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5553 = str "new_effect"  in
        let uu____5555 =
          let uu____5556 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5556  in
        FStar_Pprint.op_Hat_Hat uu____5553 uu____5555
    | FStar_Parser_AST.SubEffect se ->
        let uu____5558 = str "sub_effect"  in
        let uu____5560 =
          let uu____5561 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5561  in
        FStar_Pprint.op_Hat_Hat uu____5558 uu____5560
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5564 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5566,uu____5567) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5595 = str "%splice"  in
        let uu____5597 =
          let uu____5598 =
            let uu____5599 = str ";"  in p_list p_uident uu____5599 ids  in
          let uu____5601 =
            let uu____5602 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5602  in
          FStar_Pprint.op_Hat_Hat uu____5598 uu____5601  in
        FStar_Pprint.op_Hat_Hat uu____5595 uu____5597

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___115_5605  ->
    match uu___115_5605 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5608 = str "#set-options"  in
        let uu____5610 =
          let uu____5611 =
            let uu____5612 = str s  in FStar_Pprint.dquotes uu____5612  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5611  in
        FStar_Pprint.op_Hat_Hat uu____5608 uu____5610
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5617 = str "#reset-options"  in
        let uu____5619 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5625 =
                 let uu____5626 = str s  in FStar_Pprint.dquotes uu____5626
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5625) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5617 uu____5619
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5631 = str "#push-options"  in
        let uu____5633 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5639 =
                 let uu____5640 = str s  in FStar_Pprint.dquotes uu____5640
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5639) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5631 uu____5633
    | FStar_Parser_AST.PopOptions  -> str "#pop-options"
    | FStar_Parser_AST.RestartSolver  -> str "#restart-solver"
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5672  ->
      match uu____5672 with
      | (typedecl,fsdoc_opt) ->
          let uu____5685 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5685 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5710 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5710
               else
                 (let uu____5713 =
                    let uu____5714 =
                      let uu____5715 =
                        let uu____5716 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5716 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5715  in
                    let uu____5717 =
                      let uu____5718 =
                        let uu____5719 =
                          let uu____5720 =
                            let uu____5721 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5721  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5720
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5719
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5718  in
                    FStar_Pprint.ifflat uu____5714 uu____5717  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5713))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___116_5724  ->
      match uu___116_5724 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5753 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5753, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5770 = p_typ_sep false false t  in
          (match uu____5770 with
           | (comm,doc1) ->
               let uu____5790 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5790, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5846 =
            match uu____5846 with
            | (lid1,t,doc_opt) ->
                let uu____5863 =
                  let uu____5868 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5868
                   in
                (match uu____5863 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5886 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5886  in
          let uu____5895 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5895, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5962 =
            match uu____5962 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5991 =
                    let uu____5992 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5992  in
                  FStar_Range.extend_to_end_of_line uu____5991  in
                let uu____5997 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5997 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____6036 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6036, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6041  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6041 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6076 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6076  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6078 =
                        let uu____6081 =
                          let uu____6084 = p_fsdoc fsdoc  in
                          let uu____6085 =
                            let uu____6088 = cont lid_doc  in [uu____6088]
                             in
                          uu____6084 :: uu____6085  in
                        kw :: uu____6081  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6078
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6095 =
                        let uu____6096 =
                          let uu____6097 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6097 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6096
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6095
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6117 =
                          let uu____6118 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6118  in
                        prefix2 uu____6117 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6120  ->
      match uu____6120 with
      | (lid,t,doc_opt) ->
          let uu____6137 =
            let uu____6138 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6139 =
              let uu____6140 = p_lident lid  in
              let uu____6141 =
                let uu____6142 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6142  in
              FStar_Pprint.op_Hat_Hat uu____6140 uu____6141  in
            FStar_Pprint.op_Hat_Hat uu____6138 uu____6139  in
          FStar_Pprint.group uu____6137

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6144  ->
    match uu____6144 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6178 =
            let uu____6179 =
              let uu____6180 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6180  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6179  in
          FStar_Pprint.group uu____6178  in
        let uu____6181 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6182 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6186 =
                 let uu____6187 =
                   let uu____6188 =
                     let uu____6189 =
                       let uu____6190 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6190
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6189  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6188  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6187  in
               FStar_Pprint.group uu____6186) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6181 uu____6182

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6194  ->
      fun inner_let  ->
        match uu____6194 with
        | (pat,uu____6202) ->
            let uu____6203 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6255 =
                    let uu____6262 =
                      let uu____6267 =
                        let uu____6268 =
                          let uu____6269 =
                            let uu____6270 = str "by"  in
                            let uu____6272 =
                              let uu____6273 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6273
                               in
                            FStar_Pprint.op_Hat_Hat uu____6270 uu____6272  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6269
                           in
                        FStar_Pprint.group uu____6268  in
                      (t, uu____6267)  in
                    FStar_Pervasives_Native.Some uu____6262  in
                  (pat1, uu____6255)
              | uu____6284 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6203 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6310);
                         FStar_Parser_AST.prange = uu____6311;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6328 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6328 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6334 =
                        if inner_let
                        then
                          let uu____6348 = pats_as_binders_if_possible pats
                             in
                          match uu____6348 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6371 = pats_as_binders_if_possible pats
                              in
                           match uu____6371 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6334 with
                       | (terms,style) ->
                           let uu____6398 =
                             let uu____6399 =
                               let uu____6400 =
                                 let uu____6401 = p_lident lid  in
                                 let uu____6402 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6401
                                   uu____6402
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6400
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6399  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6398)
                  | uu____6405 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6413 =
                              let uu____6414 =
                                let uu____6415 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6415
                                 in
                              FStar_Pprint.group uu____6414  in
                            FStar_Pprint.op_Hat_Hat uu____6413 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6426 =
                        let uu____6427 =
                          let uu____6428 =
                            let uu____6429 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6429  in
                          FStar_Pprint.group uu____6428  in
                        FStar_Pprint.op_Hat_Hat uu____6427 ascr_doc  in
                      FStar_Pprint.group uu____6426))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6431  ->
      match uu____6431 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6440 = p_term_sep false false e  in
          (match uu____6440 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6450 =
                 let uu____6451 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6451  in
               let uu____6452 =
                 let uu____6453 =
                   let uu____6454 =
                     let uu____6455 =
                       let uu____6456 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6456
                        in
                     FStar_Pprint.group uu____6455  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6454  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6453  in
               FStar_Pprint.ifflat uu____6450 uu____6452)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___117_6457  ->
    match uu___117_6457 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls

and (p_effectRedefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____6482 = p_uident uid  in
        let uu____6483 = p_binders true bs  in
        let uu____6485 =
          let uu____6486 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6486  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6482 uu____6483 uu____6485

and (p_effectDefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document)
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let binders = p_binders true bs  in
          let uu____6501 =
            let uu____6502 =
              let uu____6503 =
                let uu____6504 = p_uident uid  in
                let uu____6505 = p_binders true bs  in
                let uu____6507 =
                  let uu____6508 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6508  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6504 uu____6505 uu____6507
                 in
              FStar_Pprint.group uu____6503  in
            let uu____6513 =
              let uu____6514 = str "with"  in
              let uu____6516 =
                let uu____6517 =
                  let uu____6518 =
                    let uu____6519 =
                      let uu____6520 =
                        let uu____6521 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6521
                         in
                      separate_map_last uu____6520 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6519  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6518  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6517  in
              FStar_Pprint.op_Hat_Hat uu____6514 uu____6516  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6502 uu____6513  in
          braces_with_nesting uu____6501

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6525,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6558 =
            let uu____6559 = p_lident lid  in
            let uu____6560 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6559 uu____6560  in
          let uu____6561 = p_simpleTerm ps false e  in
          prefix2 uu____6558 uu____6561
      | uu____6563 ->
          let uu____6564 =
            let uu____6566 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6566
             in
          failwith uu____6564

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6649 =
        match uu____6649 with
        | (kwd,t) ->
            let uu____6660 =
              let uu____6661 = str kwd  in
              let uu____6662 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6661 uu____6662  in
            let uu____6663 = p_simpleTerm ps false t  in
            prefix2 uu____6660 uu____6663
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6670 =
      let uu____6671 =
        let uu____6672 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6673 =
          let uu____6674 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6674  in
        FStar_Pprint.op_Hat_Hat uu____6672 uu____6673  in
      let uu____6676 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6671 uu____6676  in
    let uu____6677 =
      let uu____6678 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6678  in
    FStar_Pprint.op_Hat_Hat uu____6670 uu____6677

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___118_6679  ->
    match uu___118_6679 with
    | FStar_Parser_AST.Private  -> str "private"
    | FStar_Parser_AST.Abstract  -> str "abstract"
    | FStar_Parser_AST.Noeq  -> str "noeq"
    | FStar_Parser_AST.Unopteq  -> str "unopteq"
    | FStar_Parser_AST.Assumption  -> str "assume"
    | FStar_Parser_AST.DefaultEffect  -> str "default"
    | FStar_Parser_AST.TotalEffect  -> str "total"
    | FStar_Parser_AST.Effect_qual  -> FStar_Pprint.empty
    | FStar_Parser_AST.New  -> str "new"
    | FStar_Parser_AST.Inline  -> str "inline"
    | FStar_Parser_AST.Visible  -> FStar_Pprint.empty
    | FStar_Parser_AST.Unfold_for_unification_and_vcgen  -> str "unfold"
    | FStar_Parser_AST.Inline_for_extraction  -> str "inline_for_extraction"
    | FStar_Parser_AST.Irreducible  -> str "irreducible"
    | FStar_Parser_AST.NoExtract  -> str "noextract"
    | FStar_Parser_AST.Reifiable  -> str "reifiable"
    | FStar_Parser_AST.Reflectable  -> str "reflectable"
    | FStar_Parser_AST.Opaque  -> str "opaque"
    | FStar_Parser_AST.Logic  -> str "logic"

and (p_qualifiers : FStar_Parser_AST.qualifiers -> FStar_Pprint.document) =
  fun qs  ->
    match qs with
    | [] -> FStar_Pprint.empty
    | q::[] ->
        let uu____6699 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6699 FStar_Pprint.hardline
    | uu____6700 ->
        let uu____6701 =
          let uu____6702 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6702  in
        FStar_Pprint.op_Hat_Hat uu____6701 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___119_6705  ->
    match uu___119_6705 with
    | FStar_Parser_AST.Rec  ->
        let uu____6706 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6706
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___120_6708  ->
    match uu___120_6708 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6713,e) -> e
          | uu____6719 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6720 = str "#["  in
        let uu____6722 =
          let uu____6723 = p_term false false t1  in
          let uu____6726 =
            let uu____6727 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6727 break1  in
          FStar_Pprint.op_Hat_Hat uu____6723 uu____6726  in
        FStar_Pprint.op_Hat_Hat uu____6720 uu____6722

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6733 =
          let uu____6734 =
            let uu____6735 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6735  in
          FStar_Pprint.separate_map uu____6734 p_tuplePattern pats  in
        FStar_Pprint.group uu____6733
    | uu____6736 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6745 =
          let uu____6746 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6746 p_constructorPattern pats  in
        FStar_Pprint.group uu____6745
    | uu____6747 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6750;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6755 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6756 = p_constructorPattern hd1  in
        let uu____6757 = p_constructorPattern tl1  in
        infix0 uu____6755 uu____6756 uu____6757
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6759;_},pats)
        ->
        let uu____6765 = p_quident uid  in
        let uu____6766 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6765 uu____6766
    | uu____6767 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6783;
               FStar_Parser_AST.blevel = uu____6784;
               FStar_Parser_AST.aqual = uu____6785;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6794 =
               let uu____6795 = p_ident lid  in
               p_refinement aqual uu____6795 t1 phi  in
             soft_parens_with_nesting uu____6794
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6798;
               FStar_Parser_AST.blevel = uu____6799;
               FStar_Parser_AST.aqual = uu____6800;_},phi))
             ->
             let uu____6806 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6806
         | uu____6807 ->
             let uu____6812 =
               let uu____6813 = p_tuplePattern pat  in
               let uu____6814 =
                 let uu____6815 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6815
                  in
               FStar_Pprint.op_Hat_Hat uu____6813 uu____6814  in
             soft_parens_with_nesting uu____6812)
    | FStar_Parser_AST.PatList pats ->
        let uu____6819 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6819 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6838 =
          match uu____6838 with
          | (lid,pat) ->
              let uu____6845 = p_qlident lid  in
              let uu____6846 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6845 uu____6846
           in
        let uu____6847 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6847
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6859 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6860 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6861 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6859 uu____6860 uu____6861
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6872 =
          let uu____6873 =
            let uu____6874 =
              let uu____6875 = FStar_Ident.text_of_id op  in str uu____6875
               in
            let uu____6877 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6874 uu____6877  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6873  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6872
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6881 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6881 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6889 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6890 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6889 uu____6890
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6892 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6896;
           FStar_Parser_AST.prange = uu____6897;_},uu____6898)
        ->
        let uu____6903 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6903
    | FStar_Parser_AST.PatTuple (uu____6904,false ) ->
        let uu____6911 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6911
    | uu____6912 ->
        let uu____6913 =
          let uu____6915 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6915  in
        failwith uu____6913

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6920;_},uu____6921)
        -> true
    | uu____6928 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6934) -> true
    | uu____6936 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6943 = p_binder' is_atomic b  in
      match uu____6943 with
      | (b',t',catf) ->
          (match t' with
           | FStar_Pervasives_Native.Some typ -> catf b' typ
           | FStar_Pervasives_Native.None  -> b')

and (p_binder' :
  Prims.bool ->
    FStar_Parser_AST.binder ->
      (FStar_Pprint.document * FStar_Pprint.document
        FStar_Pervasives_Native.option * catf))
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____6982 =
            let uu____6983 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6984 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6983 uu____6984  in
          (uu____6982, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6990 = p_lident lid  in
          (uu____6990, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6997 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____7008;
                   FStar_Parser_AST.blevel = uu____7009;
                   FStar_Parser_AST.aqual = uu____7010;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____7015 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____7015 t1 phi
            | uu____7016 ->
                let t' =
                  let uu____7018 = is_typ_tuple t  in
                  if uu____7018
                  then
                    let uu____7021 = p_tmFormula t  in
                    soft_parens_with_nesting uu____7021
                  else p_tmFormula t  in
                let uu____7024 =
                  let uu____7025 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____7026 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____7025 uu____7026  in
                (uu____7024, t')
             in
          (match uu____6997 with
           | (b',t') ->
               let catf =
                 let uu____7044 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7044
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7051 =
                         let uu____7052 =
                           let uu____7053 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7053
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7052
                          in
                       FStar_Pprint.group uu____7051
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7058 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7058)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7067 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7095;
                  FStar_Parser_AST.blevel = uu____7096;
                  FStar_Parser_AST.aqual = uu____7097;_},phi)
               ->
               let uu____7101 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7101 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7122 ->
               if is_atomic
               then
                 let uu____7134 = p_atomicTerm t  in
                 (uu____7134, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7141 = p_appTerm t  in
                  (uu____7141, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7152 = p_refinement' aqual_opt binder t phi  in
          match uu____7152 with | (b,typ) -> cat_with_colon b typ

and (p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.term ->
          (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____7168 -> false
            | FStar_Parser_AST.App uu____7180 -> false
            | FStar_Parser_AST.Op uu____7188 -> false
            | uu____7196 -> true  in
          let uu____7198 = p_noSeqTerm false false phi  in
          match uu____7198 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7215 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7215)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____7224 =
                let uu____7225 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7225 binder  in
              let uu____7226 =
                let uu____7227 = p_appTerm t  in
                let uu____7228 =
                  let uu____7229 =
                    let uu____7230 =
                      let uu____7231 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7232 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7231 uu____7232  in
                    FStar_Pprint.group uu____7230  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____7229
                   in
                FStar_Pprint.op_Hat_Hat uu____7227 uu____7228  in
              (uu____7224, uu____7226)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7246 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7246

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7250 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7253 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7253)
       in
    if uu____7250
    then FStar_Pprint.underscore
    else (let uu____7258 = FStar_Ident.text_of_id lid  in str uu____7258)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7261 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7264 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7264)
       in
    if uu____7261
    then FStar_Pprint.underscore
    else (let uu____7269 = FStar_Ident.text_of_lid lid  in str uu____7269)

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (paren_if : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document)
  = fun b  -> if b then soft_parens_with_nesting else (fun x  -> x)

and (inline_comment_or_above :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun comm  ->
    fun doc1  ->
      fun sep  ->
        if comm = FStar_Pprint.empty
        then
          let uu____7290 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7290
        else
          (let uu____7293 =
             let uu____7294 =
               let uu____7295 =
                 let uu____7296 =
                   let uu____7297 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7297  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7296  in
               FStar_Pprint.group uu____7295  in
             let uu____7298 =
               let uu____7299 =
                 let uu____7300 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7300  in
               FStar_Pprint.op_Hat_Hat comm uu____7299  in
             FStar_Pprint.ifflat uu____7294 uu____7298  in
           FStar_All.pipe_left FStar_Pprint.group uu____7293)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7308 = p_noSeqTerm true false e1  in
            (match uu____7308 with
             | (comm,t1) ->
                 let uu____7317 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7318 =
                   let uu____7319 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7319
                    in
                 FStar_Pprint.op_Hat_Hat uu____7317 uu____7318)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7323 =
              let uu____7324 =
                let uu____7325 =
                  let uu____7326 = p_lident x  in
                  let uu____7327 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7326 uu____7327  in
                let uu____7328 =
                  let uu____7329 = p_noSeqTermAndComment true false e1  in
                  let uu____7332 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7329 uu____7332  in
                op_Hat_Slash_Plus_Hat uu____7325 uu____7328  in
              FStar_Pprint.group uu____7324  in
            let uu____7333 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7323 uu____7333
        | uu____7334 ->
            let uu____7335 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7335

and (p_term_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7347 = p_noSeqTerm true false e1  in
            (match uu____7347 with
             | (comm,t1) ->
                 let uu____7360 =
                   let uu____7361 =
                     let uu____7362 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7362  in
                   let uu____7363 =
                     let uu____7364 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7364
                      in
                   FStar_Pprint.op_Hat_Hat uu____7361 uu____7363  in
                 (comm, uu____7360))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7368 =
              let uu____7369 =
                let uu____7370 =
                  let uu____7371 =
                    let uu____7372 = p_lident x  in
                    let uu____7373 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7372 uu____7373  in
                  let uu____7374 =
                    let uu____7375 = p_noSeqTermAndComment true false e1  in
                    let uu____7378 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7375 uu____7378  in
                  op_Hat_Slash_Plus_Hat uu____7371 uu____7374  in
                FStar_Pprint.group uu____7370  in
              let uu____7379 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7369 uu____7379  in
            (FStar_Pprint.empty, uu____7368)
        | uu____7380 -> p_noSeqTerm ps pb e

and (p_noSeqTerm :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment_sep (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and (p_noSeqTermAndComment :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and (p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
            let uu____7400 =
              let uu____7401 = p_tmIff e1  in
              let uu____7402 =
                let uu____7403 =
                  let uu____7404 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7404
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7403  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7401 uu____7402  in
            FStar_Pprint.group uu____7400
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7410 =
              let uu____7411 = p_tmIff e1  in
              let uu____7412 =
                let uu____7413 =
                  let uu____7414 =
                    let uu____7415 = p_typ false false t  in
                    let uu____7418 =
                      let uu____7419 = str "by"  in
                      let uu____7421 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7419 uu____7421  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7415 uu____7418  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7414
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7413  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7411 uu____7412  in
            FStar_Pprint.group uu____7410
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7422;_},e1::e2::e3::[])
            ->
            let uu____7429 =
              let uu____7430 =
                let uu____7431 =
                  let uu____7432 = p_atomicTermNotQUident e1  in
                  let uu____7433 =
                    let uu____7434 =
                      let uu____7435 =
                        let uu____7436 = p_term false false e2  in
                        soft_parens_with_nesting uu____7436  in
                      let uu____7439 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7435 uu____7439  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7434  in
                  FStar_Pprint.op_Hat_Hat uu____7432 uu____7433  in
                FStar_Pprint.group uu____7431  in
              let uu____7440 =
                let uu____7441 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7441  in
              FStar_Pprint.op_Hat_Hat uu____7430 uu____7440  in
            FStar_Pprint.group uu____7429
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7442;_},e1::e2::e3::[])
            ->
            let uu____7449 =
              let uu____7450 =
                let uu____7451 =
                  let uu____7452 = p_atomicTermNotQUident e1  in
                  let uu____7453 =
                    let uu____7454 =
                      let uu____7455 =
                        let uu____7456 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7456  in
                      let uu____7459 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7455 uu____7459  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7454  in
                  FStar_Pprint.op_Hat_Hat uu____7452 uu____7453  in
                FStar_Pprint.group uu____7451  in
              let uu____7460 =
                let uu____7461 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7461  in
              FStar_Pprint.op_Hat_Hat uu____7450 uu____7460  in
            FStar_Pprint.group uu____7449
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7471 =
              let uu____7472 = str "requires"  in
              let uu____7474 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7472 uu____7474  in
            FStar_Pprint.group uu____7471
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7484 =
              let uu____7485 = str "ensures"  in
              let uu____7487 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7485 uu____7487  in
            FStar_Pprint.group uu____7484
        | FStar_Parser_AST.Attributes es ->
            let uu____7491 =
              let uu____7492 = str "attributes"  in
              let uu____7494 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7492 uu____7494  in
            FStar_Pprint.group uu____7491
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7499 =
                let uu____7500 =
                  let uu____7501 = str "if"  in
                  let uu____7503 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7501 uu____7503  in
                let uu____7506 =
                  let uu____7507 = str "then"  in
                  let uu____7509 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7507 uu____7509  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7500 uu____7506  in
              FStar_Pprint.group uu____7499
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7513,uu____7514,e31) when
                     is_unit e31 ->
                     let uu____7516 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7516
                 | uu____7519 -> p_noSeqTermAndComment false false e2  in
               let uu____7522 =
                 let uu____7523 =
                   let uu____7524 = str "if"  in
                   let uu____7526 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7524 uu____7526  in
                 let uu____7529 =
                   let uu____7530 =
                     let uu____7531 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7531 e2_doc  in
                   let uu____7533 =
                     let uu____7534 = str "else"  in
                     let uu____7536 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7534 uu____7536  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7530 uu____7533  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7523 uu____7529  in
               FStar_Pprint.group uu____7522)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7559 =
              let uu____7560 =
                let uu____7561 =
                  let uu____7562 = str "try"  in
                  let uu____7564 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7562 uu____7564  in
                let uu____7567 =
                  let uu____7568 = str "with"  in
                  let uu____7570 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7568 uu____7570  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7561 uu____7567  in
              FStar_Pprint.group uu____7560  in
            let uu____7579 = paren_if (ps || pb)  in uu____7579 uu____7559
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7606 =
              let uu____7607 =
                let uu____7608 =
                  let uu____7609 = str "match"  in
                  let uu____7611 = p_noSeqTermAndComment false false e1  in
                  let uu____7614 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7609 uu____7611 uu____7614
                   in
                let uu____7618 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7608 uu____7618  in
              FStar_Pprint.group uu____7607  in
            let uu____7627 = paren_if (ps || pb)  in uu____7627 uu____7606
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7634 =
              let uu____7635 =
                let uu____7636 =
                  let uu____7637 = str "let open"  in
                  let uu____7639 = p_quident uid  in
                  let uu____7640 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7637 uu____7639 uu____7640
                   in
                let uu____7644 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7636 uu____7644  in
              FStar_Pprint.group uu____7635  in
            let uu____7646 = paren_if ps  in uu____7646 uu____7634
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7711 is_last =
              match uu____7711 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7745 =
                          let uu____7746 = str "let"  in
                          let uu____7748 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7746 uu____7748
                           in
                        FStar_Pprint.group uu____7745
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7751 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7757 = p_term_sep false false e2  in
                  (match uu____7757 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7767 =
                         if is_last
                         then
                           let uu____7769 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7770 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7769 doc_expr1
                             uu____7770
                         else
                           (let uu____7776 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7776)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7767)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7827 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7827
                     else
                       (let uu____7838 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7838)) lbs
               in
            let lbs_doc =
              let uu____7848 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7848  in
            let uu____7849 =
              let uu____7850 =
                let uu____7851 =
                  let uu____7852 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7852
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7851  in
              FStar_Pprint.group uu____7850  in
            let uu____7854 = paren_if ps  in uu____7854 uu____7849
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7861;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7864;
                                                             FStar_Parser_AST.level
                                                               = uu____7865;_})
            when matches_var maybe_x x ->
            let uu____7892 =
              let uu____7893 =
                let uu____7894 = str "function"  in
                let uu____7896 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7894 uu____7896  in
              FStar_Pprint.group uu____7893  in
            let uu____7905 = paren_if (ps || pb)  in uu____7905 uu____7892
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7911 =
              let uu____7912 = str "quote"  in
              let uu____7914 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7912 uu____7914  in
            FStar_Pprint.group uu____7911
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7916 =
              let uu____7917 = str "`"  in
              let uu____7919 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7917 uu____7919  in
            FStar_Pprint.group uu____7916
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7921 =
              let uu____7922 = str "`%"  in
              let uu____7924 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7922 uu____7924  in
            FStar_Pprint.group uu____7921
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7926;
              FStar_Parser_AST.level = uu____7927;_}
            ->
            let uu____7928 =
              let uu____7929 = str "`@"  in
              let uu____7931 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7929 uu____7931  in
            FStar_Pprint.group uu____7928
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7933 =
              let uu____7934 = str "`#"  in
              let uu____7936 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7934 uu____7936  in
            FStar_Pprint.group uu____7933
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7945 = str "calc"  in
              let uu____7947 =
                let uu____7948 =
                  let uu____7949 = p_noSeqTermAndComment false false rel  in
                  let uu____7952 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7949 uu____7952  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7948  in
              FStar_Pprint.op_Hat_Hat uu____7945 uu____7947  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7954 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7955 =
              let uu____7956 =
                let uu____7957 =
                  let uu____7958 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7961 =
                    let uu____7962 = str ";"  in
                    let uu____7964 =
                      let uu____7965 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7965
                       in
                    FStar_Pprint.op_Hat_Hat uu____7962 uu____7964  in
                  FStar_Pprint.op_Hat_Hat uu____7958 uu____7961  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7957  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____7956
               in
            FStar_Pprint.enclose head1 uu____7954 uu____7955
        | uu____7967 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7968  ->
    fun uu____7969  ->
      match uu____7969 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7974 =
            let uu____7975 = p_noSeqTermAndComment false false rel  in
            let uu____7978 =
              let uu____7979 =
                let uu____7980 =
                  let uu____7981 =
                    let uu____7982 = p_noSeqTermAndComment false false just
                       in
                    let uu____7985 =
                      let uu____7986 =
                        let uu____7987 =
                          let uu____7988 =
                            let uu____7989 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7992 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7989 uu____7992  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7988
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7987
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7986
                       in
                    FStar_Pprint.op_Hat_Hat uu____7982 uu____7985  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7981  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7980  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7979  in
            FStar_Pprint.op_Hat_Hat uu____7975 uu____7978  in
          FStar_Pprint.group uu____7974

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___121_7994  ->
    match uu___121_7994 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____8006 =
          let uu____8007 = str "[@"  in
          let uu____8009 =
            let uu____8010 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____8011 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____8010 uu____8011  in
          FStar_Pprint.op_Hat_Slash_Hat uu____8007 uu____8009  in
        FStar_Pprint.group uu____8006

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment_sep (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8048 =
                   let uu____8049 =
                     let uu____8050 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8050 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8049 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8048 term_doc
             | pats ->
                 let uu____8058 =
                   let uu____8059 =
                     let uu____8060 =
                       let uu____8061 =
                         let uu____8062 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8062
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8061 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8065 = p_trigger trigger  in
                     prefix2 uu____8060 uu____8065  in
                   FStar_Pprint.group uu____8059  in
                 prefix2 uu____8058 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8086 =
                   let uu____8087 =
                     let uu____8088 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8088 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8087 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8086 term_doc
             | pats ->
                 let uu____8096 =
                   let uu____8097 =
                     let uu____8098 =
                       let uu____8099 =
                         let uu____8100 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8100
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8099 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8103 = p_trigger trigger  in
                     prefix2 uu____8098 uu____8103  in
                   FStar_Pprint.group uu____8097  in
                 prefix2 uu____8096 term_doc)
        | uu____8104 -> p_simpleTerm ps pb e

and (p_typ_top :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun ps  ->
      fun pb  ->
        fun e  ->
          with_comment (p_typ_top' style ps pb) e e.FStar_Parser_AST.range

and (p_typ_top' :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun ps  -> fun pb  -> fun e  -> p_tmArrow style true p_tmFormula e

and (sig_as_binders_if_possible :
  FStar_Parser_AST.term -> Prims.bool -> FStar_Pprint.document) =
  fun t  ->
    fun extra_space  ->
      let s = if extra_space then FStar_Pprint.space else FStar_Pprint.empty
         in
      let uu____8125 = all_binders_annot t  in
      if uu____8125
      then
        let uu____8128 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8128
      else
        (let uu____8139 =
           let uu____8140 =
             let uu____8141 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8141  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8140  in
         FStar_Pprint.group uu____8139)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8200 = x  in
      match uu____8200 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8265 = hd1  in
               (match uu____8265 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8337 = cb  in
      match uu____8337 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8356 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8362 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8362) hd1 tl1
                  in
               cat_with_colon uu____8356 typ)
       in
    let binders = FStar_List.fold_left fold_fun [] (FStar_List.rev pats)  in
    map_rev p_collapsed_binder binders

and (pats_as_binders_if_possible :
  FStar_Parser_AST.pattern Prims.list ->
    (FStar_Pprint.document Prims.list * annotation_style))
  =
  fun pats  ->
    let all_binders p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None ))
          ->
          (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
           | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
              ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                 FStar_Parser_AST.brange = uu____8441;
                 FStar_Parser_AST.blevel = uu____8442;
                 FStar_Parser_AST.aqual = uu____8443;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8452 =
                 let uu____8457 = p_ident lid  in
                 p_refinement' aqual uu____8457 t1 phi  in
               FStar_Pervasives_Native.Some uu____8452
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8464) ->
               let uu____8469 =
                 let uu____8474 =
                   let uu____8475 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8476 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8475 uu____8476  in
                 let uu____8477 = p_tmEqNoRefinement t  in
                 (uu____8474, uu____8477)  in
               FStar_Pervasives_Native.Some uu____8469
           | uu____8482 -> FStar_Pervasives_Native.None)
      | uu____8491 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8504 -> false
      | uu____8516 -> true  in
    let uu____8518 = map_if_all all_binders pats  in
    match uu____8518 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8550 = collapse_pats bs  in
        (uu____8550,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8567 = FStar_List.map p_atomicPattern pats  in
        (uu____8567,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8579 -> str "forall"
    | FStar_Parser_AST.QExists uu____8593 -> str "exists"
    | uu____8607 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___122_8609  ->
    match uu___122_8609 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8621 =
          let uu____8622 =
            let uu____8623 =
              let uu____8624 = str "pattern"  in
              let uu____8626 =
                let uu____8627 =
                  let uu____8628 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____8628
                   in
                FStar_Pprint.op_Hat_Hat uu____8627 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8624 uu____8626  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8623  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8622  in
        FStar_Pprint.group uu____8621

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8636 = str "\\/"  in
    FStar_Pprint.separate_map uu____8636 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8643 =
      let uu____8644 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8644 p_appTerm pats  in
    FStar_Pprint.group uu____8643

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8656 = p_term_sep false pb e1  in
            (match uu____8656 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8665 = str "fun"  in
                   let uu____8667 =
                     let uu____8668 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8668
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8665 uu____8667  in
                 let uu____8669 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8671 =
                       let uu____8672 =
                         let uu____8673 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8673  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8672
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8671
                   else
                     (let uu____8676 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8676)
                    in
                 let uu____8677 = paren_if ps  in uu____8677 uu____8669)
        | uu____8682 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8690  ->
      match uu____8690 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8714 =
                    let uu____8715 =
                      let uu____8716 =
                        let uu____8717 = p_tuplePattern p  in
                        let uu____8718 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8717 uu____8718  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8716
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8715  in
                  FStar_Pprint.group uu____8714
              | FStar_Pervasives_Native.Some f ->
                  let uu____8720 =
                    let uu____8721 =
                      let uu____8722 =
                        let uu____8723 =
                          let uu____8724 =
                            let uu____8725 = p_tuplePattern p  in
                            let uu____8726 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8725
                              uu____8726
                             in
                          FStar_Pprint.group uu____8724  in
                        let uu____8728 =
                          let uu____8729 =
                            let uu____8732 = p_tmFormula f  in
                            [uu____8732; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8729  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8723 uu____8728
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8722
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8721  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____8720
               in
            let uu____8734 = p_term_sep false pb e  in
            match uu____8734 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8744 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8744
                   else
                     (let uu____8747 =
                        let uu____8748 =
                          let uu____8749 =
                            let uu____8750 =
                              let uu____8751 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8751  in
                            op_Hat_Slash_Plus_Hat branch uu____8750  in
                          FStar_Pprint.group uu____8749  in
                        let uu____8752 =
                          let uu____8753 =
                            let uu____8754 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8754  in
                          FStar_Pprint.op_Hat_Hat branch uu____8753  in
                        FStar_Pprint.ifflat uu____8748 uu____8752  in
                      FStar_Pprint.group uu____8747))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8758 =
                       let uu____8759 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8759  in
                     op_Hat_Slash_Plus_Hat branch uu____8758)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8770 =
                      let uu____8771 =
                        let uu____8772 =
                          let uu____8773 =
                            let uu____8774 =
                              let uu____8775 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8775  in
                            FStar_Pprint.separate_map uu____8774
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8773
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8772
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8771  in
                    FStar_Pprint.group uu____8770
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8777 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8779;_},e1::e2::[])
        ->
        let uu____8785 = str "<==>"  in
        let uu____8787 = p_tmImplies e1  in
        let uu____8788 = p_tmIff e2  in
        infix0 uu____8785 uu____8787 uu____8788
    | uu____8789 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8791;_},e1::e2::[])
        ->
        let uu____8797 = str "==>"  in
        let uu____8799 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____8805 = p_tmImplies e2  in
        infix0 uu____8797 uu____8799 uu____8805
    | uu____8806 ->
        p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
          false p_tmFormula e

and (format_sig :
  annotation_style ->
    FStar_Pprint.document Prims.list ->
      Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun style  ->
    fun terms  ->
      fun no_last_op  ->
        fun flat_space  ->
          let uu____8820 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____8820 with
          | (terms',last1) ->
              let uu____8840 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8875 =
                      let uu____8876 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8876
                       in
                    let uu____8877 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8875, uu____8877)
                | Binders (n1,ln,parens1) ->
                    let uu____8891 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8899 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8891, break1, uu____8899)
                 in
              (match uu____8840 with
               | (n1,last_n,terms'1,sep,last_op) ->
                   let last2 = FStar_List.hd last1  in
                   let last_op1 =
                     if
                       ((FStar_List.length terms) > (Prims.parse_int "1")) &&
                         (Prims.op_Negation no_last_op)
                     then last_op
                     else FStar_Pprint.empty  in
                   let one_line_space =
                     if
                       (Prims.op_Negation (last2 = FStar_Pprint.empty)) ||
                         (Prims.op_Negation no_last_op)
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   let single_line_arg_indent =
                     FStar_Pprint.repeat n1 FStar_Pprint.space  in
                   let fs =
                     if flat_space
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   (match FStar_List.length terms with
                    | _0_5 when _0_5 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____8932 ->
                        let uu____8933 =
                          let uu____8934 =
                            let uu____8935 =
                              let uu____8936 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8937 =
                                let uu____8938 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8938
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8936 uu____8937
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8935  in
                          let uu____8939 =
                            let uu____8940 =
                              let uu____8941 =
                                let uu____8942 =
                                  let uu____8943 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8943  in
                                let uu____8944 =
                                  let uu____8945 =
                                    let uu____8946 =
                                      let uu____8947 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8948 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8954 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____8954)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8947
                                        uu____8948
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8946
                                     in
                                  jump2 uu____8945  in
                                FStar_Pprint.ifflat uu____8942 uu____8944  in
                              FStar_Pprint.group uu____8941  in
                            let uu____8956 =
                              let uu____8957 =
                                let uu____8958 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8958  in
                              FStar_Pprint.align uu____8957  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____8940 uu____8956
                             in
                          FStar_Pprint.ifflat uu____8934 uu____8939  in
                        FStar_Pprint.group uu____8933))

and (p_tmArrow :
  annotation_style ->
    Prims.bool ->
      (FStar_Parser_AST.term -> FStar_Pprint.document) ->
        FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun flat_space  ->
      fun p_Tm  ->
        fun e  ->
          let terms =
            match style with
            | Arrows uu____8972 -> p_tmArrow' p_Tm e
            | Binders uu____8979 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____9002 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____9008 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____9002 uu____9008
      | uu____9011 -> let uu____9012 = p_Tm e  in [uu____9012]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9065 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9091 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9065 uu____9091
        | uu____9114 ->
            let uu____9115 =
              let uu____9126 = p_Tm1 e1  in
              (uu____9126, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9115]
         in
      let fold_fun bs x =
        let uu____9224 = x  in
        match uu____9224 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9360 = hd1  in
                 (match uu____9360 with
                  | (b2s,t2,uu____9389) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9499 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9560 = cb  in
        match uu____9560 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9589 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9602 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9608 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9608) hd1 tl1
                         in
                      f uu____9602 typ))
         in
      let binders =
        let uu____9626 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9626  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9689 =
        let uu____9690 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9690 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9689  in
    let disj =
      let uu____9693 =
        let uu____9694 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9694 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9693  in
    let formula = p_tmDisjunction e  in
    FStar_Pprint.flow_map disj
      (fun d  ->
         FStar_Pprint.flow_map conj (fun x  -> FStar_Pprint.group x) d)
      formula

and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9714;_},e1::e2::[])
        ->
        let uu____9720 = p_tmDisjunction e1  in
        let uu____9725 = let uu____9730 = p_tmConjunction e2  in [uu____9730]
           in
        FStar_List.append uu____9720 uu____9725
    | uu____9739 -> let uu____9740 = p_tmConjunction e  in [uu____9740]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9750;_},e1::e2::[])
        ->
        let uu____9756 = p_tmConjunction e1  in
        let uu____9759 = let uu____9762 = p_tmTuple e2  in [uu____9762]  in
        FStar_List.append uu____9756 uu____9759
    | uu____9763 -> let uu____9764 = p_tmTuple e  in [uu____9764]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9781 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9781
          (fun uu____9789  ->
             match uu____9789 with | (e1,uu____9795) -> p_tmEq e1) args
    | uu____9796 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9805 =
             let uu____9806 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9806  in
           FStar_Pprint.group uu____9805)

and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals; pipe_right] operatorInfix0ad12)
         in
      p_tmEqWith' p_X n1 e

and (p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun curr  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Op (op,e1::e2::[]) when
            ((is_operatorInfix0ad12 op) ||
               (let uu____9825 = FStar_Ident.text_of_id op  in
                uu____9825 = "="))
              ||
              (let uu____9830 = FStar_Ident.text_of_id op  in
               uu____9830 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9836 = levels op1  in
            (match uu____9836 with
             | (left1,mine,right1) ->
                 let uu____9855 =
                   let uu____9856 = FStar_All.pipe_left str op1  in
                   let uu____9858 = p_tmEqWith' p_X left1 e1  in
                   let uu____9859 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9856 uu____9858 uu____9859  in
                 paren_if_gt curr mine uu____9855)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9860;_},e1::e2::[])
            ->
            let uu____9866 =
              let uu____9867 = p_tmEqWith p_X e1  in
              let uu____9868 =
                let uu____9869 =
                  let uu____9870 =
                    let uu____9871 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9871  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9870  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9869  in
              FStar_Pprint.op_Hat_Hat uu____9867 uu____9868  in
            FStar_Pprint.group uu____9866
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9872;_},e1::[])
            ->
            let uu____9877 = levels "-"  in
            (match uu____9877 with
             | (left1,mine,right1) ->
                 let uu____9897 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9897)
        | uu____9898 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon; amp; opinfix3; opinfix4]  in
      p_tmNoEqWith' false p_X n1 e

and (p_tmNoEqWith' :
  Prims.bool ->
    (FStar_Parser_AST.term -> FStar_Pprint.document) ->
      Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun inside_tuple  ->
    fun p_X  ->
      fun curr  ->
        fun e  ->
          match e.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Construct
              (lid,(e1,uu____9946)::(e2,uu____9948)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9968 = is_list e  in Prims.op_Negation uu____9968)
              ->
              let op = "::"  in
              let uu____9973 = levels op  in
              (match uu____9973 with
               | (left1,mine,right1) ->
                   let uu____9992 =
                     let uu____9993 = str op  in
                     let uu____9994 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9996 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9993 uu____9994 uu____9996  in
                   paren_if_gt curr mine uu____9992)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____10015 = levels op  in
              (match uu____10015 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10049 = p_binder false b  in
                         let uu____10051 =
                           let uu____10052 =
                             let uu____10053 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10053 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10052
                            in
                         FStar_Pprint.op_Hat_Hat uu____10049 uu____10051
                     | FStar_Util.Inr t ->
                         let uu____10055 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10057 =
                           let uu____10058 =
                             let uu____10059 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10059 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10058
                            in
                         FStar_Pprint.op_Hat_Hat uu____10055 uu____10057
                      in
                   let uu____10060 =
                     let uu____10061 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10066 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10061 uu____10066  in
                   paren_if_gt curr mine uu____10060)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10068;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10098 = levels op  in
              (match uu____10098 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10118 = str op  in
                     let uu____10119 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10121 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10118 uu____10119 uu____10121
                   else
                     (let uu____10125 =
                        let uu____10126 = str op  in
                        let uu____10127 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10129 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10126 uu____10127 uu____10129  in
                      paren_if_gt curr mine uu____10125))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10138 = levels op1  in
              (match uu____10138 with
               | (left1,mine,right1) ->
                   let uu____10157 =
                     let uu____10158 = str op1  in
                     let uu____10159 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10161 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10158 uu____10159 uu____10161  in
                   paren_if_gt curr mine uu____10157)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10181 =
                let uu____10182 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10183 =
                  let uu____10184 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10184 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10182 uu____10183  in
              braces_with_nesting uu____10181
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10189;_},e1::[])
              ->
              let uu____10194 =
                let uu____10195 = str "~"  in
                let uu____10197 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10195 uu____10197  in
              FStar_Pprint.group uu____10194
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10199;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10208 = levels op  in
                   (match uu____10208 with
                    | (left1,mine,right1) ->
                        let uu____10227 =
                          let uu____10228 = str op  in
                          let uu____10229 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10231 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10228 uu____10229 uu____10231  in
                        paren_if_gt curr mine uu____10227)
               | uu____10233 -> p_X e)
          | uu____10234 -> p_X e

and (p_tmEqNoRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmEqWith p_appTerm e

and (p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmEqWith p_tmRefinement e

and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmNoEqWith p_tmRefinement e

and (p_tmRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.NamedTyp (lid,e1) ->
        let uu____10241 =
          let uu____10242 = p_lident lid  in
          let uu____10243 =
            let uu____10244 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10244  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10242 uu____10243  in
        FStar_Pprint.group uu____10241
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10247 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10249 = p_appTerm e  in
    let uu____10250 =
      let uu____10251 =
        let uu____10252 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10252 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10251  in
    FStar_Pprint.op_Hat_Hat uu____10249 uu____10250

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10258 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10258 t phi
      | FStar_Parser_AST.TAnnotated uu____10259 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10265 ->
          let uu____10266 =
            let uu____10268 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10268
             in
          failwith uu____10266
      | FStar_Parser_AST.TVariable uu____10271 ->
          let uu____10272 =
            let uu____10274 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10274
             in
          failwith uu____10272
      | FStar_Parser_AST.NoName uu____10277 ->
          let uu____10278 =
            let uu____10280 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10280
             in
          failwith uu____10278

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10284  ->
      match uu____10284 with
      | (lid,e) ->
          let uu____10292 =
            let uu____10293 = p_qlident lid  in
            let uu____10294 =
              let uu____10295 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10295
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10293 uu____10294  in
          FStar_Pprint.group uu____10292

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10298 when is_general_application e ->
        let uu____10305 = head_and_args e  in
        (match uu____10305 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10352 = p_argTerm e1  in
                  let uu____10353 =
                    let uu____10354 =
                      let uu____10355 =
                        let uu____10356 = str "`"  in
                        let uu____10358 =
                          let uu____10359 = p_indexingTerm head1  in
                          let uu____10360 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10359 uu____10360  in
                        FStar_Pprint.op_Hat_Hat uu____10356 uu____10358  in
                      FStar_Pprint.group uu____10355  in
                    let uu____10362 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10354 uu____10362  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10352 uu____10353
              | uu____10363 ->
                  let uu____10370 =
                    let uu____10381 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10381
                    then
                      let uu____10415 =
                        FStar_Util.take
                          (fun uu____10439  ->
                             match uu____10439 with
                             | (uu____10445,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10415 with
                      | (fs_typ_args,args1) ->
                          let uu____10483 =
                            let uu____10484 = p_indexingTerm head1  in
                            let uu____10485 =
                              let uu____10486 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____10486
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10484 uu____10485
                             in
                          (uu____10483, args1)
                    else
                      (let uu____10501 = p_indexingTerm head1  in
                       (uu____10501, args))
                     in
                  (match uu____10370 with
                   | (head_doc,args1) ->
                       let uu____10522 =
                         let uu____10523 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____10523 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10522)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10545 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10545)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10564 =
               let uu____10565 = p_quident lid  in
               let uu____10566 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10565 uu____10566  in
             FStar_Pprint.group uu____10564
         | hd1::tl1 ->
             let uu____10583 =
               let uu____10584 =
                 let uu____10585 =
                   let uu____10586 = p_quident lid  in
                   let uu____10587 = p_argTerm hd1  in
                   prefix2 uu____10586 uu____10587  in
                 FStar_Pprint.group uu____10585  in
               let uu____10588 =
                 let uu____10589 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10589  in
               FStar_Pprint.op_Hat_Hat uu____10584 uu____10588  in
             FStar_Pprint.group uu____10583)
    | uu____10594 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10605 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____10605 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10609 = str "#"  in
        let uu____10611 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10609 uu____10611
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10614 = str "#["  in
        let uu____10616 =
          let uu____10617 = p_indexingTerm t  in
          let uu____10618 =
            let uu____10619 = str "]"  in
            let uu____10621 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10619 uu____10621  in
          FStar_Pprint.op_Hat_Hat uu____10617 uu____10618  in
        FStar_Pprint.op_Hat_Hat uu____10614 uu____10616
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10624  ->
    match uu____10624 with | (e,uu____10630) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10635;_},e1::e2::[])
          ->
          let uu____10641 =
            let uu____10642 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10643 =
              let uu____10644 =
                let uu____10645 = p_term false false e2  in
                soft_parens_with_nesting uu____10645  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10644  in
            FStar_Pprint.op_Hat_Hat uu____10642 uu____10643  in
          FStar_Pprint.group uu____10641
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10648;_},e1::e2::[])
          ->
          let uu____10654 =
            let uu____10655 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10656 =
              let uu____10657 =
                let uu____10658 = p_term false false e2  in
                soft_brackets_with_nesting uu____10658  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10657  in
            FStar_Pprint.op_Hat_Hat uu____10655 uu____10656  in
          FStar_Pprint.group uu____10654
      | uu____10661 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10666 = p_quident lid  in
        let uu____10667 =
          let uu____10668 =
            let uu____10669 = p_term false false e1  in
            soft_parens_with_nesting uu____10669  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10668  in
        FStar_Pprint.op_Hat_Hat uu____10666 uu____10667
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10677 =
          let uu____10678 = FStar_Ident.text_of_id op  in str uu____10678  in
        let uu____10680 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10677 uu____10680
    | uu____10681 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assume_lid ->
        str "assume"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____10694 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10703 =
          let uu____10704 = FStar_Ident.text_of_id op  in str uu____10704  in
        let uu____10706 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10703 uu____10706
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10710 =
          let uu____10711 =
            let uu____10712 =
              let uu____10713 = FStar_Ident.text_of_id op  in str uu____10713
               in
            let uu____10715 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10712 uu____10715  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10711  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10710
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10730 = all_explicit args  in
        if uu____10730
        then
          let uu____10733 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10734 =
            let uu____10735 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10736 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10735 p_tmEq uu____10736  in
          let uu____10743 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____10733 uu____10734 uu____10743
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10765 =
                 let uu____10766 = p_quident lid  in
                 let uu____10767 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10766 uu____10767  in
               FStar_Pprint.group uu____10765
           | hd1::tl1 ->
               let uu____10784 =
                 let uu____10785 =
                   let uu____10786 =
                     let uu____10787 = p_quident lid  in
                     let uu____10788 = p_argTerm hd1  in
                     prefix2 uu____10787 uu____10788  in
                   FStar_Pprint.group uu____10786  in
                 let uu____10789 =
                   let uu____10790 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10790  in
                 FStar_Pprint.op_Hat_Hat uu____10785 uu____10789  in
               FStar_Pprint.group uu____10784)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10797 =
          let uu____10798 = p_atomicTermNotQUident e1  in
          let uu____10799 =
            let uu____10800 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10800  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____10798 uu____10799
           in
        FStar_Pprint.group uu____10797
    | uu____10803 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10808 = p_quident constr_lid  in
        let uu____10809 =
          let uu____10810 =
            let uu____10811 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10811  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10810  in
        FStar_Pprint.op_Hat_Hat uu____10808 uu____10809
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10813 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10813 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10815 = p_term_sep false false e1  in
        (match uu____10815 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10828 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10828))
    | uu____10829 when is_array e ->
        let es = extract_from_list e  in
        let uu____10833 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10834 =
          let uu____10835 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10835
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10840 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10833 uu____10834 uu____10840
    | uu____10843 when is_list e ->
        let uu____10844 =
          let uu____10845 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10846 = extract_from_list e  in
          separate_map_or_flow_last uu____10845
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10846
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____10844 FStar_Pprint.rbracket
    | uu____10855 when is_lex_list e ->
        let uu____10856 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10857 =
          let uu____10858 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10859 = extract_from_list e  in
          separate_map_or_flow_last uu____10858
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10859
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____10856 uu____10857 FStar_Pprint.rbracket
    | uu____10868 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10872 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10873 =
          let uu____10874 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10874 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10872 uu____10873 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10884 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____10887 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10884 uu____10887
    | FStar_Parser_AST.Op (op,args) when
        let uu____10896 = handleable_op op args  in
        Prims.op_Negation uu____10896 ->
        let uu____10898 =
          let uu____10900 =
            let uu____10902 = FStar_Ident.text_of_id op  in
            let uu____10904 =
              let uu____10906 =
                let uu____10908 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____10908
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____10906  in
            Prims.strcat uu____10902 uu____10904  in
          Prims.strcat "Operation " uu____10900  in
        failwith uu____10898
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10915 = p_term false false e  in
        soft_parens_with_nesting uu____10915
    | FStar_Parser_AST.Const uu____10918 ->
        let uu____10919 = p_term false false e  in
        soft_parens_with_nesting uu____10919
    | FStar_Parser_AST.Op uu____10922 ->
        let uu____10929 = p_term false false e  in
        soft_parens_with_nesting uu____10929
    | FStar_Parser_AST.Tvar uu____10932 ->
        let uu____10933 = p_term false false e  in
        soft_parens_with_nesting uu____10933
    | FStar_Parser_AST.Var uu____10936 ->
        let uu____10937 = p_term false false e  in
        soft_parens_with_nesting uu____10937
    | FStar_Parser_AST.Name uu____10940 ->
        let uu____10941 = p_term false false e  in
        soft_parens_with_nesting uu____10941
    | FStar_Parser_AST.Construct uu____10944 ->
        let uu____10955 = p_term false false e  in
        soft_parens_with_nesting uu____10955
    | FStar_Parser_AST.Abs uu____10958 ->
        let uu____10965 = p_term false false e  in
        soft_parens_with_nesting uu____10965
    | FStar_Parser_AST.App uu____10968 ->
        let uu____10975 = p_term false false e  in
        soft_parens_with_nesting uu____10975
    | FStar_Parser_AST.Let uu____10978 ->
        let uu____10999 = p_term false false e  in
        soft_parens_with_nesting uu____10999
    | FStar_Parser_AST.LetOpen uu____11002 ->
        let uu____11007 = p_term false false e  in
        soft_parens_with_nesting uu____11007
    | FStar_Parser_AST.Seq uu____11010 ->
        let uu____11015 = p_term false false e  in
        soft_parens_with_nesting uu____11015
    | FStar_Parser_AST.Bind uu____11018 ->
        let uu____11025 = p_term false false e  in
        soft_parens_with_nesting uu____11025
    | FStar_Parser_AST.If uu____11028 ->
        let uu____11035 = p_term false false e  in
        soft_parens_with_nesting uu____11035
    | FStar_Parser_AST.Match uu____11038 ->
        let uu____11053 = p_term false false e  in
        soft_parens_with_nesting uu____11053
    | FStar_Parser_AST.TryWith uu____11056 ->
        let uu____11071 = p_term false false e  in
        soft_parens_with_nesting uu____11071
    | FStar_Parser_AST.Ascribed uu____11074 ->
        let uu____11083 = p_term false false e  in
        soft_parens_with_nesting uu____11083
    | FStar_Parser_AST.Record uu____11086 ->
        let uu____11099 = p_term false false e  in
        soft_parens_with_nesting uu____11099
    | FStar_Parser_AST.Project uu____11102 ->
        let uu____11107 = p_term false false e  in
        soft_parens_with_nesting uu____11107
    | FStar_Parser_AST.Product uu____11110 ->
        let uu____11117 = p_term false false e  in
        soft_parens_with_nesting uu____11117
    | FStar_Parser_AST.Sum uu____11120 ->
        let uu____11131 = p_term false false e  in
        soft_parens_with_nesting uu____11131
    | FStar_Parser_AST.QForall uu____11134 ->
        let uu____11147 = p_term false false e  in
        soft_parens_with_nesting uu____11147
    | FStar_Parser_AST.QExists uu____11150 ->
        let uu____11163 = p_term false false e  in
        soft_parens_with_nesting uu____11163
    | FStar_Parser_AST.Refine uu____11166 ->
        let uu____11171 = p_term false false e  in
        soft_parens_with_nesting uu____11171
    | FStar_Parser_AST.NamedTyp uu____11174 ->
        let uu____11179 = p_term false false e  in
        soft_parens_with_nesting uu____11179
    | FStar_Parser_AST.Requires uu____11182 ->
        let uu____11190 = p_term false false e  in
        soft_parens_with_nesting uu____11190
    | FStar_Parser_AST.Ensures uu____11193 ->
        let uu____11201 = p_term false false e  in
        soft_parens_with_nesting uu____11201
    | FStar_Parser_AST.Attributes uu____11204 ->
        let uu____11207 = p_term false false e  in
        soft_parens_with_nesting uu____11207
    | FStar_Parser_AST.Quote uu____11210 ->
        let uu____11215 = p_term false false e  in
        soft_parens_with_nesting uu____11215
    | FStar_Parser_AST.VQuote uu____11218 ->
        let uu____11219 = p_term false false e  in
        soft_parens_with_nesting uu____11219
    | FStar_Parser_AST.Antiquote uu____11222 ->
        let uu____11223 = p_term false false e  in
        soft_parens_with_nesting uu____11223
    | FStar_Parser_AST.CalcProof uu____11226 ->
        let uu____11235 = p_term false false e  in
        soft_parens_with_nesting uu____11235

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___125_11238  ->
    match uu___125_11238 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11247) ->
        let uu____11250 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11250
    | FStar_Const.Const_bytearray (bytes,uu____11252) ->
        let uu____11257 =
          let uu____11258 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11258  in
        let uu____11259 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11257 uu____11259
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___123_11282 =
          match uu___123_11282 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___124_11289 =
          match uu___124_11289 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11304  ->
               match uu____11304 with
               | (s,w) ->
                   let uu____11311 = signedness s  in
                   let uu____11312 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11311 uu____11312)
            sign_width_opt
           in
        let uu____11313 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11313 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11317 = FStar_Range.string_of_range r  in str uu____11317
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11321 = p_quident lid  in
        let uu____11322 =
          let uu____11323 =
            let uu____11324 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11324  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11323  in
        FStar_Pprint.op_Hat_Hat uu____11321 uu____11322

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11327 = str "u#"  in
    let uu____11329 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11327 uu____11329

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11331;_},u1::u2::[])
        ->
        let uu____11337 =
          let uu____11338 = p_universeFrom u1  in
          let uu____11339 =
            let uu____11340 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11340  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11338 uu____11339  in
        FStar_Pprint.group uu____11337
    | FStar_Parser_AST.App uu____11341 ->
        let uu____11348 = head_and_args u  in
        (match uu____11348 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11374 =
                    let uu____11375 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11376 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11384  ->
                           match uu____11384 with
                           | (u1,uu____11390) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11375 uu____11376  in
                  FStar_Pprint.group uu____11374
              | uu____11391 ->
                  let uu____11392 =
                    let uu____11394 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11394
                     in
                  failwith uu____11392))
    | uu____11397 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11423 = FStar_Ident.text_of_id id1  in str uu____11423
    | FStar_Parser_AST.Paren u1 ->
        let uu____11426 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11426
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11427;_},uu____11428::uu____11429::[])
        ->
        let uu____11433 = p_universeFrom u  in
        soft_parens_with_nesting uu____11433
    | FStar_Parser_AST.App uu____11434 ->
        let uu____11441 = p_universeFrom u  in
        soft_parens_with_nesting uu____11441
    | uu____11442 ->
        let uu____11443 =
          let uu____11445 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11445
           in
        failwith uu____11443

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    FStar_ST.op_Colon_Equals unfold_tuples false; p_term false false e
  
let (signature_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document)
  = fun e  -> p_justSig e 
let (decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun e  -> p_decl e 
let (pat_to_document : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  -> p_disjunctivePattern p 
let (binder_to_document : FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun b  -> p_binder true b 
let (modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document) =
  fun m  ->
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____11534,decls) ->
           let uu____11540 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11540
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11549,decls,uu____11551) ->
           let uu____11558 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11558
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11618  ->
         match uu____11618 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11640)) -> false
      | ([],uu____11644) -> false
      | uu____11648 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11658 -> true
         | uu____11660 -> false)
    }
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list))
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____11703,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11709,decls,uu____11711) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11763 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11776;
                 FStar_Parser_AST.doc = uu____11777;
                 FStar_Parser_AST.quals = uu____11778;
                 FStar_Parser_AST.attrs = uu____11779;_}::uu____11780 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11786 =
                   let uu____11789 =
                     let uu____11792 = FStar_List.tl ds  in d :: uu____11792
                      in
                   d0 :: uu____11789  in
                 (uu____11786, (d0.FStar_Parser_AST.drange))
             | uu____11797 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11763 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11854 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____11854 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11963 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11963, comments1))))))
  