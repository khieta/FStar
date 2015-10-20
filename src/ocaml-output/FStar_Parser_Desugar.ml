
open Prims
let as_imp = (fun _44_1 -> (match (_44_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (FStar_Absyn_Syntax.Implicit)
end
| _44_32 -> begin
None
end))

let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Absyn_Syntax.Implicit))
end
| _44_39 -> begin
(t, None)
end))

let contains_binder = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_44_43) -> begin
true
end
| _44_46 -> begin
false
end)))))

let rec unparen = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _44_51 -> begin
t
end))

let rec unlabel = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _44_57, _44_59) -> begin
(unlabel t)
end
| _44_63 -> begin
t
end))

let kind_star = (fun r -> (let _110_17 = (let _110_16 = (FStar_Absyn_Syntax.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_110_16))
in (FStar_Parser_AST.mk_term _110_17 r FStar_Parser_AST.Kind)))

let compile_op = (fun arity s -> (let name_of_char = (fun _44_2 -> (match (_44_2) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' when (arity = 1) -> begin
"Minus"
end
| '-' -> begin
"Subtraction"
end
| '/' -> begin
"Slash"
end
| '<' -> begin
"Less"
end
| '=' -> begin
"Equals"
end
| '>' -> begin
"Greater"
end
| '_' -> begin
"Underscore"
end
| '|' -> begin
"Bar"
end
| '!' -> begin
"Bang"
end
| '^' -> begin
"Hat"
end
| '%' -> begin
"Percent"
end
| '*' -> begin
"Star"
end
| '?' -> begin
"Question"
end
| ':' -> begin
"Colon"
end
| _44_86 -> begin
"UNKNOWN"
end))
in (let rec aux = (fun i -> (match ((i = (FStar_String.length s))) with
| true -> begin
[]
end
| false -> begin
(let _110_28 = (let _110_26 = (FStar_Util.char_at s i)
in (name_of_char _110_26))
in (let _110_27 = (aux (i + 1))
in (_110_28)::_110_27))
end))
in (let _110_30 = (let _110_29 = (aux 0)
in (FStar_String.concat "_" _110_29))
in (Prims.strcat "op_" _110_30)))))

let compile_op_lid = (fun n s r -> (let _110_40 = (let _110_39 = (let _110_38 = (let _110_37 = (compile_op n s)
in (_110_37, r))
in (FStar_Absyn_Syntax.mk_ident _110_38))
in (_110_39)::[])
in (FStar_All.pipe_right _110_40 FStar_Absyn_Syntax.lid_of_ids)))

let op_as_vlid = (fun env arity rng s -> (let r = (fun l -> (let _110_51 = (FStar_Absyn_Util.set_lid_range l rng)
in Some (_110_51)))
in (let fallback = (fun _44_100 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Absyn_Const.op_Eq)
end
| ":=" -> begin
(r FStar_Absyn_Const.op_ColonEq)
end
| "<" -> begin
(r FStar_Absyn_Const.op_LT)
end
| "<=" -> begin
(r FStar_Absyn_Const.op_LTE)
end
| ">" -> begin
(r FStar_Absyn_Const.op_GT)
end
| ">=" -> begin
(r FStar_Absyn_Const.op_GTE)
end
| "&&" -> begin
(r FStar_Absyn_Const.op_And)
end
| "||" -> begin
(r FStar_Absyn_Const.op_Or)
end
| "*" -> begin
(r FStar_Absyn_Const.op_Multiply)
end
| "+" -> begin
(r FStar_Absyn_Const.op_Addition)
end
| "-" when (arity = 1) -> begin
(r FStar_Absyn_Const.op_Minus)
end
| "-" -> begin
(r FStar_Absyn_Const.op_Subtraction)
end
| "/" -> begin
(r FStar_Absyn_Const.op_Division)
end
| "%" -> begin
(r FStar_Absyn_Const.op_Modulus)
end
| "!" -> begin
(r FStar_Absyn_Const.read_lid)
end
| "@" -> begin
(r FStar_Absyn_Const.list_append_lid)
end
| "^" -> begin
(r FStar_Absyn_Const.strcat_lid)
end
| "|>" -> begin
(r FStar_Absyn_Const.pipe_right_lid)
end
| "<|" -> begin
(r FStar_Absyn_Const.pipe_left_lid)
end
| "<>" -> begin
(r FStar_Absyn_Const.op_notEq)
end
| _44_122 -> begin
None
end)
end))
in (match ((let _110_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _110_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _44_133); FStar_Absyn_Syntax.tk = _44_130; FStar_Absyn_Syntax.pos = _44_128; FStar_Absyn_Syntax.fvs = _44_126; FStar_Absyn_Syntax.uvs = _44_124}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _44_139 -> begin
(fallback ())
end))))

let op_as_tylid = (fun env arity rng s -> (let r = (fun l -> (let _110_65 = (FStar_Absyn_Util.set_lid_range l rng)
in Some (_110_65)))
in (match (s) with
| "~" -> begin
(r FStar_Absyn_Const.not_lid)
end
| "==" -> begin
(r FStar_Absyn_Const.eq2_lid)
end
| "=!=" -> begin
(r FStar_Absyn_Const.neq2_lid)
end
| "<<" -> begin
(r FStar_Absyn_Const.precedes_lid)
end
| "/\\" -> begin
(r FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
(r FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
(r FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
(r FStar_Absyn_Const.iff_lid)
end
| s -> begin
(match ((let _110_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _110_66))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _44_162; FStar_Absyn_Syntax.pos = _44_160; FStar_Absyn_Syntax.fvs = _44_158; FStar_Absyn_Syntax.uvs = _44_156}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _44_168 -> begin
None
end)
end)))

let rec is_type = (fun env t -> (match ((t.FStar_Parser_AST.level = FStar_Parser_AST.Type)) with
| true -> begin
true
end
| false -> begin
(match ((let _110_73 = (unparen t)
in _110_73.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_44_173) -> begin
true
end
| FStar_Parser_AST.Op ("*", hd::_44_177) -> begin
(is_type env hd)
end
| (FStar_Parser_AST.Op ("==", _)) | (FStar_Parser_AST.Op ("=!=", _)) | (FStar_Parser_AST.Op ("~", _)) | (FStar_Parser_AST.Op ("/\\", _)) | (FStar_Parser_AST.Op ("\\/", _)) | (FStar_Parser_AST.Op ("==>", _)) | (FStar_Parser_AST.Op ("<==>", _)) | (FStar_Parser_AST.Op ("<<", _)) -> begin
true
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) t.FStar_Parser_AST.range s)) with
| None -> begin
false
end
| _44_228 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Absyn_Syntax.ident)) with
| Some (_44_251) -> begin
true
end
| _44_254 -> begin
(FStar_Parser_DesugarEnv.is_type_lid env l)
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(FStar_Parser_DesugarEnv.is_type_lid env l)
end
| (FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (l); FStar_Parser_AST.range = _; FStar_Parser_AST.level = _}, arg, FStar_Parser_AST.Nothing)) | (FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = _; FStar_Parser_AST.level = _}, arg, FStar_Parser_AST.Nothing)) when (l.FStar_Absyn_Syntax.str = "ref") -> begin
(is_type env arg)
end
| (FStar_Parser_AST.App (t, _, _)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(is_type env t)
end
| FStar_Parser_AST.Product (_44_295, t) -> begin
(not ((is_kind env t)))
end
| FStar_Parser_AST.If (t, t1, t2) -> begin
(((is_type env t) || (is_type env t1)) || (is_type env t2))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let rec aux = (fun env pats -> (match (pats) with
| [] -> begin
(is_type env t)
end
| hd::pats -> begin
(match (hd.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatVar (_)) -> begin
(aux env pats)
end
| FStar_Parser_AST.PatTvar (id, _44_321) -> begin
(let _44_327 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_44_327) with
| (env, _44_326) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(let env = (match ((is_kind env tm)) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _110_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _110_78 Prims.fst))
end
| _44_342 -> begin
env
end)
end
| false -> begin
env
end)
in (aux env pats))
end
| _44_345 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_44_350); FStar_Parser_AST.prange = _44_348}, _44_354)::[], t) -> begin
(is_type env t)
end
| _44_361 -> begin
false
end)
end))
and is_kind = (fun env t -> (match ((t.FStar_Parser_AST.level = FStar_Parser_AST.Kind)) with
| true -> begin
true
end
| false -> begin
(match ((let _110_81 = (unparen t)
in _110_81.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Absyn_Syntax.ns = _44_370; FStar_Absyn_Syntax.ident = _44_368; FStar_Absyn_Syntax.nsstr = _44_366; FStar_Absyn_Syntax.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_44_374, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _44_387 -> begin
false
end)
end))

let rec is_type_binder = (fun env b -> (match ((b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula)) with
| true -> begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_44_391) -> begin
false
end
| (FStar_Parser_AST.TAnnotated (_)) | (FStar_Parser_AST.TVariable (_)) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end
| false -> begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_44_406) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.FStar_Parser_AST.brange))))
end
| FStar_Parser_AST.TVariable (_44_409) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_44_412) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end))

let sort_ftv = (fun ftv -> (let _110_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Absyn_Syntax.idText = y.FStar_Absyn_Syntax.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Absyn_Syntax.idText y.FStar_Absyn_Syntax.idText))) _110_92)))

let rec free_type_vars_b = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_44_428) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _44_435 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_44_435) with
| (env, _44_434) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_44_437, term) -> begin
(let _110_99 = (free_type_vars env term)
in (env, _110_99))
end
| FStar_Parser_AST.TAnnotated (id, _44_443) -> begin
(let _44_449 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_44_449) with
| (env, _44_448) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _110_100 = (free_type_vars env t)
in (env, _110_100))
end))
and free_type_vars = (fun env t -> (match ((let _110_103 = (unparen t)
in _110_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _44_458 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_44_494, ts) -> begin
(FStar_List.collect (fun _44_501 -> (match (_44_501) with
| (t, _44_500) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_44_503, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _44_510) -> begin
(let _110_106 = (free_type_vars env t1)
in (let _110_105 = (free_type_vars env t2)
in (FStar_List.append _110_106 _110_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(let _44_519 = (free_type_vars_b env b)
in (match (_44_519) with
| (env, f) -> begin
(let _110_107 = (free_type_vars env t)
in (FStar_List.append f _110_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(let _44_535 = (FStar_List.fold_left (fun _44_528 binder -> (match (_44_528) with
| (env, free) -> begin
(let _44_532 = (free_type_vars_b env binder)
in (match (_44_532) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_44_535) with
| (env, free) -> begin
(let _110_110 = (free_type_vars env body)
in (FStar_List.append free _110_110))
end))
end
| FStar_Parser_AST.Project (t, _44_538) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

let head_and_args = (fun t -> (let rec aux = (fun args t -> (match ((let _110_117 = (unparen t)
in _110_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _44_582 -> begin
(t, args)
end))
in (aux [] t)))

let close = (fun env t -> (let ftv = (let _110_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _110_122))
in (match (((FStar_List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _110_126 = (let _110_125 = (let _110_124 = (kind_star x.FStar_Absyn_Syntax.idRange)
in (x, _110_124))
in FStar_Parser_AST.TAnnotated (_110_125))
in (FStar_Parser_AST.mk_binder _110_126 x.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Type (Some (FStar_Absyn_Syntax.Implicit)))))))
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))

let close_fun = (fun env t -> (let ftv = (let _110_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _110_131))
in (match (((FStar_List.length ftv) = 0)) with
| true -> begin
t
end
| false -> begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _110_135 = (let _110_134 = (let _110_133 = (kind_star x.FStar_Absyn_Syntax.idRange)
in (x, _110_133))
in FStar_Parser_AST.TAnnotated (_110_134))
in (FStar_Parser_AST.mk_binder _110_135 x.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Type (Some (FStar_Absyn_Syntax.Implicit)))))))
in (let t = (match ((let _110_136 = (unlabel t)
in _110_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_44_595) -> begin
t
end
| _44_598 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end)))

let rec uncurry = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _44_608 -> begin
(bs, t)
end))

let rec is_app_pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _44_612) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_44_618); FStar_Parser_AST.prange = _44_616}, _44_622) -> begin
true
end
| _44_626 -> begin
false
end))

let rec destruct_app_pattern = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _44_638 = (destruct_app_pattern env is_top_level p)
in (match (_44_638) with
| (name, args, _44_637) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _44_643); FStar_Parser_AST.prange = _44_640}, args) when is_top_level -> begin
(let _110_150 = (let _110_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_110_149))
in (_110_150, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _44_654); FStar_Parser_AST.prange = _44_651}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _44_662 -> begin
(FStar_All.failwith "Not an app pattern")
end))

type bnd =
| TBinder of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual)
| VBinder of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual)
| LetBinder of (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.typ)

let is_TBinder = (fun _discr_ -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))

let is_VBinder = (fun _discr_ -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))

let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

let ___TBinder____0 = (fun projectee -> (match (projectee) with
| TBinder (_44_665) -> begin
_44_665
end))

let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_44_668) -> begin
_44_668
end))

let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_44_671) -> begin
_44_671
end))

let binder_of_bnd = (fun _44_3 -> (match (_44_3) with
| TBinder (a, k, aq) -> begin
(FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder (x, t, aq) -> begin
(FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _44_684 -> begin
(FStar_All.failwith "Impossible")
end))

let as_binder = (fun env imp _44_4 -> (match (_44_4) with
| FStar_Util.Inl (None, k) -> begin
(let _110_201 = (FStar_Absyn_Syntax.null_t_binder k)
in (_110_201, env))
end
| FStar_Util.Inr (None, t) -> begin
(let _110_202 = (FStar_Absyn_Syntax.null_v_binder t)
in (_110_202, env))
end
| FStar_Util.Inl (Some (a), k) -> begin
(let _44_703 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_44_703) with
| (env, a) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), imp), env)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _44_711 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_44_711) with
| (env, x) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), imp), env)
end))
end))

type env_t =
FStar_Parser_DesugarEnv.env

type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list

let label_conjuncts = (fun tag polarity label_opt f -> (let label = (fun f -> (let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _44_721 -> begin
(let _110_213 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _110_213))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled ((f, msg, polarity))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _110_217 = (let _110_216 = (aux g)
in FStar_Parser_AST.Paren (_110_216))
in (FStar_Parser_AST.mk_term _110_217 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", f1::f2::[]) -> begin
(let _110_223 = (let _110_222 = (let _110_221 = (let _110_220 = (aux f1)
in (let _110_219 = (let _110_218 = (aux f2)
in (_110_218)::[])
in (_110_220)::_110_219))
in ("/\\", _110_221))
in FStar_Parser_AST.Op (_110_222))
in (FStar_Parser_AST.mk_term _110_223 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _110_227 = (let _110_226 = (let _110_225 = (aux f2)
in (let _110_224 = (aux f3)
in (f1, _110_225, _110_224)))
in FStar_Parser_AST.If (_110_226))
in (FStar_Parser_AST.mk_term _110_227 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _110_230 = (let _110_229 = (let _110_228 = (aux g)
in (binders, _110_228))
in FStar_Parser_AST.Abs (_110_229))
in (FStar_Parser_AST.mk_term _110_230 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _44_743 -> begin
(label f)
end))
in (aux f))))

let mk_lb = (fun _44_747 -> (match (_44_747) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))

let rec desugar_data_pat = (fun env p -> (let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _44_5 -> (match (_44_5) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText = x.FStar_Absyn_Syntax.idText)
end
| _44_758 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
(l, e, y)
end
| _44_763 -> begin
(let _44_766 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_44_766) with
| (e, x) -> begin
((FStar_Util.Inr (x))::l, e, x)
end))
end))
in (let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _44_6 -> (match (_44_6) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText = a.FStar_Absyn_Syntax.idText)
end
| _44_775 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
(l, e, b)
end
| _44_780 -> begin
(let _44_783 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_44_783) with
| (e, a) -> begin
((FStar_Util.Inl (a))::l, e, a)
end))
end))
in (let rec aux = (fun loc env p -> (let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p.FStar_Parser_AST.prange))
in (let pos_r = (fun r q -> (FStar_Absyn_Syntax.withinfo q None r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(let _44_805 = (aux loc env p)
in (match (_44_805) with
| (loc, env, var, p, _44_804) -> begin
(let _44_822 = (FStar_List.fold_left (fun _44_809 p -> (match (_44_809) with
| (loc, env, ps) -> begin
(let _44_818 = (aux loc env p)
in (match (_44_818) with
| (loc, env, _44_814, p, _44_817) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_44_822) with
| (loc, env, ps) -> begin
(let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (let _44_824 = (let _110_302 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _110_302))
in (loc, env, var, pat, false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let p = (match ((is_kind env t)) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_44_831) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(let _44_837 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar ((x, imp)); FStar_Parser_AST.prange = _44_837.FStar_Parser_AST.prange})
end
| _44_840 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end)
end
| false -> begin
p
end)
in (let _44_847 = (aux loc env p)
in (match (_44_847) with
| (loc, env', binder, p, imp) -> begin
(let binder = (match (binder) with
| LetBinder (_44_849) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _44_853, aq) -> begin
(let _110_304 = (let _110_303 = (desugar_kind env t)
in (x, _110_303, aq))
in TBinder (_110_304))
end
| VBinder (x, _44_859, aq) -> begin
(let t = (close_fun env t)
in (let _110_306 = (let _110_305 = (desugar_typ env t)
in (x, _110_305, aq))
in VBinder (_110_306)))
end)
in (loc, env', binder, p, imp))
end)))
end
| FStar_Parser_AST.PatTvar (a, imp) -> begin
(let aq = (match (imp) with
| true -> begin
Some (FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (match ((a.FStar_Absyn_Syntax.idText = "\'_")) with
| true -> begin
(let a = (FStar_All.pipe_left FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _110_307 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, FStar_Absyn_Syntax.kun, aq)), _110_307, imp)))
end
| false -> begin
(let _44_874 = (resolvea loc env a)
in (match (_44_874) with
| (loc, env, abvd) -> begin
(let _110_308 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, FStar_Absyn_Syntax.kun, aq)), _110_308, imp))
end))
end))
end
| FStar_Parser_AST.PatWild -> begin
(let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _110_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _110_309, false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _110_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _110_310, false)))
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(let aq = (match (imp) with
| true -> begin
Some (FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _44_889 = (resolvex loc env x)
in (match (_44_889) with
| (loc, env, xbvd) -> begin
(let _110_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, FStar_Absyn_Syntax.tun, aq)), _110_311, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _110_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _110_312, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _44_895}, args) -> begin
(let _44_917 = (FStar_List.fold_right (fun arg _44_906 -> (match (_44_906) with
| (loc, env, args) -> begin
(let _44_913 = (aux loc env arg)
in (match (_44_913) with
| (loc, env, _44_910, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_44_917) with
| (loc, env, args) -> begin
(let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _110_315 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _110_315, false))))
end))
end
| FStar_Parser_AST.PatApp (_44_921) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _44_941 = (FStar_List.fold_right (fun pat _44_929 -> (match (_44_929) with
| (loc, env, pats) -> begin
(let _44_937 = (aux loc env pat)
in (match (_44_937) with
| (loc, env, _44_933, pat, _44_936) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_44_941) with
| (loc, env, pats) -> begin
(let pat = (let _110_328 = (let _110_327 = (let _110_323 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _110_323))
in (let _110_326 = (let _110_325 = (let _110_324 = (FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid)
in (_110_324, Some (FStar_Absyn_Syntax.Data_ctor), []))
in FStar_Absyn_Syntax.Pat_cons (_110_325))
in (FStar_All.pipe_left _110_327 _110_326)))
in (FStar_List.fold_right (fun hd tl -> (let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (let _110_322 = (let _110_321 = (let _110_320 = (FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid)
in (_110_320, Some (FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[]))
in FStar_Absyn_Syntax.Pat_cons (_110_321))
in (FStar_All.pipe_left (pos_r r) _110_322)))) pats _110_328))
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(let _44_967 = (FStar_List.fold_left (fun _44_954 p -> (match (_44_954) with
| (loc, env, pats) -> begin
(let _44_963 = (aux loc env p)
in (match (_44_963) with
| (loc, env, _44_959, pat, _44_962) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_44_967) with
| (loc, env, args) -> begin
(let args = (FStar_List.rev args)
in (let l = (match (dep) with
| true -> begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
| false -> begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end)
in (let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _44_973) -> begin
v
end
| _44_977 -> begin
(FStar_All.failwith "impossible")
end)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _110_331 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _110_331, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(let _44_987 = (FStar_List.hd fields)
in (match (_44_987) with
| (f, _44_986) -> begin
(let _44_991 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_44_991) with
| (record, _44_990) -> begin
(let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _44_994 -> (match (_44_994) with
| (f, p) -> begin
(let _110_333 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_110_333, p))
end))))
in (let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _44_999 -> (match (_44_999) with
| (f, _44_998) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _44_1003 -> (match (_44_1003) with
| (g, _44_1002) -> begin
(FStar_Absyn_Syntax.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_44_1006, p) -> begin
p
end)
end))))
in (let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (let _44_1018 = (aux loc env app)
in (match (_44_1018) with
| (env, e, b, p, _44_1017) -> begin
(let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _44_1021, args) -> begin
(let _110_341 = (let _110_340 = (let _110_339 = (let _110_338 = (let _110_337 = (let _110_336 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _110_336))
in FStar_Absyn_Syntax.Record_ctor (_110_337))
in Some (_110_338))
in (fv, _110_339, args))
in FStar_Absyn_Syntax.Pat_cons (_110_340))
in (FStar_All.pipe_left pos _110_341))
end
| _44_1026 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (let _44_1035 = (aux [] env p)
in (match (_44_1035) with
| (_44_1029, env, b, p, _44_1034) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top = (fun top env p -> (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _44_1041) -> begin
(let _110_347 = (let _110_346 = (let _110_345 = (FStar_Parser_DesugarEnv.qualify env x)
in (_110_345, FStar_Absyn_Syntax.tun))
in LetBinder (_110_346))
in (env, _110_347, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _44_1048); FStar_Parser_AST.prange = _44_1045}, t) -> begin
(let _110_351 = (let _110_350 = (let _110_349 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _110_348 = (desugar_typ env t)
in (_110_349, _110_348)))
in LetBinder (_110_350))
in (env, _110_351, None))
end
| _44_1056 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end
| false -> begin
(let _44_1060 = (desugar_data_pat env p)
in (match (_44_1060) with
| (env, binder, p) -> begin
(let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _44_1071 -> begin
Some (p)
end)
in (env, binder, p))
end))
end))
and desugar_binding_pat = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top = (fun _44_1075 env pat -> (let _44_1083 = (desugar_data_pat env pat)
in (match (_44_1083) with
| (env, _44_1081, pat) -> begin
(env, pat)
end)))
and desugar_match_pat = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp = (fun env t -> (match ((is_type env t)) with
| true -> begin
(let _110_361 = (desugar_typ env t)
in FStar_Util.Inl (_110_361))
end
| false -> begin
(let _110_362 = (desugar_exp env t)
in FStar_Util.Inr (_110_362))
end))
and desugar_exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top = (fun top_level env top -> (let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (let setpos = (fun e -> (let _44_1097 = e
in {FStar_Absyn_Syntax.n = _44_1097.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _44_1097.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _44_1097.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _44_1097.FStar_Absyn_Syntax.uvs}))
in (match ((let _110_382 = (unparen top)
in _110_382.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (c) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_constant c))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_vlid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (let _110_385 = (FStar_Absyn_Syntax.range_of_lid l)
in (FStar_Absyn_Util.fvar None l _110_385))
in (let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _110_387 = (desugar_typ_or_exp env t)
in (_110_387, None)))))
in (let _110_388 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _110_388))))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(match ((l.FStar_Absyn_Syntax.str = "ref")) with
| true -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_lid env FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(let _110_391 = (let _110_390 = (let _110_389 = (FStar_Absyn_Syntax.range_of_lid l)
in ("Identifier \'ref\' not found; include lib/st.fst in your path", _110_389))
in FStar_Absyn_Syntax.Error (_110_390))
in (Prims.raise _110_391))
end
| Some (e) -> begin
(setpos e)
end)
end
| false -> begin
(let _110_392 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _110_392))
end)
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let dt = (let _110_397 = (let _110_396 = (let _110_395 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_110_395, Some (FStar_Absyn_Syntax.Data_ctor)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _110_396))
in (FStar_All.pipe_left pos _110_397))
in (match (args) with
| [] -> begin
dt
end
| _44_1124 -> begin
(let args = (FStar_List.map (fun _44_1127 -> (match (_44_1127) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _110_402 = (let _110_401 = (let _110_400 = (let _110_399 = (FStar_Absyn_Util.mk_exp_app dt args)
in (_110_399, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_110_400))
in (FStar_Absyn_Syntax.mk_Exp_meta _110_401))
in (FStar_All.pipe_left setpos _110_402)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let _44_1164 = (FStar_List.fold_left (fun _44_1136 pat -> (match (_44_1136) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _44_1139}, t) -> begin
(let ftvs = (let _110_405 = (free_type_vars env t)
in (FStar_List.append _110_405 ftvs))
in (let _110_407 = (let _110_406 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _110_406))
in (_110_407, ftvs)))
end
| FStar_Parser_AST.PatTvar (a, _44_1151) -> begin
(let _110_409 = (let _110_408 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _110_408))
in (_110_409, ftvs))
end
| FStar_Parser_AST.PatAscribed (_44_1155, t) -> begin
(let _110_411 = (let _110_410 = (free_type_vars env t)
in (FStar_List.append _110_410 ftvs))
in (env, _110_411))
end
| _44_1160 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_44_1164) with
| (_44_1162, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _110_413 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _110_413 binders))
in (let rec aux = (fun env bs sc_pat_opt _44_7 -> (match (_44_7) with
| [] -> begin
(let body = (desugar_exp env body)
in (let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(FStar_Absyn_Syntax.mk_Exp_match (sc, ((pat, None, body))::[]) None body.FStar_Absyn_Syntax.pos)
end
| None -> begin
body
end)
in (FStar_Absyn_Syntax.mk_Exp_abs' ((FStar_List.rev bs), body) None top.FStar_Parser_AST.range)))
end
| p::rest -> begin
(let _44_1187 = (desugar_binding_pat env p)
in (match (_44_1187) with
| (env, b, pat) -> begin
(let _44_1247 = (match (b) with
| LetBinder (_44_1189) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _110_422 = (binder_of_bnd b)
in (_110_422, sc_pat_opt))
end
| VBinder (x, t, aq) -> begin
(let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _44_1204) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _110_424 = (let _110_423 = (FStar_Absyn_Util.bvar_to_exp b)
in (_110_423, p))
in Some (_110_424))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Absyn_Syntax.n, p'.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Exp_bvar (_44_1218), _44_1221) -> begin
(let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (let sc = (let _110_431 = (let _110_430 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _110_429 = (let _110_428 = (FStar_Absyn_Syntax.varg sc)
in (let _110_427 = (let _110_426 = (let _110_425 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _110_425))
in (_110_426)::[])
in (_110_428)::_110_427))
in (_110_430, _110_429)))
in (FStar_Absyn_Syntax.mk_Exp_app _110_431 None top.FStar_Parser_AST.range))
in (let p = (let _110_435 = (let _110_433 = (let _110_432 = (FStar_Absyn_Util.fv tup)
in (_110_432, Some (FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))
in FStar_Absyn_Syntax.Pat_cons (_110_433))
in (let _110_434 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo _110_435 None _110_434)))
in Some ((sc, p)))))
end
| (FStar_Absyn_Syntax.Exp_app (_44_1227, args), FStar_Absyn_Syntax.Pat_cons (_44_1232, _44_1234, pats)) -> begin
(let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (let sc = (let _110_441 = (let _110_440 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _110_439 = (let _110_438 = (let _110_437 = (let _110_436 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _110_436))
in (_110_437)::[])
in (FStar_List.append args _110_438))
in (_110_440, _110_439)))
in (FStar_Absyn_Syntax.mk_Exp_app _110_441 None top.FStar_Parser_AST.range))
in (let p = (let _110_445 = (let _110_443 = (let _110_442 = (FStar_Absyn_Util.fv tup)
in (_110_442, Some (FStar_Absyn_Syntax.Data_ctor), (FStar_List.append pats (((p, false))::[]))))
in FStar_Absyn_Syntax.Pat_cons (_110_443))
in (let _110_444 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo _110_445 None _110_444)))
in Some ((sc, p)))))
end
| _44_1243 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((FStar_Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_44_1247) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _44_1251; FStar_Parser_AST.level = _44_1249}, arg, _44_1257) when ((FStar_Absyn_Syntax.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Absyn_Syntax.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(let phi = (desugar_formula env arg)
in (let _110_456 = (let _110_455 = (let _110_454 = (let _110_448 = (FStar_Absyn_Syntax.range_of_lid a)
in (FStar_Absyn_Util.fvar None a _110_448))
in (let _110_453 = (let _110_452 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _110_451 = (let _110_450 = (let _110_449 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _110_449))
in (_110_450)::[])
in (_110_452)::_110_451))
in (_110_454, _110_453)))
in (FStar_Absyn_Syntax.mk_Exp_app _110_455))
in (FStar_All.pipe_left pos _110_456)))
end
| FStar_Parser_AST.App (_44_1262) -> begin
(let rec aux = (fun args e -> (match ((let _110_461 = (unparen e)
in _110_461.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(let arg = (let _110_462 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _110_462))
in (aux ((arg)::args) e))
end
| _44_1274 -> begin
(let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _110_468 = (let _110_467 = (let _110_466 = (let _110_465 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_110_465, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_110_466))
in (FStar_Absyn_Syntax.mk_Exp_meta _110_467))
in (FStar_All.pipe_left setpos _110_468))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(let ds_let_rec = (fun _44_1290 -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _44_1294 -> (match (_44_1294) with
| (p, def) -> begin
(match ((is_app_pattern p)) with
| true -> begin
(let _110_472 = (destruct_app_pattern env top_level p)
in (_110_472, def))
end
| false -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _110_473 = (destruct_app_pattern env top_level p)
in (_110_473, def))
end
| _44_1300 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _44_1305); FStar_Parser_AST.prange = _44_1302}, t) -> begin
(match (top_level) with
| true -> begin
(let _110_476 = (let _110_475 = (let _110_474 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_110_474))
in (_110_475, [], Some (t)))
in (_110_476, def))
end
| false -> begin
((FStar_Util.Inl (id), [], Some (t)), def)
end)
end
| FStar_Parser_AST.PatVar (id, _44_1314) -> begin
(match (top_level) with
| true -> begin
(let _110_479 = (let _110_478 = (let _110_477 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_110_477))
in (_110_478, [], None))
in (_110_479, def))
end
| false -> begin
((FStar_Util.Inl (id), [], None), def)
end)
end
| _44_1318 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end)
end))))
in (let _44_1344 = (FStar_List.fold_left (fun _44_1322 _44_1331 -> (match ((_44_1322, _44_1331)) with
| ((env, fnames), ((f, _44_1325, _44_1327), _44_1330)) -> begin
(let _44_1341 = (match (f) with
| FStar_Util.Inl (x) -> begin
(let _44_1336 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_44_1336) with
| (env, xx) -> begin
(env, FStar_Util.Inl (xx))
end))
end
| FStar_Util.Inr (l) -> begin
(let _110_482 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in (_110_482, FStar_Util.Inr (l)))
end)
in (match (_44_1341) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_44_1344) with
| (env', fnames) -> begin
(let fnames = (FStar_List.rev fnames)
in (let desugar_one_def = (fun env lbname _44_1355 -> (match (_44_1355) with
| ((_44_1350, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _110_489 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _110_489 FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _44_1362 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (let body = (desugar_exp env def)
in (mk_lb (lbname, FStar_Absyn_Syntax.tun, body)))))
end))
in (let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| false -> begin
env
end)) fnames funs)
in (let body = (desugar_exp env' body)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (let ds_non_rec = (fun pat t1 t2 -> (let t1 = (desugar_exp env t1)
in (let _44_1375 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_44_1375) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_44_1377) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder (x, t, _44_1387) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _110_501 = (let _110_500 = (FStar_Absyn_Util.bvd_to_exp x t)
in (_110_500, ((pat, None, body))::[]))
in (FStar_Absyn_Syntax.mk_Exp_match _110_501 None body.FStar_Absyn_Syntax.pos))
end)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ((mk_lb (FStar_Util.Inl (x), t, t1)))::[]), body)))))
end)
end))))
in (match ((is_rec || (is_app_pattern pat))) with
| true -> begin
(ds_let_rec ())
end
| false -> begin
(ds_non_rec pat _snd body)
end)))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _110_514 = (let _110_513 = (let _110_512 = (desugar_exp env t1)
in (let _110_511 = (let _110_510 = (let _110_506 = (desugar_exp env t2)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (true))) None t2.FStar_Parser_AST.range), None, _110_506))
in (let _110_509 = (let _110_508 = (let _110_507 = (desugar_exp env t3)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (false))) None t3.FStar_Parser_AST.range), None, _110_507))
in (_110_508)::[])
in (_110_510)::_110_509))
in (_110_512, _110_511)))
in (FStar_Absyn_Syntax.mk_Exp_match _110_513))
in (FStar_All.pipe_left pos _110_514))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let r = top.FStar_Parser_AST.range
in (let handler = (FStar_Parser_AST.mk_function branches r r)
in (let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Absyn_Syntax.Const_unit)) r), None, e))::[]) r r)
in (let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Absyn_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let desugar_branch = (fun _44_1426 -> (match (_44_1426) with
| (pat, wopt, b) -> begin
(let _44_1429 = (desugar_match_pat env pat)
in (match (_44_1429) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _110_517 = (desugar_exp env e)
in Some (_110_517))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _110_523 = (let _110_522 = (let _110_521 = (desugar_exp env e)
in (let _110_520 = (FStar_List.map desugar_branch branches)
in (_110_521, _110_520)))
in (FStar_Absyn_Syntax.mk_Exp_match _110_522))
in (FStar_All.pipe_left pos _110_523)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _110_529 = (let _110_528 = (let _110_527 = (desugar_exp env e)
in (let _110_526 = (desugar_typ env t)
in (_110_527, _110_526, None)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _110_528))
in (FStar_All.pipe_left pos _110_529))
end
| FStar_Parser_AST.Record (_44_1440, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(let _44_1451 = (FStar_List.hd fields)
in (match (_44_1451) with
| (f, _44_1450) -> begin
(let qfn = (fun g -> (FStar_Absyn_Syntax.lid_of_ids (FStar_List.append f.FStar_Absyn_Syntax.ns ((g)::[]))))
in (let _44_1457 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_44_1457) with
| (record, _44_1456) -> begin
(let get_field = (fun xopt f -> (let fn = f.FStar_Absyn_Syntax.ident
in (let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _44_1465 -> (match (_44_1465) with
| (g, _44_1464) -> begin
(let gn = g.FStar_Absyn_Syntax.ident
in (fn.FStar_Absyn_Syntax.idText = gn.FStar_Absyn_Syntax.idText))
end))))
in (match (found) with
| Some (_44_1469, e) -> begin
(let _110_537 = (qfn fn)
in (_110_537, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _110_541 = (let _110_540 = (let _110_539 = (let _110_538 = (FStar_Absyn_Syntax.text_of_lid f)
in (FStar_Util.format1 "Field %s is missing" _110_538))
in (_110_539, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_110_540))
in (Prims.raise _110_541))
end
| Some (x) -> begin
(let _110_542 = (qfn fn)
in (_110_542, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _110_547 = (let _110_546 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _44_1481 -> (match (_44_1481) with
| (f, _44_1480) -> begin
(let _110_545 = (let _110_544 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _110_544))
in (_110_545, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_DesugarEnv.constrname, _110_546))
in FStar_Parser_AST.Construct (_110_547))
end
| Some (e) -> begin
(let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (let xterm = (let _110_549 = (let _110_548 = (FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_110_548))
in (FStar_Parser_AST.mk_term _110_549 x.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Expr))
in (let record = (let _110_552 = (let _110_551 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _44_1489 -> (match (_44_1489) with
| (f, _44_1488) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _110_551))
in FStar_Parser_AST.Record (_110_552))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Absyn_Syntax.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _44_1512); FStar_Absyn_Syntax.tk = _44_1509; FStar_Absyn_Syntax.pos = _44_1507; FStar_Absyn_Syntax.fvs = _44_1505; FStar_Absyn_Syntax.uvs = _44_1503}, args); FStar_Absyn_Syntax.tk = _44_1501; FStar_Absyn_Syntax.pos = _44_1499; FStar_Absyn_Syntax.fvs = _44_1497; FStar_Absyn_Syntax.uvs = _44_1495}, FStar_Absyn_Syntax.Data_app)) -> begin
(let e = (let _110_562 = (let _110_561 = (let _110_560 = (let _110_559 = (let _110_558 = (let _110_557 = (let _110_556 = (let _110_555 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _110_555))
in FStar_Absyn_Syntax.Record_ctor (_110_556))
in Some (_110_557))
in (fv, _110_558))
in (FStar_Absyn_Syntax.mk_Exp_fvar _110_559 None e.FStar_Absyn_Syntax.pos))
in (_110_560, args))
in (FStar_Absyn_Syntax.mk_Exp_app _110_561))
in (FStar_All.pipe_left pos _110_562))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Data_app)))))
end
| _44_1526 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(let _44_1533 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_44_1533) with
| (fieldname, is_rec) -> begin
(let e = (desugar_exp env e)
in (let fn = (let _44_1538 = (FStar_Util.prefix fieldname.FStar_Absyn_Syntax.ns)
in (match (_44_1538) with
| (ns, _44_1537) -> begin
(FStar_Absyn_Syntax.lid_of_ids (FStar_List.append ns ((f.FStar_Absyn_Syntax.ident)::[])))
end))
in (let qual = (match (is_rec) with
| true -> begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end
| false -> begin
None
end)
in (let _110_570 = (let _110_569 = (let _110_568 = (let _110_565 = (FStar_Absyn_Syntax.range_of_lid f)
in (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Record_projector (fn))) fieldname _110_565))
in (let _110_567 = (let _110_566 = (FStar_Absyn_Syntax.varg e)
in (_110_566)::[])
in (_110_568, _110_567)))
in (FStar_Absyn_Syntax.mk_Exp_app _110_569))
in (FStar_All.pipe_left pos _110_570)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _44_1544 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ = (fun env top -> (let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _44_1551 = t
in {FStar_Absyn_Syntax.n = _44_1551.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _44_1551.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _44_1551.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _44_1551.FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun t -> (let rec aux = (fun args t -> (match ((let _110_593 = (unparen t)
in _110_593.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _44_1569 -> begin
(t, args)
end))
in (aux [] t)))
in (match (top.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.tun)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(let t = (label_conjuncts "pre-condition" true lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _110_594 = (desugar_exp env t)
in (FStar_All.pipe_right _110_594 FStar_Absyn_Util.b2t))
end))
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in (match ((is_type env t)) with
| true -> begin
(desugar_typ env t)
end
| false -> begin
(let _110_595 = (desugar_exp env t)
in (FStar_All.pipe_right _110_595 FStar_Absyn_Util.b2t))
end))
end
| FStar_Parser_AST.Op ("*", t1::_44_1583::[]) -> begin
(match ((is_type env t1)) with
| true -> begin
(let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _44_1598 -> begin
(t)::[]
end))
in (let targs = (let _110_600 = (flatten top)
in (FStar_All.pipe_right _110_600 (FStar_List.map (fun t -> (let _110_599 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _110_599))))))
in (let tup = (let _110_601 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _110_601))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end
| false -> begin
(let _110_607 = (let _110_606 = (let _110_605 = (let _110_604 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _110_604))
in (_110_605, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_110_606))
in (Prims.raise _110_607))
end)
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _110_608 = (desugar_exp env top)
in (FStar_All.pipe_right _110_608 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (FStar_List.map (fun t -> (let _110_610 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _110_610))) args)
in (let _110_611 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _110_611 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _110_612 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _110_612))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Absyn_Syntax.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Absyn_Syntax.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _110_613 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _110_613))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _110_614 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _110_614)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let t = (let _110_615 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _110_615))
in (let args = (FStar_List.map (fun _44_1634 -> (match (_44_1634) with
| (t, imp) -> begin
(let _110_617 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _110_617))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let rec aux = (fun env bs _44_8 -> (match (_44_8) with
| [] -> begin
(let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.rev bs), body))))
end
| hd::tl -> begin
(let _44_1652 = (desugar_binding_pat env hd)
in (match (_44_1652) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _110_629 = (let _110_628 = (let _110_627 = (let _110_626 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _110_626))
in (_110_627, hd.FStar_Parser_AST.prange))
in FStar_Absyn_Syntax.Error (_110_628))
in (Prims.raise _110_629))
end
| None -> begin
(let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_44_1658) -> begin
(let rec aux = (fun args e -> (match ((let _110_634 = (unparen e)
in _110_634.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(let arg = (let _110_635 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _110_635))
in (aux ((arg)::args) e))
end
| _44_1670 -> begin
(let head = (desugar_typ env e)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Product ([], t) -> begin
(FStar_All.failwith "Impossible: product with no binders")
end
| FStar_Parser_AST.Product (binders, t) -> begin
(let _44_1682 = (uncurry binders t)
in (match (_44_1682) with
| (bs, t) -> begin
(let rec aux = (fun env bs _44_9 -> (match (_44_9) with
| [] -> begin
(let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.rev bs), cod))))
end
| hd::tl -> begin
(let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _44_1696 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_44_1696) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _44_1703) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(let _44_1717 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _44_1709), env) -> begin
(x, env)
end
| _44_1714 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_44_1717) with
| (b, env) -> begin
(let f = (match ((is_type env f)) with
| true -> begin
(desugar_formula env f)
end
| false -> begin
(let _110_646 = (desugar_exp env f)
in (FStar_All.pipe_right _110_646 FStar_Absyn_Util.b2t))
end)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _110_654 = (let _110_653 = (let _110_652 = (desugar_typ env t)
in (let _110_651 = (desugar_kind env k)
in (_110_652, _110_651)))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _110_653))
in (FStar_All.pipe_left wpos _110_654))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(let _44_1751 = (FStar_List.fold_left (fun _44_1736 b -> (match (_44_1736) with
| (env, tparams, typs) -> begin
(let _44_1740 = (desugar_exp_binder env b)
in (match (_44_1740) with
| (xopt, t) -> begin
(let _44_1746 = (match (xopt) with
| None -> begin
(let _110_657 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in (env, _110_657))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_44_1746) with
| (env, x) -> begin
(let _110_661 = (let _110_660 = (let _110_659 = (let _110_658 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _110_658))
in (_110_659)::[])
in (FStar_List.append typs _110_660))
in (env, (FStar_List.append tparams (((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _110_661))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_44_1751) with
| (env, _44_1749, targs) -> begin
(let tup = (let _110_662 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _110_662))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| FStar_Parser_AST.Record (_44_1754) -> begin
(FStar_All.failwith "Unexpected record type")
end
| FStar_Parser_AST.Let (false, (x, v)::[], t) -> begin
(let let_v = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.let_in_typ)) top.FStar_Parser_AST.range top.FStar_Parser_AST.level), v, FStar_Parser_AST.Nothing))) v.FStar_Parser_AST.range v.FStar_Parser_AST.level)
in (let t' = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((let_v, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs (((x)::[], t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), FStar_Parser_AST.Nothing))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_typ env t')))
end
| (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _44_1773 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _44_1775 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp = (fun r default_ok env t -> (let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun t -> (let _44_1786 = (head_and_args t)
in (match (_44_1786) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText = "Lemma") -> begin
(let unit = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (let _44_1812 = (FStar_All.pipe_right args (FStar_List.partition (fun _44_1794 -> (match (_44_1794) with
| (arg, _44_1793) -> begin
(match ((let _110_674 = (unparen arg)
in _110_674.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _44_1798; FStar_Parser_AST.level = _44_1796}, _44_1803, _44_1805) -> begin
(d.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText = "decreases")
end
| _44_1809 -> begin
false
end)
end))))
in (match (_44_1812) with
| (decreases_clause, args) -> begin
(let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (unit)::(req_true)::(ens)::(nil_pat)::[])
end
| req::ens::[] -> begin
(unit)::(req)::(ens)::(nil_pat)::[]
end
| more -> begin
(unit)::more
end)
in (let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct ((lemma, (FStar_List.append args decreases_clause)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _110_675 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Absyn_Syntax.lid_equals _110_675 FStar_Absyn_Const.prims_lid))) -> begin
(let args = (FStar_List.map (fun _44_1827 -> (match (_44_1827) with
| (t, imp) -> begin
(let _110_677 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _110_677))
end)) args)
in (let _110_678 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _110_678 args)))
end
| _44_1830 -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _44_1834 = (FStar_Absyn_Util.head_and_args t)
in (match (_44_1834) with
| (head, args) -> begin
(match ((let _110_680 = (let _110_679 = (FStar_Absyn_Util.compress_typ head)
in _110_679.FStar_Absyn_Syntax.n)
in (_110_680, args))) with
| (FStar_Absyn_Syntax.Typ_const (eff), (FStar_Util.Inl (result_typ), _44_1841)::rest) -> begin
(let _44_1881 = (FStar_All.pipe_right rest (FStar_List.partition (fun _44_10 -> (match (_44_10) with
| (FStar_Util.Inr (_44_1847), _44_1850) -> begin
false
end
| (FStar_Util.Inl (t), _44_1855) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _44_1864; FStar_Absyn_Syntax.pos = _44_1862; FStar_Absyn_Syntax.fvs = _44_1860; FStar_Absyn_Syntax.uvs = _44_1858}, (FStar_Util.Inr (_44_1869), _44_1872)::[]) -> begin
(FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _44_1878 -> begin
false
end)
end))))
in (match (_44_1881) with
| (dec, rest) -> begin
(let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _44_11 -> (match (_44_11) with
| (FStar_Util.Inl (t), _44_1886) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_44_1889, (FStar_Util.Inr (arg), _44_1893)::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _44_1899 -> begin
(FStar_All.failwith "impos")
end)
end
| _44_1901 -> begin
(FStar_All.failwith "impos")
end))))
in (match (((FStar_Parser_DesugarEnv.is_effect_name env eff.FStar_Absyn_Syntax.v) || (FStar_Absyn_Syntax.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid))) with
| true -> begin
(match (((FStar_Absyn_Syntax.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0))) with
| true -> begin
(FStar_Absyn_Syntax.mk_Total result_typ)
end
| false -> begin
(let flags = (match ((FStar_Absyn_Syntax.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Absyn_Syntax.LEMMA)::[]
end
| false -> begin
(match ((FStar_Absyn_Syntax.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| false -> begin
(match ((FStar_Absyn_Syntax.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_ML_lid)) with
| true -> begin
(FStar_Absyn_Syntax.MLEFFECT)::[]
end
| false -> begin
[]
end)
end)
end)
in (let rest = (match ((FStar_Absyn_Syntax.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid)) with
| true -> begin
(match (rest) with
| req::ens::(FStar_Util.Inr (pat), aq)::[] -> begin
(let _110_687 = (let _110_686 = (let _110_685 = (let _110_684 = (let _110_683 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((pat, FStar_Absyn_Syntax.Meta_smt_pat))))
in FStar_Util.Inr (_110_683))
in (_110_684, aq))
in (_110_685)::[])
in (ens)::_110_686)
in (req)::_110_687)
end
| _44_1912 -> begin
rest
end)
end
| false -> begin
rest
end)
in (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = eff.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.result_typ = result_typ; FStar_Absyn_Syntax.effect_args = rest; FStar_Absyn_Syntax.flags = (FStar_List.append flags decreases_clause)})))
end)
end
| false -> begin
(match (default_ok) with
| true -> begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end
| false -> begin
(let _110_689 = (let _110_688 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _110_688))
in (fail _110_689))
end)
end))
end))
end
| _44_1915 -> begin
(match (default_ok) with
| true -> begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end
| false -> begin
(let _110_691 = (let _110_690 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _110_690))
in (fail _110_691))
end)
end)
end))))))
and desugar_kind = (fun env k -> (let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (let setpos = (fun kk -> (let _44_1922 = kk
in {FStar_Absyn_Syntax.n = _44_1922.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _44_1922.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _44_1922.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _44_1922.FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Absyn_Syntax.ns = _44_1931; FStar_Absyn_Syntax.ident = _44_1929; FStar_Absyn_Syntax.nsstr = _44_1927; FStar_Absyn_Syntax.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Absyn_Syntax.ns = _44_1940; FStar_Absyn_Syntax.ident = _44_1938; FStar_Absyn_Syntax.nsstr = _44_1936; FStar_Absyn_Syntax.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _110_703 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _110_703))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _44_1948 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(let _44_1956 = (uncurry bs k)
in (match (_44_1956) with
| (bs, k) -> begin
(let rec aux = (fun env bs _44_12 -> (match (_44_12) with
| [] -> begin
(let _110_714 = (let _110_713 = (let _110_712 = (desugar_kind env k)
in ((FStar_List.rev bs), _110_712))
in (FStar_Absyn_Syntax.mk_Kind_arrow _110_713))
in (FStar_All.pipe_left pos _110_714))
end
| hd::tl -> begin
(let _44_1967 = (let _110_716 = (let _110_715 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _110_715 hd))
in (FStar_All.pipe_right _110_716 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_44_1967) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_DesugarEnv.find_kind_abbrev env l)) with
| None -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end
| Some (l) -> begin
(let args = (FStar_List.map (fun _44_1977 -> (match (_44_1977) with
| (t, b) -> begin
(let qual = (match ((b = FStar_Parser_AST.Hash)) with
| true -> begin
Some (FStar_Absyn_Syntax.Implicit)
end
| false -> begin
None
end)
in (let _110_718 = (desugar_typ_or_exp env t)
in (_110_718, qual)))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _44_1981 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' = (fun env f -> (let connective = (fun s -> (match (s) with
| "/\\" -> begin
Some (FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
Some (FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
Some (FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
Some (FStar_Absyn_Const.iff_lid)
end
| "~" -> begin
Some (FStar_Absyn_Const.not_lid)
end
| _44_1992 -> begin
None
end))
in (let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _44_1997 = t
in {FStar_Absyn_Syntax.n = _44_1997.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _44_1997.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _44_1997.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _44_1997.FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun q qt b pats body -> (let tk = (desugar_binder env (let _44_2005 = b
in {FStar_Parser_AST.b = _44_2005.FStar_Parser_AST.b; FStar_Parser_AST.brange = _44_2005.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _44_2005.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _44_2015 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_44_2015) with
| (env, a) -> begin
(let pats = (FStar_List.map (fun e -> (let _110_749 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _110_749))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _44_2021 -> begin
(let _110_750 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (FStar_All.pipe_left setpos _110_750))
end)
in (let body = (let _110_756 = (let _110_755 = (let _110_754 = (let _110_753 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_110_753)::[])
in (_110_754, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _110_755))
in (FStar_All.pipe_left pos _110_756))
in (let _110_761 = (let _110_760 = (let _110_757 = (FStar_Absyn_Util.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _110_757 FStar_Absyn_Syntax.kun))
in (let _110_759 = (let _110_758 = (FStar_Absyn_Syntax.targ body)
in (_110_758)::[])
in (FStar_Absyn_Util.mk_typ_app _110_760 _110_759)))
in (FStar_All.pipe_left setpos _110_761))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _44_2031 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_44_2031) with
| (env, x) -> begin
(let pats = (FStar_List.map (fun e -> (let _110_763 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _110_763))) pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _44_2037 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (let _110_769 = (let _110_768 = (let _110_767 = (let _110_766 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_110_766)::[])
in (_110_767, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _110_768))
in (FStar_All.pipe_left pos _110_769))
in (let _110_774 = (let _110_773 = (let _110_770 = (FStar_Absyn_Util.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _110_770 FStar_Absyn_Syntax.kun))
in (let _110_772 = (let _110_771 = (FStar_Absyn_Syntax.targ body)
in (_110_771)::[])
in (FStar_Absyn_Util.mk_typ_app _110_773 _110_772)))
in (FStar_All.pipe_left setpos _110_774))))))
end))
end
| _44_2041 -> begin
(FStar_All.failwith "impossible")
end)))
in (let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _110_789 = (q (rest, pats, body))
in (let _110_788 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _110_789 _110_788 FStar_Parser_AST.Formula)))
in (let _110_790 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _110_790 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _44_2055 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _110_791 = (unparen f)
in _110_791.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, l, FStar_Absyn_Syntax.dummyRange, p)))))
end
| FStar_Parser_AST.Op ("==", hd::_args) -> begin
(let args = (hd)::_args
in (let args = (FStar_List.map (fun t -> (let _110_793 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _110_793))) args)
in (let eq = (match ((is_type env hd)) with
| true -> begin
(let _110_794 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _110_794 FStar_Absyn_Syntax.kun))
end
| false -> begin
(let _110_795 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _110_795 FStar_Absyn_Syntax.kun))
end)
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match (((connective s), args)) with
| (Some (conn), _44_2081::_44_2079::[]) -> begin
(let _110_800 = (let _110_796 = (FStar_Absyn_Util.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _110_796 FStar_Absyn_Syntax.kun))
in (let _110_799 = (FStar_List.map (fun x -> (let _110_798 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _110_798))) args)
in (FStar_Absyn_Util.mk_typ_app _110_800 _110_799)))
end
| _44_2086 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _110_801 = (desugar_exp env f)
in (FStar_All.pipe_right _110_801 FStar_Absyn_Util.b2t))
end)
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _110_806 = (let _110_802 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _110_802 FStar_Absyn_Syntax.kun))
in (let _110_805 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _110_804 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _110_804))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _110_806 _110_805)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _110_808 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _110_808)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _110_810 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _110_810)))
end
| FStar_Parser_AST.QForall (b::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.forall_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.QExists (b::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.exists_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _44_2148 -> begin
(match ((is_type env f)) with
| true -> begin
(desugar_typ env f)
end
| false -> begin
(let _110_811 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _110_811))
end)
end)))))))
and desugar_formula = (fun env t -> (desugar_formula' (let _44_2151 = env
in {FStar_Parser_DesugarEnv.curmodule = _44_2151.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _44_2151.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _44_2151.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.sigaccum = _44_2151.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _44_2151.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _44_2151.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _44_2151.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _44_2151.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _44_2151.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _44_2151.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder = (fun env b -> (match ((is_type_binder env b)) with
| true -> begin
(let _110_816 = (desugar_type_binder env b)
in FStar_Util.Inl (_110_816))
end
| false -> begin
(let _110_817 = (desugar_exp_binder env b)
in FStar_Util.Inr (_110_817))
end))
and typars_of_binders = (fun env bs -> (let _44_2184 = (FStar_List.fold_left (fun _44_2159 b -> (match (_44_2159) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _44_2161 = b
in {FStar_Parser_AST.b = _44_2161.FStar_Parser_AST.b; FStar_Parser_AST.brange = _44_2161.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _44_2161.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _44_2171 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_44_2171) with
| (env, a) -> begin
(env, ((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), b.FStar_Parser_AST.aqual))::out)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _44_2179 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_44_2179) with
| (env, x) -> begin
(env, ((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), b.FStar_Parser_AST.aqual))::out)
end))
end
| _44_2181 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_44_2184) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_exp_binder = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _110_824 = (desugar_typ env t)
in (Some (x), _110_824))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _110_825 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _110_825))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _110_826 = (desugar_typ env t)
in (None, _110_826))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Absyn_Syntax.tun)
end
| _44_2198 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.FStar_Parser_AST.brange))))
end))
and desugar_type_binder = (fun env b -> (let fail = (fun _44_2202 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.FStar_Parser_AST.brange))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _110_831 = (desugar_kind env t)
in (Some (x), _110_831))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _110_832 = (desugar_kind env t)
in (None, _110_832))
end
| FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _44_2213 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _44_2213.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _44_2213.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _44_2213.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _44_2213.FStar_Absyn_Syntax.uvs}))
end
| _44_2216 -> begin
(fail ())
end)))

let gather_tc_binders = (fun tps k -> (let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_44_2227, k) -> begin
(aux bs k)
end
| _44_2232 -> begin
bs
end))
in (let _110_841 = (aux tps k)
in (FStar_All.pipe_right _110_841 FStar_Absyn_Util.name_binders))))

let mk_data_discriminators = (fun quals env t tps k datas -> (let quals = (fun q -> (match (((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end
| false -> begin
(FStar_List.append q quals)
end))
in (let binders = (gather_tc_binders tps k)
in (let p = (FStar_Absyn_Syntax.range_of_lid t)
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _44_2246 -> (match (_44_2246) with
| (x, _44_2245) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (let _110_862 = (let _110_861 = (let _110_860 = (let _110_859 = (let _110_858 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _110_857 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_110_858, _110_857)))
in (FStar_Absyn_Syntax.mk_Typ_app' _110_859 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _110_860))
in (_110_861)::[])
in (FStar_List.append imp_binders _110_862))
in (let disc_type = (let _110_865 = (let _110_864 = (let _110_863 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _110_863 p))
in (binders, _110_864))
in (FStar_Absyn_Syntax.mk_Typ_fun _110_865 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _110_869 = (let _110_868 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in (let _110_867 = (FStar_Absyn_Syntax.range_of_lid disc_name)
in (disc_name, disc_type, _110_868, _110_867)))
in FStar_Absyn_Syntax.Sig_val_decl (_110_869)))))))))))))

let mk_indexed_projectors = (fun fvq refine_domain env _44_2258 lid formals t -> (match (_44_2258) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (FStar_Absyn_Syntax.range_of_lid lid)
in (let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (let projectee = (let _110_880 = (FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _110_879 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _110_880; FStar_Absyn_Syntax.realname = _110_879}))
in (let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (let arg_binder = (let arg_typ = (let _110_883 = (let _110_882 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _110_881 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_110_882, _110_881)))
in (FStar_Absyn_Syntax.mk_Typ_app' _110_883 None p))
in (match ((not (refine_domain))) with
| true -> begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end
| false -> begin
(let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _110_893 = (let _110_892 = (let _110_891 = (let _110_890 = (let _110_889 = (let _110_888 = (let _110_887 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _110_886 = (let _110_885 = (let _110_884 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _110_884))
in (_110_885)::[])
in (_110_887, _110_886)))
in (FStar_Absyn_Syntax.mk_Exp_app _110_888 None p))
in (FStar_Absyn_Util.b2t _110_889))
in (x, _110_890))
in (FStar_Absyn_Syntax.mk_Typ_refine _110_891 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _110_892))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _110_893))))
end))
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _44_2275 -> (match (_44_2275) with
| (x, _44_2274) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _110_901 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(let _44_2286 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_44_2286) with
| (field_name, _44_2285) -> begin
(let proj = (let _110_898 = (let _110_897 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in (_110_897, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _110_898 None p))
in (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, proj)))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(let _44_2293 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_44_2293) with
| (field_name, _44_2292) -> begin
(let proj = (let _110_900 = (let _110_899 = (FStar_Absyn_Util.fvar None field_name p)
in (_110_899, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _110_900 None p))
in (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, proj)))::[])
end))
end))))
in (FStar_All.pipe_right _110_901 FStar_List.flatten))
in (let ntps = (FStar_List.length tps)
in (let all_params = (let _110_903 = (FStar_All.pipe_right tps (FStar_List.map (fun _44_2300 -> (match (_44_2300) with
| (b, _44_2299) -> begin
(b, Some (FStar_Absyn_Syntax.Implicit))
end))))
in (FStar_List.append _110_903 formals))
in (let _110_941 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(let _44_2309 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_44_2309) with
| (field_name, _44_2308) -> begin
(let kk = (let _110_907 = (let _110_906 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (binders, _110_906))
in (FStar_Absyn_Syntax.mk_Kind_arrow _110_907 p))
in (let _110_910 = (let _110_909 = (let _110_908 = (FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, [], kk, [], [], (FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inl (a.FStar_Absyn_Syntax.v))))::[], _110_908))
in FStar_Absyn_Syntax.Sig_tycon (_110_909))
in (_110_910)::[]))
end))
end
| FStar_Util.Inr (x) -> begin
(let _44_2316 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_44_2316) with
| (field_name, _44_2315) -> begin
(let t = (let _110_913 = (let _110_912 = (let _110_911 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _110_911 p))
in (binders, _110_912))
in (FStar_Absyn_Syntax.mk_Typ_fun _110_913 None p))
in (let quals = (fun q -> (match (((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(FStar_Absyn_Syntax.Assumption)::q
end
| false -> begin
q
end))
in (let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inr (x.FStar_Absyn_Syntax.v))))::[]))
in (let impl = (match ((((let _110_916 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.prims_lid _110_916)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (FStar_ST.read FStar_Options.__temp_no_proj))) with
| true -> begin
[]
end
| false -> begin
(let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let as_imp = (fun _44_13 -> (match (_44_13) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _44_2326 -> begin
false
end))
in (let arg_pats = (let _110_931 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_44_2331), imp) -> begin
(match ((j < ntps)) with
| true -> begin
[]
end
| false -> begin
(let _110_924 = (let _110_923 = (let _110_922 = (let _110_921 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_110_921))
in (pos _110_922))
in (_110_923, (as_imp imp)))
in (_110_924)::[])
end)
end
| (FStar_Util.Inr (_44_2336), imp) -> begin
(match (((i + ntps) = j)) with
| true -> begin
(let _110_926 = (let _110_925 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in (_110_925, (as_imp imp)))
in (_110_926)::[])
end
| false -> begin
(let _110_930 = (let _110_929 = (let _110_928 = (let _110_927 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_110_927))
in (pos _110_928))
in (_110_929, (as_imp imp)))
in (_110_930)::[])
end)
end))))
in (FStar_All.pipe_right _110_931 FStar_List.flatten))
in (let pat = (let _110_936 = (let _110_934 = (let _110_933 = (let _110_932 = (FStar_Absyn_Util.fv lid)
in (_110_932, Some (fvq), arg_pats))
in FStar_Absyn_Syntax.Pat_cons (_110_933))
in (FStar_All.pipe_right _110_934 pos))
in (let _110_935 = (FStar_Absyn_Util.bvar_to_exp projection)
in (_110_936, None, _110_935)))
in (let body = (FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (let imp = (let _110_937 = (FStar_Absyn_Syntax.range_of_lid field_name)
in (FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None _110_937))
in (let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end)
in (let _110_940 = (let _110_939 = (let _110_938 = (FStar_Absyn_Syntax.range_of_lid field_name)
in (field_name, t, quals, _110_938))
in FStar_Absyn_Syntax.Sig_val_decl (_110_939))
in (_110_940)::impl)))))
end))
end))))
in (FStar_All.pipe_right _110_941 FStar_List.flatten))))))))))))))
end))

let mk_data_projectors = (fun env _44_16 -> (match (_44_16) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _44_2353, _44_2355) when (not ((FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = (match ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _44_14 -> (match (_44_14) with
| FStar_Absyn_Syntax.RecordConstructor (_44_2360) -> begin
true
end
| _44_2363 -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
(let _44_2369 = tycon
in (match (_44_2369) with
| (l, _44_2366, _44_2368) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _44_2373 -> begin
true
end)
end))
end)
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(let cod = (FStar_Absyn_Util.comp_result cod)
in (let qual = (match ((FStar_Util.find_map quals (fun _44_15 -> (match (_44_15) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((lid, fns)))
end
| _44_2384 -> begin
None
end)))) with
| None -> begin
FStar_Absyn_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (mk_indexed_projectors qual refine_domain env tycon lid formals cod)))
end
| _44_2390 -> begin
[]
end))
end
| _44_2392 -> begin
[]
end))

let rec desugar_tycon = (fun env rng quals tcs -> (let tycon_id = (fun _44_17 -> (match (_44_17) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _110_961 = (let _110_960 = (FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_110_960))
in (FStar_Parser_AST.mk_term _110_961 x.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (let apply_binders = (fun t binders -> (let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _44_2457 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _110_974 = (let _110_973 = (let _110_972 = (binder_to_term b)
in (out, _110_972, (imp_of_aqual b)))
in FStar_Parser_AST.App (_110_973))
in (FStar_Parser_AST.mk_term _110_974 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (let tycon_record_as_variant = (fun _44_18 -> (match (_44_18) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(let constrName = (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "Mk" id.FStar_Absyn_Syntax.idText), id.FStar_Absyn_Syntax.idRange))
in (let mfields = (FStar_List.map (fun _44_2470 -> (match (_44_2470) with
| (x, t) -> begin
(let _110_980 = (let _110_979 = (let _110_978 = (FStar_Absyn_Util.mangle_field_name x)
in (_110_978, t))
in FStar_Parser_AST.Annotated (_110_979))
in (FStar_Parser_AST.mk_binder _110_980 x.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Expr None))
end)) fields)
in (let result = (let _110_983 = (let _110_982 = (let _110_981 = (FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_110_981))
in (FStar_Parser_AST.mk_term _110_982 id.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Type))
in (apply_binders _110_983 parms))
in (let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Type)
in (let _110_985 = (FStar_All.pipe_right fields (FStar_List.map (fun _44_2477 -> (match (_44_2477) with
| (x, _44_2476) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _110_985))))))
end
| _44_2479 -> begin
(FStar_All.failwith "impossible")
end))
in (let desugar_abstract_tc = (fun quals _env mutuals _44_19 -> (match (_44_19) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(let _44_2493 = (typars_of_binders _env binders)
in (match (_44_2493) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (let tconstr = (let _110_996 = (let _110_995 = (let _110_994 = (FStar_Absyn_Syntax.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_110_994))
in (FStar_Parser_AST.mk_term _110_995 id.FStar_Absyn_Syntax.idRange FStar_Parser_AST.Type))
in (apply_binders _110_996 binders))
in (let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, _env2, se, tconstr)))))))
end))
end
| _44_2504 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (let push_tparam = (fun env _44_20 -> (match (_44_20) with
| (FStar_Util.Inr (x), _44_2511) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _44_2516) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_44_2520)::[] -> begin
(let tc = (FStar_List.hd tcs)
in (let _44_2531 = (desugar_abstract_tc quals env [] tc)
in (match (_44_2531) with
| (_44_2525, _44_2527, se, _44_2530) -> begin
(let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(let _44_2542 = (typars_of_binders env binders)
in (match (_44_2542) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
(match ((FStar_Util.for_some (fun _44_21 -> (match (_44_21) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _44_2547 -> begin
false
end)) quals)) with
| true -> begin
FStar_Absyn_Syntax.mk_Kind_effect
end
| false -> begin
FStar_Absyn_Syntax.kun
end)
end
| Some (k) -> begin
(desugar_kind env' k)
end)
in (let t0 = t
in (let quals = (match ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _44_22 -> (match (_44_22) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _44_2555 -> begin
false
end))))) with
| true -> begin
quals
end
| false -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Absyn_Syntax.Logic)::quals
end
| false -> begin
quals
end)
end)
in (let se = (match ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Effect))) with
| true -> begin
(let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let _110_1008 = (let _110_1007 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _110_1006 = (FStar_All.pipe_right quals (FStar_List.filter (fun _44_23 -> (match (_44_23) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _44_2561 -> begin
true
end))))
in (_110_1007, typars, c, _110_1006, rng)))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_110_1008)))
end
| false -> begin
(let t = (desugar_typ env' t)
in (let _110_1010 = (let _110_1009 = (FStar_Parser_DesugarEnv.qualify env id)
in (_110_1009, typars, k, t, quals, rng))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_110_1010)))
end)
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_44_2566)::[] -> begin
(let trec = (FStar_List.hd tcs)
in (let _44_2572 = (tycon_record_as_variant trec)
in (match (_44_2572) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _44_2576::_44_2574 -> begin
(let env0 = env
in (let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun quals et tc -> (let _44_2587 = et
in (match (_44_2587) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_44_2589) -> begin
(let trec = tc
in (let _44_2594 = (tycon_record_as_variant trec)
in (match (_44_2594) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(let _44_2606 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_44_2606) with
| (env, _44_2603, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(let _44_2618 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_44_2618) with
| (env, _44_2615, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _44_2620 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (let _44_2623 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_44_2623) with
| (env, tcs) -> begin
(let tcs = (FStar_List.rev tcs)
in (let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _44_25 -> (match (_44_25) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _44_2630, _44_2632, _44_2634, _44_2636), t, quals) -> begin
(let env_tps = (push_tparams env tpars)
in (let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _44_2650, tags, _44_2653), constrs, tconstr, quals) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tpars)
in (let _44_2684 = (let _110_1026 = (FStar_All.pipe_right constrs (FStar_List.map (fun _44_2666 -> (match (_44_2666) with
| (id, topt, of_notation) -> begin
(let t = (match (of_notation) with
| true -> begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[], tconstr))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end
| None -> begin
tconstr
end)
end
| false -> begin
(match (topt) with
| None -> begin
(FStar_All.failwith "Impossible")
end
| Some (t) -> begin
t
end)
end)
in (let t = (let _110_1021 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _110_1020 = (close env_tps t)
in (desugar_typ _110_1021 _110_1020)))
in (let name = (FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _44_24 -> (match (_44_24) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _44_2680 -> begin
[]
end))))
in (let _110_1025 = (let _110_1024 = (let _110_1023 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in (name, _110_1023, tycon, quals, mutuals, rng))
in FStar_Absyn_Syntax.Sig_datacon (_110_1024))
in (name, _110_1025))))))
end))))
in (FStar_All.pipe_left FStar_List.split _110_1026))
in (match (_44_2684) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _44_2686 -> begin
(FStar_All.failwith "impossible")
end))))
in (let bundle = (let _110_1028 = (let _110_1027 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _110_1027, rng))
in FStar_Absyn_Syntax.Sig_bundle (_110_1028))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _44_26 -> (match (_44_26) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _44_2696, constrs, quals, _44_2700) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _44_2704 -> begin
[]
end))))
in (let ops = (FStar_List.append discs data_ops)
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end)))))))))))

let desugar_binders = (fun env binders -> (let _44_2735 = (FStar_List.fold_left (fun _44_2713 b -> (match (_44_2713) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _44_2722 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_44_2722) with
| (env, a) -> begin
(let _110_1037 = (let _110_1036 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_110_1036)::binders)
in (env, _110_1037))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _44_2730 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_44_2730) with
| (env, x) -> begin
(let _110_1039 = (let _110_1038 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_110_1038)::binders)
in (env, _110_1039))
end))
end
| _44_2732 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_44_2735) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

let rec desugar_decl = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(let se = FStar_Absyn_Syntax.Sig_pragma ((p, d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(desugar_tycon env d.FStar_Parser_AST.drange qual tcs)
end
| FStar_Parser_AST.ToplevelLet (isrec, lets) -> begin
(match ((let _110_1045 = (let _110_1044 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Absyn_Syntax.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _110_1044))
in _110_1045.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _44_2754) -> begin
(let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _44_2761 -> begin
(FStar_All.failwith "impossible")
end))))
in (let quals = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _44_27 -> (match (_44_27) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_44_2771); FStar_Absyn_Syntax.lbtyp = _44_2769; FStar_Absyn_Syntax.lbeff = _44_2767; FStar_Absyn_Syntax.lbdef = _44_2765} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _44_2779; FStar_Absyn_Syntax.lbeff = _44_2777; FStar_Absyn_Syntax.lbdef = _44_2775} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
in (let s = FStar_Absyn_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _44_2787 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(let e = (desugar_exp env t)
in (let se = FStar_Absyn_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(let f = (desugar_formula env t)
in (let _110_1051 = (let _110_1050 = (let _110_1049 = (let _110_1048 = (FStar_Parser_DesugarEnv.qualify env id)
in (_110_1048, f, (FStar_Absyn_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_assume (_110_1049))
in (_110_1050)::[])
in (env, _110_1051)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(let t = (let _110_1052 = (close_fun env t)
in (desugar_typ env _110_1052))
in (let quals = (match ((env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface)) with
| true -> begin
(FStar_Absyn_Syntax.Assumption)::quals
end
| false -> begin
quals
end)
in (let se = (let _110_1054 = (let _110_1053 = (FStar_Parser_DesugarEnv.qualify env id)
in (_110_1053, t, quals, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_val_decl (_110_1054))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(let t = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (let l = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(let t = (desugar_typ env term)
in (let t = (let _110_1059 = (let _110_1058 = (let _110_1055 = (FStar_Absyn_Syntax.null_v_binder t)
in (_110_1055)::[])
in (let _110_1057 = (let _110_1056 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _110_1056))
in (_110_1058, _110_1057)))
in (FStar_Absyn_Syntax.mk_Typ_fun _110_1059 None d.FStar_Parser_AST.drange))
in (let l = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(let _44_2840 = (desugar_binders env binders)
in (match (_44_2840) with
| (env_k, binders) -> begin
(let k = (desugar_kind env_k k)
in (let name = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((name, binders, k, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(let env0 = env
in (let _44_2856 = (desugar_binders env eff_binders)
in (match (_44_2856) with
| (env, binders) -> begin
(let defn = (desugar_typ env defn)
in (let _44_2860 = (FStar_Absyn_Util.head_and_args defn)
in (match (_44_2860) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _110_1064 = (let _110_1063 = (let _110_1062 = (let _110_1061 = (let _110_1060 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat "Effect " _110_1060))
in (Prims.strcat _110_1061 " not found"))
in (_110_1062, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_110_1063))
in (Prims.raise _110_1064))
end
| Some (ed) -> begin
(let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (let sub = (FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _110_1081 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _110_1080 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _110_1079 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _110_1078 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _110_1077 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _110_1076 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _110_1075 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _110_1074 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _110_1073 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _110_1072 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _110_1071 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _110_1070 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _110_1069 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _110_1068 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _110_1067 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _110_1066 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _110_1081; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = quals; FStar_Absyn_Syntax.signature = _110_1080; FStar_Absyn_Syntax.ret = _110_1079; FStar_Absyn_Syntax.bind_wp = _110_1078; FStar_Absyn_Syntax.bind_wlp = _110_1077; FStar_Absyn_Syntax.if_then_else = _110_1076; FStar_Absyn_Syntax.ite_wp = _110_1075; FStar_Absyn_Syntax.ite_wlp = _110_1074; FStar_Absyn_Syntax.wp_binop = _110_1073; FStar_Absyn_Syntax.wp_as_type = _110_1072; FStar_Absyn_Syntax.close_wp = _110_1071; FStar_Absyn_Syntax.close_wp_t = _110_1070; FStar_Absyn_Syntax.assert_p = _110_1069; FStar_Absyn_Syntax.assume_p = _110_1068; FStar_Absyn_Syntax.null_wp = _110_1067; FStar_Absyn_Syntax.trivial = _110_1066}))))))))))))))))
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _44_2872 -> begin
(let _110_1085 = (let _110_1084 = (let _110_1083 = (let _110_1082 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _110_1082 " is not an effect"))
in (_110_1083, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_110_1084))
in (Prims.raise _110_1085))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(let env0 = env
in (let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (let _44_2886 = (desugar_binders env eff_binders)
in (match (_44_2886) with
| (env, binders) -> begin
(let eff_k = (desugar_kind env eff_kind)
in (let _44_2897 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _44_2890 decl -> (match (_44_2890) with
| (env, out) -> begin
(let _44_2894 = (desugar_decl env decl)
in (match (_44_2894) with
| (env, ses) -> begin
(let _110_1089 = (let _110_1088 = (FStar_List.hd ses)
in (_110_1088)::out)
in (env, _110_1089))
end))
end)) (env, [])))
in (match (_44_2897) with
| (env, decls) -> begin
(let decls = (FStar_List.rev decls)
in (let lookup = (fun s -> (match ((let _110_1093 = (let _110_1092 = (FStar_Absyn_Syntax.mk_ident (s, d.FStar_Parser_AST.drange))
in (FStar_Parser_DesugarEnv.qualify env _110_1092))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _110_1093))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat (Prims.strcat "Monad " eff_name.FStar_Absyn_Syntax.idText) " expects definition of ") s), d.FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _110_1108 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _110_1107 = (lookup "return")
in (let _110_1106 = (lookup "bind_wp")
in (let _110_1105 = (lookup "bind_wlp")
in (let _110_1104 = (lookup "if_then_else")
in (let _110_1103 = (lookup "ite_wp")
in (let _110_1102 = (lookup "ite_wlp")
in (let _110_1101 = (lookup "wp_binop")
in (let _110_1100 = (lookup "wp_as_type")
in (let _110_1099 = (lookup "close_wp")
in (let _110_1098 = (lookup "close_wp_t")
in (let _110_1097 = (lookup "assert_p")
in (let _110_1096 = (lookup "assume_p")
in (let _110_1095 = (lookup "null_wp")
in (let _110_1094 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _110_1108; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = quals; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _110_1107; FStar_Absyn_Syntax.bind_wp = _110_1106; FStar_Absyn_Syntax.bind_wlp = _110_1105; FStar_Absyn_Syntax.if_then_else = _110_1104; FStar_Absyn_Syntax.ite_wp = _110_1103; FStar_Absyn_Syntax.ite_wlp = _110_1102; FStar_Absyn_Syntax.wp_binop = _110_1101; FStar_Absyn_Syntax.wp_as_type = _110_1100; FStar_Absyn_Syntax.close_wp = _110_1099; FStar_Absyn_Syntax.close_wp_t = _110_1098; FStar_Absyn_Syntax.assert_p = _110_1097; FStar_Absyn_Syntax.assume_p = _110_1096; FStar_Absyn_Syntax.null_wp = _110_1095; FStar_Absyn_Syntax.trivial = _110_1094})))))))))))))))
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _110_1115 = (let _110_1114 = (let _110_1113 = (let _110_1112 = (let _110_1111 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Effect name " _110_1111))
in (Prims.strcat _110_1112 " not found"))
in (_110_1113, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_110_1114))
in (Prims.raise _110_1115))
end
| Some (l) -> begin
l
end))
in (let src = (lookup l.FStar_Parser_AST.msource)
in (let dst = (lookup l.FStar_Parser_AST.mdest)
in (let lift = (desugar_typ env l.FStar_Parser_AST.lift_op)
in (let se = FStar_Absyn_Syntax.Sig_sub_effect (({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

let desugar_decls = (fun env decls -> (FStar_List.fold_left (fun _44_2922 d -> (match (_44_2922) with
| (env, sigelts) -> begin
(let _44_2926 = (desugar_decl env d)
in (match (_44_2926) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

let open_prims_all = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]

let desugar_modul_common = (fun curmod env m -> (let open_ns = (fun mname d -> (let d = (match (((FStar_List.length mname.FStar_Absyn_Syntax.ns) <> 0)) with
| true -> begin
(let _110_1132 = (let _110_1131 = (let _110_1129 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Absyn_Syntax.ns)
in FStar_Parser_AST.Open (_110_1129))
in (let _110_1130 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _110_1131 _110_1130)))
in (_110_1132)::d)
end
| false -> begin
d
end)
in d))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod, _44_2937) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _44_2956 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _110_1134 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _110_1133 = (open_ns mname decls)
in (_110_1134, mname, _110_1133, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _110_1136 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _110_1135 = (open_ns mname decls)
in (_110_1136, mname, _110_1135, false)))
end)
in (match (_44_2956) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(let _44_2959 = (desugar_decls env decls)
in (match (_44_2959) with
| (env, sigelts) -> begin
(let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul, pop_when_done))
end))
end)))))

let desugar_partial_modul = (fun curmod env m -> (let m = (match ((FStar_ST.read FStar_Options.interactive_fsi)) with
| true -> begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _110_1143 = (let _110_1142 = (let _110_1141 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_Util.for_some (fun m -> (m = mname.FStar_Absyn_Syntax.str)) _110_1141))
in (mname, decls, _110_1142))
in FStar_Parser_AST.Interface (_110_1143))
end
| FStar_Parser_AST.Interface (mname, _44_2971, _44_2973) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText))
end)
end
| false -> begin
m
end)
in (let _44_2981 = (desugar_modul_common curmod env m)
in (match (_44_2981) with
| (x, y, _44_2980) -> begin
(x, y)
end))))

let desugar_modul = (fun env m -> (let _44_2987 = (desugar_modul_common None env m)
in (match (_44_2987) with
| (env, modul, pop_when_done) -> begin
(let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _44_2989 = (match ((FStar_Options.should_dump modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)) with
| true -> begin
(let _110_1148 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.fprint1 "%s\n" _110_1148))
end
| false -> begin
()
end)
in (let _110_1149 = (match (pop_when_done) with
| true -> begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end
| false -> begin
env
end)
in (_110_1149, modul))))
end)))

let desugar_file = (fun env f -> (let _44_3002 = (FStar_List.fold_left (fun _44_2995 m -> (match (_44_2995) with
| (env, mods) -> begin
(let _44_2999 = (desugar_modul env m)
in (match (_44_2999) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_44_3002) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

let add_modul_to_env = (fun m en -> (let _44_3007 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_44_3007) with
| (en, pop_when_done) -> begin
(let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (let _44_3008 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _44_3008.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _44_3008.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.sigaccum = _44_3008.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _44_3008.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _44_3008.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _44_3008.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _44_3008.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _44_3008.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _44_3008.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _44_3008.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in (match (pop_when_done) with
| true -> begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end
| false -> begin
env
end)))
end)))




