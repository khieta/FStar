module CanonDeep

open FStar.Tactics
open FStar.Reflection
open FStar.Reflection.Arith
open FStar.Mul
module O = FStar.Order

(* This is the pure part of canon_point *)
(* TODO: need Tot to state the lemma Nik wanted,
         but order not easy at all *)
let rec canon_point (e:expr) : Dv expr =
  match e with
  // Evaluate constants
  | Plus (Lit a) (Lit b) -> Lit (a + b)
  | Mult (Lit a) (Lit b) -> Lit (a * b)

  // Forget about negations
  | Neg e -> canon_point (Mult (Lit (-1)) e)

  // Distribute
  | Mult a (Plus b c) ->
      let l = canon_point (Mult a b) in
      let r = canon_point (Mult a c) in
      canon_point (Plus l r)

  | Mult (Plus a b) c ->
      let l = canon_point (Mult a c) in
      let r = canon_point (Mult b c) in
      canon_point (Plus l r)

  // Associate to the left
  | Mult a (Mult b c) ->
      let l = canon_point (Mult a b) in
      let r = canon_point c in
      canon_point (Mult l r)

  | Plus a (Plus b c) ->
      let l = canon_point (Plus a b) in
      let r = canon_point c in
      canon_point (Plus l r)

  | Plus (Plus a b) c ->
      if O.gt (compare_expr b c)
      then begin
          let l = canon_point (Plus a c) in
          Plus l b
      end
      else e

  | Mult (Mult a b) c ->
      if O.gt (compare_expr b c)
      then begin
          let l = canon_point (Mult a c) in
          Mult l b
      end
      else e

  | Plus a (Lit 0) -> a
  | Plus (Lit 0) b -> b

  | Plus a b ->
      if O.gt (compare_expr a b)
      then Plus b a
      else e

  | Mult (Lit 0) _ -> Lit 0
  | Mult _ (Lit 0) -> Lit 0

  | Mult (Lit 1) r -> r
  | Mult l (Lit 1) -> l

  | Mult a b ->
      if O.gt (compare_expr a b)
      then Mult b a
      else e

  // Forget about subtraction
  | Minus a b ->
      let r = canon_point (Neg b) in
      canon_point (Plus a r)

  | _ -> e

(* This is trying to emulate `pointwise canon_point` *)
let rec canon_expr (e:expr) : Dv expr =
  match e with
  | Atom _ _ | Lit _ -> e
  | Plus l r -> canon_point (Plus (canon_expr l) (canon_expr r))
  | Minus l r -> canon_point (Minus (canon_expr l) (canon_expr r))
  | Mult l r -> canon_point (Mult (canon_expr l) (canon_expr r))
  | Neg l -> canon_point (Neg (canon_expr l))
  | Land l r -> canon_point (Land (canon_expr l) (canon_expr r))
  | Lor l r -> canon_point (Lor (canon_expr l) (canon_expr r))
  | Lxor l r -> canon_point (Lxor (canon_expr l) (canon_expr r))
  | Ladd l r -> canon_point (Ladd (canon_expr l) (canon_expr r))
  | Lsub l r -> canon_point (Lsub (canon_expr l) (canon_expr r))
  | Shl l r -> canon_point (Shl (canon_expr l) (canon_expr r))
  | Shr l r -> canon_point (Shr (canon_expr l) (canon_expr r))
  | NatToBv l -> canon_point (NatToBv (canon_expr l))
  | Udiv l r -> canon_point (Udiv (canon_expr l) (canon_expr r))
  | Umod l r -> canon_point (Umod (canon_expr l) (canon_expr r))
  | MulMod l r -> canon_point (MulMod (canon_expr l) (canon_expr r))

(* TODO: stop gap until we have lift from DIV to TAC;
         actually until we can prove canon_expr in Tot, huh?
         (see cannon_correct below) *)
let canon_expr' (e:expr) : Tot expr = e

let pack_fv' (n:name) : term = pack (Tv_FVar (pack_fv n))

let rec expr_to_term (e:expr) : Tot term =
  match e with
  | Atom i t -> t
  | Lit i -> pack (Tv_Const (C_Int i))
  | Plus l r -> mk_e_app (pack_fv' add_qn) [expr_to_term l; expr_to_term r]
  | Minus l r -> mk_e_app (pack_fv' minus_qn) [expr_to_term l; expr_to_term r]
  | Mult l r -> mk_e_app (pack_fv' mult_qn) [expr_to_term l; expr_to_term r]
                (* <- TODO this has some chance of not round-tripping well
                           since there is also mult'_qn *)
  | Neg l -> mk_e_app (pack_fv' neg_qn) [expr_to_term l]
    (* TODO all the ones below also have implicit arguments that have to be *)
    (*      passed too (number of bits); just how am I supposed to know them? *)
  | Land l r -> mk_e_app (pack_fv' land_qn) [expr_to_term l; expr_to_term r]
  | Lor l r -> mk_e_app (pack_fv' lor_qn) [expr_to_term l; expr_to_term r]
  | Lxor l r -> mk_e_app (pack_fv' lxor_qn) [expr_to_term l; expr_to_term r]
  | Ladd l r -> mk_e_app (pack_fv' land_qn) [expr_to_term l; expr_to_term r]
  | Lsub l r -> mk_e_app (pack_fv' lsub_qn) [expr_to_term l; expr_to_term r]
  | Shl l r -> mk_e_app (pack_fv' shiftl_qn) [expr_to_term l; expr_to_term r]
  | Shr l r -> mk_e_app (pack_fv' shiftr_qn) [expr_to_term l; expr_to_term r]
  | NatToBv l -> mk_e_app (pack_fv' nat_bv_qn) [expr_to_term l]
  | Udiv l r -> mk_e_app (pack_fv' udiv_qn) [expr_to_term l; expr_to_term r]
  | Umod l r -> mk_e_app (pack_fv' umod_qn) [expr_to_term l; expr_to_term r]
  | MulMod l r -> mk_e_app (pack_fv' shiftr_qn) [expr_to_term l; expr_to_term r]

let canon_correct (e:expr) :
  Lemma (expr_to_term e == expr_to_term (canon_expr' e)) = () // cheating

let term_to_expr (t:term) : Tac expr =
  admit(); (* TODO: patterns are incomplete nonsense *)
  match run_tm (is_arith_expr t) with
  | Inr e -> e
  | Inl _ -> fail "Term is not an arithmetic expression"

let canon_term (t:term) : Tac expr = canon_expr' (term_to_expr t)

let canon_deep () : Tac unit =
  norm [];
  let g = cur_goal () in
  match term_as_formula g with
  | Comp c l r -> let el = term_to_expr l in
                  let er = term_to_expr r in
                  grewrite l (expr_to_term (canon_expr' el));
                  grewrite r (expr_to_term (canon_expr' er));
                  simpl (); dump "here I am"; admit1();
                  admit1(); // canon_correct el
                  admit1() // canon_correct er
  | _ -> idtac()

assume val w : int
assume val x : int
assume val y : int
assume val z : int

// Testing the canonizer, it should be the only thing needed for this file
let check_canon_deep () =
    canon_deep ();
    or_else qed
            (fun () -> dump "`canon deep` left the following goals";
                       fail "")

let lem0 =  assert_by_tactic (x * (y * z) == (x * y) * z) check_canon_deep
