(* Copyright 2011 Cornell University
 * Copyright 2012 Cornell University
 *
 *
 * This file is part of EventML - a tool aiming at specifying
 * distributed protocols in an ML like language.  It is an interface
 * to the logic of events and is compiled into Nuprl.  It is written
 * by the NUPRL group of Cornell University, Ithaca, NY.
 *
 * EventML is a free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * EventML is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with EventML.  If not, see <http://www.gnu.org/licenses/>.
 *
 *  o Authors:     Vincent Rahli
 *  o Affiliation: Cornell University, NUPRL group
 *  o Date:        29 July 2011
 *  o File name:   NuprlTerms.sml
 *  o Description: Datatype for nuprl terms
 *)


signature TOREF = sig
    type 'a t
    val get : 'a t -> 'a
    val mk  : 'a -> 'a t
    val set : 'a t -> 'a -> unit
end

structure ToRefRef :> TOREF = struct
type 'a t = 'a ref
fun get x = !x
fun mk x = ref x
fun set x y = (x := y)
end

structure ToRefId :> TOREF = struct
type 'a t = 'a
fun get x = x
fun mk x = x
fun set x y = ()
end

structure ToRefFun :> TOREF = struct
type 'a t = unit -> 'a
fun get x = x ()
fun mk x = fn () => x
fun set x y = ()
end

structure NuprlTerms :> NUPRL_TERMS = struct

structure T  = ListFormat
structure EH = LibBase
structure II = IntInf
structure TR = ToRefRef

structure KEY  = struct type ord_key = string val compare = String.compare end
structure SET  = BinarySetFn(KEY)
structure VARS = SET
(*structure VARS = ListSetFn(KEY)*)
(*structure MAP  = SplayMapFn(KEY)*)
structure MAP  = BinaryMapFn(KEY)
(*structure MAP  = ListMapFn(KEY)*)
structure SUB  = MAP

type 'a toref             = 'a TR.t

type nuprl_nat            = II.int

type variable             = string

type opid                 = string

type parameter_kind       = string (* such as: "token", "nat", "level-expression" *)
type parameter_value      = string

type tag                  = string toref

type opid_tag             = opid * tag
type parameter            = parameter_value * parameter_kind

type operator             = opid_tag * parameter list

datatype nuprl_term       = TERM     of operator * nuprl_bound_term list (* generic term    *)
			  | CLO_TERM of nuprl_ref_term * env             (* closure         *)
			  | VAR_TERM of variable                         (* variable        *)
			  | LAM_TERM of variable * nuprl_ref_term        (* lambda          *)
			  | WAI_TERM of nuprl_ref_term * nuprl_ref_term  (* wait            *)
			  | APP_TERM of nuprl_ref_term * nuprl_ref_term  (* application     *)
			  | INL_TERM of nuprl_ref_term                   (* left injection  *)
			  | INR_TERM of nuprl_ref_term                   (* right injection *)
			  | FIX_TERM of nuprl_ref_term                   (* fixpoint        *)
			  | PAI_TERM of nuprl_ref_term * nuprl_ref_term  (* pair            *)
			  | NIL_TERM                                     (* nil             *)
			  | CON_TERM of nuprl_ref_term * nuprl_ref_term  (* cons            *)
			  | NAT_TERM of nuprl_nat                        (* natural number  *)
			  | SPR_TERM of nuprl_ref_term * variable * variable * nuprl_ref_term                   (* spread *)
			  | DEC_TERM of nuprl_ref_term * variable * nuprl_ref_term * variable * nuprl_ref_term  (* decide *)
			  | LIN_TERM of nuprl_ref_term * nuprl_ref_term * variable * variable * variable * nuprl_ref_term  (* list induction *)
     and nuprl_bound_term = B_TERM   of variable list * nuprl_ref_term
     and nuprl_ref_term   = R_TERM   of nuprl_term toref
     and env              = ENV      of nuprl_ref_term MAP.map


type sign = (parameter_value option * parameter_kind) list * int list

(* An item is as follows:
 *   - string:   name of the abstraction (and not of the term)
 *   - sign:     signature of the term (lhs) (e.g., foo(0;1;0) -> [0;1;0] + parameters)
 *   - string:   object identifier
 *   - term:     left-hand-side of abstration
 *   - term:     right-hand-side of abstration
 *)
type item     = {id   : string,
		 sign : sign,
		 obid : string,
		 lhs  : nuprl_ref_term,
		 rhs  : nuprl_ref_term,
		 wfs  : nuprl_ref_term list}
type abs_lib  = item toref list MAP.map ref
type tof_lib  = nuprl_term toref MAP.map ref
type lib      = {abs : abs_lib, (* abstractions *)
		 tof : tof_lib} (* TERMOFs      *)

fun get_item_sign (item : item) = #sign item

val get = TR.get
val mk  = TR.mk
val set = TR.set


(* ------ REF TERMS ------ *)

fun rterm2term (R_TERM rt) = TR.get rt

fun mk_rterm term = R_TERM (TR.mk term)

fun set_rterm (R_TERM rt) term = TR.set rt term


(* ------ TAGS ------ *)

val mk_tag  = mk
val get_tag = get
val set_tag = set

val default_dtag = "OPID"
val dummy_dtag   = ""
val dtag         = mk_tag default_dtag

fun get_dtag () = dtag
fun set_dtag v  = set_tag dtag v

fun set_dummy_dtag () = set_dtag dummy_dtag
fun reset_dtag     () = set_dtag default_dtag


(* ------ SWITCH BETWEEN SML BASIC TERMS AND NUPRL ------ *)

val switch_LC = ref false

fun set_LC   () = switch_LC := true
fun reset_LC () = switch_LC := false
fun is_LC    () = !switch_LC


(* ------ BASIC CONSTRUCTORS ------ *)

fun mk_nuprl_variable_parameter  tok    = (tok,             "v")
fun mk_nuprl_natural_parameter   tag    = (II.toString tag, "n")
fun mk_nuprl_token_parameter     token  = (token,           "t")
fun mk_nuprl_string_parameter    string = (string,          "s")
fun mk_nuprl_level_exp_parameter level  = (level,           "l")
fun mk_nuprl_obid_parameter      obid   = (obid,            "o")
fun mk_nuprl_ut2_parameter       id     = (id,              "ut2")
fun mk_nuprl_bool_parameter      bool   = (if bool then "T" else "F", "b")

fun mk_nuprl_parameter (param : parameter) = param

fun mk_lc_term "variable"       tag ((var,kind) :: params) [] = VAR_TERM var
  | mk_lc_term "lambda"         tag params [B_TERM ([var], body)] = LAM_TERM (var, body)
  | mk_lc_term "!wait"          tag params [B_TERM ([], time), B_TERM ([], exp)] = WAI_TERM (time, exp)
  | mk_lc_term "apply"          tag params [B_TERM ([], func), B_TERM ([], arg)] = APP_TERM (func, arg)
  | mk_lc_term "pair"           tag params [B_TERM ([], left), B_TERM ([], right)] = PAI_TERM (left, right)
  | mk_lc_term "nil"            tag params [] = NIL_TERM
  | mk_lc_term "cons"           tag params [B_TERM ([], x), B_TERM ([], xs)] = CON_TERM (x, xs)
  | mk_lc_term "natural_number" tag ((n,kind) :: params) [] = (case II.fromString n of
								   NONE => (*default to 0*) NAT_TERM 0
								 | SOME x => NAT_TERM x)
  | mk_lc_term "inl"            tag params [B_TERM ([], term)] = INL_TERM term
  | mk_lc_term "inr"            tag params [B_TERM ([], term)] = INR_TERM term
  | mk_lc_term "fix"            tag params [B_TERM ([], term)] = FIX_TERM term
  | mk_lc_term "spread"         tag params [B_TERM ([], pair), B_TERM ([v1, v2], term)] = SPR_TERM (pair, v1, v2, term)
  | mk_lc_term "decide"         tag params [B_TERM ([], dec), B_TERM ([v1], term1), B_TERM ([v2], term2)] = DEC_TERM (dec, v1, term1, v2, term2)
  | mk_lc_term "list_ind"       tag params [B_TERM ([], lst), B_TERM ([], nilcase), B_TERM ([x,xs,r], conscase)] = LIN_TERM (lst, nilcase, x, xs, r, conscase)
  | mk_lc_term opid tag params brterms = TERM (((opid, tag), params), brterms)

fun mk_term opid tag params brterms =
    if is_LC ()
    then mk_lc_term opid tag params brterms
    else TERM (((opid, tag), params), brterms)

fun mk_nuprl_ref_term (opid, params) b_rterms =
    let val subs = map (fn (vars, rterm) => B_TERM (vars, rterm)) b_rterms
    in mk_term opid dtag params subs
    end

fun mk_nuprl_term (opid, params) b_terms =
    let val subs = map (fn (vars, term) => B_TERM (vars, mk_rterm term)) b_terms
    in mk_term opid dtag params subs
    end

fun mk_nuprl_ref_simple_term opid ref_term_list =
    let val subs = map (fn term => B_TERM ([], term)) ref_term_list
    in mk_term opid dtag [] subs
    end

fun mk_nuprl_simple_term opid term_list =
    let val subs = map (fn term => B_TERM ([], mk_rterm term)) term_list
    in mk_term opid dtag [] subs
    end

fun make_term opid tag params brterms = TERM (((opid, tag), params), brterms)

fun make_nuprl_ref_term (opid, params) b_rterms =
    let val subs = map (fn (vars, rterm) => B_TERM (vars, rterm)) b_rterms
    in make_term opid dtag params subs
    end

fun make_nuprl_term (opid, params) b_terms =
    let val subs = map (fn (vars, term) => B_TERM (vars, mk_rterm term)) b_terms
    in make_term opid dtag params subs
    end

fun make_nuprl_ref_simple_term opid ref_term_list =
    let val subs = map (fn term => B_TERM ([], term)) ref_term_list
    in make_term opid dtag [] subs
    end

fun make_nuprl_simple_term opid term_list =
    let val subs = map (fn term => B_TERM ([], mk_rterm term)) term_list
    in make_term opid dtag [] subs
    end


(* ------ A FEW USEFUL FUNCTIONS ------ *)

fun opid_of_term (TERM (((opid, _), _), _)) = opid
  | opid_of_term (VAR_TERM _) = "variable"
  | opid_of_term (LAM_TERM _) = "lambda"
  | opid_of_term (WAI_TERM _) = "!wait"
  | opid_of_term (APP_TERM _) = "apply"
  | opid_of_term (PAI_TERM _) = "pair"
  | opid_of_term NIL_TERM     = "nil"
  | opid_of_term (CON_TERM _) = "cons"
  | opid_of_term (NAT_TERM _) = "natural_number"
  | opid_of_term (INL_TERM _) = "inl"
  | opid_of_term (INR_TERM _) = "inr"
  | opid_of_term (FIX_TERM _) = "fix"
  | opid_of_term (SPR_TERM _) = "spread"
  | opid_of_term (DEC_TERM _) = "decide"
  | opid_of_term (LIN_TERM _) = "list_ind"
  | opid_of_term (CLO_TERM _) = "!!closure"

(* -- tests -- *)
fun is_nuprl_variable_term (TERM ((("variable", _), _), _)) = true
  | is_nuprl_variable_term (VAR_TERM _) = true
  | is_nuprl_variable_term _ = false

fun is_nuprl_lambda_term (TERM ((("lambda", _), _), _)) = true
  | is_nuprl_lambda_term (LAM_TERM _) = true
  | is_nuprl_lambda_term _ = false

fun is_nuprl_wait_term (TERM ((("!wait", _), _), _)) = true
  | is_nuprl_wait_term (WAI_TERM _) = true
  | is_nuprl_wait_term _ = false

fun is_nuprl_apply_term (TERM ((("apply", _), _), _)) = true
  | is_nuprl_apply_term (APP_TERM _) = true
  | is_nuprl_apply_term _ = false

fun is_nuprl_natural_number_term (TERM ((("natural_number", _), _), _)) = true
  | is_nuprl_natural_number_term (NAT_TERM _) = true
  | is_nuprl_natural_number_term _ = false

fun is_nuprl_cons_term (TERM ((("cons", _), _), _)) = true
  | is_nuprl_cons_term (CON_TERM _) = true
  | is_nuprl_cons_term _ = false

fun is_nuprl_nil_term (TERM ((("nil", _), _), _)) = true
  | is_nuprl_nil_term NIL_TERM = true
  | is_nuprl_nil_term _ = false

fun is_nuprl_pair_term (TERM ((("pair", _), _), _)) = true
  | is_nuprl_pair_term (PAI_TERM _) = true
  | is_nuprl_pair_term _ = false

fun is_nuprl_inl_term (TERM ((("inl", _), _), _)) = true
  | is_nuprl_inl_term (INL_TERM _) = true
  | is_nuprl_inl_term _ = false

fun is_nuprl_inr_term (TERM ((("inr", _), _), _)) = true
  | is_nuprl_inr_term (INR_TERM _) = true
  | is_nuprl_inr_term _ = false

fun is_nuprl_fix_term (TERM ((("fix", _), _), _)) = true
  | is_nuprl_fix_term (FIX_TERM _) = true
  | is_nuprl_fix_term _ = false

(* -- destructors -- *)
fun dest_variable (TERM ((("variable", _), [(var, "v")]), _)) = var
  | dest_variable (VAR_TERM var) = var
  | dest_variable term = raise Fail "dest_variable"

fun dest_lambda n (TERM ((("lambda", _), _), [B_TERM ([var], body)])) = (var, rterm2term body)
  | dest_lambda n (LAM_TERM (var, body)) = (var, rterm2term body)
  | dest_lambda n term = raise Fail ("dest_lambda(" ^ Int.toString n ^ "):" ^ opid_of_term term)

fun dest_wait (TERM ((("!wait", _), _), [B_TERM ([], time), B_TERM ([], exp)])) = (rterm2term time, rterm2term exp)
  | dest_wait (WAI_TERM (time, exp)) = (rterm2term time, rterm2term exp)
  | dest_wait term = raise Fail ("dest_wait")

fun dest_apply (TERM ((("apply", _), _), [B_TERM ([], rterm1), B_TERM ([], rterm2)])) = (rterm2term rterm1, rterm2term rterm2)
  | dest_apply (APP_TERM (rterm1, rterm2)) = (rterm2term rterm1, rterm2term rterm2)
  | dest_apply term = raise Fail ("dest_apply:" ^ opid_of_term term)

fun dest_pair n (TERM ((("pair", _), _), [B_TERM ([], rt1), B_TERM ([], rt2)])) = (rterm2term rt1, rterm2term rt2)
  | dest_pair n (PAI_TERM (rterm1, rterm2)) = (rterm2term rterm1, rterm2term rterm2)
  | dest_pair n term = raise Fail ("dest_pair(" ^ opid_of_term term ^ "," ^ Int.toString n ^ ")")

fun dest_cons (TERM ((("cons", _), _), [B_TERM ([], rt1), B_TERM ([], rt2)])) = (rterm2term rt1, rterm2term rt2)
  | dest_cons (CON_TERM (rterm1, rterm2)) = (rterm2term rterm1, rterm2term rterm2)
  | dest_cons term = raise Fail ("dest_cons")

fun dest_natural_number (TERM ((("natural_number", tag), ((n, kind) :: params)), [])) =
    (case II.fromString n of
	 NONE => raise Fail ("dest_natural_number:no_nat_in_string(" ^ n ^ ")")
       | SOME x => x)
  | dest_natural_number (NAT_TERM n) = n
  | dest_natural_number _ = raise EH.Impossible "dest_natural_number"

fun dest_inl (TERM ((("inl", _), _), [B_TERM ([], rterm)])) = rterm2term rterm
  | dest_inl (INL_TERM rterm) = rterm2term rterm
  | dest_inl term = raise Fail ("dest_inl")

fun dest_inr (TERM ((("inr", _), _), [B_TERM ([], rterm)])) = rterm2term rterm
  | dest_inr (INR_TERM rterm) = rterm2term rterm
  | dest_inr term = raise Fail ("dest_inr")

fun dest_fix (TERM ((("fix", _), _), [B_TERM ([], rterm)])) = rterm2term rterm
  | dest_fix (FIX_TERM rterm) = rterm2term rterm
  | dest_fix term = raise Fail ("dest_fix")


(* variable *)
fun mk_nuprl_variable_term tok = mk_nuprl_term ("variable", [mk_nuprl_variable_parameter tok]) []

fun make_nuprl_variable_term tok = make_nuprl_term ("variable", [mk_nuprl_variable_parameter tok]) []

fun mk_variable tok = VAR_TERM tok

fun mk_variable_term tok =
    if is_LC ()
    then mk_variable tok
    else mk_nuprl_variable_term tok

(* apply *)
fun mk_nuprl_apply_term func arg = mk_nuprl_simple_term "apply" [func, arg]

fun mk_nuprl_apply_ref_term func arg = mk_nuprl_ref_simple_term "apply" [func, arg]

fun make_nuprl_apply_ref_term func arg = make_nuprl_ref_simple_term "apply" [func, arg]

fun mk_apply func arg = APP_TERM (mk_rterm func, mk_rterm arg)

fun mk_apply_ref func arg = APP_TERM (func, arg)

fun mk_apply_term func arg =
    if is_LC ()
    then mk_apply func arg
    else mk_nuprl_apply_term func arg

fun mk_apply_ref_term func arg =
    if is_LC ()
    then mk_apply_ref func arg
    else mk_nuprl_apply_ref_term func arg

(* lambda *)
fun mk_nuprl_lambda_term var term = mk_nuprl_term ("lambda", []) [([var], term)]

fun mk_nuprl_lambda_ref_term var rterm = mk_nuprl_ref_term ("lambda", []) [([var], rterm)]

fun make_nuprl_lambda_ref_term var rterm = make_nuprl_ref_term ("lambda", []) [([var], rterm)]

fun mk_lambda var term = LAM_TERM (var, mk_rterm term)

fun mk_lambda_term var term =
    if is_LC ()
    then mk_lambda var term
    else mk_nuprl_lambda_term var term

(* wait *)
fun mk_nuprl_wait_term time exp = mk_nuprl_simple_term "!wait" [time, exp]

fun mk_nuprl_wait_ref_term time exp = mk_nuprl_ref_simple_term "!wait" [time, exp]

fun make_nuprl_wait_ref_term time exp = make_nuprl_ref_simple_term "!wait" [time, exp]

fun mk_wait time exp = WAI_TERM (mk_rterm time, mk_rterm exp)

fun mk_wait_term time exp =
    if is_LC ()
    then mk_wait time exp
    else mk_nuprl_wait_term time exp

(* pair *)
fun mk_nuprl_pair_term left right = mk_nuprl_simple_term "pair" [left, right]

fun mk_nuprl_pair_ref_term left right = mk_nuprl_ref_simple_term "pair" [left, right]

fun make_nuprl_pair_ref_term left right = make_nuprl_ref_simple_term "pair" [left, right]

fun mk_pair left right = PAI_TERM (mk_rterm left, mk_rterm right)

fun mk_pair_term left right =
    if is_LC ()
    then mk_pair left right
    else mk_nuprl_pair_term left right

(* nil *)
fun mk_nuprl_nil_term   () = mk_nuprl_simple_term       "nil" []
fun make_nuprl_nil_term () = make_nuprl_ref_simple_term "nil" []
fun mk_nil              () = NIL_TERM
fun mk_nil_term         () = if is_LC () then mk_nil () else mk_nuprl_nil_term ()

(* cons *)
fun mk_nuprl_cons_term left right = mk_nuprl_simple_term "cons" [left, right]

fun mk_nuprl_cons_ref_term left right = mk_nuprl_ref_simple_term "cons" [left, right]

fun make_nuprl_cons_ref_term left right = make_nuprl_ref_simple_term "cons" [left, right]

fun mk_cons left right = CON_TERM (mk_rterm left, mk_rterm right)

fun mk_cons_term left right =
    if is_LC ()
    then mk_cons left right
    else mk_nuprl_cons_term left right

(* natural number *)
fun mk_nuprl_natural_number_term nat = mk_nuprl_term ("natural_number", [mk_nuprl_natural_parameter nat]) []

fun make_nuprl_natural_number_term nat = make_nuprl_term ("natural_number", [mk_nuprl_natural_parameter nat]) []

(* injections *)
fun mk_nuprl_inl_term term = mk_nuprl_simple_term "inl" [term]
fun mk_nuprl_inr_term term = mk_nuprl_simple_term "inr" [term]

fun mk_nuprl_inl_ref_term term = mk_nuprl_ref_simple_term "inl" [term]
fun mk_nuprl_inr_ref_term term = mk_nuprl_ref_simple_term "inr" [term]

fun make_nuprl_inl_ref_term term = make_nuprl_ref_simple_term "inl" [term]
fun make_nuprl_inr_ref_term term = make_nuprl_ref_simple_term "inr" [term]

fun mk_inl term = INL_TERM (mk_rterm term)
fun mk_inr term = INR_TERM (mk_rterm term)

fun mk_inl_term term =
    if is_LC ()
    then mk_inl term
    else mk_nuprl_inl_term term
fun mk_inr_term term =
    if is_LC ()
    then mk_inr term
    else mk_nuprl_inr_term term

(* fix *)
fun mk_nuprl_fix_term term = mk_nuprl_simple_term "fix" [term]

fun mk_nuprl_fix_ref_term term = mk_nuprl_ref_simple_term "fix" [term]

fun make_nuprl_fix_ref_term term = make_nuprl_ref_simple_term "fix" [term]

fun mk_fix term = FIX_TERM (mk_rterm term)

fun mk_fix_term term =
    if is_LC ()
    then mk_fix term
    else mk_nuprl_fix_term term

(* spread *)
fun mk_nuprl_spread_term  pair (v1, v2, bterm) =
    mk_nuprl_term ("spread", []) [([], pair), ([v1, v2], bterm)]

fun mk_nuprl_spread_ref_term  pair (v1, v2, bterm) =
    mk_nuprl_ref_term ("spread", []) [([], pair), ([v1, v2], bterm)]

fun make_nuprl_spread_ref_term  pair (v1, v2, bterm) =
    make_nuprl_ref_term ("spread", []) [([], pair), ([v1, v2], bterm)]

fun mk_spread pair (var1, var2, term) = SPR_TERM (mk_rterm pair, var1, var2, mk_rterm term)

fun mk_spread_term pair (var1, var2, term) =
    if is_LC ()
    then mk_spread pair (var1, var2, term)
    else mk_nuprl_spread_term pair (var1, var2, term)

(* decide *)
fun mk_nuprl_decide_term dec (var1, bterm1) (var2, bterm2) =
    mk_nuprl_term ("decide", []) [([], dec), ([var1], bterm1), ([var2], bterm2)]

fun mk_nuprl_decide_ref_term dec (var1, bterm1) (var2, bterm2) =
    mk_nuprl_ref_term ("decide", []) [([], dec), ([var1], bterm1), ([var2], bterm2)]

fun make_nuprl_decide_ref_term dec (var1, bterm1) (var2, bterm2) =
    make_nuprl_ref_term ("decide", []) [([], dec), ([var1], bterm1), ([var2], bterm2)]

fun mk_decide dec (var1, term1) (var2, term2) = DEC_TERM (mk_rterm dec, var1, mk_rterm term1, var2, mk_rterm term2)

fun mk_decide_term dec (var1, term1) (var2, term2) =
    if is_LC ()
    then mk_decide dec (var1, term1) (var2, term2)
    else mk_nuprl_decide_term dec (var1, term1) (var2, term2)

(* list_ind *)
fun mk_nuprl_list_ind_term lst nilcase (x, xs, r, conscase) =
    mk_nuprl_term ("list_ind", []) [([], lst), ([], nilcase), ([x,xs,r], conscase)]

fun mk_nuprl_list_ind_ref_term lst nilcase (x, xs, r, conscase) =
    mk_nuprl_ref_term ("list_ind", []) [([], lst), ([], nilcase), ([x, xs, r], conscase)]

fun make_nuprl_list_ind_ref_term lst nilcase (x, xs, r, conscase) =
    make_nuprl_ref_term ("list_ind", []) [([], lst), ([], nilcase), ([x, xs, r], conscase)]

fun mk_list_ind lst nilcase (x, xs, r, conscase) = LIN_TERM (mk_rterm lst, mk_rterm nilcase, x, xs, r, mk_rterm conscase)

fun mk_list_ind_ref lst nilcase (x, xs, r, conscase) = LIN_TERM (lst, nilcase, x, xs, r, conscase)

fun mk_list_ind_term lst nilcase (x, xs, r, conscase) =
    if is_LC ()
    then mk_list_ind lst nilcase (x, xs, r, conscase)
    else mk_nuprl_list_ind_term lst nilcase (x, xs, r, conscase)

fun mk_list_ind_ref_term lst nilcase (x, xs, r, conscase) =
    if is_LC ()
    then mk_list_ind_ref lst nilcase (x, xs, r, conscase)
    else mk_nuprl_list_ind_ref_term lst nilcase (x, xs, r, conscase)


(* ------ CLOSURES ------ *)

val em_env = ENV MAP.empty

fun is_em_env (ENV env) = MAP.isEmpty env

fun mk_ct (rterm, env) =
    if is_em_env env
    then rterm2term rterm
    else CLO_TERM (rterm, env)

fun mk_rct (term, env) = mk_ct (mk_rterm term, env)

fun is_ct (CLO_TERM _) = true
  | is_ct _ = false

fun get_ct (CLO_TERM clos) = clos
  | get_ct _ = raise Fail "get_ct"

fun dest_clos (rterm, env) = (rterm2term rterm, env)

fun dest_ct (CLO_TERM clos) = dest_clos clos
  | dest_ct _ = raise Fail "dest_ct"

fun lookup_clos (ENV env) var = MAP.find (env, var)

fun lookup env var =
    case lookup_clos env var of
	SOME rterm =>
	(case rterm2term rterm of
	     CLO_TERM (rterm, e) => SOME (rterm2term rterm, e)
	   | term => SOME (term, em_env))
      | NONE => NONE

fun get_bterms (TERM (_, bterms)) = bterms
  | get_bterms (VAR_TERM _) = []
  | get_bterms (LAM_TERM (var, rterm)) = [B_TERM ([var], rterm)]
  | get_bterms (WAI_TERM (rterm1, rterm2)) = [B_TERM ([], rterm1), B_TERM ([], rterm2)]
  | get_bterms (APP_TERM (rterm1, rterm2)) = [B_TERM ([], rterm1), B_TERM ([], rterm2)]
  | get_bterms (PAI_TERM (rterm1, rterm2)) = [B_TERM ([], rterm1), B_TERM ([], rterm2)]
  | get_bterms NIL_TERM = []
  | get_bterms (CON_TERM (rterm1, rterm2)) = [B_TERM ([], rterm1), B_TERM ([], rterm2)]
  | get_bterms (NAT_TERM n) = []
  | get_bterms (INL_TERM rterm) = [B_TERM ([], rterm)]
  | get_bterms (INR_TERM rterm) = [B_TERM ([], rterm)]
  | get_bterms (FIX_TERM rterm) = [B_TERM ([], rterm)]
  | get_bterms (SPR_TERM (pair, var1, var2, rterm)) = [B_TERM ([], pair), B_TERM ([var1, var2], rterm)]
  | get_bterms (DEC_TERM (dec, var1, rterm1, var2, rterm2)) = [B_TERM ([], dec), B_TERM ([var1], rterm1), B_TERM ([var2], rterm2)]
  | get_bterms (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = [B_TERM ([], lst), B_TERM ([], nilcase), B_TERM ([x, xs, r], conscase)]
  | get_bterms (CLO_TERM clos) = raise Fail "get_brterms"

(* -- free variables -- *)
fun domain_set (ENV m) =
    MAP.foldri (fn (i, _, set) => VARS.add (set, i))
	       VARS.empty
	       m

val empty_vars = VARS.empty

fun fo_free_vars bounds (term as TERM (operator, bterms)) =
    if is_nuprl_variable_term term
    then let val v = dest_variable term
	 in if VARS.member (bounds, v)
	    then VARS.empty
	    else VARS.singleton v
	 end
    else List.foldr (fn (bterm, vars) =>
			VARS.union (vars, fo_free_vars_bterm bounds bterm))
		    empty_vars
		    bterms
  | fo_free_vars bounds (term as VAR_TERM var) =
    if VARS.member (bounds, var)
    then VARS.empty
    else VARS.singleton var
  | fo_free_vars bounds (term as CLO_TERM clos) =
    fo_free_vars_clos bounds clos
  | fo_free_vars bounds (term as LAM_TERM (var, rterm)) = fo_free_vars_rterm (VARS.add (bounds, var)) rterm
  | fo_free_vars bounds (term as WAI_TERM (rterm1, rterm2)) = VARS.union (fo_free_vars_rterm bounds rterm1, fo_free_vars_rterm bounds rterm2)
  | fo_free_vars bounds (term as APP_TERM (rterm1, rterm2)) = VARS.union (fo_free_vars_rterm bounds rterm1, fo_free_vars_rterm bounds rterm2)
  | fo_free_vars bounds (term as PAI_TERM (rterm1, rterm2)) = VARS.union (fo_free_vars_rterm bounds rterm1, fo_free_vars_rterm bounds rterm2)
  | fo_free_vars bounds (term as NIL_TERM) = VARS.empty
  | fo_free_vars bounds (term as CON_TERM (rterm1, rterm2)) = VARS.union (fo_free_vars_rterm bounds rterm1, fo_free_vars_rterm bounds rterm2)
  | fo_free_vars bounds (term as NAT_TERM n) = VARS.empty
  | fo_free_vars bounds (term as INL_TERM rterm) = fo_free_vars_rterm bounds rterm
  | fo_free_vars bounds (term as INR_TERM rterm) = fo_free_vars_rterm bounds rterm
  | fo_free_vars bounds (term as FIX_TERM rterm) = fo_free_vars_rterm bounds rterm
  | fo_free_vars bounds (term as SPR_TERM (pair, var1, var2, rterm)) =
    VARS.union (fo_free_vars_rterm bounds pair,
		fo_free_vars_rterm (VARS.add (VARS.add (bounds, var1), var2)) rterm)
  | fo_free_vars bounds (term as DEC_TERM (dec, var1, rterm1, var2, rterm2)) =
    VARS.union (fo_free_vars_rterm bounds dec,
		VARS.union (fo_free_vars_rterm (VARS.add (bounds, var1)) rterm1,
			    fo_free_vars_rterm (VARS.add (bounds, var2)) rterm2))
  | fo_free_vars bounds (term as LIN_TERM (lst, nilcase, x, xs, r, conscase)) =
    VARS.union (fo_free_vars_rterm bounds lst,
		VARS.union
		    (fo_free_vars_rterm bounds nilcase,
		     fo_free_vars_rterm (VARS.addList (bounds, [x, xs, r])) conscase))

and fo_free_vars_clos bounds (rterm, env) =
    fo_free_vars_rterm (VARS.union (bounds, domain_set env)) rterm

and fo_free_vars_rterm bounds rterm = fo_free_vars bounds (rterm2term rterm)

and fo_free_vars_bterm bounds (B_TERM (vars, rterm)) =
    fo_free_vars_rterm (VARS.addList (bounds, vars)) rterm

val free_vars = fo_free_vars VARS.empty

(* -- free variables - mapping from variables to occurence-- *)
val empty_vars_map = MAP.empty

fun free_vars_union_map m1 m2 = MAP.unionWith (fn (n, m) => n + m) (m1, m2)

fun fo_free_vars_map bounds (term as TERM (operator, bterms)) =
    if is_nuprl_variable_term term
    then let val v = dest_variable term
	 in if VARS.member (bounds, v)
	    then empty_vars_map
	    else MAP.singleton (v, 1)
	 end
    else List.foldr (fn (bterm, vars) =>
			free_vars_union_map
			    vars
			    (fo_free_vars_bterm_map bounds bterm))
		    empty_vars_map
		    bterms
  | fo_free_vars_map bounds (term as VAR_TERM var) =
    if VARS.member (bounds, var)
    then empty_vars_map
    else MAP.singleton (var, 1)
  | fo_free_vars_map bounds (term as CLO_TERM clos) = fo_free_vars_clos_map bounds clos
  | fo_free_vars_map bounds (term as LAM_TERM (var, rterm)) = fo_free_vars_rterm_map (VARS.add (bounds, var)) rterm
  | fo_free_vars_map bounds (term as WAI_TERM (rterm1, rterm2)) = free_vars_union_map (fo_free_vars_rterm_map bounds rterm1) (fo_free_vars_rterm_map bounds rterm2)
  | fo_free_vars_map bounds (term as APP_TERM (rterm1, rterm2)) = free_vars_union_map (fo_free_vars_rterm_map bounds rterm1) (fo_free_vars_rterm_map bounds rterm2)
  | fo_free_vars_map bounds (term as PAI_TERM (rterm1, rterm2)) = free_vars_union_map (fo_free_vars_rterm_map bounds rterm1) (fo_free_vars_rterm_map bounds rterm2)
  | fo_free_vars_map bounds (term as NIL_TERM) = empty_vars_map
  | fo_free_vars_map bounds (term as CON_TERM (rterm1, rterm2)) = free_vars_union_map (fo_free_vars_rterm_map bounds rterm1) (fo_free_vars_rterm_map bounds rterm2)
  | fo_free_vars_map bounds (term as NAT_TERM n) = empty_vars_map
  | fo_free_vars_map bounds (term as INL_TERM rterm) = fo_free_vars_rterm_map bounds rterm
  | fo_free_vars_map bounds (term as INR_TERM rterm) = fo_free_vars_rterm_map bounds rterm
  | fo_free_vars_map bounds (term as FIX_TERM rterm) = fo_free_vars_rterm_map bounds rterm
  | fo_free_vars_map bounds (term as SPR_TERM (pair, var1, var2, rterm)) =
    free_vars_union_map
	(fo_free_vars_rterm_map bounds pair)
	(fo_free_vars_rterm_map (VARS.add (VARS.add (bounds, var1), var2)) rterm)
  | fo_free_vars_map bounds (term as DEC_TERM (dec, var1, rterm1, var2, rterm2)) =
    free_vars_union_map
	(fo_free_vars_rterm_map bounds dec)
	(free_vars_union_map
	     (fo_free_vars_rterm_map (VARS.add (bounds, var1)) rterm1)
	     (fo_free_vars_rterm_map (VARS.add (bounds, var2)) rterm2))
  | fo_free_vars_map bounds (term as LIN_TERM (lst, nilcase, x, xs, r, conscase)) =
    free_vars_union_map
	(fo_free_vars_rterm_map bounds lst)
	(free_vars_union_map
	     (fo_free_vars_rterm_map bounds nilcase)
	     (fo_free_vars_rterm_map (VARS.addList (bounds, [x, xs, r])) conscase))

and fo_free_vars_clos_map bounds (rterm, env) =
    free_vars_union_map
	(fo_free_vars_rterm_map (VARS.union (bounds, domain_set env)) rterm)
	(fo_free_vars_env_map bounds env)

and fo_free_vars_env_map bounds (ENV env) =
    MAP.foldr
	(fn (rterm, vars) =>
	    free_vars_union_map
		vars
		(fo_free_vars_rterm_map bounds rterm))
	empty_vars_map
	env

and fo_free_vars_rterm_map bounds rterm = fo_free_vars_map bounds (rterm2term rterm)

and fo_free_vars_bterm_map bounds (B_TERM (vars, rterm)) =
    fo_free_vars_rterm_map (VARS.addList (bounds, vars)) rterm

val free_vars_map = fo_free_vars_map VARS.empty

fun find_free_vars_map m x =
    case MAP.find (m, x) of
	SOME x => x
      | NONE => 0

(* -- simple closure: (v, [v -> t]) *)
fun is_simple_closure (rterm, env) =
    let val term = rterm2term rterm
    in is_nuprl_variable_term term
       andalso
       Option.isSome (lookup_clos env (dest_variable term))
    end

(* shallow term: op(v1,..,vn) *)
fun is_shallow_term (TERM (_, bterms)) =
    foldr (fn (B_TERM ([], rterm), SOME vars) =>
	      let val t = rterm2term rterm
	      in if is_nuprl_variable_term t
		 then SOME (VARS.add (vars, dest_variable t))
		 else NONE
	      end
	    | _ => NONE)
	  (SOME VARS.empty)
	  bterms
  | is_shallow_term _ = NONE

fun prune_clos (term, ENV env) =
    let (*val env' =
	    case is_shallow_term term of
		SOME vars =>
		MAP.filteri (fn (v, _) => VARS.member (vars, v)) env
	      | NONE => env*)
	val frees = free_vars term
	val env' = MAP.filteri (fn (v, _) => VARS.member (frees, v)) env
    in mk_rct (term, ENV env')
    end

(*val prune_clos = mk_rclos*)

fun add2env_one (ENV env) (v,t,e) =
    if v = ""
    then ENV env
    else if is_nuprl_variable_term t
    then let val tv = dest_variable t
	 in case lookup_clos e tv of
		SOME c => (*if is_simple_closure c
			    then raise Fail "simple_closure"
			    else*) ENV (MAP.insert (env, v, c))
	      | NONE => raise Fail ("add2env_one(" ^ tv ^ ")") (*mk_rclos (t, e)*)
	 end
    else if is_ct t
    then let val (t',e') = dest_ct t
	 in  add2env_one (ENV env) (v,t',e')
	 end
    else if null (get_bterms t)
    then ENV (MAP.insert (env, v, mk_rterm t))
    else ENV (MAP.insert (env, v, mk_rterm (prune_clos (t, e))))

fun add2env env [] = env
  | add2env env (x :: xs) = add2env (add2env_one env x) xs

fun term2env (TERM (opr, [B_TERM ([v], thunk), B_TERM ([], env)])) =
    let val (t,e) = dest_pair 20 (rterm2term thunk)
	val (ENV env') = rterm2env env
    in ENV (MAP.insert (env', v, mk_rterm (mk_rct (t, term2env e))))
    end
  | term2env _ = raise Fail "term2env"

and rterm2env rterm = term2env (rterm2term rterm)

fun close term env =
    let fun aux (CLO_TERM clos) bounds env =
	    let val (t,e) = dest_clos clos
	    in aux t bounds e
	    end
	  | aux (LAM_TERM (var, rterm)) bounds env =
	    let val bs = VARS.add (bounds, var)
		val t  = aux (rterm2term rterm) bs env
	    in LAM_TERM (var, mk_rterm t)
	    end
	  | aux (WAI_TERM (rterm1, rterm2)) bounds env =
	    let val t1 = aux (rterm2term rterm1) bounds env
		val t2 = aux (rterm2term rterm2) bounds env
	    in WAI_TERM (mk_rterm t1, mk_rterm t2)
	    end
	  | aux (APP_TERM (rterm1, rterm2)) bounds env =
	    let val t1 = aux (rterm2term rterm1) bounds env
		val t2 = aux (rterm2term rterm2) bounds env
	    in APP_TERM (mk_rterm t1, mk_rterm t2)
	    end
	  | aux (PAI_TERM (rterm1, rterm2)) bounds env =
	    let val t1 = aux (rterm2term rterm1) bounds env
		val t2 = aux (rterm2term rterm2) bounds env
	    in PAI_TERM (mk_rterm t1, mk_rterm t2)
	    end
	  | aux NIL_TERM bounds env = NIL_TERM
	  | aux (CON_TERM (rterm1, rterm2)) bounds env =
	    let val t1 = aux (rterm2term rterm1) bounds env
		val t2 = aux (rterm2term rterm2) bounds env
	    in CON_TERM (mk_rterm t1, mk_rterm t2)
	    end
	  | aux (NAT_TERM n) bounds env = NAT_TERM n
	  | aux (INL_TERM rterm) bounds env =
	    let val t = aux (rterm2term rterm) bounds env
	    in INL_TERM (mk_rterm t)
	    end
	  | aux (INR_TERM rterm) bounds env =
	    let val t = aux (rterm2term rterm) bounds env
	    in INR_TERM (mk_rterm t)
	    end
	  | aux (FIX_TERM rterm) bounds env =
	    let val t = aux (rterm2term rterm) bounds env
	    in FIX_TERM (mk_rterm t)
	    end
	  | aux (SPR_TERM (pair, var1, var2, rterm)) bounds env =
	    let val p  = aux (rterm2term pair) bounds env
		val bs = VARS.addList (bounds, [var1, var2])
		val t  = aux (rterm2term rterm) bs env
	    in SPR_TERM (mk_rterm p, var1, var2, mk_rterm t)
	    end
	  | aux (DEC_TERM (dec, var1, rterm1, var2, rterm2)) bounds env =
	    let val d  = aux (rterm2term dec) bounds env
		val b1 = VARS.add (bounds, var1)
		val t1 = aux (rterm2term rterm1) b1 env
		val b2 = VARS.add (bounds, var2)
		val t2 = aux (rterm2term rterm2) b2 env
	    in DEC_TERM (mk_rterm d, var1, mk_rterm t1, var2, mk_rterm t2)
	    end
	  | aux (LIN_TERM (lst, nilcase, x, xs, r, conscase)) bounds env =
	    let val l  = aux (rterm2term lst) bounds env
		val n  = aux (rterm2term nilcase) bounds env
		val bs = VARS.addList (bounds, [x, xs, r])
		val c  = aux (rterm2term conscase) bs env
	    in LIN_TERM (mk_rterm l, mk_rterm n, x, xs, r, mk_rterm c)
	    end
	  | aux (term as VAR_TERM var) bounds env =
	    if VARS.member (bounds, var)
	    then term
	    else (case lookup env var of
		      SOME (t,e) => aux t bounds e
		    | NONE => term)
	  | aux (term as TERM (opr as ((opid, tag), params), bterms)) bounds env =
	    if opid = "variable"
	    then let val v = dest_variable term
		 in if VARS.member (bounds, v)
		    then term
		    else case lookup env v of
			     SOME (t,e) => aux t bounds e
			   | NONE => term
		 end
	    else let val bterms' =
			 map (fn B_TERM (vs, rt) =>
				 let val t1 = rterm2term rt
				     val bs = VARS.addList (bounds, vs)
				     val t2 = aux t1 bs env
				 in B_TERM (vs, mk_rterm t2)
				 end)
			     bterms
		 in TERM (opr, bterms')
		 end
	(*val _ = print ("[closing]\n")*)
    in aux term VARS.empty env
    end


(* ------ TO STRING ------ *)

fun toStringOpid  opid  = opid
fun toStringTag   tag   = get_tag tag
fun toStringValue value = value
fun toStringKind  kind  = kind

fun toStringParameter (value, kind) = toStringValue value ^ ":" ^ toStringKind kind

fun toStringParameters params =
    T.fmt {init  = "",
	   final = "",
	   sep   = ",",
	   fmt   = toStringParameter}
	  params

fun toStringOpidTag (opid, tag) = toStringOpid opid ^ ":" ^ toStringTag tag

fun toStringOperator (opid_tag, []) = toStringOpidTag opid_tag
  | toStringOperator (opid_tag, parameters) =
    toStringOpidTag opid_tag ^ "," ^ toStringParameters parameters

fun toStringVars vars =
    T.fmt {init  = "",
	   final = "",
	   sep   = ",",
	   fmt   = fn v => v ^ ":v"}
	  vars

fun toStringTerm (TERM (operator, [])) ind =
    "{" ^ toStringOperator operator ^ "}()"
  | toStringTerm (TERM (operator, bterms)) ind =
    let val ind' = ind ^ " "
    in "{" ^ toStringOperator operator    ^ "}\n" ^ ind ^
       "(" ^ toStringBTerms   bterms ind' ^ ")"
    end
  | toStringTerm (VAR_TERM var)                                ind = toStringTerm (make_nuprl_variable_term var)            ind
  | toStringTerm (LAM_TERM (var, rterm))                       ind = toStringTerm (make_nuprl_lambda_ref_term var rterm)    ind
  | toStringTerm (WAI_TERM (rterm1, rterm2))                   ind = toStringTerm (make_nuprl_wait_ref_term rterm1 rterm2)  ind
  | toStringTerm (APP_TERM (rterm1, rterm2))                   ind = toStringTerm (make_nuprl_apply_ref_term rterm1 rterm2) ind
  | toStringTerm (PAI_TERM (rterm1, rterm2))                   ind = toStringTerm (make_nuprl_pair_ref_term rterm1 rterm2)  ind
  | toStringTerm NIL_TERM                                      ind = toStringTerm (make_nuprl_nil_term ())                  ind
  | toStringTerm (CON_TERM (rterm1, rterm2))                   ind = toStringTerm (make_nuprl_cons_ref_term rterm1 rterm2)  ind
  | toStringTerm (NAT_TERM nat)                                ind = toStringTerm (make_nuprl_natural_number_term nat)      ind
  | toStringTerm (INL_TERM rterm)                              ind = toStringTerm (make_nuprl_inl_ref_term rterm)           ind
  | toStringTerm (INR_TERM rterm)                              ind = toStringTerm (make_nuprl_inr_ref_term rterm)           ind
  | toStringTerm (FIX_TERM rterm)                              ind = toStringTerm (make_nuprl_fix_ref_term rterm)           ind
  | toStringTerm (SPR_TERM (pair, var1, var2, rterm))          ind = toStringTerm (make_nuprl_spread_ref_term pair (var1, var2, rterm))           ind
  | toStringTerm (DEC_TERM (dec, var1, rterm1, var2, rterm2))  ind = toStringTerm (make_nuprl_decide_ref_term dec (var1, rterm1) (var2, rterm2))  ind
  | toStringTerm (LIN_TERM (lst, nilcase, x, xs, r, conscase)) ind = toStringTerm (make_nuprl_list_ind_ref_term lst nilcase (x, xs, r, conscase)) ind
  | toStringTerm (CLO_TERM clos) ind = toStringClos clos ind

and toStringClos (rterm, env) ind =
    let val ind' = ind ^ " "
    in "{!closure:OPID}\n" ^ ind ^
       "(" ^ toStringRTerm rterm ind' ^ ";\n" ^ ind'
       ^ toStringEnv env ind' ^ ")"
    end

and toStringEnv (ENV m) ind =
    #1 (MAP.foldri (fn (var, rterm, (str, ind)) =>
		       let val ind1 = ind  ^ " "
		       in ("{env:OPID}\n"
			   ^ ind
			   ^ "({bound_id:OPID," ^ toStringVars [var] ^ "}\n"
			   ^ ind1
			   ^ toStringRTerm rterm ind1 ^ ";\n"
			   ^ ind1
			   ^ str ^ ")",
			   ind1)
		       end)
		   ("", ind)
		   m)

and toStringRTerm ref_term = toStringTerm (rterm2term ref_term)

and toStringBTerm (B_TERM ([],   rterm)) ind = toStringRTerm rterm ind
  | toStringBTerm (B_TERM (vars, rterm)) ind =
    let val str = toStringVars vars
    in "{bound_id:OPID," ^ str ^ "}\n" ^ ind ^
       "(" ^ toStringRTerm rterm (ind ^ " ") ^ ")"
    end

and toStringBTerms bterms ind =
    T.fmt {init  = "",
	   final = "",
	   sep   = ";\n" ^ ind,
	   fmt   = fn bterm => toStringBTerm bterm ind}
	  bterms

and toStringTerms terms ind =
    T.fmt {init  = "",
	   final = "",
	   sep   = ";\n" ^ ind,
	   fmt   = fn term => toStringTerm term ind}
	  terms

val toStringTerm  = fn term  => toStringTerm  term  ""
val toStringRTerm = fn rterm => toStringRTerm rterm ""
val toStringEnv   = fn env   => toStringEnv   env   ""

(* -- write to file while traversing the tree *)

fun toStringTerm_stream out (TERM (operator, [])) ind =
    TextIO.output (out, "{" ^ toStringOperator operator   ^ "}()")
  | toStringTerm_stream out (TERM (operator, bterms)) ind =
    let val ind' = ind ^ " "
	val opr  = toStringOperator operator
    in TextIO.output (out, "{" ^ opr ^ "}\n" ^ ind ^ "(");
       toStringBTerms_stream out bterms ind';
       TextIO.output (out, ")")
    end
  | toStringTerm_stream out (VAR_TERM var)              ind = toStringTerm_stream out (make_nuprl_variable_term var)            ind
  | toStringTerm_stream out (LAM_TERM (var, rterm))     ind = toStringTerm_stream out (make_nuprl_lambda_ref_term var rterm)    ind
  | toStringTerm_stream out (WAI_TERM (rterm1, rterm2)) ind = toStringTerm_stream out (make_nuprl_wait_ref_term rterm1 rterm2)  ind
  | toStringTerm_stream out (APP_TERM (rterm1, rterm2)) ind = toStringTerm_stream out (make_nuprl_apply_ref_term rterm1 rterm2) ind
  | toStringTerm_stream out (PAI_TERM (rterm1, rterm2)) ind = toStringTerm_stream out (make_nuprl_pair_ref_term rterm1 rterm2)  ind
  | toStringTerm_stream out NIL_TERM                    ind = toStringTerm_stream out (make_nuprl_nil_term ())                  ind
  | toStringTerm_stream out (CON_TERM (rterm1, rterm2)) ind = toStringTerm_stream out (make_nuprl_cons_ref_term rterm1 rterm2)  ind
  | toStringTerm_stream out (NAT_TERM nat)              ind = toStringTerm_stream out (make_nuprl_natural_number_term nat)      ind
  | toStringTerm_stream out (INL_TERM rterm)            ind = toStringTerm_stream out (mk_nuprl_inl_ref_term rterm)             ind
  | toStringTerm_stream out (INR_TERM rterm)            ind = toStringTerm_stream out (mk_nuprl_inr_ref_term rterm)             ind
  | toStringTerm_stream out (FIX_TERM rterm)            ind = toStringTerm_stream out (mk_nuprl_fix_ref_term rterm)             ind
  | toStringTerm_stream out (SPR_TERM (pair, var1, var2, rterm))          ind = toStringTerm_stream out (mk_nuprl_spread_ref_term pair (var1, var2, rterm))           ind
  | toStringTerm_stream out (DEC_TERM (dec, var1, rterm1, var2, rterm2))  ind = toStringTerm_stream out (mk_nuprl_decide_ref_term dec (var1, rterm1) (var2, rterm2))  ind
  | toStringTerm_stream out (LIN_TERM (lst, nilcase, x, xs, r, conscase)) ind = toStringTerm_stream out (mk_nuprl_list_ind_ref_term lst nilcase (x, xs, r, conscase)) ind
  | toStringTerm_stream out (CLO_TERM clos) ind = toStringClos_stream out clos ind

and toStringClos_stream out (rterm, env) ind =
    let val ind' = ind ^ " "
    in TextIO.output (out, "{!closure:OPID}\n" ^ ind ^ "(");
       toStringRTerm_stream out rterm ind';
       TextIO.output (out, ";\n" ^ ind');
       toStringEnv_stream out env ind';
       TextIO.output (out, ")")
    end

and toStringEnv_stream out (ENV m) ind =
    (MAP.foldli (fn (var, rterm, ind) =>
		    let val ind1 = ind  ^ " "
		    in (TextIO.output (out, "{env:OPID}\n" ^ ind);
			TextIO.output (out, "({bound_id:OPID," ^ toStringVars [var] ^ "}\n" ^ ind1);
			toStringRTerm_stream out rterm ind1;
			TextIO.output (out, "\n" ^ ind1);
			ind1)
		    end)
		ind
		m;
     ())

and toStringRTerm_stream out ref_term =
    toStringTerm_stream out (rterm2term ref_term)

and toStringBTerm_stream out (B_TERM ([],   rterm)) ind =
    toStringRTerm_stream out rterm ind
  | toStringBTerm_stream out (B_TERM (vars, rterm)) ind =
    let val str = toStringVars vars
    in TextIO.output (out, "{bound_id:OPID," ^ str ^ "}\n" ^ ind ^ "(");
       toStringRTerm_stream out rterm (ind ^ " ");
       TextIO.output (out, ")")
    end

and toStringBTerms_stream out [] ind = ()
  | toStringBTerms_stream out [x] ind = toStringBTerm_stream out x ind
  | toStringBTerms_stream out (x :: xs) ind =
    (toStringBTerm_stream out x ind;
     TextIO.output (out, ";\n" ^ ind);
     toStringBTerms_stream out xs ind)

fun toStringTermStream term file =
    let val out = TextIO.openOut file
	val _   = toStringTerm_stream out term ""
	val _   = TextIO.closeOut out
    in ()
    end


(* -- pretty printer -- *)

fun ppTerm (TERM ((("apply", _), []), [B_TERM ([], f),
				       B_TERM ([], a)])) = "(" ^ ppRTerm f ^ ")(" ^ ppRTerm a ^ ")"
  | ppTerm (TERM ((("int_eq", _), []), [B_TERM ([], x),
					B_TERM ([], y),
					B_TERM ([], w),
					B_TERM ([], z)])) = "if " ^ ppRTerm x ^ " = " ^ ppRTerm y ^ " then " ^ ppRTerm w ^ " else " ^ ppRTerm z
  | ppTerm (TERM ((("subtract", _), []), [B_TERM ([], x),
					  B_TERM ([], y)])) = ppRTerm x ^ "-" ^ ppRTerm y
  | ppTerm (TERM ((("add", _), []), [B_TERM ([], x),
				     B_TERM ([], y)])) = ppRTerm x ^ "+" ^ ppRTerm y
  | ppTerm (TERM ((("pair", _), []), [B_TERM ([], x),
				      B_TERM ([], y)])) = "(" ^ ppRTerm x ^ "," ^ ppRTerm y ^ ")"
  | ppTerm (TERM ((("variable", _),       [(v,vkind)]), [])) = v
  | ppTerm (TERM ((("natural_number", _), [(n,nkind)]), [])) = n
  | ppTerm (TERM ((("ycomb", _), []), [])) = "Y"
  | ppTerm (TERM ((("lambda", _), []), [B_TERM ([x], f)])) = "\\" ^ x ^ ". " ^ ppRTerm f
  | ppTerm (TERM ((("nil", _), []), [])) = "[]"
  | ppTerm (TERM ((("inl", _), []), [B_TERM ([], t)])) = "inl(" ^ ppRTerm t ^ ")"
  | ppTerm (TERM ((("inr", _), []), [B_TERM ([], t)])) = "inr(" ^ ppRTerm t ^ ")"
  | ppTerm (TERM ((("fix", _), []), [B_TERM ([], t)])) = "fix(" ^ ppRTerm t ^ ")"
  | ppTerm (TERM ((("ifthenelse", _), []), [B_TERM ([], b),
					    B_TERM ([], t1),
					    B_TERM ([], t2)])) = "if " ^ ppRTerm b ^ "\nthen " ^ ppRTerm t1 ^ "\nelse " ^ ppRTerm t2
  | ppTerm (TERM ((("decide", _), []), [B_TERM ([], dec),
					B_TERM ([v1], t1),
					B_TERM ([v2], t2)])) = "case " ^ ppRTerm dec ^ " of inl(" ^ v1 ^ ") => " ^ ppRTerm t1 ^ " | inr(" ^ v2 ^ ") => " ^ ppRTerm t2
  | ppTerm (TERM ((("spread", _), []), [B_TERM ([], pair),
					B_TERM ([x1,x2], t)])) = "let " ^ x1 ^ "," ^ x2 ^ " = " ^ ppRTerm pair ^ " in " ^ ppRTerm t
  | ppTerm (TERM ((("list_ind", _), []), [B_TERM ([], L),
					  B_TERM ([], base),
					  B_TERM ([x,xs], reccase)])) = "rec-case " ^ ppRTerm L ^ " of [] => " ^ ppRTerm base ^ " | " ^ x ^ "." ^ xs ^ " => " ^ ppRTerm reccase
  | ppTerm (TERM ((("callbyvalue", _), []), [B_TERM ([], arg),
					     B_TERM ([x], B)])) = "let " ^ x ^ " := " ^ ppRTerm arg ^ "\nin " ^ ppRTerm B
  | ppTerm (TERM ((("callbyvalueall", _), []), [B_TERM ([], arg),
						B_TERM ([x], B)])) = "let " ^ x ^ " <- " ^ ppRTerm arg ^ "\nin " ^ ppRTerm B
  | ppTerm (TERM (((opid, _), params), bterms)) = opid ^ "(" ^ ppBTerms bterms ^ ")"
  | ppTerm term = toStringTerm term

and ppBTerms bterms =
    T.fmt {init  = "",
	   final = "",
	   sep   = ",",
	   fmt   = ppBTerm}
	  bterms

and ppBTerm (B_TERM (vars, rterm)) =
    T.fmt {init  = "",
	   final = "",
	   sep   = ".",
	   fmt   = fn x => x} vars
    ^ ppRTerm rterm

and ppRTerm ref_term = ppTerm (rterm2term ref_term)


(* ------ ACCESSORS ------ *)

fun opr_of_term (TERM (((opid, _), params), _)) = (opid, params)
  | opr_of_term (VAR_TERM v) = ("variable",       [(v, "v")])
  | opr_of_term (LAM_TERM _) = ("lambda",         [])
  | opr_of_term (WAI_TERM _) = ("!wait",          [])
  | opr_of_term (APP_TERM _) = ("apply",          [])
  | opr_of_term (PAI_TERM _) = ("pair",           [])
  | opr_of_term NIL_TERM     = ("nil",            [])
  | opr_of_term (CON_TERM _) = ("cons",           [])
  | opr_of_term (NAT_TERM n) = ("natural_number", [(II.toString n, "n")])
  | opr_of_term (INL_TERM _) = ("inl",            [])
  | opr_of_term (INR_TERM _) = ("inr",            [])
  | opr_of_term (FIX_TERM _) = ("fix",            [])
  | opr_of_term (SPR_TERM _) = ("spread",         [])
  | opr_of_term (DEC_TERM _) = ("decide",         [])
  | opr_of_term (LIN_TERM _) = ("list_ind",       [])
  | opr_of_term (CLO_TERM clos) = raise Fail "opr_of_term"

fun parameters_of_term (TERM (((_, _), params), _)) = params
  | parameters_of_term (VAR_TERM v) = [(v,"v")]
  | parameters_of_term (LAM_TERM _) = []
  | parameters_of_term (WAI_TERM _) = []
  | parameters_of_term (APP_TERM _) = []
  | parameters_of_term (PAI_TERM _) = []
  | parameters_of_term NIL_TERM     = []
  | parameters_of_term (CON_TERM _) = []
  | parameters_of_term (NAT_TERM n) = [(II.toString n,"n")]
  | parameters_of_term (INL_TERM _) = []
  | parameters_of_term (INR_TERM _) = []
  | parameters_of_term (FIX_TERM _) = []
  | parameters_of_term (SPR_TERM _) = []
  | parameters_of_term (DEC_TERM _) = []
  | parameters_of_term (LIN_TERM _) = []
  | parameters_of_term (CLO_TERM clos) = raise Fail "parameters_of_term"

fun bterms_of_term (TERM (_, bterms))          = map (fn (B_TERM (vars, rterm)) => (vars, rterm)) bterms
  | bterms_of_term (VAR_TERM _)                = []
  | bterms_of_term (LAM_TERM (var, rterm))     = [([var],rterm)]
  | bterms_of_term (WAI_TERM (rterm1, rterm2)) = [([],rterm1), ([],rterm2)]
  | bterms_of_term (APP_TERM (rterm1, rterm2)) = [([],rterm1), ([],rterm2)]
  | bterms_of_term (PAI_TERM (rterm1, rterm2)) = [([],rterm1), ([],rterm2)]
  | bterms_of_term NIL_TERM                    = []
  | bterms_of_term (CON_TERM (rterm1, rterm2)) = [([],rterm1), ([],rterm2)]
  | bterms_of_term (NAT_TERM n)                = []
  | bterms_of_term (INL_TERM rterm)            = [([],rterm)]
  | bterms_of_term (INR_TERM rterm)            = [([],rterm)]
  | bterms_of_term (FIX_TERM rterm)            = [([],rterm)]
  | bterms_of_term (SPR_TERM (pair, var1, var2, rterm)) = [([],pair), ([var1,var2],rterm)]
  | bterms_of_term (DEC_TERM (dec, var1, rterm1, var2, rterm2)) = [([],dec), ([var1],rterm1), ([var2],rterm2)]
  | bterms_of_term (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = [([],lst), ([],nilcase), ([x,xs,r],conscase)]
  | bterms_of_term (CLO_TERM clos) = raise Fail "bterms_of_term"

fun brterms_of_term (TERM (_, bterms))          = map (fn (B_TERM (vars, rterm)) => (vars, rterm2term rterm)) bterms
  | brterms_of_term (VAR_TERM _)                = []
  | brterms_of_term (LAM_TERM (var, rterm))     = [([var],rterm2term rterm)]
  | brterms_of_term (WAI_TERM (rterm1, rterm2)) = [([],rterm2term rterm1), ([],rterm2term rterm2)]
  | brterms_of_term (APP_TERM (rterm1, rterm2)) = [([],rterm2term rterm1), ([],rterm2term rterm2)]
  | brterms_of_term (PAI_TERM (rterm1, rterm2)) = [([],rterm2term rterm1), ([],rterm2term rterm2)]
  | brterms_of_term NIL_TERM                    = []
  | brterms_of_term (CON_TERM (rterm1, rterm2)) = [([],rterm2term rterm1), ([],rterm2term rterm2)]
  | brterms_of_term (NAT_TERM n)                = []
  | brterms_of_term (INL_TERM rterm)            = [([],rterm2term rterm)]
  | brterms_of_term (INR_TERM rterm)            = [([],rterm2term rterm)]
  | brterms_of_term (FIX_TERM rterm)            = [([],rterm2term rterm)]
  | brterms_of_term (SPR_TERM (pair, var1, var2, rterm)) = [([],rterm2term pair), ([var1,var2],rterm2term rterm)]
  | brterms_of_term (DEC_TERM (dec, var1, rterm1, var2, rterm2)) = [([],rterm2term dec), ([var1],rterm2term rterm1), ([var2],rterm2term rterm2)]
  | brterms_of_term (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = [([],rterm2term lst), ([],rterm2term nilcase), ([x,xs,r],rterm2term conscase)]
  | brterms_of_term (CLO_TERM clos) = raise Fail "brterms_of_term"

fun subterms (TERM (_, bterms))          = map (fn (B_TERM (_, rterm)) => rterm) bterms
  | subterms (VAR_TERM _)                = []
  | subterms (LAM_TERM (var, rterm))     = [rterm]
  | subterms (WAI_TERM (rterm1, rterm2)) = [rterm1, rterm2]
  | subterms (APP_TERM (rterm1, rterm2)) = [rterm1, rterm2]
  | subterms (PAI_TERM (rterm1, rterm2)) = [rterm1, rterm2]
  | subterms NIL_TERM                    = []
  | subterms (CON_TERM (rterm1, rterm2)) = [rterm1, rterm2]
  | subterms (NAT_TERM n)                = []
  | subterms (INL_TERM rterm)            = [rterm]
  | subterms (INR_TERM rterm)            = [rterm]
  | subterms (FIX_TERM rterm)            = [rterm]
  | subterms (SPR_TERM (pair, var1, var2, rterm)) = [pair, rterm]
  | subterms (DEC_TERM (dec, var1, rterm1, var2, rterm2)) = [dec, rterm1, rterm2]
  | subterms (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = [lst, nilcase, conscase]
  | subterms (CLO_TERM clos) = raise Fail "subterms"

fun subtermn n (TERM (_, bterm_list)) =
    (case List.nth (bterm_list, n - 1) of
	 B_TERM ([], t) => rterm2term t
       | _ => raise Fail "subtermn")
  | subtermn n (VAR_TERM var) = raise Fail "subtermn:VAR_TERM"
  | subtermn n (LAM_TERM (var, rterm)) = raise Fail "subtermn:LAM_TERM"
  | subtermn n (WAI_TERM (rterm1, rterm2)) =
    if n = 1
    then rterm2term rterm1
    else if n = 2
    then rterm2term rterm2
    else raise Fail "subtermn:WAI_TERM"
  | subtermn n (APP_TERM (rterm1, rterm2)) =
    if n = 1
    then rterm2term rterm1
    else if n = 2
    then rterm2term rterm2
    else raise Fail "subtermn:APP_TERM"
  | subtermn n (PAI_TERM (rterm1, rterm2)) =
    if n = 1
    then rterm2term rterm1
    else if n = 2
    then rterm2term rterm2
    else raise Fail "subtermn:PAI_TERM"
  | subtermn n NIL_TERM = raise Fail "subtermn:NIL_TERM"
  | subtermn n (CON_TERM (rterm1, rterm2)) =
    if n = 1
    then rterm2term rterm1
    else if n = 2
    then rterm2term rterm2
    else raise Fail "subtermn:CON_TERM"
  | subtermn n (NAT_TERM _) = raise Fail "subtermn:NAT_TERM"
  | subtermn n (INL_TERM rterm) =
    if n = 1
    then rterm2term rterm
    else raise Fail "subtermn:INL_TERM"
  | subtermn n (INR_TERM rterm) =
    if n = 1
    then rterm2term rterm
    else raise Fail "subtermn:INR_TERM"
  | subtermn n (FIX_TERM rterm) =
    if n = 1
    then rterm2term rterm
    else raise Fail "subtermn:FIX_TERM"
  | subtermn n (SPR_TERM (pair, var1, var2, rterm)) =
    if n = 1
    then rterm2term pair
    else raise Fail "subtermn:SPR_TERM"
  | subtermn n (DEC_TERM (dec, var1, rterm1, var2, rterm2)) =
    if n = 1
    then rterm2term dec
    else raise Fail "subtermn:DEC_TERM"
  | subtermn n (LIN_TERM (lst, nilcase, x, xs, r, conscase)) =
    if n = 1
    then rterm2term lst
    else raise Fail "subtermn:LIN_TERM"
  | subtermn n (CLO_TERM clos) = raise Fail "subtermn:CLO_TERM"

fun subterms_n n bterms =
    let val (vars, rt) = List.nth (bterms, n)
    in rterm2term rt
    end

fun type_of_parameter  (_, kind)  = kind
fun value_of_parameter (value, _) = value

fun destruct_natural_parameter (n,"n") = Option.valOf (Int.fromString n)
  | destruct_natural_parameter _ = raise Fail "destruct_natural_parameter"

fun firstnat term = destruct_natural_parameter (hd (parameters_of_term term))

fun get_obid_parameters [] = NONE
  | get_obid_parameters ((p,k) :: xs) =
    if k = "o"
    then SOME p
    else get_obid_parameters xs

fun sign_to_string (lst1, lst2) =
    "("
    ^ (T.fmt {init  = "[",
	      final = "]",
	      sep   = ",",
	      fmt   = fn (SOME v, k) => toStringValue v ^ ":" ^ toStringKind k
		       | (NONE, k) => "-:" ^ toStringKind k}
	     lst1)
    ^ ","
    ^ (T.fmt {init  = "[",
	      final = "]",
	      sep   = ",",
	      fmt   = Int.toString}
	     lst2)
    ^ ")"

fun is_abstract_metavar v = String.isPrefix "%a" v

fun getSignature (term as TERM (_, lst)) =
    let val params = parameters_of_term term
	val types  = map (fn (v, k) =>
			     if is_abstract_metavar v
			     then (NONE, k)
			     else (SOME v, k))
			 params
	val subs   = map (fn (B_TERM (vs, _)) => List.length vs) lst
    in (types, subs)
    end
  | getSignature (term as VAR_TERM _) = raise Fail "getSignature:VAR_TERM"
  | getSignature (term as LAM_TERM _) = raise Fail "getSignature:LAM_TERM"
  | getSignature (term as WAI_TERM _) = raise Fail "getSignature:WAI_TERM"
  | getSignature (term as APP_TERM _) = raise Fail "getSignature:APP_TERM"
  | getSignature (term as PAI_TERM _) = raise Fail "getSignature:PAI_TERM"
  | getSignature (term as NIL_TERM)   = raise Fail "getSignature:NIL_TERM"
  | getSignature (term as CON_TERM _) = raise Fail "getSignature:CON_TERM"
  | getSignature (term as NAT_TERM _) = raise Fail "getSignature:NAT_TERM"
  | getSignature (term as INL_TERM _) = raise Fail "getSignature:INL_TERM"
  | getSignature (term as INR_TERM _) = raise Fail "getSignature:INR_TERM"
  | getSignature (term as FIX_TERM _) = raise Fail "getSignature:FIX_TERM"
  | getSignature (term as SPR_TERM _) = raise Fail "getSignature:SPR_TERM"
  | getSignature (term as DEC_TERM _) = raise Fail "getSignature:DEC_TERM"
  | getSignature (term as LIN_TERM _) = raise Fail "getSignature:LIN_TERM"
  | getSignature (term as CLO_TERM _) = raise Fail "getSignature:CLO_TERM"

fun eq_kinds (k1, k2) =
    (k1 = "t" andalso k2 = "token")
    orelse
    (k2 = "t" andalso k1 = "token")
    orelse
    k1 = k2

fun eq_sign_kinds ((v1, k1), (v2, k2)) =
    (case (v1, v2) of
	 (SOME a, SOME b) => (a : parameter_value) = b
       | _ => true)
    andalso
    eq_kinds (k1, k2)

fun eq_signs ((kinds1, subs1) : sign)
	     ((kinds2, subs2) : sign) =
    (List.all eq_sign_kinds (ListPair.zipEq (kinds1, kinds2))
     andalso
     subs1 = subs2)
    handle _ => false


(* size of a term -- number of nodes *)
fun size (TERM (opr, bterms)) =
    foldr (fn (bterm, n) =>
	      let (*val _ = print ("[partial size: " ^ Int.toString n ^ "]\n")*)
	      in n + size_bterm bterm
	      end)
	  1
	  bterms
  | size (VAR_TERM var) = 1
  | size (LAM_TERM (var, rterm)) = 1 + size_rterm rterm
  | size (WAI_TERM (rterm1, rterm2)) = 1 + size_rterm rterm1 + size_rterm rterm2
  | size (APP_TERM (rterm1, rterm2)) = 1 + size_rterm rterm1 + size_rterm rterm2
  | size (PAI_TERM (rterm1, rterm2)) = 1 + size_rterm rterm1 + size_rterm rterm2
  | size NIL_TERM = 0
  | size (CON_TERM (rterm1, rterm2)) = 1 + size_rterm rterm1 + size_rterm rterm2
  | size (NAT_TERM _) = 0
  | size (INL_TERM rterm) = 1 + size_rterm rterm
  | size (INR_TERM rterm) = 1 + size_rterm rterm
  | size (FIX_TERM rterm) = 1 + size_rterm rterm
  | size (SPR_TERM (pair, var1, var2, rterm)) = 1 + size_rterm pair + size_rterm rterm
  | size (DEC_TERM (dec, var1, rterm1, var2, rterm2)) = 1 + size_rterm dec + size_rterm rterm1 + size_rterm rterm2
  | size (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = 1 + size_rterm lst + size_rterm nilcase + size_rterm conscase
  | size (CLO_TERM clos) = size_clos clos

and size_rterm rterm = size (rterm2term rterm)

and size_bterm (B_TERM (vars, rterm)) = size_rterm rterm

and size_clos (rterm, env) = size_rterm rterm + size_env env

and size_env (ENV env) =
    MAP.foldr (fn (rterm, n) => size_rterm rterm + n) 0 env


(* size of a term -- number of nodes -- uses IntInf *)
fun large_size (TERM (opr, bterms)) =
    foldr (fn (bterm, n) => IntInf.+ (n, large_size_bterm bterm))
	  1
	  bterms
  | large_size (VAR_TERM var) = 1
  | large_size (LAM_TERM (var, rterm)) = 1 + large_size_rterm rterm
  | large_size (WAI_TERM (rterm1, rterm2)) = 1 + large_size_rterm rterm1 + large_size_rterm rterm2
  | large_size (APP_TERM (rterm1, rterm2)) = 1 + large_size_rterm rterm1 + large_size_rterm rterm2
  | large_size (PAI_TERM (rterm1, rterm2)) = 1 + large_size_rterm rterm1 + large_size_rterm rterm2
  | large_size NIL_TERM = 0
  | large_size (CON_TERM (rterm1, rterm2)) = 1 + large_size_rterm rterm1 + large_size_rterm rterm2
  | large_size (NAT_TERM _) = 0
  | large_size (INL_TERM rterm) = 1 + large_size_rterm rterm
  | large_size (INR_TERM rterm) = 1 + large_size_rterm rterm
  | large_size (FIX_TERM rterm) = 1 + large_size_rterm rterm
  | large_size (SPR_TERM (pair, var1, var2, rterm)) = 1 + large_size_rterm pair + large_size_rterm rterm
  | large_size (DEC_TERM (dec, var1, rterm1, var2, rterm2)) = 1 + large_size_rterm dec + large_size_rterm rterm1 + large_size_rterm rterm2
  | large_size (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = 1 + large_size_rterm lst + large_size_rterm nilcase + large_size_rterm conscase
  | large_size (CLO_TERM clos) = large_size_clos clos

and large_size_rterm rterm = large_size (rterm2term rterm)

and large_size_bterm (B_TERM (vars, rterm)) = large_size_rterm rterm

and large_size_clos (rterm, env) = IntInf.+ (large_size_rterm rterm, large_size_env env)

and large_size_env (ENV env) =
    MAP.foldr (fn (rterm, n) => IntInf.+ (large_size_rterm rterm, n)) 0 env


(* size of the environment of a term term *)
fun env_size (TERM (opr, bterms)) = foldr (fn (bterm, n) => n + env_size_bterm bterm) 0 bterms
  | env_size (VAR_TERM var) = 0
  | env_size (LAM_TERM (var, rterm)) = env_size_rterm rterm
  | env_size (WAI_TERM (rterm1, rterm2)) = env_size_rterm rterm1 + env_size_rterm rterm2
  | env_size (APP_TERM (rterm1, rterm2)) = env_size_rterm rterm1 + env_size_rterm rterm2
  | env_size (PAI_TERM (rterm1, rterm2)) = env_size_rterm rterm1 + env_size_rterm rterm2
  | env_size NIL_TERM = 0
  | env_size (CON_TERM (rterm1, rterm2)) = env_size_rterm rterm1 + env_size_rterm rterm2
  | env_size (NAT_TERM _) = 0
  | env_size (INL_TERM rterm) = env_size_rterm rterm
  | env_size (INR_TERM rterm) = env_size_rterm rterm
  | env_size (FIX_TERM rterm) = env_size_rterm rterm
  | env_size (SPR_TERM (pair, var1, var2, rterm)) = env_size_rterm pair + env_size_rterm rterm
  | env_size (DEC_TERM (dec, var1, rterm1, var2, rterm2)) = env_size_rterm dec + env_size_rterm rterm1 + env_size_rterm rterm2
  | env_size (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = env_size_rterm lst + env_size_rterm nilcase + env_size_rterm conscase
  | env_size (CLO_TERM clos) = env_size_clos clos

and env_size_rterm rterm = env_size (rterm2term rterm)

and env_size_bterm (B_TERM (vars, rterm)) = env_size_rterm rterm

and env_size_clos (rterm, env) = env_size_rterm rterm + size_env env


(* depth of a term *)
fun env_depth (TERM (opr, bterms)) =
    foldr (fn (bterm, n) => Int.max (n, env_depth_bterm bterm)) 0 bterms
  | env_depth (VAR_TERM var) = 0
  | env_depth (LAM_TERM (var, rterm)) = env_depth_rterm rterm
  | env_depth (WAI_TERM (rterm1, rterm2)) = env_depth_rterm rterm1 + env_depth_rterm rterm2
  | env_depth (APP_TERM (rterm1, rterm2)) = env_depth_rterm rterm1 + env_depth_rterm rterm2
  | env_depth (PAI_TERM (rterm1, rterm2)) = env_depth_rterm rterm1 + env_depth_rterm rterm2
  | env_depth NIL_TERM = 0
  | env_depth (CON_TERM (rterm1, rterm2)) = env_depth_rterm rterm1 + env_depth_rterm rterm2
  | env_depth (NAT_TERM _) = 0
  | env_depth (INL_TERM rterm) = env_depth_rterm rterm
  | env_depth (INR_TERM rterm) = env_depth_rterm rterm
  | env_depth (FIX_TERM rterm) = env_depth_rterm rterm
  | env_depth (SPR_TERM (pair, var1, var2, rterm)) = env_depth_rterm pair + env_depth_rterm rterm
  | env_depth (DEC_TERM (dec, var1, rterm1, var2, rterm2)) = env_depth_rterm dec + env_depth_rterm rterm1 + env_depth_rterm rterm2
  | env_depth (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = env_depth_rterm lst + env_depth_rterm nilcase + env_depth_rterm conscase
  | env_depth (CLO_TERM clos) = env_depth_clos clos

and env_depth_rterm rterm = env_depth (rterm2term rterm)

and env_depth_bterm (B_TERM (vars, rterm)) = env_depth_rterm rterm

and env_depth_clos (rterm, env) =
    Int.max (env_depth_rterm rterm, env_depth_env env + 1)

and env_depth_env (ENV env) =
    MAP.foldr (fn (rterm, n) => Int.max (env_depth_rterm rterm, n)) 0 env


(* ------ CHECKERS ------ *)

fun is_nuprl_term token term = (opid_of_term term = token)
fun is_nuprl_ref_term token rterm = is_nuprl_term token (rterm2term rterm)

val is_nuprl_minus_term               = is_nuprl_term "minus"
val is_nuprl_type_term                = is_nuprl_term "universe"
val is_nuprl_function_term            = is_nuprl_term "function"
val is_nuprl_iwf_lemmas_term          = is_nuprl_term "!wf"
val is_nuprl_iabstraction_term        = is_nuprl_term "!abstraction"
val is_nuprl_int_term                 = is_nuprl_term "int"
val is_nuprl_loc_term                 = is_nuprl_term "Id"
val is_nuprl_atom_term                = is_nuprl_term "atom"
val is_nuprl_list_term                = is_nuprl_term "list"
val is_nuprl_bool_term                = is_nuprl_term "bool"
val is_nuprl_unit_term                = is_nuprl_term "unit"
val is_nuprl_product_term             = is_nuprl_term "product"
val is_nuprl_select_term              = is_nuprl_term "select"
val is_nuprl_iclosure_term            = is_nuprl_term "!closure"
val is_nuprl_eclass_term              = is_nuprl_term "eclass"
val is_nuprl_iabstraction_term        = is_nuprl_term "!abstraction"
val is_nuprl_all_term                 = is_nuprl_term "all"
val is_nuprl_uall_term                = is_nuprl_term "uall"
val is_nuprl_bag_term                 = is_nuprl_term "bag"
val is_nuprl_eqof_term                = is_nuprl_term "eqof"
val is_nuprl_eq_int_term              = is_nuprl_term "eq_int"
val is_nuprl_eq_id_term               = is_nuprl_term "eq_id"
val is_nuprl_iinclude_properties_term = is_nuprl_term "!include_properties"

fun is_nuprl_iwftheorem_term (TERM ((("!theorem", _), [(name, "t")]), [B_TERM ([], theorem)])) =
    String.isSuffix "_wf" name
  | is_nuprl_iwftheorem_term _ = false

fun equal_parameters param1 param2 = (param1 : parameter) = param2


(* ------ LIBRARY HANDLING ------ *)

val to_keep =
    ["NI_Auto",
     "isect_1",
     "core_2",
     "well_fnd",
     "int_1",
     "bool_1",
     "union",
     "subtype_0",
     "sqequal_1",
     "fun_1",
     "rfunction_1",
     "rel_1",
     "quot_1",
     "int_2",
     "list_1",
     "prog_1",
     "subtype_1",
     "num_thy_1",
     "basic",
     "tree_1",
     "nat_extra",
     "list+",
     "sets_1",
     "list_2",
     "list_3",
     "call by value",
     "general",
     "atoms",
     "decidable-equality",
     "event-ordering",
     "process-model",
     "event-logic-applications",
     "event-structures2",
     "event-system"]

val to_filter_out =
    ["test",
     "DivA",
     "ppcc",
     "gen_algebra_1",
     "groups_1",
     "rings_1",
     "algebras_1",
     "perms_1",
     "perms_2",
     "factor_1",
     "mset",
     "basic-tactics",
     "tactics",
     "polynom_1",
     "polynom_2",
     "polynom_3",
     "polynom_4",
     "rationals",
     "reals",
     "better\\ polynomials",
     "polynomials",
     "randomness",
     "realizability",
     "FullyIntensional",
     "concrete-message-automata",
     "dependent\\ intersection",
     "message-automata"]

fun isin_str str lst = List.exists (fn s : string => s = str) lst

fun filter_library lst [] = []
  | filter_library lst (term as (TERM (((opid, tag), []), b_terms)) :: terms) =
    if get_tag tag = "t"
    then if isin_str opid lst
	 then filter_library lst terms
	 else term :: filter_library lst terms
    else raise Fail "filter_library"
  | filter_library _ _ = raise Fail "filter_library"

fun emlib () : lib = {abs = ref MAP.empty, tof = ref MAP.empty}

fun union_libs ({abs = abs1, tof = tof1} : lib)
	       ({abs = abs2, tof = tof2} : lib) =
    {abs = ref (MAP.unionWithi (fn (id, x, y) =>
				   let (*val _ =
					   if id = "Memory1-prc"
					   then print ("[-----------------------------------------" ^ Int.toString (length x) ^ "-" ^ Int.toString (length y) ^ "]\n")
					   else ()*)
				   in x @ y
				   end)
			       (!abs1, !abs2)),
     tof = ref (MAP.unionWithi (fn (id, x, y) => y)
			       (!tof1, !tof2))}

fun mk_item id sign obid lhs rhs wfs =
    {id = id, sign = sign, obid = obid, lhs = lhs, rhs = rhs, wfs = wfs}

fun insert_abs (lib as {abs, tof}) id info =
    let val a = !abs
	(*val _ = if id = "Memory1-prc"
		then print ("[---------------------------------------------------]\n")
		else ()*)
	val _ = case MAP.find (a, id) of
		    SOME lst => abs := MAP.insert (a, id, (TR.mk info) :: lst)
		  | NONE     => abs := MAP.insert (a, id, [TR.mk info])
    in lib
    end

fun insert_tof (lib as {abs, tof}) obid rhs =
    (tof := MAP.insert (!tof, obid, TR.mk rhs); lib)

datatype lib_kind =
	 ABS of string * item
       | TOF of string * nuprl_term

fun term2map (TERM (((id, tag), [(obid, "o")]),
		    [B_TERM ([], lhs),
		     B_TERM ([], rhs),
		     B_TERM ([], wfs)])) =
    if get_tag tag = "t"
    then let val trhs  = rterm2term rhs
	 in if is_nuprl_term "!primitive" trhs
	    then NONE
	    else let val tlhs = rterm2term lhs
		     val twfs = rterm2term wfs
		     val opid = opid_of_term tlhs
		     val sign = getSignature tlhs
		     val subs = subterms twfs
		     val item = mk_item id sign obid lhs rhs subs
		 in SOME (ABS (opid, item))
		 end
	 end
    else raise Fail "wrong format:term2map:abs"
  | term2map (TERM (((id, tag), [(obid, "o")]),
		    [B_TERM ([], termof),
		     B_TERM ([], extract)])) =
    if get_tag tag = "t"
    then let val ttermof = rterm2term termof
	 in if is_nuprl_term "TERMOF" ttermof
	    then case get_obid_parameters (parameters_of_term ttermof) of
		     SOME oid =>
		     if oid = obid
		     then SOME (TOF (oid, rterm2term extract))
		     else raise Fail "wrong object identifier"
		   | NONE => NONE
	    else NONE
	 end
    else raise Fail "wrong format:term2map:termof"
  | term2map _ = raise Fail "wrong format:term2map"

fun b_terms2map [] = emlib ()
  | b_terms2map ((B_TERM ([], term)) :: b_terms) =
    (case term2map (rterm2term term) of
	 SOME (ABS (opid, item)) =>
	 insert_abs (b_terms2map b_terms) opid item
       | SOME (TOF (oid, rhs)) =>
	 insert_tof (b_terms2map b_terms) oid rhs
       | NONE => b_terms2map b_terms)
  | b_terms2map _ = raise Fail "wrong format:b_terms2map"

fun terms2map [] = emlib ()
  | terms2map ((TERM (((opid, tag), []), b_terms)) :: terms) =
    if get_tag tag = "t"
    then let val _    = print ("[loading theory: " ^ opid ^ "]\n")
	     val map1 = b_terms2map b_terms
	     val map2 = terms2map terms
	 in union_libs map1 map2
	 end
    else raise Fail ("wrong format:terms2map:lib" ^ get_tag tag ^ "-")
  | terms2map _ =  raise Fail "wrong format:terms2map"

fun terms2map' [] = emlib ()
  | terms2map' ((TERM (((opid, tag), []), b_terms)) :: terms) =
    if get_tag tag = "t"
    then if isin_str opid to_filter_out
	 then (print ("[not loading " ^ opid ^ " theory]\n"); terms2map' terms)
	 else let val map1 = b_terms2map b_terms
		  val map2 = terms2map' terms
	      in union_libs map1 map2
	      end
    else raise Fail "wrong format:terms2map':lib"
  | terms2map' _ = raise Fail "wrong format:terms2map'"

fun find_sign abs term =
    let val sign = getSignature term
	val opid = opid_of_term term
	fun aux ritem =
	    let val {id, sign = sign', obid, lhs, rhs, wfs} = TR.get ritem
	    in not (is_nuprl_ref_term "!primitive" rhs)
	       andalso
	       (eq_signs sign sign')
	    end
    in case MAP.find (!abs, opid) of
	   SOME lst =>
	   (case List.find aux lst of
		  SOME ritem => TR.get ritem
		| NONE => raise Fail ("find_sign:wrong-signature-for-"
				      ^ opid
				      ^ "-"
				      ^ sign_to_string sign
				      ^ "-"
				      ^ T.fmt {init  = "[",
					       final = "]",
					       sep   = ",",
					       fmt   = fn i => sign_to_string (get_item_sign (TR.get i))}
					      lst))
	 | NONE => raise Fail ("find_sign:" ^ opid ^ "-not-in-lib")
    end

fun get_opids term = SET.add (get_opids_bterms (get_bterms term), opid_of_term term)
and get_opids_bterms bterms = foldr (fn (bterm, set) => SET.union (set, get_opids_bterm bterm)) SET.empty bterms
and get_opids_bterm (B_TERM (vars, rterm)) = get_opids (rterm2term rterm)

fun closure_term_wrt_lib set (lib as {abs, tof}) =
    let val m = !abs
    in SET.foldr (fn (opid, set) =>
		     case MAP.find (m, opid) of
			 SOME lst =>
			 foldr (fn ({id, sign, obid, lhs, rhs, wfs}, set) =>
				   let val set1 = get_opids rhs
				       val set2 = closure_term_wrt_lib set1 lib
				   in SET.union (set, set2)
				   end)
			       set
			       lst
		       | NONE => set)
		 set
		 set
    end


(* ------ DESTRUCTORS ------ *)

fun dest_simple_term term =
    let val opid  = opid_of_term term
	val terms =
	    map (fn ([], term) => term
		  | _ => (print (toStringTerm term); raise EH.Impossible "dest_simple_term"))
		(bterms_of_term term)
    in (opid, terms)
    end

fun dest_simple_null_term term =
    let val opid  = opid_of_term term
	val terms =
	    map (fn ([],   term) => term
		  | ([""], term) => term
		  | _ => (print (toStringTerm term); raise EH.Impossible "dest_simple_term"))
		(bterms_of_term term)
    in (opid, terms)
    end

fun dest_term term =
    ((opid_of_term term, parameters_of_term term), bterms_of_term term)

fun full_dest_term (TERM (((opid, _), params), bterms)) =
    ((opid, params), map (fn (B_TERM (vars, rterm)) => (vars, rterm2term rterm)) bterms)
  | full_dest_term (VAR_TERM var)              = raise Fail "full_dest_term:VAR_TERM"
  | full_dest_term (LAM_TERM (var, rterm))     = raise Fail "full_dest_term:LAM_TERM"
  | full_dest_term (WAI_TERM (rterm1, rterm2)) = raise Fail "full_dest_term:WAI_TERM"
  | full_dest_term (APP_TERM (rterm1, rterm2)) = raise Fail "full_dest_term:APP_TERM"
  | full_dest_term (PAI_TERM (rterm1, rterm2)) = raise Fail "full_dest_term:PAI_TERM"
  | full_dest_term NIL_TERM                    = raise Fail "full_dest_term:NIL_TERM"
  | full_dest_term (CON_TERM (rterm1, rterm2)) = raise Fail "full_dest_term:CON_TERM"
  | full_dest_term (NAT_TERM n)                = raise Fail "full_dest_term:NAT_TERM"
  | full_dest_term (INL_TERM rterm)            = raise Fail "full_dest_term:INL_TERM"
  | full_dest_term (INR_TERM rterm)            = raise Fail "full_dest_term:INR_TERM"
  | full_dest_term (FIX_TERM rterm)            = raise Fail "full_dest_term:FIX_TERM"
  | full_dest_term (SPR_TERM (pair, var1, var2, rterm))          = raise Fail "full_dest_term:SPR_TERM"
  | full_dest_term (DEC_TERM (dec, var1, rterm1, var2, rterm2))  = raise Fail "full_dest_term:DEC_TERM"
  | full_dest_term (LIN_TERM (lst, nilcase, x, xs, r, conscase)) = raise Fail "full_dest_term:LIN_TERM"
  | full_dest_term (CLO_TERM clos) = raise Fail "full_dest_term:CLO_TERM"

fun dest_list term =
    if is_nuprl_cons_term term
    then let val (h, t) = dest_cons term
	 in h :: (dest_list t)
	 end
    else if is_nuprl_nil_term term
    then []
    else raise EH.Impossible "dest_list"

fun dest_lambdas term =
    if is_nuprl_lambda_term term
    then case bterms_of_term term of
	     [([x], B)] =>
	     let val (bounds, body) = dest_lambdas (rterm2term B)
	     in (x :: bounds, body)
	     end
	   | _ => raise Fail "dest_lambdas"
    else ([], term)

fun dest_alls_ualls term =
    let val b = is_nuprl_all_term term
    in if b orelse is_nuprl_uall_term term
       then case bterms_of_term term of
		[([], typ), ([x], B)] =>
		let val (bounds, body) = dest_alls_ualls (rterm2term B)
		in ((x, rterm2term typ, b) :: bounds, body)
		end
	      | _ => raise Fail "dest_alls_ualls"
       else ([], term)
    end

fun dest_so_variable (TERM ((("variable", _), [(var, "v")]), bterms)) =
    (var, map (fn B_TERM ([], rt) => rterm2term rt
		| _ => raise Fail "dest_so_variable")
	      bterms)
  | dest_so_variable _ = raise Fail "dest_so_variable"

fun dest_eclass (TERM ((("eclass", tag), params),
		       [B_TERM ([],      info),
			B_TERM ([es, e], X)])) =
    (rterm2term info, es, e, rterm2term X)
  | dest_eclass _ = raise EH.Impossible "dest_eclass"

fun dest_let (TERM ((("let", tag), params),
		    [B_TERM ([],  exp1),
		     B_TERM ([v], exp2)])) =
    (rterm2term exp1, v, rterm2term exp2)
  | dest_let _ = raise EH.Impossible "dest_let"

fun dest_function (TERM ((("function", tag), params),
			 [B_TERM ([],   term1),
			  B_TERM ([""], term2)])) =
    (rterm2term term1, rterm2term term2)
  | dest_function _ = raise EH.Impossible "dest_function"

fun dest_functions term =
    if is_nuprl_function_term term
    then let val (t1, t2) = dest_function term
	     val (lst, T) = dest_functions t2
	 in (t1 :: lst, T)
	 end
    else ([], term)

fun dest_product (TERM ((("product", tag), params),
			[B_TERM ([],   term1),
			 B_TERM ([""], term2)])) =
    (rterm2term term1, rterm2term term2)
  | dest_product _ = raise Fail "dest_product"

fun dest_iabstraction (TERM ((("!abstraction", tag), []),
			     [B_TERM ([], t1),
			      B_TERM ([], t2),
			      B_TERM ([], t3)])) =
    (t1, t2, t3)
  | dest_iabstraction _ = raise EH.Impossible "dest_iabstraction"

fun dest_iinclude_properties (TERM ((("!include_properties", tag), []),
				    [B_TERM ([], t1),
				     B_TERM ([], t2)])) =
    (t1, t2)
  | dest_iinclude_properties _ = raise EH.Impossible "dest_iinclude_properties"

fun dest_iwftheorem (TERM ((("!theorem", _), [(name, "t")]),
			   [B_TERM ([], theorem)])) = rterm2term theorem
  | dest_iwftheorem _ = raise EH.Impossible "dest_iwftheorem"

fun dest_id (TERM ((("token", tag), [(id, "ut2")]), [])) = id
  | dest_id _ = raise EH.Impossible "dest_id"

fun gen_dest_single (TERM (((opid, tag), parms), [B_TERM ([], term)])) str msg =
    if opid = str
    then rterm2term term
    else raise EH.Impossible msg
  | gen_dest_single term opid msg = raise Fail ("gen_dest_single:" ^ msg)

fun dest_minus        term = gen_dest_single term "minus"        "dest_minus"
fun dest_bnot         term = gen_dest_single term "bnot"         "dest_bnot"
fun dest_bag          term = gen_dest_single term "bag"          "dest_bag"
fun dest_type_list    term = gen_dest_single term "list"         "dest_type_list"
fun dest_eqof         term = gen_dest_single term "eqof"         "dest_eqof"
fun dest_primed_class term = gen_dest_single term "primed-class" "dest_primed_class"
fun dest_es_eq        term = gen_dest_single term "es-eq"        "dest_es_eq"

fun dest_integer m term =
    (if is_nuprl_natural_number_term term
     then dest_natural_number term
     else if is_nuprl_minus_term term
     then II.~ (dest_natural_number (dest_minus term))
     else raise Fail "")
    handle Fail str => raise Fail ("dest_integer:not-int-"
				   ^ Int.toString m
				   ^ "(" ^ toStringTerm term
				   ^ ")"
				   ^ str)

fun dest_small_integer term = II.toInt (dest_integer 1 term)

fun dest_iport (TERM ((("!port", tag), [(str, "n")]), [])) =
    (case II.fromString str of
	 NONE => raise Fail ("dest_integer:not-int-in-string(" ^ str ^ ")")
       | SOME x => II.toInt x)
  | dest_iport _ = raise Fail "dest_iport"

fun dest_ihost (TERM ((("!host", tag), [(x, "s")]), [])) = x
  | dest_ihost _ = raise Fail "dest_ihost"

fun dest_rec_comb (TERM ((("rec-comb", tag), []),
			 [B_TERM ([], Xs),
			  B_TERM ([], F),
			  B_TERM ([], init)])) =
    (rterm2term Xs, rterm2term F, rterm2term init)
  | dest_rec_comb _ =  raise EH.Impossible "dest_rec_comb"

fun gen_dest_pair (TERM (((opid, tag), params),
			 [B_TERM ([], term1),
			  B_TERM ([], term2)])) str msg =
    if opid = str
    then (rterm2term term1, rterm2term term2)
    else raise EH.Impossible msg
  | gen_dest_pair term opid msg =  raise EH.Impossible msg

fun dest_select    term = gen_dest_pair term "select"    "dest_select"
fun dest_prior_prc term = gen_dest_pair term "prior-prc" "dest_prior_prc"
fun dest_iclosure  term = gen_dest_pair term "!closure"  "dest_iclosure"
fun dest_lt_int    term = gen_dest_pair term "lt_int"    "dest_lt_int"
fun dest_le_int    term = gen_dest_pair term "le_int"    "dest_le_int"
fun dest_eq_int    term = gen_dest_pair term "eq_int"    "dest_eq_int"
fun dest_eq_id     term = gen_dest_pair term "eq_id"     "dest_eq_id"
fun dest_band      term = gen_dest_pair term "band"      "dest_band"
fun dest_member    term = gen_dest_pair term "member"    "dest_member"

fun dest_applies (TERM ((("apply", tag), []),
			[B_TERM ([], f),
			 B_TERM ([], arg)])) =
    let val (x, xs) = dest_applies (rterm2term f)
    in (x, xs @ [rterm2term arg])
    end
  | dest_applies term = (term, [])

fun is_nuprl_minus_natural_number_term term =
    is_nuprl_minus_term term
    andalso
    is_nuprl_natural_number_term (dest_minus term)

fun is_nuprl_integer_term term =
    is_nuprl_natural_number_term term
    orelse
    is_nuprl_minus_natural_number_term term

fun is_nuprl_event_orderingp_term lvl (TERM ((("event-ordering+", tag), [(l,_)]), [B_TERM ([], info)])) = (l = lvl)
  | is_nuprl_event_orderingp_term _ _ = false

fun is_nuprl_prop_term lvl (TERM ((("prop", tag), [(l,_)]), [])) = (l = lvl)
  | is_nuprl_prop_term _ _ = false


(* ------ CONSTRUCTORS ------ *)

fun mk_nuprl_small_natural_number_term int = mk_nuprl_natural_number_term (II.fromInt int)

fun mk_nuprl_token_term tok =
    TERM ((("token", dtag), [mk_nuprl_token_parameter tok]), [])

fun mk_nuprl_minus_term term = mk_nuprl_simple_term "minus" [term]

fun mk_nuprl_df_program_meaning_term term =
    mk_nuprl_simple_term "df-program-meaning" [term]

val mk_nuprl_axiom_term = mk_nuprl_simple_term "axiom" []

fun mk_nuprl_mkid_term id =
    TERM ((("token", dtag), [mk_nuprl_ut2_parameter id]), [])

fun mk_nuprl_ihost_term host =
    TERM ((("!host", dtag), [mk_nuprl_string_parameter host]), [])

fun mk_nuprl_iport_term port =
    TERM ((("!port", dtag), [mk_nuprl_natural_parameter (II.fromInt port)]), [])

fun mk_nuprl_integer_term int =
    if II.< (int, 0)
    then mk_nuprl_minus_term (mk_nuprl_natural_number_term (II.~ int))
    else mk_nuprl_natural_number_term int

fun mk_nuprl_int_from_string str =
    case II.fromString str of
	NONE => raise Fail "mk_nuprl_int_from_string"
      | SOME n => mk_nuprl_integer_term n

(* This is a crude hack!! *)
fun mk_nuprl_real_from_string str =
    case Real.fromString str of
	NONE   => raise Fail "mk_nuprl_real_from_string"
      | SOME r => mk_nuprl_integer_term (Real.toLargeInt (IEEEReal.getRoundingMode ()) r)

fun mk_nuprl_small_integer_term int = mk_nuprl_integer_term (II.fromInt int)

fun mk_nuprl_applies_term func args =
    foldl (fn (arg, f) => mk_nuprl_simple_term "apply" [f, arg])
	  func
	  args

fun mk_nuprl_let_term var pat body =
    mk_nuprl_term ("let", []) [([], pat), ([var], body)]

fun mk_nuprl_rec_term var term = mk_nuprl_term ("rec", []) [([var], term)]

fun mk_nuprl_lambdas_term vars term =
    foldr (fn (var, term) => mk_nuprl_lambda_term var term)
	  term
	  vars

fun mk_nuprl_spreadn_term pair ([],       bterm) = raise EH.Impossible ""
  | mk_nuprl_spreadn_term pair ([_],      bterm) = raise EH.Impossible ""
  | mk_nuprl_spreadn_term pair ([v1, v2], bterm) = mk_nuprl_spread_term pair (v1, v2, bterm)
  | mk_nuprl_spreadn_term pair (vars,     bterm) = mk_nuprl_term ("spreadn", []) [([], pair), (vars,     bterm)]

fun mk_nuprl_isl_term  term = mk_nuprl_simple_term "isl"  [term]
fun mk_nuprl_isr_term  term = mk_nuprl_simple_term "isr"  [term]
fun mk_nuprl_outl_term term = mk_nuprl_simple_term "outl" [term]
fun mk_nuprl_outr_term term = mk_nuprl_simple_term "outr" [term]

val mk_nuprl_ycomb_term = mk_nuprl_simple_term "ycomb" []

fun mk_nuprl_genrec_term (n, r, B) =
    mk_nuprl_term ("genrec", []) [([n, r], B)]

fun mk_nuprl_bind_class_term f (x, g) =
    mk_nuprl_term ("bind-class", []) [([], f), ([x], g)]

fun mk_nuprl_combined_class_term         f lst = mk_nuprl_simple_term "simple-comb"            [f, lst]
fun mk_nuprl_rec_combined_class_term     f lst = mk_nuprl_simple_term "rec-combined-class"     [lst, f]
fun mk_nuprl_combined_loc_class_term     f lst = mk_nuprl_simple_term "simple-loc-comb"        [f, lst]
fun mk_nuprl_rec_combined_loc_class_term f lst = mk_nuprl_simple_term "rec-combined-loc-class" [lst, f]

fun mk_nuprl_rec_comb_term f classes init = mk_nuprl_simple_term "rec-comb" [classes, f, init]

fun mk_nuprl_so_apply1_term f x     = mk_nuprl_simple_term "so_apply" [f, x]
fun mk_nuprl_so_apply2_term f x y   = mk_nuprl_simple_term "so_apply" [f, x, y]
fun mk_nuprl_so_apply3_term f x y z = mk_nuprl_simple_term "so_apply" [f, x, y, z]

fun mk_nuprl_combined0_class_term bag =
    mk_nuprl_simple_term "simple-comb-0" [bag]
fun mk_nuprl_combined1_class_term f class =
    mk_nuprl_simple_term "simple-comb-1" [f, class]
fun mk_nuprl_combined2_class_term f class1 class2 =
    mk_nuprl_simple_term "simple-comb-2" [f, class1, class2]
fun mk_nuprl_combined3_class_term f class1 class2 class3 =
    mk_nuprl_simple_term "simple-comb-3" [f, class1, class2, class3]

fun mk_nuprl_combined0_loc_class_term bag =
    mk_nuprl_simple_term "simple-loc-comb-0" [bag]
fun mk_nuprl_combined1_loc_class_term f class =
    mk_nuprl_simple_term "simple-loc-comb-1" [f, class]
fun mk_nuprl_combined2_loc_class_term f class1 class2 =
    mk_nuprl_simple_term "simple-loc-comb-2" [f, class1, class2]
fun mk_nuprl_combined3_loc_class_term f class1 class2 class3 =
    mk_nuprl_simple_term "simple-loc-comb-3" [f, class1, class2, class3]

fun mk_nuprl_rec_combined0_class_term bag =
    mk_nuprl_simple_term "rec-combined-class-0" [bag]
fun mk_nuprl_rec_combined1_class_term f class =
    mk_nuprl_simple_term "rec-combined-class-1" [f, class]
fun mk_nuprl_rec_combined2_class_term f class1 class2 =
    mk_nuprl_simple_term "rec-combined-class-2" [f, class1, class2]
fun mk_nuprl_rec_combined3_class_term f class1 class2 class3 =
    mk_nuprl_simple_term "rec-combined-class-3" [f, class1, class2, class3]

fun mk_nuprl_rec_combined0_class_opt_term opt bag =
    mk_nuprl_simple_term "rec-combined-class-opt-0" [bag, opt]
fun mk_nuprl_rec_combined1_class_opt_term opt f class =
    mk_nuprl_simple_term "rec-combined-class-opt-1" [f, opt, class]
fun mk_nuprl_rec_combined2_class_opt_term opt f class1 class2 =
    mk_nuprl_simple_term "rec-combined-class-opt-2" [f, opt, class1, class2]
fun mk_nuprl_rec_combined3_class_opt_term opt f class1 class2 class3 =
    mk_nuprl_simple_term "rec-combined-class-opt-3" [f, opt, class1, class2, class3]

fun mk_nuprl_rec_combined0_loc_class_term bag =
    mk_nuprl_simple_term "rec-combined-loc-class-0" [bag]
fun mk_nuprl_rec_combined1_loc_class_term f class =
    mk_nuprl_simple_term "rec-combined-loc-class-1" [f, class]
fun mk_nuprl_rec_combined2_loc_class_term f class1 class2 =
    mk_nuprl_simple_term "rec-combined-loc-class-2" [f, class1, class2]
fun mk_nuprl_rec_combined3_loc_class_term f class1 class2 class3 =
    mk_nuprl_simple_term "rec-combined-loc-class-3" [f, class1, class2, class3]

fun mk_nuprl_rec_combined0_loc_class_opt_term opt bag =
    mk_nuprl_simple_term "rec-combined-loc-class-opt-0" [bag, opt]
fun mk_nuprl_rec_combined1_loc_class_opt_term opt f class =
    mk_nuprl_simple_term "rec-combined-loc-class-opt-1" [f, opt, class]
fun mk_nuprl_rec_combined2_loc_class_opt_term opt f class1 class2 =
    mk_nuprl_simple_term "rec-combined-loc-class-opt-2" [f, opt, class1, class2]
fun mk_nuprl_rec_combined3_loc_class_opt_term opt f class1 class2 class3 =
    mk_nuprl_simple_term "rec-combined-loc-class-opt-3" [f, opt, class1, class2, class3]

fun mk_nuprl_lifting0_term f = mk_nuprl_simple_term "lifting-0" [f]
fun mk_nuprl_lifting1_term f = mk_nuprl_simple_term "lifting-1" [f]
fun mk_nuprl_lifting2_term f = mk_nuprl_simple_term "lifting-2" [f]
fun mk_nuprl_lifting3_term f = mk_nuprl_simple_term "lifting-3" [f]
fun mk_nuprl_lifting4_term f = mk_nuprl_simple_term "lifting-4" [f]

fun mk_nuprl_lifting_gen_term n f = mk_nuprl_simple_term "lifting-gen" [n, f]

fun mk_nuprl_lifting_loc0_term f = mk_nuprl_simple_term "lifting-loc-0" [f]
fun mk_nuprl_lifting_loc1_term f = mk_nuprl_simple_term "lifting-loc-1" [f]
fun mk_nuprl_lifting_loc2_term f = mk_nuprl_simple_term "lifting-loc-2" [f]
fun mk_nuprl_lifting_loc3_term f = mk_nuprl_simple_term "lifting-loc-3" [f]
fun mk_nuprl_lifting_loc4_term f = mk_nuprl_simple_term "lifting-loc-4" [f]

fun mk_nuprl_lifting_loc_gen_term n f = mk_nuprl_simple_term "lifting-loc-gen" [n, f]

fun mk_nuprl_concat_lifting0_term f = mk_nuprl_simple_term "concat-lifting-0" [f]
fun mk_nuprl_concat_lifting1_term f = mk_nuprl_simple_term "concat-lifting-1" [f]
fun mk_nuprl_concat_lifting2_term f = mk_nuprl_simple_term "concat-lifting-2" [f]
fun mk_nuprl_concat_lifting3_term f = mk_nuprl_simple_term "concat-lifting-3" [f]
fun mk_nuprl_concat_lifting4_term f = mk_nuprl_simple_term "concat-lifting-4" [f]

fun mk_nuprl_concat_lifting_gen_term n f = mk_nuprl_simple_term "concat-lifting-gen" [n, f]

fun mk_nuprl_concat_lifting_loc0_term f = mk_nuprl_simple_term "concat-lifting-loc-0" [f]
fun mk_nuprl_concat_lifting_loc1_term f = mk_nuprl_simple_term "concat-lifting-loc-1" [f]
fun mk_nuprl_concat_lifting_loc2_term f = mk_nuprl_simple_term "concat-lifting-loc-2" [f]
fun mk_nuprl_concat_lifting_loc3_term f = mk_nuprl_simple_term "concat-lifting-loc-3" [f]
fun mk_nuprl_concat_lifting_loc4_term f = mk_nuprl_simple_term "concat-lifting-loc-4" [f]

fun mk_nuprl_concat_lifting_loc_gen_term n f = mk_nuprl_simple_term "concat-lifting-loc-gen" [n, f]

fun mk_nuprl_fun_term   term1 term2 =
    mk_nuprl_term ("function", []) [([], term1), ([""], term2)]

fun mk_nuprl_prod_term  term1 term2 =
    mk_nuprl_term ("product", []) [([], term1), ([""], term2)]

fun mk_nuprl_type_term i = mk_nuprl_term ("universe", [mk_nuprl_level_exp_parameter i]) []
fun mk_nuprl_msg_term  i = mk_nuprl_term ("Message",  [mk_nuprl_level_exp_parameter i]) []

fun mk_nuprl_event_orderingp_term i = mk_nuprl_term ("event-ordering+", [mk_nuprl_level_exp_parameter (i ^ "'")]) [([], mk_nuprl_msg_term i)]

fun mk_nuprl_valuealltype_term i = mk_nuprl_term ("vatype", [mk_nuprl_level_exp_parameter i]) []

fun mk_nuprl_class_term term =
    mk_nuprl_term ("eclass", [mk_nuprl_level_exp_parameter "i'"])
		  [([], mk_nuprl_msg_term "i"),
		   (["es", "e"], term)]

fun mk_nuprl_normal_locally_programmable_term typ class =
    mk_nuprl_term ("normal-locally-programmable", [mk_nuprl_level_exp_parameter "i'"])
		  [([], mk_nuprl_msg_term "i"),
		   ([], typ),
		   ([], class)]

val mk_nuprl_nlp_term = mk_nuprl_normal_locally_programmable_term

fun mk_nuprl_local_class_msg_term typ class =
    mk_nuprl_term ("local-class", [mk_nuprl_level_exp_parameter "i'"])
		  [([], mk_nuprl_msg_term "i"),
		   ([], typ),
		   ([], class)]

fun mk_nuprl_single_valued_classrel_term es class typ =
    mk_nuprl_term ("single-valued-classrel", [])
		  [([], es),
		   ([], class),
		   ([], typ)]

fun mk_nuprl_programmable_term typ class =
    mk_nuprl_term ("programmable", [mk_nuprl_level_exp_parameter "i'"])
		  [([], mk_nuprl_msg_term "i"),
		   ([], typ),
		   ([], class)]

fun mk_nuprl_std_ma_term eo class headers =
    mk_nuprl_term ("std-ma", [mk_nuprl_level_exp_parameter "i"])
		  [([], eo),
		   ([], class),
		   ([], headers)]

fun mk_nuprl_message_constraint_term eo class headers =
    mk_nuprl_term ("message-constraint", [mk_nuprl_level_exp_parameter "i"])
		  [([], eo),
		   ([], class),
		   ([], headers)]

fun mk_nuprl_messages_delivered_term eo class =
    mk_nuprl_term ("messages-delivered", [mk_nuprl_level_exp_parameter "i"])
		  [([], eo),
		   ([], class)]

val mk_nuprl_event_ordering_p_term =
    mk_nuprl_term ("event-ordering+", [mk_nuprl_level_exp_parameter "i'"])
		  [([], mk_nuprl_msg_term "i")]

fun mk_nuprl_prop_term i =
    mk_nuprl_term ("prop", [mk_nuprl_level_exp_parameter i]) []

(* 0 argument *)
val mk_nuprl_int_term            = mk_nuprl_simple_term "int"             []
val mk_nuprl_real_term           = mk_nuprl_simple_term "real"            []
val mk_nuprl_bool_term           = mk_nuprl_simple_term "bool"            []
val mk_nuprl_unit_term           = mk_nuprl_simple_term "unit"            []
val mk_nuprl_atom_term           = mk_nuprl_simple_term "atom"            []
val mk_nuprl_top_term            = mk_nuprl_simple_term "top"             []
val mk_nuprl_nat_term            = mk_nuprl_simple_term "nat"             []
val mk_nuprl_loc_term            = mk_nuprl_simple_term "Id"              []
val mk_nuprl_name_term           = mk_nuprl_simple_term "name"            [] (* Atom List *)
val mk_nuprl_empty_env_term      = mk_nuprl_simple_term "env"             []
val mk_nuprl_inewline_term       = mk_nuprl_simple_term "!newline"        []
val mk_nuprl_empty_bag_term      = mk_nuprl_simple_term "empty-bag"       []
val mk_nuprl_icons_nil_term      = mk_nuprl_simple_term "!cons"           []
val mk_nuprl_itext_nil_term      = mk_nuprl_simple_term "!text_cons"      []
val mk_nuprl_bool_deq_term       = mk_nuprl_simple_term "bool-deq"        []
val mk_nuprl_int_deq_term        = mk_nuprl_simple_term "int-deq"         []
val mk_nuprl_atom_deq_term       = mk_nuprl_simple_term "atom-deq"        []
val mk_nuprl_nat_deq_term        = mk_nuprl_simple_term "nat-deq"         []
val mk_nuprl_loc_deq_term        = mk_nuprl_simple_term "id-deq"          []
val mk_nuprl_unit_deq_term       = mk_nuprl_simple_term "unit-deq"        []
val mk_nuprl_btrue_term          = mk_nuprl_simple_term "btrue"           []
val mk_nuprl_bfalse_term         = mk_nuprl_simple_term "bfalse"          []
val mk_nuprl_condition_cons_term = mk_nuprl_simple_term "!condition_cons" []
val mk_nuprl_it_term             = mk_nuprl_simple_term "it"              []
val mk_nuprl_ioid_term           = mk_nuprl_simple_term "!oid"            []

(* 1 argument *)
fun mk_nuprl_once_class_term                   class = mk_nuprl_simple_term "once-class"                    [class]
fun mk_nuprl_send_once_class_term              class = mk_nuprl_simple_term "send-once-class"               [class]
fun mk_nuprl_send_once_loc_class_term          class = mk_nuprl_simple_term "send-once-loc-class"           [class]
fun mk_nuprl_on_loc_class_term                 class = mk_nuprl_simple_term "on-loc-class"                  [class]
fun mk_nuprl_but_first_class_term              class = mk_nuprl_simple_term "but-first-class"               [class]
fun mk_nuprl_skip_first_class_term             class = mk_nuprl_simple_term "skip-first-class"              [class]
fun mk_nuprl_primed_class_term                 class = mk_nuprl_simple_term "primed-class"                  [class]
fun mk_nuprl_single_bag_term                   elt   = mk_nuprl_simple_term "single-bag"                    [elt]
fun mk_nuprl_bnot_term                         term  = mk_nuprl_simple_term "bnot"                          [term]
fun mk_nuprl_not_term                          term  = mk_nuprl_simple_term "not"                           [term]
fun mk_nuprl_pi1_term                          term  = mk_nuprl_simple_term "pi1"                           [term]
fun mk_nuprl_pi2_term                          term  = mk_nuprl_simple_term "pi2"                           [term]
fun mk_nuprl_hd_term                           term  = mk_nuprl_simple_term "hd"                            [term]
fun mk_nuprl_tl_term                           term  = mk_nuprl_simple_term "tl"                            [term]
fun mk_nuprl_es_eq_term                        es    = mk_nuprl_simple_term "es-eq"                         [es]
fun mk_nuprl_list_deq_term                     term  = mk_nuprl_simple_term "list-deq"                      [term]
fun mk_nuprl_eqof_term                         term  = mk_nuprl_simple_term "eqof"                          [term]
fun mk_nuprl_valueall_type_term                typ   = mk_nuprl_simple_term "valueall-type"                 [typ]
fun mk_nuprl_list_term                         term  = mk_nuprl_simple_term "list"                          [term]
fun mk_nuprl_bag_term                          term  = mk_nuprl_simple_term "bag"                           [term]
fun mk_nuprl_deq_term                          term  = mk_nuprl_simple_term "deq"                           [term]
fun mk_nuprl_esE_term                          es    = mk_nuprl_simple_term "es-E"                          [es]
fun mk_nuprl_assert_term                       b     = mk_nuprl_simple_term "assert"                        [b]
fun mk_nuprl_msg_header_term                   term  = mk_nuprl_simple_term "msg-header"                    [term]
fun mk_nuprl_msg_type_term                     term  = mk_nuprl_simple_term "msg-type"                      [term]
fun mk_nuprl_msg_body_term                     term  = mk_nuprl_simple_term "msg-body"                      [term]
fun mk_nuprl_bag_null_term                     bag   = mk_nuprl_simple_term "bag-null"                      [bag]
fun mk_nuprl_bag_only_term                     bag   = mk_nuprl_simple_term "bag-only"                      [bag]
fun mk_nuprl_bag_size_term                     bag   = mk_nuprl_simple_term "bag-size"                      [bag]
fun mk_nuprl_evalall_term                      term  = mk_nuprl_simple_term "evalall"                       [term]
fun mk_nuprl_once_class_program_term           term  = mk_nuprl_simple_term "once-class-program"            [term]
fun mk_nuprl_return_loc_bag_class_program_term term  = mk_nuprl_simple_term "return-loc-bag-class-program"  [term]
fun mk_nuprl_return_loc_bag_class_term         term  = mk_nuprl_simple_term "return-loc-bag-class"          [term]
fun mk_nuprl_on_loc_class_program_term         term  = mk_nuprl_simple_term "on-loc-class-program"          [term]

(* 2 arguments *)
fun mk_nuprl_class_at_term               class  locs   = mk_nuprl_simple_term "class-at"               [class,  locs]
fun mk_nuprl_base_locs_headers_term      term1  term2  = mk_nuprl_simple_term "base-locs-headers"      [term1,  term2]
fun mk_nuprl_general_base_class_term     term1  term2  = mk_nuprl_simple_term "general-base-class"     [term1,  term2]
fun mk_nuprl_base_headers_msg_val_term   term1  term2  = mk_nuprl_simple_term "base-headers-msg-val"   [term1,  term2]
fun mk_nuprl_concat_term                 list1  list2  = mk_nuprl_simple_term "append"                 [list1,  list2]
fun mk_nuprl_select_term                 ind    list   = mk_nuprl_simple_term "select"                 [ind,    list]
fun mk_nuprl_parallel_class_term         class1 class2 = mk_nuprl_simple_term "parallel-class"         [class1, class2]
fun mk_nuprl_until_class_term            class1 class2 = mk_nuprl_simple_term "until-class"            [class1, class2]
fun mk_nuprl_primed_class_opt_term       class  bag    = mk_nuprl_simple_term "primed-class-opt"       [class,  bag]
fun mk_nuprl_class_opt_term              class  bag    = mk_nuprl_simple_term "class-opt"              [class,  bag]
fun mk_nuprl_class_opt_class_term        class1 class2 = mk_nuprl_simple_term "class-opt-class"        [class1, class2]
fun mk_nuprl_base_prc_term               name   typ    = mk_nuprl_simple_term "base-prc"               [name,   typ]
fun mk_nuprl_once_prc_term               typ    class  = mk_nuprl_simple_term "once-prc"               [typ,    class]
fun mk_nuprl_send_once_loc_prc_term      typ    bag    = mk_nuprl_simple_term "send-once-loc-prc"      [typ,    bag]
fun mk_nuprl_on_loc_prc_term             typ    fX     = mk_nuprl_simple_term "on-loc-prc"             [typ,    fX]
fun mk_nuprl_but_first_prc_term          typ    class  = mk_nuprl_simple_term "but-first-prc"          [typ,    class]
fun mk_nuprl_skip_first_prc_term         typ    class  = mk_nuprl_simple_term "skip-first-prc"         [typ,    class]
fun mk_nuprl_prior_prc_term              typ    class  = mk_nuprl_simple_term "prior-prc"              [typ,    class]
fun mk_nuprl_or_term                     term1  term2  = mk_nuprl_simple_term "or"                     [term1,  term2]
fun mk_nuprl_and_term                    term1  term2  = mk_nuprl_simple_term "and"                    [term1,  term2]
fun mk_nuprl_rec_bind_class_term         X      Y      = mk_nuprl_simple_term "rec-bind-class"         [X,      Y]
fun mk_nuprl_member_term                 term1  term2  = mk_nuprl_simple_term "member"                 [term1,  term2]
fun mk_nuprl_eq_atom_term                nt1    nt2    = mk_nuprl_simple_term "eq_atom"                [nt1,    nt2]
fun mk_nuprl_eq_bool_term                nt1    nt2    = mk_nuprl_simple_term "eq_bool"                [nt1,    nt2]
fun mk_nuprl_eq_int_term                 nt1    nt2    = mk_nuprl_simple_term "eq_int"                 [nt1,    nt2]
fun mk_nuprl_eq_id_term                  nt1    nt2    = mk_nuprl_simple_term "eq_id"                  [nt1,    nt2]
fun mk_nuprl_eq_loc_term                 nt1    nt2    = mk_nuprl_simple_term "eq_id"                  [nt1,    nt2]
fun mk_nuprl_bor_term                    term1  term2  = mk_nuprl_simple_term "bor"                    [term1,  term2]
fun mk_nuprl_band_term                   term1  term2  = mk_nuprl_simple_term "band"                   [term1,  term2]
fun mk_nuprl_iff_term                    term1  term2  = mk_nuprl_simple_term "iff"                    [term1,  term2]
fun mk_nuprl_uiff_term                   term1  term2  = mk_nuprl_simple_term "uiff"                   [term1,  term2]
fun mk_nuprl_implies_term                term1  term2  = mk_nuprl_simple_term "implies"                [term1,  term2]
fun mk_nuprl_uimplies_term               term1  term2  = mk_nuprl_simple_term "uimplies"               [term1,  term2]
fun mk_nuprl_proddeq_term                term1  term2  = mk_nuprl_simple_term "proddeq"                [term1,  term2]
fun mk_nuprl_sumdeq_term                 term1  term2  = mk_nuprl_simple_term "sumdeq"                 [term1,  term2]
fun mk_nuprl_add_term                    term1  term2  = mk_nuprl_simple_term "add"                    [term1,  term2]
fun mk_nuprl_subtract_term               term1  term2  = mk_nuprl_simple_term "subtract"               [term1,  term2]
fun mk_nuprl_multiply_term               term1  term2  = mk_nuprl_simple_term "multiply"               [term1,  term2]
fun mk_nuprl_remainder_term              term1  term2  = mk_nuprl_simple_term "remainder"              [term1,  term2]
fun mk_nuprl_divide_term                 term1  term2  = mk_nuprl_simple_term "divide"                 [term1,  term2]
fun mk_nuprl_lt_int_term                 term1  term2  = mk_nuprl_simple_term "lt_int"                 [term1,  term2]
fun mk_nuprl_le_int_term                 term1  term2  = mk_nuprl_simple_term "le_int"                 [term1,  term2]
fun mk_nuprl_less_than_term              term1  term2  = mk_nuprl_simple_term "less_than"              [term1,  term2]
fun mk_nuprl_le_term                     term1  term2  = mk_nuprl_simple_term "le"                     [term1,  term2]
fun mk_nuprl_es_pred_term                es     e      = mk_nuprl_simple_term "es-pred"                [es,     e]
fun mk_nuprl_union_term                  term1  term2  = mk_nuprl_simple_term "union"                  [term1,  term2]
fun mk_nuprl_msg_has_type_term           term1  term2  = mk_nuprl_simple_term "msg-has-type"           [term1,  term2]
fun mk_nuprl_name_eq_term                term1  term2  = mk_nuprl_simple_term "name_eq"                [term1,  term2]
fun mk_nuprl_icons_cons_term             term1  term2  = mk_nuprl_simple_term "!cons"                  [term1,  term2]
fun mk_nuprl_itext_cons_term             term1  term2  = mk_nuprl_simple_term "!text_cons"             [term1,  term2]
fun mk_nuprl_iclosure_term               term   env    = mk_nuprl_simple_term "!closure"               [term,   env]
fun mk_nuprl_iinclude_properties_term    prop   term   = mk_nuprl_simple_term "!include_properties"    [prop,   term]
fun mk_nuprl_cons_bag_term               head   tail   = mk_nuprl_simple_term "cons-bag"               [head,   tail]
fun mk_nuprl_bag_map_term                f      bag    = mk_nuprl_simple_term "bag-map"                [f,      bag]
fun mk_nuprl_eq_term_term                term1  term2  = mk_nuprl_simple_term "eq_term"                [term1,  term2]
fun mk_nuprl_class_at_program_term       proc   locs   = mk_nuprl_simple_term "class-at-program"       [proc,   locs]
fun mk_nuprl_base_class_program_term     hdr    typ    = mk_nuprl_simple_term "base-class-program"     [hdr,    typ]
fun mk_nuprl_parallel_class_program_term term1  term2  = mk_nuprl_simple_term "parallel-class-program" [term1,  term2]
fun mk_nuprl_bind_class_program_term     term1  term2  = mk_nuprl_simple_term "bind-class-program"     [term1,  term2]
fun mk_nuprl_until_class_program_term    term1  term2  = mk_nuprl_simple_term "until-class-program"    [term1,  term2]
fun mk_nuprl_eclass0_term                term1  term2  = mk_nuprl_simple_term "eclass0"                [term1,  term2]
fun mk_nuprl_eclass0_program_term        term1  term2  = mk_nuprl_simple_term "eclass0-program"        [term1,  term2]
fun mk_nuprl_eclass1_term                term1  term2  = mk_nuprl_simple_term "eclass1"                [term1,  term2]
fun mk_nuprl_eclass1_program_term        term1  term2  = mk_nuprl_simple_term "eclass1-program"        [term1,  term2]
fun mk_nuprl_eclass2_term                term1  term2  = mk_nuprl_simple_term "eclass2"                [term1,  term2]
fun mk_nuprl_eclass2_program_term        term1  term2  = mk_nuprl_simple_term "eclass2-program"        [term1,  term2]
fun mk_nuprl_eclass3_term                term1  term2  = mk_nuprl_simple_term "eclass3"                [term1,  term2]
fun mk_nuprl_eclass3_program_term        term1  term2  = mk_nuprl_simple_term "eclass3-program"        [term1,  term2]

(* 3 arguments *)
fun mk_nuprl_base_headers_msg_val_loc_term term1 term2 term3 = mk_nuprl_simple_term "base-headers-msg-val-loc" [term1, term2, term3]
fun mk_nuprl_base_at_prc_term              name  typ   locs  = mk_nuprl_simple_term "base-at-prc"              [name,  typ,   locs]
fun mk_nuprl_until_prc_term                typ   X1    X2    = mk_nuprl_simple_term "until-prc"                [typ,   X1,    X2]
fun mk_nuprl_at_prc_term                   typ   X     locs  = mk_nuprl_simple_term "at-prc"                   [typ,   X,     locs]
fun mk_nuprl_parallel_prc_term             typ   X     Y     = mk_nuprl_simple_term "parallel-prc"             [typ,   X,     Y]
fun mk_nuprl_prior_init_prc_term           typ   X     init  = mk_nuprl_simple_term "prior-init-prc"           [typ,   X,     init]
fun mk_nuprl_ite_term                      term1 term2 term3 = mk_nuprl_simple_term "ifthenelse"               [term1, term2, term3]
fun mk_nuprl_equal_term                    term1 term2 ty    = mk_nuprl_simple_term "equal"                    [ty,    term1, term2]
fun mk_nuprl_reduce_term                   term1 term2 term3 = mk_nuprl_simple_term "reduce"                   [term1, term2, term3]
fun mk_nuprl_es_eq_E_term                  es    term1 term2 = mk_nuprl_simple_term "es-eq-E"                  [es,    term1, term2]
fun mk_nuprl_es_causl_term                 es    term1 term2 = mk_nuprl_simple_term "es-causl"                 [es,    term1, term2]
fun mk_nuprl_es_functional_class_term      es    typ   cls   = mk_nuprl_simple_term "es-functional-class"      [es,    typ,   cls]
fun mk_nuprl_classfun_term                 es    cls   e     = mk_nuprl_simple_term "classfun"                 [es,    cls,   e]
fun mk_nuprl_eq_bag_term                   deq   term1 term2 = mk_nuprl_simple_term "bag-eq"                   [deq,   term1, term2]
fun mk_nuprl_state_class1_term             init  tr    term  = mk_nuprl_simple_term "state-class1"             [init,  tr,    term]
fun mk_nuprl_state_class1_program_term     init  tr    term  = mk_nuprl_simple_term "state-class1-program"     [init,  tr,    term]
fun mk_nuprl_memory_class1_term            init  tr    term  = mk_nuprl_simple_term "memory-class1"            [init,  tr,    term]
fun mk_nuprl_memory_class1_program_term    init  tr    term  = mk_nuprl_simple_term "memory-class1-program"    [init,  tr,    term]
fun mk_nuprl_make_msg_term                 hdr   typ   v     = mk_nuprl_simple_term "make-Msg"                 [hdr,   typ,   v]
fun mk_nuprl_es_locl_term                  es    e1    e2    = mk_nuprl_simple_term "es-locl"                  [es,    e1,    e2]
fun mk_nuprl_es_le_term                    es    e1    e2    = mk_nuprl_simple_term "es-le"                    [es,    e1,    e2]
fun mk_nuprl_state1_term                   init  tr    term  = mk_nuprl_simple_term "State1"                   [init,  tr,    term]
fun mk_nuprl_memory1_term                  init  tr    term  = mk_nuprl_simple_term "Memory1"                  [init,  tr,    term]

(* 4 arguments *)
fun mk_nuprl_product_deq_term                 typ1 typ2 deq1 deq2 = mk_nuprl_simple_term "product-deq"                 [typ1, typ2, deq1, deq2]
fun mk_nuprl_union_deq_term                   typ1 typ2 deq1 deq2 = mk_nuprl_simple_term "union-deq"                   [typ1, typ2, deq1, deq2]
fun mk_nuprl_bind_prc_term                    typA typB X    Y    = mk_nuprl_simple_term "bind-prc"                    [typA, typB, X,    Y]
fun mk_nuprl_loc_comb1_prc_term               typ  n    Xprs F    = mk_nuprl_simple_term "loc-comb1-prc"               [typ,  n,    Xprs, F]
fun mk_nuprl_rec_combined_loc_class1_prc_term typ  n    Xprs F    = mk_nuprl_simple_term "rec-combined-loc-class1-prc" [typ,  n,    Xprs, F]
fun mk_nuprl_state1_prc_term                  typ  init tr   term = mk_nuprl_simple_term "State1-prc"                  [typ,  init, tr,   term]
fun mk_nuprl_memory1_prc_term                 typ  init tr   term = mk_nuprl_simple_term "Memory1-prc"                 [typ,  init, tr,   term]

(* 5 arguments *)
fun mk_nuprl_classrel_term              es   T   X     e   v     = mk_nuprl_simple_term "classrel"              [es,   T,   X,     e,   v]
fun mk_nuprl_rec_bind_prc_term          A    B   X     Y   arg   = mk_nuprl_simple_term "rec-bind-prc"          [A,    B,   X,     Y,   arg]
fun mk_nuprl_state_class2_term          init tr1 term1 tr2 term2 = mk_nuprl_simple_term "state-class2"          [init, tr1, term1, tr2, term2]
fun mk_nuprl_state_class2_program_term  init tr1 term1 tr2 term2 = mk_nuprl_simple_term "state-class2-program"  [init, tr1, term1, tr2, term2]
fun mk_nuprl_memory_class2_term         init tr1 term1 tr2 term2 = mk_nuprl_simple_term "memory-class2"         [init, tr1, term1, tr2, term2]
fun mk_nuprl_memory_class2_program_term init tr1 term1 tr2 term2 = mk_nuprl_simple_term "memory-class2-program" [init, tr1, term1, tr2, term2]
fun mk_nuprl_state2_term                init tr1 term1 tr2 term2 = mk_nuprl_simple_term "State2"                [init, tr1, term1, tr2, term2]
fun mk_nuprl_memory2_term               init tr1 term1 tr2 term2 = mk_nuprl_simple_term "Memory2"               [init, tr1, term1, tr2, term2]

(* 6 arguments *)
fun mk_nuprl_rec_comb_prc_term typ n Xprs init F strict = mk_nuprl_simple_term "rec-comb-prc" [typ, n, Xprs, init, F, strict]

(* 7 arguments *)
fun mk_nuprl_state_class3_term          init tr1 term1 tr2 term2 tr3 term3 = mk_nuprl_simple_term "state-class3"          [init, tr1, term1, tr2, term2, tr3, term3]
fun mk_nuprl_state_class3_program_term  init tr1 term1 tr2 term2 tr3 term3 = mk_nuprl_simple_term "state-class3-program"  [init, tr1, term1, tr2, term2, tr3, term3]
fun mk_nuprl_memory_class3_term         init tr1 term1 tr2 term2 tr3 term3 = mk_nuprl_simple_term "memory-class3"         [init, tr1, term1, tr2, term2, tr3, term3]
fun mk_nuprl_memory_class3_program_term init tr1 term1 tr2 term2 tr3 term3 = mk_nuprl_simple_term "memory-class3-program" [init, tr1, term1, tr2, term2, tr3, term3]
fun mk_nuprl_state3_term                init tr1 term1 tr2 term2 tr3 term3 = mk_nuprl_simple_term "State3"                [init, tr1, term1, tr2, term2, tr3, term3]
fun mk_nuprl_memory3_term               init tr1 term1 tr2 term2 tr3 term3 = mk_nuprl_simple_term "Memory3"               [init, tr1, term1, tr2, term2, tr3, term3]

(* 8 arguments *)
fun mk_nuprl_state2_prc_term  typ1 typ2 typ init tr1 term1 tr2 term2 = mk_nuprl_simple_term "State2-prc"  [typ1, typ2, typ, init, tr1, term1, tr2, term2]
fun mk_nuprl_memory2_prc_term typ1 typ2 typ init tr1 term1 tr2 term2 = mk_nuprl_simple_term "Memory2-prc" [typ1, typ2, typ, init, tr1, term1, tr2, term2]

(* 9 arguments *)
fun mk_nuprl_state_class4_term          init tr1 term1 tr2 term2 tr3 term3 tr4 term4 = mk_nuprl_simple_term "state-class4"          [init, tr1, term1, tr2, term2, tr3, term3, tr4, term4]
fun mk_nuprl_state_class4_program_term  init tr1 term1 tr2 term2 tr3 term3 tr4 term4 = mk_nuprl_simple_term "state-class4-program"  [init, tr1, term1, tr2, term2, tr3, term3, tr4, term4]
fun mk_nuprl_memory_class4_term         init tr1 term1 tr2 term2 tr3 term3 tr4 term4 = mk_nuprl_simple_term "memory-class4"         [init, tr1, term1, tr2, term2, tr3, term3, tr4, term4]
fun mk_nuprl_memory_class4_program_term init tr1 term1 tr2 term2 tr3 term3 tr4 term4 = mk_nuprl_simple_term "memory-class4-program" [init, tr1, term1, tr2, term2, tr3, term3, tr4, term4]
fun mk_nuprl_state4_term                init tr1 term1 tr2 term2 tr3 term3 tr4 term4 = mk_nuprl_simple_term "State4"                [init, tr1, term1, tr2, term2, tr3, term3, tr4, term4]
fun mk_nuprl_memory4_term               init tr1 term1 tr2 term2 tr3 term3 tr4 term4 = mk_nuprl_simple_term "Memory4"               [init, tr1, term1, tr2, term2, tr3, term3, tr4, term4]

(* 11 arguments *)
fun mk_nuprl_state3_prc_term  typ1 typ2 typ3 typ init tr1 term1 tr2 term2 tr3 term3 = mk_nuprl_simple_term "State3-prc"  [typ1, typ2, typ3, typ, init, tr1, term1, tr2, term2, tr3, term3]
fun mk_nuprl_memory3_prc_term typ1 typ2 typ3 typ init tr1 term1 tr2 term2 tr3 term3 = mk_nuprl_simple_term "Memory3-prc" [typ1, typ2, typ3, typ, init, tr1, term1, tr2, term2, tr3, term3]

(* 14 arguments *)
fun mk_nuprl_state4_prc_term  typ1 typ2 typ3 typ4 typ init tr1 term1 tr2 term2 tr3 term3 tr4 term4 = mk_nuprl_simple_term "State4-prc"  [typ1, typ2, typ3, typ4, typ, init, tr1, term1, tr2, term2, tr3, term3, tr4, term4]
fun mk_nuprl_memory4_prc_term typ1 typ2 typ3 typ4 typ init tr1 term1 tr2 term2 tr3 term3 tr4 term4 = mk_nuprl_simple_term "Memory4-prc" [typ1, typ2, typ3, typ4, typ, init, tr1, term1, tr2, term2, tr3, term3, tr4, term4]

fun mk_nuprl_eq_prod_term deq1 deq2 nt1 nt2 =
    let	val bdeq = mk_nuprl_proddeq_term deq1 deq2
	val app1 = mk_nuprl_apply_term bdeq nt1
	val app2 = mk_nuprl_apply_term app1 nt2
    in app2
    end

fun mk_nuprl_eq_union_term deq1 deq2 nt1 nt2 =
    let	val bdeq = mk_nuprl_sumdeq_term deq1 deq2
	val app1 = mk_nuprl_apply_term bdeq nt1
	val app2 = mk_nuprl_apply_term app1 nt2
    in app2
    end

fun mk_nuprl_eq_list_term deq nt1 nt2 =
    let	val bdeq = mk_nuprl_list_deq_term deq
	val app1 = mk_nuprl_apply_term bdeq nt1
	val app2 = mk_nuprl_apply_term app1 nt2
    in app2
    end

fun mk_nuprl_itext_list_term [] = mk_nuprl_itext_nil_term
  | mk_nuprl_itext_list_term (x :: xs) =
    mk_nuprl_itext_cons_term x (mk_nuprl_itext_list_term xs)

fun mk_nuprl_all_term term1 (var, term2) =
    mk_nuprl_term ("all", []) [([], term1), ([var], term2)]

fun mk_nuprl_uall_term term1 (var, term2) =
    mk_nuprl_term ("uall", []) [([], term1), ([var], term2)]

fun mk_nuprl_exists_term term1 (var, term2) =
    mk_nuprl_term ("exists", []) [([], term1), ([var], term2)]

fun mk_nuprl_isect_term term1 (var, term2) =
    mk_nuprl_term ("isect", []) [([], term1), ([var], term2)]

fun mk_nuprl_ind_term i (x, rd, downcase) basecase (y, ru, upcase) =
    mk_nuprl_term ("ind", []) [([], i), ([x, rd], downcase), ([], basecase), ([y, ru], upcase)]

fun mk_nuprl_ind_ref_term i (x, rd, downcase) basecase (y, ru, upcase) =
    mk_nuprl_ref_term ("ind", []) [([], mk_rterm i), ([x, rd], downcase), ([], basecase), ([y, ru], upcase)]

fun mk_nuprl_rec_ind_term arg (f, x, B) =
    mk_nuprl_term ("rec_ind", []) [([], arg), ([f, x], B)]

fun mk_nuprl_rec_ind_ref_term arg (f, x, B) =
    mk_nuprl_ref_term ("rec_ind", []) [([], mk_rterm arg), ([f, x], B)]

fun mk_nuprl_finite_list_term list =
    foldr (fn (elt, list) => mk_nuprl_cons_term elt list)
	  (mk_nuprl_nil_term ())
	  list

fun mk_nuprl_iabstraction_term t1 t2 =
    mk_nuprl_simple_term "!abstraction" [mk_nuprl_condition_cons_term, t1, t2]

fun mk_nuprl_itheorem_term name term =
    mk_nuprl_term ("!theorem", [mk_nuprl_token_parameter name]) [([], term)]

fun mk_nuprl_iupdate_term name term =
    mk_nuprl_term ("!update", [mk_nuprl_token_parameter name]) [([], term)]

fun mk_nuprl_iinsert_object_term term =
    mk_nuprl_simple_term "!insert_object_id_in_operator" [term]

fun mk_nuprl_iinsert_object_p_term name term =
    mk_nuprl_term ("!insert_object_id_in_operator", [mk_nuprl_token_parameter name, mk_nuprl_natural_parameter 0]) [([], term)]

fun mk_nuprl_iproperty_term name value =
    mk_nuprl_term ("!property", [mk_nuprl_token_parameter name]) [([], value)]

fun mk_nuprl_istring_term string =
    mk_nuprl_term ("!string", [mk_nuprl_string_parameter string]) []

fun mk_nuprl_ibool_term bool =
    mk_nuprl_term ("!bool", [mk_nuprl_bool_parameter bool]) []

fun mk_nuprl_ilist_term [] = mk_nuprl_icons_nil_term
  | mk_nuprl_ilist_term (term :: terms) = mk_nuprl_icons_cons_term term (mk_nuprl_ilist_term terms)

fun mk_nuprl_itext_term str =
    mk_nuprl_term  ("!text", [mk_nuprl_string_parameter str]) []

fun mk_nuprl_iwf_lemmas_term wf_lemmas = mk_nuprl_simple_term "!wf" wf_lemmas

fun mk_nuprl_icomment_term name comment =
    mk_nuprl_term ("!comment", [mk_nuprl_string_parameter name]) [([], comment)]

fun mk_nuprl_cons_env_term v pair env =
    mk_nuprl_term ("env", []) [([v], pair), ([], env)]

fun mk_nuprl_callbyvalue_term arg (x, B) =
    mk_nuprl_term ("callbyvalue", []) [([], arg), ([x], B)]

fun mk_nuprl_callbyvalueall_term arg (x, B) =
    mk_nuprl_term ("callbyvalueall", []) [([], arg), ([x], B)]

(*fun mk_nuprl_mlnk_term term = mk_nuprl_simple_term "mlnk" [term]
fun mk_nuprl_mtag_term term = mk_nuprl_simple_term "mtag" [term]
fun mk_nuprl_mval_term term = mk_nuprl_simple_term "mval" [term]*)

fun build_primitive_value term params =
    let val opid = opid_of_term term
    in if List.exists (fn x => x = opid) ["inl", "inr", "pair", "cons"]
       then mk_nuprl_simple_term opid params
       else term
    end

fun toDeq term =
    if is_nuprl_int_term term
    then mk_nuprl_int_deq_term
    else if is_nuprl_bool_term term
    then mk_nuprl_bool_deq_term
    else if is_nuprl_unit_term term
    then mk_nuprl_unit_deq_term
    else if is_nuprl_loc_term term
    then mk_nuprl_loc_deq_term
    else if is_nuprl_atom_term term
    then mk_nuprl_atom_deq_term
    else if is_nuprl_list_term term
    then mk_nuprl_list_deq_term (toDeq (dest_type_list term))
    else if is_nuprl_product_term term
    then let val (t1, t2) = dest_product term
	 in mk_nuprl_proddeq_term (toDeq t1) (toDeq t2)
	 end
    else raise Fail "toDeq"


fun do_primitive_int_op opid value1 value2 =
    let (*val _  = print ("[doing primitive operator on int]\n")
	val _  = print ("[" ^ opid_of_term value1 ^ "]\n")
	val _  = print ("[" ^ opid_of_term value2 ^ "]\n")
	val _  = print (toStringTerm value1 ^ "\n" ^ toStringTerm value2 ^ "\n")*)
	val n1 = dest_integer 2 value1
	val n2 = dest_integer 3 value2
	val n  = case opid of
		     "add"       => II.+   (n1, n2)
		   | "subtract"  => II.-   (n1, n2)
		   | "multiply"  => II.*   (n1, n2)
		   | "divide"    => II.div (n1, n2)
		   | "remainder" => II.rem (n1, n2)
		   | _           => raise Fail "wrong term"
    in mk_nuprl_integer_term n
    end

fun do_primitive_wait value exp =
    let val n = dest_integer 4 value
	val _ = print ("[---------sleeping for " ^ II.toString n ^ "s---------]\n")
	val _ = OS.Process.sleep (Time.fromSeconds (II.toLarge n))
    in exp
    end

fun do_primitive_minus value =
    let val n = dest_integer 4 value
    in mk_nuprl_integer_term (~n)
    end

fun do_primitive_cmp cmp value1 value2 =
    if cmp = "int_eq" orelse cmp = "less"
    then let val n1 = dest_integer 5 value1
	     val n2 = dest_integer 6 value2
	 in if cmp = "less"
	    then II.< (n1, n2)
	    else n1 = n2
	 end
    else raise Fail "unknown primitive comparison"

fun is_zero term = II.compare (dest_integer 7 term, 0)

fun inc_integer term = mk_nuprl_integer_term (II.+ (dest_integer 8 term, 1))
fun dec_integer term = mk_nuprl_integer_term (II.- (dest_integer 9 term, 1))

fun compare_atomn n value1 value2 =
    let val op_id1 = opid_of_term value1
	val op_id2 = opid_of_term value2
    in case (parameters_of_term value1,
	     parameters_of_term value2) of
	   ([param1], [param2]) =>
	   (* NOTE: both values should only have one parameter *)
	   let val ptype = type_of_parameter param1
	   in if op_id1 = "token"
		 andalso op_id1 = op_id2
		 (* NOTE: both values have to be tokens *)
		 andalso ptype = type_of_parameter param2
		 (* NOTE: both value have to have the the same kind of parameters *)
		 andalso (case n of (* NOTE: what are these: *)
			      0 => (ptype = "token" orelse ptype = "t")
			    | 1 => ptype = "ut1"
			    | 2 => ptype = "ut2"
			    | _ => false)
	      then equal_parameters param1 param2
	      else raise Fail ("compare_atomn - "
			       ^ op_id1 ^ " "
			       ^ opid_of_term value2 ^ " "
			       ^ ptype ^ " "
			       ^ type_of_parameter param2 ^ " "
			       ^ Int.toString n)
	   end
	 | (ps1, ps2) =>
	   raise Fail ("compare_atomn("
		       ^ op_id1 ^ ":"
		       ^ Int.toString (List.length ps1) ^ ","
		       ^ op_id2 ^ ":"
		       ^ Int.toString (List.length ps2) ^ ")")
    end

(* ------ FREE VARS and SUBSTITUTIONS ------ *)

fun remove_list vars lst =
    foldr (fn (var, vars) => VARS.delete (vars, var) handle _ => vars)
	  vars
	  lst

fun new_free_var frees var =
    let val var' = var ^ "'"
    in if VARS.member (frees, var')
       then new_free_var frees var'
       else var'
    end

datatype ran_sub = FO of nuprl_term
		 | SO of variable list * nuprl_term

val isin_var_list = isin_str

fun filter_sub vars = SUB.filteri (fn (v, _) => not (isin_var_list v vars))

fun filter_ren vars = SUB.filteri (fn (v, _) => not (isin_var_list v vars))

fun insert_sub sub (v, t) = SUB.insert (sub, v, FO t)

fun insert_ren ren (v, t) = SUB.insert (ren, v, t)

fun insert_list_sub sub list = foldr (fn (x, sub) => insert_sub sub x) sub list

fun insert_list_ren ren list = foldr (fn (x, ren) => insert_ren ren x) ren list

val empty_sub = SUB.empty : ran_sub SUB.map

val empty_ren = SUB.empty : variable SUB.map

val gen_sub = insert_list_sub empty_sub

val gen_ren = insert_list_ren empty_ren

fun apply_ren ren v =
    case SUB.find (ren, v) of
	NONE => v
      | SOME u => u

fun rename_operator (opid_tag, params) ren =
    let val params' =
	    map (fn (v, k) =>
		    case SUB.find (ren, v) of
			SOME v' => (v', k)
		      | NONE    => (v,  k))
		params
    in (opid_tag, params')
    end

fun domain (ENV m) =
    MAP.foldri (fn (i, _, lst) => i :: lst)
	       []
	       m

fun fo_subst_aux (sub, ren) (term as TERM (operator, bterms)) =
    if is_nuprl_variable_term term
    then let val (v, ts) = dest_so_variable term
	 in apply_sub (sub, ren) (v, ts) term
	 end
    else let val operator' = rename_operator operator ren
	     val bterms'   = map (fo_subst_bterm (sub, ren)) bterms
	 in TERM (operator', bterms')
	 end
  | fo_subst_aux (sub, ren) (term as CLO_TERM clos) =
    CLO_TERM (fo_subst_clos (sub, ren) clos)
  | fo_subst_aux (sub, ren) (term as VAR_TERM var) =
    apply_sub (sub, ren) (var, []) term
  | fo_subst_aux (sub, ren) (term as LAM_TERM (var, rterm)) =
    let val (vars, t) = fo_rename (sub, ren) ([var], rterm2term rterm)
    in case vars of
	   [v] => LAM_TERM (v, mk_rterm t)
	 | _   => raise Fail "fo_subst_aux:LAM_TERM"
    end
  | fo_subst_aux (sub, ren) (term as WAI_TERM (rterm1, rterm2)) =
    WAI_TERM (fo_subst_rterm (sub, ren) rterm1,
	      fo_subst_rterm (sub, ren) rterm2)
  | fo_subst_aux (sub, ren) (term as APP_TERM (rterm1, rterm2)) =
    APP_TERM (fo_subst_rterm (sub, ren) rterm1,
	      fo_subst_rterm (sub, ren) rterm2)
  | fo_subst_aux (sub, ren) (term as PAI_TERM (rterm1, rterm2)) =
    PAI_TERM (fo_subst_rterm (sub, ren) rterm1,
	      fo_subst_rterm (sub, ren) rterm2)
  | fo_subst_aux (sub, ren) (term as NIL_TERM) = term
  | fo_subst_aux (sub, ren) (term as CON_TERM (rterm1, rterm2)) =
    CON_TERM (fo_subst_rterm (sub, ren) rterm1,
	      fo_subst_rterm (sub, ren) rterm2)
  | fo_subst_aux (sub, ren) (term as NAT_TERM n) = term
  | fo_subst_aux (sub, ren) (term as INL_TERM rterm) = INL_TERM (fo_subst_rterm (sub, ren) rterm)
  | fo_subst_aux (sub, ren) (term as INR_TERM rterm) = INR_TERM (fo_subst_rterm (sub, ren) rterm)
  | fo_subst_aux (sub, ren) (term as FIX_TERM rterm) = FIX_TERM (fo_subst_rterm (sub, ren) rterm)
  | fo_subst_aux (sub, ren) (term as SPR_TERM (pair, var1, var2, rterm)) =
    let val p = fo_subst_rterm (sub, ren) pair
	val (vars, t) = fo_rename (sub, ren) ([var1, var2], rterm2term rterm)
    in case vars of
	   [v1,v2] => SPR_TERM (p, v1, v2, mk_rterm t)
	 | _ => raise Fail "fo_subst_aux:DEC_TERM"
    end
  | fo_subst_aux (sub, ren) (term as DEC_TERM (dec, var1, rterm1, var2, rterm2)) =
    let val d = fo_subst_rterm (sub, ren) dec
	val (vars1, t1) = fo_rename (sub, ren) ([var1], rterm2term rterm1)
	val (vars2, t2) = fo_rename (sub, ren) ([var2], rterm2term rterm2)
    in case (vars1, vars2) of
	   ([v1], [v2]) => DEC_TERM (d, v1, mk_rterm t1, v2, mk_rterm t2)
	 | _ => raise Fail "fo_subst_aux:DEC_TERM"
    end
  | fo_subst_aux (sub, ren) (term as LIN_TERM (lst, nilcase, x, xs, r, conscase)) =
    let val l = fo_subst_rterm (sub, ren) lst
	val n = fo_subst_rterm (sub, ren) nilcase
	val (vars, c) = fo_rename (sub, ren) ([x, xs, r], rterm2term conscase)
    in case vars of
	   [x, xs, r] => LIN_TERM (l, n, x, xs, r , mk_rterm c)
	 | _ => raise Fail "fo_subst_aux:LIN_TERM"
    end

and fo_subst_rterm (sub, ren) rterm =
    mk_rterm (fo_subst_aux (sub, ren) (rterm2term rterm))

and fo_subst_clos (sub, ren) (rterm, env) =
    let val term  = rterm2term rterm
	val dom   = domain env
	val sub'  = filter_sub dom sub
	val ren'  = filter_ren dom ren
	val term' = fo_subst_aux (sub', ren') term
	val env'  = fo_subst_env (sub', ren') env
    in (mk_rterm term', env')
    end

and fo_subst_env (sub, ren) (ENV m) =
    ENV (MAP.map (fo_subst_rterm (sub, ren)) m)

and fo_subst_bterm (sub, ren) (B_TERM (vars, term)) =
    let val (vars', term') = fo_rename (sub, ren) (vars, rterm2term term)
    in B_TERM (vars', mk_rterm term')
    end

and apply_sub (sub, ren) (v, ts) t =
    case SUB.find (sub, v) of
	NONE => t
      | SOME (FO t') => t'
      | SOME (SO (vars, t')) =>
	let val lst =
		map (fn (v1, t2) => (v1, fo_subst_aux (sub, empty_ren) t2))
		    (ListPair.zipEq (vars, ts))
	in fo_subst_aux (gen_sub lst, empty_ren) t'
	end handle _ => raise Fail "apply_sub"

(* renames the variables in vars (and term) that occur in the
 * range of sub, and also remove the part of sub such that its
 * domain is in vars. *)
and fo_rename (sub, ren) (vars, term) =
    let val sub' = filter_sub vars sub
	(* freesSub is the free variable list of sub's range.
	 * In the (SO (vars, t)) case, we only need to get the free variables
	 * in t that are not in vars. *)
	val freesSub =
	    SUB.foldr
		(fn (SO (vs, t), vars) =>
		    VARS.union (vars, fo_free_vars (VARS.fromList vs) t)
		  | (FO t, vars) =>
		    VARS.union (vars, free_vars t))
		empty_vars
		sub'
	val freesTerm = free_vars term
	val getNewFreeVar = new_free_var (VARS.union (freesSub, freesTerm))
	val (vars', sub'') =
	    List.foldr (fn (var, (vars, sub)) =>
			   if VARS.member (freesSub, var)
			   (* then the bound variable would capture one of
			    * the free variables of the substitution. *)
			   then let val var' = getNewFreeVar var
				    val tvar' = mk_nuprl_variable_term var'
				in (var' :: vars, insert_sub sub (var, tvar'))
				end
			   else (var :: vars, sub))
		       ([], sub')
		       vars
    in (vars', fo_subst_aux (sub'', ren) term)
    end

fun fo_subst list term = fo_subst_aux (gen_sub list, empty_ren) term

fun correct_lhs (vars, rterm) =
    let val term = rterm2term rterm
    in if List.null vars
       then if is_nuprl_variable_term term
	    then dest_variable term
	    else raise Fail "correct_lhs"
       else let val (v, ts) = dest_so_variable term
	    in if List.all
		      (fn (v, t) =>
			  is_nuprl_variable_term t
			  andalso
			  v = dest_variable t)
		      (ListPair.zipEq (vars, ts))
	       then v
	       else raise Fail "correct_lhs"
	    end handle _ => raise Fail "correct_lhs"
    end

fun matching term1 (*term*) term2 (*lhs*) =
    let val ((opid1, params1), bterms1) = dest_term term1
	val ((opid2, params2), bterms2) = dest_term term2
	val (sub_subterms, is_fo_sub) =
	    if opid1 = opid2 andalso length bterms1 = length bterms2
	    then foldr (fn (((vs1, t1), bterm2), (sub, is_fo_sub)) =>
			   let val b = is_fo_sub andalso null vs1
			       val v = correct_lhs bterm2
			   in (SUB.insert (sub, v, SO (vs1, rterm2term t1)), b)
			   end)
		       (empty_sub, true)
		       (ListPair.zip (bterms1, bterms2))
	    else raise Fail "matching"
	val (ren_params, is_em_ren) =
	    if length params1 = length params2
	    then foldr (fn (((v1, k1), (v2, k2)), (ren, is_em_ren)) =>
			   if eq_kinds (k1, k2)
			      andalso
			      not (is_abstract_metavar v1)
			   then if is_abstract_metavar v2
				then (insert_ren ren (v2, v1), false)
				else if v1 = v2
				then (ren, is_em_ren)
				else raise Fail "matching"
			   else raise Fail "matching")
		       (empty_ren, true)
		       (ListPair.zip (params1, params2))
	    else raise Fail "matching"
    in ((sub_subterms, is_fo_sub), (ren_params, is_em_ren))
    end


(* -- ... -- *)

fun replace_prog (id, p) (TERM (operator as ((opid, tag), params), bterms)) =
    if id = opid
    then p
    else let val bterms' =
		 map (fn (B_TERM (vars, term)) =>
			 B_TERM (vars, mk_rterm (replace_prog (id, p) (rterm2term term))))
		     bterms
	 in TERM (operator, bterms')
	 end
  | replace_prog (id, p) (term as VAR_TERM var) = term
  | replace_prog (id, p) (term as LAM_TERM (var, rterm)) =
    LAM_TERM (var, mk_rterm (replace_prog (id, p) (rterm2term rterm)))
  | replace_prog (id, p) (term as WAI_TERM (rterm1, rterm2)) =
    WAI_TERM (mk_rterm (replace_prog (id, p) (rterm2term rterm1)),
		 mk_rterm (replace_prog (id, p) (rterm2term rterm2)))
  | replace_prog (id, p) (term as APP_TERM (rterm1, rterm2)) =
    APP_TERM (mk_rterm (replace_prog (id, p) (rterm2term rterm1)),
		 mk_rterm (replace_prog (id, p) (rterm2term rterm2)))
  | replace_prog (id, p) (term as PAI_TERM (rterm1, rterm2)) =
    PAI_TERM (mk_rterm (replace_prog (id, p) (rterm2term rterm1)),
		 mk_rterm (replace_prog (id, p) (rterm2term rterm2)))
  | replace_prog (id, p) (term as NIL_TERM) = term
  | replace_prog (id, p) (term as CON_TERM (rterm1, rterm2)) =
    CON_TERM (mk_rterm (replace_prog (id, p) (rterm2term rterm1)),
		 mk_rterm (replace_prog (id, p) (rterm2term rterm2)))
  | replace_prog (id, p) (term as (NAT_TERM n)) = term
  | replace_prog (id, p) (term as INL_TERM rterm) =
    INL_TERM (mk_rterm (replace_prog (id, p) (rterm2term rterm)))
  | replace_prog (id, p) (term as INR_TERM rterm) =
    INR_TERM (mk_rterm (replace_prog (id, p) (rterm2term rterm)))
  | replace_prog (id, p) (term as FIX_TERM rterm) =
    FIX_TERM (mk_rterm (replace_prog (id, p) (rterm2term rterm)))
  | replace_prog (id, p) (term as SPR_TERM (pair, var1, var2, rterm)) =
    SPR_TERM (mk_rterm (replace_prog (id, p) (rterm2term pair)),
		 var1,
		 var2,
		 mk_rterm (replace_prog (id, p) (rterm2term rterm)))
  | replace_prog (id, p) (term as DEC_TERM (dec, var1, rterm1, var2, rterm2)) =
    DEC_TERM (mk_rterm (replace_prog (id, p) (rterm2term dec)),
		 var1,
		 mk_rterm (replace_prog (id, p) (rterm2term rterm1)),
		 var2,
		 mk_rterm (replace_prog (id, p) (rterm2term rterm2)))
  | replace_prog (id, p) (term as LIN_TERM (lst, nilcase, x, xs, r, conscase)) =
    LIN_TERM (mk_rterm (replace_prog (id, p) (rterm2term lst)),
		 mk_rterm (replace_prog (id, p) (rterm2term nilcase)),
		 x,
		 xs,
		 r,
		 mk_rterm (replace_prog (id, p) (rterm2term conscase)))
  | replace_prog (id, p) (CLO_TERM clos) = raise Fail "replace_prog:C_TERM"

fun replace_terms [] term = term
  | replace_terms (sub :: subs) term = replace_prog sub (replace_terms subs term)


(* -- ... -- *)

type timer = {real : Timer.real_timer,
	      cpu  : Timer.cpu_timer}

fun startTimer () = {real = Timer.startRealTimer (),
		     cpu  = Timer.startCPUTimer ()}

fun getTime (timer : timer) = Timer.checkRealTimer (#real timer)

fun getMilliTime timer = Time.toMilliseconds (getTime timer)

val time = ref (0 : IntInf.int)

fun print_lib_stats {abs, tof} =
    let val n1 = MAP.numItems (!abs)
	val n2 = MAP.numItems (!tof)
    in print ("[library size: "
	      ^ Int.toString n1
	      ^ " abstractions, "
	      ^ Int.toString n2
	      ^ " extracts"
	      ^ "]\n")
    end

fun is_in_lib {abs, tof} id =
    case MAP.find (!abs, id) of
	SOME _ => true
      | NONE => false

fun is_in_lib_tof_sub {abs, tof} id =
    List.exists
	(fn (x,_) => Substring.isSubstring id (Substring.full x))
	(MAP.listItemsi (!tof))

fun print_debug_opid opid str =
    if opid = "pv11_p1_Acceptor-program"
    then print ("[unfolding(" ^ opid ^ "):" ^ str ^ "]\n")
    else ()

fun unfold_ab clos term lhs rhs =
    let (*val _ = print (opid_of_term term ^ "\n")*)
	(*val _ = print_debug_opid (opid_of_term term) "matching IN"*)
	val ((sub_t, is_fo_sub), (ren_p, is_em_ren)) = matching term lhs
	(*val _ = print_debug_opid (opid_of_term term) "matching OUT"*)
	(*val _ = print (toStringTerm term ^ "\n")
	val _ = print (toStringTerm lhs  ^ "\n")*)
	(*val _ = print ("--\n")*)
    in if is_fo_sub andalso is_em_ren andalso Option.isSome clos
       then let val e = Option.valOf clos
		val env =
		    SUB.foldri (fn (v, FO t, env) =>
				   let val pair = mk_nuprl_pair_term t e
				   in mk_nuprl_cons_env_term v pair env
				   end
				 | (v, SO ([], t), env) =>
				   let val pair = mk_nuprl_pair_term t e
				   in mk_nuprl_cons_env_term v pair env
				   end
				 | _ => raise Fail "unfold:closure")
			       e
			       sub_t
	    in mk_nuprl_iclosure_term rhs env
	    end
       else (*let val s   = Int.toString (size rhs)
		val b1  = Bool.toString is_fo_sub
		val b2  = Bool.toString is_em_ren
		val b3  = Bool.toString (Option.isSome clos)
		val t   = startTimer ()
		val ret =*) fo_subst_aux (sub_t, ren_p) rhs
			    (*handle Fail str => raise Fail (str ^ ":unfold_ab:fo_subst_aux")*)
		(*val t1  = IntInf.toString (!time)
		val _   = time := !time + getMilliTime t
		val t2  = IntInf.toString (!time)
		val str = s ^ "-" ^ b1 ^ "-" ^ b2 ^ "-" ^ b3 ^ "-" ^ t1 ^ "-" ^ t2
		val _   = print ("[subst:" ^ str ^ "]\n")
	    in ret
	    end*)
    end

fun ct_unfold_ab clos term lhs rhs =
    let val ((sub_t, is_fo_sub), (ren_p, is_em_ren)) = matching term lhs
    in if is_fo_sub andalso is_em_ren andalso Option.isSome clos
       then let val env1 = Option.valOf clos
		val env2 =
		    SUB.foldri (fn (v, FO t, env) => add2env_one env (v,t,env1)
				 | (v, SO ([], t), env) => add2env_one env (v,t,env1)
				 | _ => raise Fail "unfold:closure")
			       env1
			       sub_t
	    in mk_rct (rhs, env2)
	    end
       else fo_subst_aux (sub_t, ren_p) rhs
    end

fun unfold_all (lib as {abs, tof}) (term as TERM (operator, bterms)) =
    (let val opid = opid_of_term term
	 (*val _    = print_debug_opid opid "trying to unfold"*)
	 val {id, sign, obid, lhs, rhs, wfs} = find_sign abs term
	     (*handle Fail str => (print ("--error--" ^ str ^ "\n"); raise Fail str)*)
	 (*val _    = print_debug_opid opid "found in lib"*)
	 val t    = unfold_ab NONE term (rterm2term lhs) (rterm2term rhs)
	     (*handle Fail str => (print_debug_opid opid ("cannot unfold(" ^ str ^ ")"); raise Fail str)
		  | err => (print_debug_opid opid "cannot unfold"; raise err)*)
	 (*val _    = print_debug_opid opid "unfolded"*)
     in unfold_all lib t
     end handle err =>
		if is_nuprl_term "TERMOF" term
		then case get_obid_parameters (parameters_of_term term) of
			 SOME obid =>
			 (case MAP.find (!tof, obid) of
			      SOME rhs => unfold_all lib (get rhs)
			    | NONE => raise Fail ("unfold_all:not_found:" ^ obid))
		       | NONE => raise Fail "unfold_all:wrong_format"
		else TERM (operator, map (unfold_bterm_all lib) bterms))
  | unfold_all lib (term as VAR_TERM _) = term
  | unfold_all lib (term as LAM_TERM (var, rterm)) =
    LAM_TERM (var, mk_rterm (unfold_all lib (rterm2term rterm)))
  | unfold_all lib (term as WAI_TERM (rterm1, rterm2)) =
    WAI_TERM (mk_rterm (unfold_all lib (rterm2term rterm1)),
	      mk_rterm (unfold_all lib (rterm2term rterm2)))
  | unfold_all lib (term as APP_TERM (rterm1, rterm2)) =
    APP_TERM (mk_rterm (unfold_all lib (rterm2term rterm1)),
	      mk_rterm (unfold_all lib (rterm2term rterm2)))
  | unfold_all lib (term as PAI_TERM (rterm1, rterm2)) =
    PAI_TERM (mk_rterm (unfold_all lib (rterm2term rterm1)),
	      mk_rterm (unfold_all lib (rterm2term rterm2)))
  | unfold_all lib (term as NIL_TERM) = term
  | unfold_all lib (term as CON_TERM (rterm1, rterm2)) =
    CON_TERM (mk_rterm (unfold_all lib (rterm2term rterm1)),
	      mk_rterm (unfold_all lib (rterm2term rterm2)))
  | unfold_all lib (term as NAT_TERM n) = term
  | unfold_all lib (term as INL_TERM rterm) =
    INL_TERM (mk_rterm (unfold_all lib (rterm2term rterm)))
  | unfold_all lib (term as INR_TERM rterm) =
    INR_TERM (mk_rterm (unfold_all lib (rterm2term rterm)))
  | unfold_all lib (term as FIX_TERM rterm) =
    FIX_TERM (mk_rterm (unfold_all lib (rterm2term rterm)))
  | unfold_all lib (term as SPR_TERM (pair, var1, var2, rterm)) =
    SPR_TERM (mk_rterm (unfold_all lib (rterm2term pair)),
	      var1,
	      var2,
	      mk_rterm (unfold_all lib (rterm2term rterm)))
  | unfold_all lib (term as DEC_TERM (dec, var1, rterm1, var2, rterm2)) =
    DEC_TERM (mk_rterm (unfold_all lib (rterm2term dec)),
	      var1,
	      mk_rterm (unfold_all lib (rterm2term rterm1)),
	      var2,
	      mk_rterm (unfold_all lib (rterm2term rterm2)))
  | unfold_all lib (term as LIN_TERM (lst, nilcase, x, xs, r, conscase)) =
    LIN_TERM (mk_rterm (unfold_all lib (rterm2term lst)),
	      mk_rterm (unfold_all lib (rterm2term nilcase)),
	      x,
	      xs,
	      r,
	      mk_rterm (unfold_all lib (rterm2term conscase)))
  | unfold_all lib (term as CLO_TERM _) = raise Fail "unfold_all:CLO_TERM"

and unfold_bterm_all lib (B_TERM (vars, term)) =
    B_TERM (vars, mk_rterm (unfold_all lib (rterm2term term)))

fun alpha_equal_bterms_aux ren (vars1, term1) (vars2, term2) =
    length vars1 = length vars2
    andalso
    let val list = ListPair.zip (vars1,vars2)
	val ren' = insert_list_ren ren list
    in alpha_equal_terms_aux ren' (rterm2term term1) (rterm2term term2)
    end

and alpha_equal_terms_aux ren term1 term2 =
    (is_nuprl_variable_term term1
     andalso
     is_nuprl_variable_term term2
     andalso
     let val v1 = dest_variable term1
	 val v2 = dest_variable term2
     in apply_ren ren v1 = v2
     end)
    orelse
    (let val (opr1,bterms1) = dest_term term1
	 val (opr2,bterms2) = dest_term term2
     in opr1 = opr2
	andalso
	length bterms1 = length bterms2
	andalso
	List.all (fn (bterm1, bterm2) => alpha_equal_bterms_aux ren bterm1 bterm2)
		 (ListPair.zip (bterms1, bterms2))
     end)

val alpha_equal_terms = alpha_equal_terms_aux empty_ren

fun mct (term, env) =
    if alpha_equal_terms env mk_nuprl_empty_env_term
    then term
    else mk_nuprl_iclosure_term term env

(* environments *)
fun dest_env env =
    case dest_term env of
	(opr,[([w], thunk),([], e)]) => (w, rterm2term thunk, rterm2term e)
      | _ => raise Fail "dest_env"

fun lookup_binding env var =
    let val (w,thunk,e) = dest_env env
    in if w = var
       then SOME (dest_pair 6 thunk)
       else lookup_binding e var
    end handle _ => NONE

fun length_env env =
    let val (_,_,e) = dest_env env
    in 1 + length_env e
    end handle _ => 0

fun domain env =
    let val (w,thunk,e) = dest_env env
    in w :: domain e
    end handle _ => []

fun print_first_env env =
    let val (w,thunk,e) = dest_env env
    in w ^ ":" ^ toStringTerm thunk
    end handle _ => ""

fun clean_env env vars =
    let val (w,thunk,e) = dest_env env
    in if VARS.member (vars, w)
       then clean_env e vars
       else mk_nuprl_cons_env_term w thunk (clean_env e vars)
    end handle _ => env

fun add_env_bindings' env [] = env
  | add_env_bindings' env ((var, term, env') :: bindings) =
    if var = ""
    then add_env_bindings' env bindings
    else let val (t,e) =
		 if is_nuprl_variable_term term
		 then case lookup_binding env' (dest_variable term) of
			  SOME p => p
			| NONE => (term, env')
		 else (term, env')
	     val pair = mk_nuprl_pair_term t e
	     val new_env = mk_nuprl_cons_env_term var pair env
	 in add_env_bindings' new_env bindings
	 end

fun add_env_bindings env bindings =
    let val (vars, bindings') =
	    foldr (fn (b as (var, _, _), (vars, bindings)) =>
		      if var = ""
		      then (vars, bindings)
		      else (VARS.add (vars, var), b :: bindings))
		  (VARS.empty, [])
		  bindings
    in add_env_bindings' (clean_env env vars) bindings'
    end

fun closure2term' term env =
    let (*val _ = print "closure2term\n"*)
	(*val _ = raise Fail "closure2term\n"*)
	fun aux term bounds env =
	    if is_nuprl_iclosure_term term
	    then let val (t,e) = dest_iclosure term
		 in aux t bounds e
		 end
	    else if is_nuprl_variable_term term
	    then let val v = dest_variable term
		 in if VARS.member (bounds, v)
		    then term
		    else case lookup_binding env v of
			     SOME (t,e) => aux t bounds e
			   | NONE => term
		 end
	    else let val (opr,bterms) = dest_term term
		     fun addBounds vs = VARS.addList (bounds, vs)
		     val bterms' = map (fn (vs, t) => (vs, aux (rterm2term t) (addBounds vs) env)) bterms
		 in mk_nuprl_term opr bterms'
		 end
    in aux term VARS.empty env
    end

fun closure2term term env =
    let fun aux term env =
	    if is_nuprl_iclosure_term term
	    then let val (t,e) = dest_iclosure term
		 in aux t e
		 end
	    else if is_nuprl_variable_term term
	    then let val v = dest_variable term
		 in case lookup_binding env v of
			SOME (t,e) => aux t e
		      | NONE => term
		 end
	    else let val (opr,bterms) = dest_term term
		     val bterms' = map (fn (vs, t) => (vs, aux (rterm2term t) (clean_env env (VARS.fromList vs)))) bterms
		 in mk_nuprl_term opr bterms'
		 end
    (*(\x.y)[y->(\u.x)[x->1]]*)
    in aux term env
    end


(* ------ PARTIAL EVALUATION & STRICTNESS ANALYSIS ------ *)

fun partial_ev_opt (term as TERM (opr as ((opid, tag), params), bterms)) =
    let val bterms' = partial_ev_opt_bterms bterms
    in if opid = "add"
	  orelse opid = "subtract"
	  orelse opid = "multiply"
	  orelse opid = "divide"
	  orelse opid = "remainder"
	  orelse opid = "less"
	  orelse opid = "int_eq"
       then case bterms' of
		[B_TERM ([], n1), B_TERM ([], n2)] =>
		let val n1 = rterm2term n1
		    val n2 = rterm2term n2
		in if is_nuprl_integer_term n1
		      andalso is_nuprl_integer_term n2
		   then if opid = "add"
			   orelse opid = "subtract"
			   orelse opid = "multiply"
			   orelse opid = "divide"
			   orelse opid = "remainder"
			then do_primitive_int_op opid n1 n2
			else if opid = "less"
				orelse opid = "int_eq"
			then if do_primitive_cmp opid n1 n2
			     then mk_nuprl_btrue_term
			     else mk_nuprl_bfalse_term
			else TERM (opr, bterms')
    		   else TERM (opr, bterms')
		end
	      | _ => TERM (opr, bterms')
       else if opid = "atom_eq"
       then case bterms' of
		[B_TERM ([], a1),
		 B_TERM ([], a2),
		 B_TERM ([], t1),
		 B_TERM ([], t2)] =>
		(let val a1 = rterm2term a1
		     val a2 = rterm2term a2
		     val n  = firstnat term handle _ => 0
		 in if compare_atomn n a1 a2
		    then rterm2term t1
		    else rterm2term t2
		 end handle _ =>  TERM (opr, bterms'))
	      | _ => TERM (opr, bterms')
       else TERM (opr, bterms') (* !! not finished - I should also check the other reductions spread, decide *)
    end
  | partial_ev_opt (term as VAR_TERM var) = term
  | partial_ev_opt (term as LAM_TERM (var, rterm)) = LAM_TERM (var, partial_ev_opt_rterm rterm)
  | partial_ev_opt (term as WAI_TERM (rterm1, rterm2)) = WAI_TERM (partial_ev_opt_rterm rterm1, partial_ev_opt_rterm rterm2)
  | partial_ev_opt (term as APP_TERM (rterm1, rterm2)) =
    let val rterm1' = partial_ev_opt_rterm rterm1
	val rterm2' = partial_ev_opt_rterm rterm2
	val f       = rterm2term rterm1'
	val arg     = rterm2term rterm2'
    in if opid_of_term f = "lambda"
       then let val (x,B) = dest_lambda 0 f
	    in case find_free_vars_map (free_vars_map B) x of
		   0 => B (* x does not occur in B *)
		 | 1 => partial_ev_opt (fo_subst [(x,arg)] B)
		 | _ => if List.length (subterms arg) = 0 (* if the argument has no subterms we might as well do the substitution *)
			then partial_ev_opt (fo_subst [(x,arg)] B)
			else APP_TERM (rterm1', rterm2')
	    end
       else APP_TERM (rterm1', rterm2')
    end
  | partial_ev_opt (term as PAI_TERM (rterm1, rterm2)) = PAI_TERM (partial_ev_opt_rterm rterm1, partial_ev_opt_rterm rterm2)
  | partial_ev_opt (term as NIL_TERM) = term
  | partial_ev_opt (term as CON_TERM (rterm1, rterm2)) = CON_TERM (partial_ev_opt_rterm rterm1, partial_ev_opt_rterm rterm2)
  | partial_ev_opt (term as NAT_TERM _) = term
  | partial_ev_opt (term as INL_TERM rterm) = INL_TERM (partial_ev_opt_rterm rterm)
  | partial_ev_opt (term as INR_TERM rterm) = INR_TERM (partial_ev_opt_rterm rterm)
  | partial_ev_opt (term as FIX_TERM rterm) = FIX_TERM (partial_ev_opt_rterm rterm)
  | partial_ev_opt (term as SPR_TERM (pair, var1, var2, rterm)) =
    let val pair'  = partial_ev_opt_rterm pair
	val rterm' = partial_ev_opt_rterm rterm
	val p      = rterm2term pair'
    in if opid_of_term p = "pair"
       then let val t = rterm2term rterm'
		val m = free_vars_map t
		val (a,b) = dest_pair 7 p
	    in case (find_free_vars_map m var1, find_free_vars_map m var2) of
		   (0, 0) => t
		 | (1, 0) => partial_ev_opt (fo_subst [(var1,a)] t)
		 | (0, 1) => partial_ev_opt (fo_subst [(var2,b)] t)
		 | (_, 0) => if List.length (subterms a) = 0
			     then partial_ev_opt (fo_subst [(var1,a)] t)
			     else APP_TERM (mk_rterm (LAM_TERM (var1,rterm')), mk_rterm a)
		 | (0, _) => if List.length (subterms b) = 0
			     then partial_ev_opt (fo_subst [(var2,b)] t)
			     else APP_TERM (mk_rterm (LAM_TERM (var2,rterm')), mk_rterm b)
		 | (1, 1) => partial_ev_opt (fo_subst [(var1,a),(var2,b)] t)
		 | (_, _) => if List.length (subterms a) = 0 andalso List.length (subterms b) = 0
			     then partial_ev_opt (fo_subst [(var1,a),(var2,b)] t)
			     else SPR_TERM (pair', var1, var2, rterm')
	    end
       else SPR_TERM (pair', var1, var2, rterm')
    end
  | partial_ev_opt (term as DEC_TERM (dec, var1, rterm1, var2, rterm2)) =
    let val dec'    = partial_ev_opt_rterm dec
	val rterm1' = partial_ev_opt_rterm rterm1
	val rterm2' = partial_ev_opt_rterm rterm2
	val d       = rterm2term dec'
	val opid    = opid_of_term d
	val b_inl   = opid = "inl"
	val b_inr   = opid = "inr"
    in if b_inl orelse b_inr
       then let val (x,v,rt) =
		    if b_inl
		    then (dest_inl d, var1, rterm1')
		    else (dest_inr d, var2, rterm2')
		val t = rterm2term rt
	    in case find_free_vars_map (free_vars_map t) v of
		   0 => t
		 | 1 => partial_ev_opt (fo_subst [(v,x)] t)
		 | _ => if List.length (subterms x) = 0
			then partial_ev_opt (fo_subst [(v,x)] t)
			else APP_TERM (mk_rterm (LAM_TERM (v,rt)), mk_rterm x)
	    end
       else DEC_TERM (dec', var1, rterm1', var2, rterm2')
    end
  | partial_ev_opt (term as LIN_TERM (lst, nilcase, x, xs, r, conscase)) =
    let fun dest term =
	    let val opid = opid_of_term term
	    in if opid = "nil"
	       then SOME []
	       else if opid = "cons"
	       then let val (h,t) = dest_cons term
		    in Option.map (fn lst => h :: lst) (dest t)
		    end
	       else NONE
	    end
	fun default () =
	    LIN_TERM (partial_ev_opt_rterm lst,
		      partial_ev_opt_rterm nilcase,
		      x,
		      xs,
		      r,
		      partial_ev_opt_rterm conscase)
	val lst      = rterm2term lst
	val nilcase  = rterm2term nilcase
	val conscase = rterm2term conscase
	val m        = free_vars_map conscase
    in case (find_free_vars_map m x,
	     find_free_vars_map m xs,
	     find_free_vars_map m r,
	     dest lst) of
	   (_, _, _, NONE) => default ()
	 | (n1, n2, n3, SOME elts) =>
	   if n1 <= 1 andalso n2 <= 1 andalso n3 <=1
	   then let val (rest, term) =
			foldr
			    (fn (elt,(rest,list)) =>
				let val nrest = mk_nuprl_finite_list_term rest
				    val rest' = elt :: rest
				    val list' = fo_subst [(x,elt),(xs,nrest),(r,list)] conscase
				in (rest', list')
				end)
			    ([],nilcase)
			    elts
		in partial_ev_opt term
		end
	   else default ()
    end
  | partial_ev_opt (term as CLO_TERM clos) =
    let val (clos' as (rterm, env)) = partial_ev_opt_clos clos
    in if is_em_env env
       then rterm2term rterm
       else CLO_TERM clos'
    end

and partial_ev_opt_clos (rterm, env) =
    let val rterm' = partial_ev_opt_rterm rterm
	val (ENV env') = partial_ev_opt_env env
	val term = rterm2term rterm'
	val vars = free_vars_map term
	val (sub, m) =
	    MAP.foldri
		(fn (v, t, (sub, m)) =>
		    case MAP.find (vars, v) of
			SOME n =>
			if n = 0
			then (sub, m)
			else if n = 1
			then ((v,rterm2term t) :: sub, m)
			else (sub, MAP.insert (m, v, t))
		      | NONE => (sub, m))
		([], MAP.empty) (* we reconstruct the term (a substitution) and environment *)
		env'
	val term' = if List.null sub then term else fo_subst sub term
    in (mk_rterm term', ENV m)
    end

and partial_ev_opt_env (ENV env) = ENV (MAP.map partial_ev_opt_rterm env)

and partial_ev_opt_rterm rterm = mk_rterm (partial_ev_opt (rterm2term rterm))

and partial_ev_opt_bterms bterms = map partial_ev_opt_bterm bterms

and partial_ev_opt_bterm (B_TERM (vars, rterm)) =
    B_TERM (vars, partial_ev_opt_rterm rterm)


(* ------ NUPRL TO EventML ------ *)

datatype alpha = NEXT of string * (unit -> alpha)

val lstAlpha =
    ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
     "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"]

fun streamId [] pref () = streamId lstAlpha (pref ^ "a") ()
  | streamId (x :: xs) pref () =
    let val f = streamId xs pref
    in NEXT (pref ^ x, f)
    end

fun is_list (TERM ((("cons", _), []), [B_TERM ([], x), B_TERM ([], xs)])) =
    Option.map (fn lst => x :: lst) (is_ref_list xs)
  | is_list (TERM ((("nil", _), []), [])) = SOME []
  | is_list _ = NONE

and is_ref_list rterm = is_list (rterm2term rterm)

fun isAtomic t =
    let val opid = opid_of_term t
	val lst  = ["variable", "int", "pair", "natural_number", "prop", "universe"]
    in Option.isSome (List.find (fn x => x = opid) lst)
    end

fun printUkn t n = "-"
    (*(print (toStringTerm t ^ "\n"); "---" ^ Int.toString n)*)

fun nuprl2eml_term sub (TERM ((("apply", _), []), [B_TERM ([], f), B_TERM ([], a)])) =
    nuprl2eml_ref_atm sub f ^ " " ^ nuprl2eml_ref_atm sub a
  | nuprl2eml_term sub (TERM ((("cons", _), []), [B_TERM ([], x), B_TERM ([], xs)])) =
    (case is_ref_list xs of
	 SOME lst => ListFormat.fmt {final = "]", fmt = nuprl2eml_ref_term sub, init = "[", sep = "; "} (x :: lst)
       | NONE => nuprl2eml_ref_term sub x ^ " . " ^ nuprl2eml_ref_term sub xs)
  | nuprl2eml_term sub (TERM ((("subtract", _), []), [B_TERM ([], x), B_TERM ([], y)])) =
    nuprl2eml_ref_term sub x ^ " - " ^ nuprl2eml_ref_term sub y
  | nuprl2eml_term sub (TERM ((("add", _), []), [B_TERM ([], x), B_TERM ([], y)])) =
    nuprl2eml_ref_term sub x ^ " + " ^ nuprl2eml_ref_term sub y
  | nuprl2eml_term sub (TERM ((("pair", _), []), [B_TERM ([], x), B_TERM ([], y)])) =
    "(" ^ nuprl2eml_ref_term sub x ^ "," ^ nuprl2eml_ref_term sub y ^ ")"
  | nuprl2eml_term sub (TERM ((("variable", _), [(v,vkind)]), [])) =
    (case SUB.find (sub, v) of
	 SOME t => t
       | NONE => v)
  | nuprl2eml_term sub (TERM ((("natural_number", _), [(n,nkind)]), [])) = n
  | nuprl2eml_term sub (TERM ((("token", _), [(t,tkind)]), [])) = "`" ^ t ^ "`"
  | nuprl2eml_term sub (term as TERM ((("lambda", _), []), [B_TERM ([x], f)])) =
    printUkn term 0 (*"\\" ^ x ^ ". " ^ nuprl2eml_term sub f*)
  | nuprl2eml_term sub (TERM ((("inr", _), []), [B_TERM ([], t)])) =
    if is_nuprl_ref_term "axiom" t
    then "false" (* NOTE: Arghh, this can be bad because inr(axiom) is not actually equal to false in EML. *)
    else "inr(" ^ nuprl2eml_ref_term sub t ^ ")"
  | nuprl2eml_term sub (TERM ((("inl", _), []), [B_TERM ([], t)])) =
    if is_nuprl_ref_term "axiom" t
    then "true"
    else "inl(" ^ nuprl2eml_ref_term sub t ^ ")"
  | nuprl2eml_term sub (TERM ((("minus", _), []), [B_TERM ([], t)])) =
    "~" ^ nuprl2eml_ref_term sub t
  | nuprl2eml_term sub (TERM ((("it", _), []), [])) = "it"
  | nuprl2eml_term sub (TERM ((("int", _), []), [])) = "Int"
  | nuprl2eml_term sub (TERM ((("bool", _), []), [])) = "Bool"
  | nuprl2eml_term sub (TERM ((("real", _), []), [])) = "Real"
  | nuprl2eml_term sub (TERM ((("atom", _), []), [])) = "Atom"
  | nuprl2eml_term sub (TERM ((("universe", _), params), [])) = "Type"
  | nuprl2eml_term sub (TERM ((("prop", _), params), [])) = "Prop"
  | nuprl2eml_term sub (TERM ((("list", _), []), [B_TERM ([], t)])) =
    nuprl2eml_ref_term sub t ^ " List"
  (* NOTE: This is just a crude hack. For class we should check that the level expression
   * is 'correct', that the Info is a Msg and that es and e don't occur in t. *)
  | nuprl2eml_term sub (TERM ((("eclass", _), [lvl_exp]), [B_TERM ([], info), B_TERM ([es, e], t)])) =
    nuprl2eml_ref_term sub t ^ " Class"
  | nuprl2eml_term sub (TERM ((("product", _), []), [B_TERM ([], t1), B_TERM ([""], t2)])) =
    nuprl2eml_ref_atm sub t1 ^ " * " ^ nuprl2eml_ref_atm sub t2
  | nuprl2eml_term sub (TERM ((("union", _), []), [B_TERM ([], t1), B_TERM ([], t2)])) =
    nuprl2eml_ref_atm sub t1 ^ " + " ^ nuprl2eml_ref_atm sub t2
  | nuprl2eml_term sub (TERM ((("function", _), []), [B_TERM ([], t1), B_TERM ([""], t2)])) =
    nuprl2eml_ref_atm sub t1 ^ " -> " ^ nuprl2eml_ref_term sub t2
  | nuprl2eml_term sub (TERM ((("nil", _), []), [])) = "[]"
  | nuprl2eml_term sub (TERM ((("make-Msg", _), []), [B_TERM ([], header), B_TERM ([], typ), B_TERM ([], body)])) =
    "(" ^ nuprl2eml_ref_term sub header ^ "," ^ nuprl2eml_ref_term sub typ ^ "," ^ nuprl2eml_ref_term sub body ^ ")"
  | nuprl2eml_term sub (VAR_TERM v) =
    (case SUB.find (sub, v) of
	 SOME t => t
       | NONE => v)
  | nuprl2eml_term sub (term as LAM_TERM _) = printUkn term 0
  | nuprl2eml_term sub (WAI_TERM (t, e)) = "wait(" ^ nuprl2eml_ref_atm sub t ^ ", " ^ nuprl2eml_ref_atm sub e ^ ")"
  | nuprl2eml_term sub (APP_TERM (f, a)) = nuprl2eml_ref_atm sub f ^ " " ^ nuprl2eml_ref_atm sub a
  | nuprl2eml_term sub (PAI_TERM (x, y)) = "(" ^ nuprl2eml_ref_term sub x ^ "," ^ nuprl2eml_ref_term sub y ^ ")"
  | nuprl2eml_term sub NIL_TERM = "[]"
  | nuprl2eml_term sub (CON_TERM (t1, t2)) =
    (case is_ref_list t2 of
	 SOME lst => ListFormat.fmt {final = "]", fmt = nuprl2eml_ref_term sub, init = "[", sep = "; "} (t1 :: lst)
       | NONE => nuprl2eml_ref_term sub t1 ^ " . " ^ nuprl2eml_ref_term sub t2)
  | nuprl2eml_term sub (NAT_TERM n) = II.toString n
  | nuprl2eml_term sub (INL_TERM t) =
    if is_nuprl_ref_term "axiom" t
    then "true"
    else "inl(" ^ nuprl2eml_ref_term sub t ^ ")"
  | nuprl2eml_term sub (INR_TERM t) =
    if is_nuprl_ref_term "axiom" t
    then "false" (* NOTE: Arghh, this can be bad because inr(axiom) is not actually equal to false in EML. *)
    else "inr(" ^ nuprl2eml_ref_term sub t ^ ")"
  | nuprl2eml_term sub (FIX_TERM t) = "fix(" ^ nuprl2eml_ref_term sub t ^ ")"
  | nuprl2eml_term sub (term as SPR_TERM _) = printUkn term 0
  | nuprl2eml_term sub (term as DEC_TERM _) = printUkn term 0
  | nuprl2eml_term sub (term as LIN_TERM _) = printUkn term 0
  | nuprl2eml_term sub term = (*printUkn term 1*)
    let val ((opid, params), bterms) = dest_term term
    in if List.null bterms andalso List.null params
       then opid
       else printUkn term 1
    end
    (*let val ((opid, params), bterms) = dest_term term
    in if List.all (fn (vars, t) => List.null vars) bterms
       then foldl (fn ((vars, t), str) => str ^ " " ^ nuprl2eml' t)
		  opid
		  bterms
       else toStringTerm term
    end*)

and nuprl2eml_ref_term sub rterm = nuprl2eml_term sub (rterm2term rterm)

and nuprl2eml_atm sub t =
    let val str = nuprl2eml_term sub t
    in if isAtomic t then str else "(" ^ str ^ ")"
    end

and nuprl2eml_ref_atm sub rterm = nuprl2eml_atm sub (rterm2term rterm)

fun nuprl2eml_isect sub stream (term as TERM ((("isect", _), []),
					      [B_TERM ([],  t1),
					       B_TERM ([v], t2)])) =
    if is_nuprl_ref_term "universe" t1
    then if Option.isSome (SUB.find (sub, v))
	 then nuprl2eml_ref_isect sub stream t2
	 else let val NEXT (tv, str) = stream ()
		  val sub' = SUB.insert (sub, v, tv)
	      in nuprl2eml_ref_isect sub' str t2
	      end
    else printUkn term 9
  | nuprl2eml_isect sub _ term = nuprl2eml_term sub term

and nuprl2eml_ref_isect sub stream rterm =
    nuprl2eml_isect sub stream (rterm2term rterm)

fun nuprl2eml_all id sub stream (term as TERM ((("all", _), []),
					       [B_TERM ([],  t1),
						B_TERM ([v], t2)])) =
    if is_nuprl_ref_term "universe" t1
    then if Option.isSome (SUB.find (sub, v))
	 then nuprl2eml_ref_all id sub stream t2
	 else let val NEXT (tv, str) = stream ()
		  val sub' = SUB.insert (sub, v, tv)
	      in nuprl2eml_ref_all id sub' str t2
	      end
    else printUkn term 2
  | nuprl2eml_all id sub stream (term as TERM ((("uall", _), []),
					       [B_TERM ([],  t1),
						B_TERM ([v], t2)])) =
    if is_nuprl_ref_term "universe" t1
    then if Option.isSome (SUB.find (sub, v))
	 then nuprl2eml_ref_all id sub stream t2
	 else let val NEXT (tv, str) = stream ()
		  val sub' = SUB.insert (sub, v, tv)
	      in nuprl2eml_ref_all id sub' str t2
	      end
    else printUkn term 3
  | nuprl2eml_all id sub stream (term as TERM ((("member", _), []),
					       [B_TERM ([], t1),
						B_TERM ([], t2)])) =
    if is_nuprl_ref_term id t2
    then nuprl2eml_ref_isect sub stream t1
    else printUkn term 4
  | nuprl2eml_all id sub stream term = printUkn term 5

and nuprl2eml_ref_all id sub stream rterm =
    nuprl2eml_all id sub stream (rterm2term rterm)

fun nuprl2eml_wf id (TERM ((("!theorem", _), [name]),
			   [B_TERM ([], t)])) =
    nuprl2eml_ref_all id
		      (SUB.empty : string SUB.map)
		      (streamId lstAlpha "'")
		      t
  | nuprl2eml_wf id term = printUkn term 6

fun nuprl2eml_abs id (term as TERM ((("!abstraction", _), []),
				    [B_TERM ([], cond),
				     B_TERM ([], t1),
				     B_TERM ([], t2)])) =
     if is_nuprl_ref_term id t1
     then nuprl2eml_ref_term SUB.empty t2
     else printUkn term 7
   | nuprl2eml_abs id term = printUkn term 8

fun nuprlTerm2eml term = nuprl2eml_term (SUB.empty : string SUB.map) term

(* nuprl2eml_wf "it" *)

fun nuprl2haskell_var var =
    "hs_" ^ (String.map (fn #"%" => #"p" | c => c) var) ^ "_var"


(* ------ Nuprl to Haskell ------ *)
fun nuprl2haskell_term ind sub term =
    case term of
	TERM ((("apply", _), []), [B_TERM ([], f), B_TERM ([], a)]) =>
	if is_nuprl_lambda_term (rterm2term f)
	then let val (var, b) = dest_lambda 0 (rterm2term f)
	     in "let "
		^ nuprl2haskell_var var
		^ " = "
		^ nuprl2haskell_ref_term ind sub a
		^ " in\n"
		^ nuprl2haskell_term ind sub b
	     end
	else nuprl2haskell_ref_atm ind sub f ^ " " ^ nuprl2haskell_ref_atm ind sub a
      | TERM ((("cons", _), []), [B_TERM ([], x), B_TERM ([], xs)]) =>
	(case is_ref_list xs of
	     SOME lst => T.fmt {init = "[", sep = ", ", final = "]", fmt = nuprl2haskell_ref_term ind sub} (x :: lst)
	   | NONE => nuprl2haskell_ref_term ind sub x ^ " : " ^ nuprl2haskell_ref_term ind sub xs)
      | TERM ((("subtract", _), []), [B_TERM ([], x), B_TERM ([], y)]) =>
	nuprl2haskell_ref_term ind sub x ^ " - " ^ nuprl2haskell_ref_term ind sub y
      | TERM ((("add", _), []), [B_TERM ([], x), B_TERM ([], y)]) =>
	nuprl2haskell_ref_term ind sub x ^ " + " ^ nuprl2haskell_ref_term ind sub y
      | TERM ((("divide", _), []), [B_TERM ([], x), B_TERM ([], y)]) =>
	"div " ^ nuprl2haskell_ref_term ind sub x ^ " " ^ nuprl2haskell_ref_term ind sub y
      | TERM ((("pair", _), []), [B_TERM ([], x), B_TERM ([], y)]) =>
	"(" ^ nuprl2haskell_ref_term ind sub x ^ "," ^ nuprl2haskell_ref_term ind sub y ^ ")"
      | TERM ((("variable", _), [(v,vkind)]), []) =>
	(case SUB.find (sub, v) of
	     SOME v => v
	   | NONE   => nuprl2haskell_var v)
      | TERM ((("natural_number", _), [(n,nkind)]), []) => n
      | TERM ((("token", _), [(t,tkind)]), []) => "\"" ^ t ^ "\""
      | TERM ((("lambda", _), []), [B_TERM ([x], f)]) =>
	let val (vars, b) = dest_lambdas (rterm2term f)
	in "\\"
	   ^ T.fmt {init = "", sep = " ", final = "", fmt = nuprl2haskell_var}
		   (x :: vars)
	   ^ " ->\n" ^ nuprl2haskell_term ind sub b
	end
      | TERM ((("inr", _), []), [B_TERM ([], t)]) =>
	if is_nuprl_ref_term "axiom" t
	then "False" (* NOTE: Arghh, this can be bad because inr(axiom) is not actually equal to false in EML. *)
	else "Inr(" ^ nuprl2haskell_ref_term ind sub t ^ ")"
      | TERM ((("inl", _), []), [B_TERM ([], t)]) =>
	if is_nuprl_ref_term "axiom" t
	then "True"
	else "Inl(" ^ nuprl2haskell_ref_term ind sub t ^ ")"
      | TERM ((("minus", _), []), [B_TERM ([], t)]) =>
	"-" ^ nuprl2haskell_ref_term ind sub t
      | TERM ((("it", _),   []), []) => "()"
      | TERM ((("int", _),  []), []) => "NInt"
      | TERM ((("bool", _), []), []) => "NBool"
      | TERM ((("real", _), []), []) => "NReal"
      | TERM ((("atom", _), []), []) => "NAtom"
      | TERM ((("atom", _), [(n,nkind)]), []) =>
	(case n of
	     "2" => "NLoc"
	   | "1" => "NAtom"
	   | _   => raise Fail ("nuprl2haskell:atom(" ^ n ^ ")"))
      | TERM ((("universe", _), params), []) => "NType"
      | TERM ((("prop", _), params), []) => "NProp"
      | TERM ((("list", _), []), [B_TERM ([], t)]) =>
	"NHiddenType" (*"NList(" ^ nuprl2haskell_ref_term ind sub t ^ ")"*)
      | TERM ((("eclass", _), [lvl_exp]), [B_TERM ([], info), B_TERM ([es, e], t)]) =>
	"NHiddenType" (*"NClass(" ^ nuprl2haskell_ref_term ind sub t ^ ")"*)
      | TERM ((("union", _), []), [B_TERM ([], t1), B_TERM ([], t2)]) =>
	"NHiddenType" (*"NUnion (" ^ nuprl2haskell_ref_atm ind sub t1 ^ ") (" ^ nuprl2haskell_ref_atm ind sub t2 ^ ")"*)
      | TERM ((("product", _), []), [B_TERM ([], t1), B_TERM ([v], t2)]) =>
	"NHiddenType" (*"NProd " ^ nuprl2haskell_var v ^ " (" ^ nuprl2haskell_ref_atm ind sub t1 ^ ") (" ^ nuprl2haskell_ref_atm ind sub t2 ^ ")"*)
      | TERM ((("function", _), []), [B_TERM ([], t1), B_TERM ([v], t2)]) =>
	"NHiddenType" (*"NFun " ^ nuprl2haskell_var v ^ " (" ^ nuprl2haskell_ref_atm ind sub t1 ^ ") (" ^ nuprl2haskell_ref_term ind sub t2 ^ ")"*)
      | TERM ((("set", _), []), [B_TERM ([], t1), B_TERM ([v], t2)]) =>
	"NHiddenType" (*"NSet (" ^ nuprl2haskell_ref_atm ind sub t1 ^ ")" ^ nuprl2haskell_var v ^ " (" ^ nuprl2haskell_ref_term ind sub t2 ^ ")"*)
      | TERM ((("quotient", _), []), [B_TERM ([], t1), B_TERM ([v1,v2], f)]) =>
	"NQuot" (* To finish!!!!!!! *)
      | TERM ((("equal", _), []), [B_TERM ([], typ), B_TERM ([], t1), B_TERM ([], t2)]) =>
	"NEq" (* To finish!!!!!!! *)
      | TERM ((("valueall-type", _), []), [B_TERM ([], typ)]) =>
	"NVAType" (* To finish!!!!!!! *)
      | TERM ((("nil", _), []), []) => "[]"
      | TERM ((("make-Msg", _), []), [B_TERM ([], header), B_TERM ([], typ), B_TERM ([], body)]) =>
	"(" ^ nuprl2haskell_ref_term ind sub header ^ "," ^ nuprl2haskell_ref_term ind sub typ ^ "," ^ nuprl2haskell_ref_term ind sub body ^ ")"
      | TERM ((("atom_eq", _), params), [B_TERM ([], t1), B_TERM ([], t2), B_TERM ([], t3), B_TERM ([], t4)]) =>
	"if "
	^ nuprl2haskell_ref_term ind sub t1
	^ " = "
	^ nuprl2haskell_ref_term ind sub t2
	^ " then "
	^ nuprl2haskell_ref_term ind sub t3
	^ " else "
	^ nuprl2haskell_ref_term ind sub t4
      | TERM ((("eq_term", _), params), [B_TERM ([], t1), B_TERM ([], t2)]) =>
	nuprl2haskell_ref_term ind sub t1 ^ " = " ^ nuprl2haskell_ref_term ind sub t2
      | TERM ((("less", _), []), [B_TERM ([], t1), B_TERM ([], t2), B_TERM ([], t3), B_TERM ([], t4)]) =>
	"if "
	^ nuprl2haskell_ref_term ind sub t1
	^ " < "
	^ nuprl2haskell_ref_term ind sub t2
	^ " then "
	^ nuprl2haskell_ref_term ind sub t3
	^ " else "
	^ nuprl2haskell_ref_term ind sub t4
      | TERM ((("int_eq", _), []), [B_TERM ([], t1), B_TERM ([], t2), B_TERM ([], t3), B_TERM ([], t4)]) =>
	"if "
	^ nuprl2haskell_ref_term ind sub t1
	^ " = "
	^ nuprl2haskell_ref_term ind sub t2
	^ " then "
	^ nuprl2haskell_ref_term ind sub t3
	^ " else "
	^ nuprl2haskell_ref_term ind sub t4
      | TERM ((("callbyvalueall", _), []), [B_TERM ([], arg), B_TERM ([x], B)]) =>
	"(\\" ^ nuprl2haskell_var x ^ " -> " ^ nuprl2haskell_ref_term ind sub B ^ ") $! " ^ nuprl2haskell_ref_term ind sub arg
      | TERM ((("callbyvalue", _), []), [B_TERM ([], arg), B_TERM ([x], B)]) =>
	"(\\" ^ nuprl2haskell_var x ^ " -> " ^ nuprl2haskell_ref_term ind sub B ^ ") $! " ^ nuprl2haskell_ref_term ind sub arg
      | TERM ((("list_ind", _), []), [B_TERM ([], L), B_TERM ([], nilcase), B_TERM ([x, xs, r], conscase)]) =>
	let val f   = "f"
	    val lst = "L"
	in "let " ^ f ^ " " ^ lst ^ " = case " ^ lst ^ " of"
	   ^ "\n"
	   ^ "  [] -> " ^ nuprl2haskell_ref_term ind sub nilcase
	   ^ "\n"
	   ^ "  " ^ nuprl2haskell_var x ^ " : " ^ nuprl2haskell_var xs ^ " -> (let " ^ nuprl2haskell_var r ^ " = " ^ f ^ " " ^ nuprl2haskell_var xs ^ " in " ^ nuprl2haskell_ref_term ind sub conscase ^ ")"
	   ^ "\n"
	   ^ "in " ^ f ^ " " ^ nuprl2haskell_ref_term ind sub L
	end
      | TERM ((("axiom", _), []), []) => "()"
      | VAR_TERM v => (case SUB.find (sub, v) of SOME v => v | NONE => nuprl2haskell_var v)
      | LAM_TERM (x, f) =>
	let val (vars, b) = dest_lambdas (rterm2term f)
	in "\\"
	   ^ T.fmt {init = "", sep = " ", final = "", fmt = nuprl2haskell_var}
		   (x :: vars)
	   ^ " ->\n" ^ nuprl2haskell_term ind sub b
	end
      | WAI_TERM (t, e) => raise Fail "nuprl2haskell_term:WAI:TERM"
      | APP_TERM (f, a) =>
	if is_nuprl_lambda_term (rterm2term f)
	then let val (var, b) = dest_lambda 0 (rterm2term f)
	     in "let "
		^ nuprl2haskell_var var
		^ " = "
		^ nuprl2haskell_ref_term ind sub a
		^ " in\n"
		^ nuprl2haskell_term ind sub b
	     end
	else nuprl2haskell_ref_atm ind sub f ^ " " ^ nuprl2haskell_ref_atm ind sub a
      | PAI_TERM (x, y) => "(" ^ nuprl2haskell_ref_term ind sub x ^ "," ^ nuprl2haskell_ref_term ind sub y ^ ")"
      | NIL_TERM => "[]"
      | CON_TERM (t1, t2) =>
	(case is_ref_list t2 of
	     SOME lst => ListFormat.fmt {final = "]", fmt = nuprl2haskell_ref_term ind sub, init = "[", sep = ", "} (t1 :: lst)
	   | NONE => nuprl2haskell_ref_term ind sub t1 ^ " : " ^ nuprl2haskell_ref_term ind sub t2)
      | NAT_TERM n => II.toString n
      | INL_TERM t =>
	if is_nuprl_ref_term "axiom" t
	then "True"
	else "Inl(" ^ nuprl2haskell_ref_term ind sub t ^ ")"
      | INR_TERM t =>
	if is_nuprl_ref_term "axiom" t
	then "False" (* NOTE: Arghh, this can be bad because inr(axiom) is not actually equal to false in EML. *)
	else "Inr(" ^ nuprl2haskell_ref_term ind sub t ^ ")"
      | FIX_TERM t => raise Fail "to_haskell:FIX"
      | SPR_TERM (pair, var1, var2, rterm) =>
	"let (" ^ nuprl2haskell_var var1 ^ "," ^ nuprl2haskell_var var2 ^ ") ="
	^ "\n"
	^ nuprl2haskell_ref_term ind sub pair ^ " in"
	^ "\n"
	^ nuprl2haskell_ref_term ind sub rterm
      | DEC_TERM (dec, var1, rterm1, var2, rterm2) =>
	"case " ^ nuprl2haskell_ref_term ind sub dec ^ " of"
	^ "\n"
	^ "  Inl " ^ nuprl2haskell_var var1 ^ " -> " ^ nuprl2haskell_ref_term ind sub rterm1
	^ "\n"
	^ "  Inr " ^ nuprl2haskell_var var2 ^ " -> " ^ nuprl2haskell_ref_term ind sub rterm2
      | LIN_TERM (lst, nilcase, x, xs, r, conscase) => raise Fail ("nuprl2haskell:LIN_TERM")
      | CLO_TERM _ => raise Fail ("nuprl2haskell:CLO_TERM")
      | TERM (((opid, tag), parameters), subterms) =>
	raise Fail ("nuprl2haskell:"
		    ^ opid
		    ^ "("
		    ^ Int.toString (List.length parameters)
		    ^ "-"
		    ^ Int.toString (List.length subterms)
		    ^ ")")

and nuprl2haskell_ref_term ind sub rterm = nuprl2haskell_term ind sub (rterm2term rterm)

and nuprl2haskell_atm ind sub t =
    let val str = nuprl2haskell_term ind sub t
    in if isAtomic t then str else "(" ^ str ^ ")"
    end

and nuprl2haskell_ref_atm ind sub rterm = nuprl2haskell_atm ind sub (rterm2term rterm)

fun nuprl2haskell term =
    let val prelude1 = "data DisjointUnion a b = Inl a | Inr b"
	val prelude2 = "data NType = NHiddenType | NInt | NBool | NReal | NAtom | NLoc | NType | NProp | NList NType | NCLass NType | NUnion NType NType | NProd string NType NType | NFun string NType NType | NSet NType string NType | NQuot | NEq | NVAType"
	val str = nuprl2haskell_term "  " SUB.empty term
    in prelude1 ^ "\n\n" ^ prelude2 ^ "\n\n" ^ "main =\n" ^ str
    end


end
