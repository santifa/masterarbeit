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
 *  o File name:   Primitive.sml
 *  o Description: Some primitive functions.
 *)


structure Primitive :> PRIMITIVE = struct

structure B = Tools
structure T = NuprlTerms


(**** DO PRIMITIVE FUNCTIONS ****)

structure SET = BinarySetFn(type ord_key = string val compare = String.compare)

val primitive_values =
    SET.addList (SET.empty, ["pair","lambda","inl","inr","nil","cons",
			     "natural_number","axiom","token","equal",
			     "union","product","function","list","isect",
			     "int","atom","atomn","set","rec","quotient",
			     "subtype_rel","tunion"])
val primitive_test_op =
    SET.addList (SET.empty, ["inl", "inr", "pair", "lambda", "token"])

fun destruct_ut2_parameter param =
    if T.type_of_parameter param = "ut2"
    then T.value_of_parameter param
    else raise Fail "improper-parameter-type"

fun do_primitive_test test value =
    let val opid = T.opid_of_term value
    in if SET.member (primitive_test_op, opid)
	  orelse T.is_nuprl_integer_term value
       then if test = "isint"
	    then T.is_nuprl_integer_term value
	    else if test = "isatom2"
	    then case T.parameters_of_term value of
		     [param] => opid = "token" andalso B.can destruct_ut2_parameter param
		   | _ => raise Fail "do_primitive_test"
	    else let val list = [("ispair",  "pair"),
				 ("isinl",   "inl"),
				 ("isinr",   "inr"),
				 ("isatom2", "token")]
		 in opid = B.apply_alist list test
		 end
       else raise Fail "do_primitive_test"
    end

fun is_primitive_value term =
    let val opid = T.opid_of_term term
    in SET.member (primitive_values, opid)
       orelse
       T.is_nuprl_minus_natural_number_term term
    end

fun is_complete_primitive_value term =
    if T.is_nuprl_term "!closure" term
    then is_complete_primitive_value (T.subtermn 1 term)
    else if T.is_ct term
    then is_complete_primitive_value (#1 (T.dest_ct term))
    else is_primitive_value term
	 andalso
	 let val (opr,bterms) = T.dest_term term
	     val unbound_subterms =
		 List.mapPartial (fn (vars,term) =>
				     if List.null vars
				     then SOME (T.rterm2term term)
				     else NONE)
				 bterms
	 in List.all is_complete_primitive_value unbound_subterms
	 end

end
