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
 *  o Date:        20 May 2011
 *  o File name:   Evaluator1.sml
 *  o Description: .
 *)


structure Evaluator1 = struct

structure B = Tools
structure T = NuprlTerms
structure P = Primitive
structure E = EvalProperties

fun member (element : string) list = List.exists (fn v => v = element) list

fun NextStepEval1 t steps0 principals non_principals steps (lib as (map,user)) =
    let val opid = T.opid_of_term t

    in if member opid ["add", "subtract", "multiply", "divide", "remainder"]
       then let val ((v1,u1),(v2,u2)) = B.get2 principals
	    in (T.do_primitive_int_op opid v1 v2, user, B.decr_steps steps, false)
	    end

       else if opid = "minus"
       then let val (v,u) = B.get1 principals
	    in if T.is_nuprl_term "natural_number" v
	       then (T.mk_nuprl_simple_term "minus" [v], u, steps, false)
	       else (T.do_primitive_minus v, u, B.decr_steps steps, false)
	    end

       else if member opid ["less", "int_eq"]
       then let val ((v1,u1),(v2,u2)) = B.get2 principals
		val (t3,t4) = B.get2_0bound non_principals
	    in if T.do_primitive_cmp opid v1 v2
	       then (T.rterm2term t3, user, B.decr_steps steps, true)
	       else (T.rterm2term t4, user, B.decr_steps steps, true)
	    end

       else if opid = "atom_eq"
       then let val n = (T.firstnat t) handle _ => 0
		val ((v1,u1),(v2,u2)) = B.get2 principals
		val (t3,t4) = B.get2_0bound non_principals
	    in if T.compare_atomn n v1 v2
	       then (T.rterm2term t3, user, B.decr_steps steps, true)
	       else (T.rterm2term t4, user, B.decr_steps steps, true)
	    end

       else if opid = "eq_term"
       then let val ((v1,u1),(v2,u2)) = B.get2 principals
	    in if P.is_complete_primitive_value v1
		  andalso
		  P.is_complete_primitive_value v2
	       then if T.alpha_equal_terms v1 v2
		    then (T.mk_inl_term T.mk_nuprl_axiom_term, user, B.decr_steps steps, false)
		    else (T.mk_inr_term T.mk_nuprl_axiom_term, user, B.decr_steps steps, false)
	       else raise Fail "eq_term"
	    end

       else if member opid ["isinr", "isinl", "ispair", "isint", "islambda", "isatom2"]
       then let val (v1,u1) = B.get1 principals
		val (t2,t3) = B.get2_0bound non_principals
	    in if P.do_primitive_test opid v1
	       then (T.rterm2term t2, user, B.decr_steps steps, true)
	       else (T.rterm2term t3, user, B.decr_steps steps, true)
	    end

       else if opid = "spread"
       then let val (v1,u1) = B.get1 principals
		val (x,y,B) = B.get1_2bound non_principals
		val (a, b)  = T.dest_pair 5 v1
		    handle _ => raise Fail (T.toStringTerm t ^ "\n-+-+-+-\n" ^ T.toStringTerm v1 ^ "\n-+-+-+-\n" ^ Int.toString steps)
		val t1 = E.mk_ilibrary a u1
		val t2 = E.mk_ilibrary b u1
	    in (T.fo_subst [(x,t1),(y,t2)] (T.rterm2term B), user, B.decr_steps steps, true)
	    end

       else if opid = "decide"
       then let val (v1,u1) = B.get1 principals
		val (x,A,y,B) = B.get2_1bound non_principals
		val t1 = E.mk_ilibrary (T.subtermn 1 v1) u1
	    in if T.is_nuprl_term "inl" v1
	       then (T.fo_subst [(x, t1)] (T.rterm2term A), user, B.decr_steps steps, true)
	       else if T.is_nuprl_term "inr" v1
	       then (T.fo_subst [(y, t1)] (T.rterm2term B), user, B.decr_steps steps, true)
	       else raise Fail "decide"
	    end

       else if opid = "apply"
       then let val arg = B.get1_0bound non_principals
		val arg = T.rterm2term arg
	    in if steps < 0 andalso T.is_nuprl_term "ycomb" (T.subtermn 1 t)
	       then (T.mk_apply_term arg t, user, B.decr_steps steps0, true)
	       else let val (f,u) = B.get1 principals
			val (x,B) = T.dest_lambda 6 f
			val targ = E.mk_ilibrary arg user
		    in (T.fo_subst [(x, targ)] B, u, B.decr_steps steps, true)
		    end
	    end

       else if opid = "fix"
       then let val f = B.get1_0bound non_principals
	    in (T.mk_apply_term (T.rterm2term f) t, user, B.decr_steps steps, true)
	    end

       else if opid = "!wait"
       then let val (t,_) = B.get1 principals
		val w     = B.get1_0bound non_principals
	    in (T.do_primitive_wait t (T.rterm2term w), user, B.decr_steps steps, true)
	    end

       else if opid = "callbyvalue"
       then let val (q,u) = B.get1 principals
		val (x,B) = B.get1_1bound non_principals
		val tq = E.mk_ilibrary q u
	    in if P.is_primitive_value q
	       then (T.fo_subst [(x, tq)] (T.rterm2term B), user, B.decr_steps steps, true)
	       else raise Fail "callbyvalue"
	    end

       else if opid = "callbyvalueall"
       then let val (q,u) = B.get1 principals
		val (x,B) = B.get1_1bound non_principals
		val tq = E.mk_ilibrary q u
	    in if P.is_complete_primitive_value q
	       then (T.fo_subst [(x, tq)] (T.rterm2term B), user, B.decr_steps steps, true)
	       else ((*print (T.toStringTerm q);*)
		     raise Fail "callbyvalueall")
	    end
(**)
       else if opid = "list_ind"
       then let val (q,u) = B.get1 principals
		val (nilcase,x,xs,r,conscase) = B.get2_03bound non_principals
		val nilcase  = T.rterm2term nilcase
		val conscase = T.rterm2term conscase
	    in if T.is_nuprl_term "nil" q
	       then (nilcase, user, B.decr_steps steps, true)
	       else if T.is_nuprl_term "cons" q
	       then let val (qa,qb) = B.get2 (T.subterms q)
			val qa = T.rterm2term qa
			val qb = T.rterm2term qb
			val t2 = T.mk_list_ind_term qb nilcase (x,xs,r,conscase)
		    in (T.fo_subst [(x,qa),(xs,qb),(r,t2)] conscase, user, B.decr_steps steps, true)
		    end
	       else raise Fail "list_ind"
	    end

       else if opid = "ind"
       then let val (q,u) = B.get1 principals
		val (x,rd,downcase,basecase,y,ru,upcase) = B.get3_202bound non_principals
		val downcase = T.rterm2term downcase
		val basecase = T.rterm2term basecase
		val upcase   = T.rterm2term upcase
		val ord = T.is_zero q
		val t' = if ord = EQUAL then basecase
			 else let val (p,r,w,c) =
				      if ord = GREATER
				      then (T.dec_integer q,ru,y,upcase)
				      else (T.inc_integer q,rd,x,downcase)
				  val t2 = T.mk_nuprl_ind_term p (x,rd,downcase) basecase (y,ru,upcase)
			      in (T.fo_subst [(w,q),(r,t2)] c)
			      end
	    in (t', user, B.decr_steps steps, true)
	    end

       else if opid = "rec_ind"
       then let val (arg,f,x,B) = B.get2_02bound non_principals
		val arg = T.rterm2term arg
		val B   = T.rterm2term B
		val B'  = T.mk_nuprl_rec_ind_term (T.mk_variable_term x) (f,x,B)
		val function = T.mk_lambda_term x B'
	    in (T.fo_subst [(x,arg),(f,function)] B, user, B.decr_steps steps, true)
	    end

       else if opid = "variable"
       then (t, user, steps, false)

       else if opid = "!abstraction"
       then let val ((v1,u1),(v2,u2),(v3,u3)) = B.get3 principals
	    in (T.mk_nuprl_iabstraction_term v2 v3, user, steps, false)
	    end

       else if opid = "!library"
       then let val (q,u) = B.get2_0bound non_principals
	    in (T.rterm2term q, T.rterm2term u, steps, true)
	    end

       else if E.is_termof_term lib t
       then (E.unfold_tof t, user, B.decr_steps steps, true)
       (*then (apply_conv (TagC (mk_tag_term 1)) t, user, B.decr_steps steps, true)*)

       else if E.is_abstraction_term lib t
       then (E.unfold_abs NONE t, E.get_found_user user, B.decr_steps steps, true)

       else (t, user, steps, false)

    end

(* EVALUATOR1 - recursive descent *)
fun Evaluator1 lib steps term =

    let fun EvalList (terms, steps, lib) eval =
	    foldl (fn ((vars,t), (steps,terms)) =>
		      if List.null vars
		      then let val (t1,steps1,(l,u)) = eval (T.rterm2term t,steps, lib)
			   in (steps1, terms @ [(t1,u)])
			   end
		      else raise Fail "EvalList")
		  (steps,[])
		  terms

	fun Eval (t, steps, lib) =
	    let val (opr,subterms) = T.dest_term t
		val (opid,params) = opr
		val b = E.is_eval_all opid
		val eval = if b then EvalAll o Eval else Eval
		(*val _ = print (Bool.toString b ^ "\n" ^ T.toStringTerm t ^ "\n")*)
		val (principals,non_principals) = B.split (E.num_principals opid) subterms
		val (steps1,terms) = EvalList (principals, steps, lib) eval
		fun abort () = (T.mk_nuprl_ref_term opr ((map (fn (t,_) => ([],T.mk_rterm t)) terms) @ non_principals),
				steps1,
				lib)
	    in let val (t',u,steps',ev) = NextStepEval1 t steps terms non_principals steps1 lib
	       in (if ev then Eval else fn x => x) (t', steps', (#1 lib, u))
	       end (*handle _ => abort ()*)
	    end

	and EvalAll (t, steps, lib) =
	    let val (opr,subterms) = T.dest_term t
		val (opid,params) = opr
		val (principals,non_principals) = B.split (E.num_principal_all opid) subterms
		val (steps1,terms) = EvalList (principals, steps, lib) (EvalAll o Eval)
	    in (T.mk_nuprl_ref_term opr ((map (fn (t,_) => ([],T.mk_rterm t)) terms) @ non_principals),
		steps1,
		lib)
	    end

	val (answer,num,_) = Eval (term, steps, lib)

    in (E.strip_ilib answer, steps - num)
    end

end
