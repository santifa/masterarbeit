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
 *  o File name:   Evaluator2.sml
 *  o Description: uses closures.
 *)


structure Evaluator2 = struct

structure B = Tools
structure T = NuprlTerms
structure P = Primitive
structure E = EvalProperties
structure M = Monad

val empty_env = T.mk_nuprl_empty_env_term

val >>= = M.bind
infix >>=

val mct = T.mct
val mk_rct = T.mk_rct
val em_env = T.em_env

fun upd_lib user' x (n,((map,user),cls)) = (x, (n,((map,user'),cls)))

fun upd_get_found_user x (n,((map,user),cls)) =
    (x, (B.decr_steps n, ((map,E.get_found_user user),cls)))

structure MAP = BinaryMapFn(type ord_key = string val compare = String.compare)
structure SET = BinarySetFn(type ord_key = string val compare = String.compare)

fun apply_ren ren (var : T.variable) =
    case MAP.find (ren, var) of
	SOME v' => v'
      | NONE => raise Fail "apply_ren"

fun update_ren ren vars1 vars2 =
    B.accumulate2 (fn ren => fn u => fn v => MAP.insert (ren, u, v))
		  ren
		  vars1
		  vars2

fun alpha_equal_closure_terms v1 e1 v2 e2 =
    let fun aux renamings (vs1,t1) env1 (vs2,t2) env2 =
	    let val renamings' = update_ren renamings vs1 vs2
		val op1 = T.opid_of_term t1
	    in if op1 = "!closure"
	       then let val (t, e) = T.dest_iclosure t1
		    in aux renamings' ([],t) e ([],t2) env2
		    end
	       else let val op2 = T.opid_of_term t2
		    in if op2 = "!closure"
		       then let val (t, e) = T.dest_iclosure t2
			    in aux renamings' ([],t1) env1 ([],t) e
			    end
		       else if op1 = "variable"
		       then let val v = T.dest_variable t1
			    in let val v' = apply_ren renamings' v
			       in op2 = "variable" andalso T.dest_variable t2 = v'
			       end handle _ => (case T.lookup_binding env1 v of
						    SOME (t,e) => aux renamings' ([],t) e ([],t2) env2
						  | NONE => raise Fail "alpha_equal_closure_terms")
			    end
		       else if op2 = "variable"
		       then let val v = T.dest_variable t2
			    in (op1 = "variable"
				andalso
				apply_ren renamings' (T.dest_variable t1) = v)
			       handle _ => (case T.lookup_binding env2 v of
						SOME (t,e) => aux renamings' ([],t1) env1 ([],t) e
					      | NONE => raise Fail "alpha_equal_closure_terms")
			    end
		       else op1 = op2
			    andalso B.all2 T.equal_parameters (T.parameters_of_term t1) (T.parameters_of_term t2)
			    andalso B.all2 (fn x => fn y => aux renamings' x env1 y env2) (T.brterms_of_term t1) (T.brterms_of_term t2)
		    end
	    end
    in aux MAP.empty ([],v1) e1 ([],v2) e2
    end handle _ => false

fun ct_alpha_equal_closure_terms v1 e1 v2 e2 =
    let fun aux renamings (vs1,t1) env1 (vs2,t2) env2 =
	    let val renamings' = update_ren renamings vs1 vs2
		val op1 = T.opid_of_term t1
	    in if op1 = "!!closure"
	       then let val (t, e) = T.dest_ct t1
		    in aux renamings' ([],t) e ([],t2) env2
		    end
	       else let val op2 = T.opid_of_term t2
		    in if op2 = "!!closure"
		       then let val (t, e) = T.dest_ct t2
			    in aux renamings' ([],t1) env1 ([],t) e
			    end
		       else if op1 = "variable"
		       then let val v = T.dest_variable t1
			    in let val v' = apply_ren renamings' v
			       in op2 = "variable" andalso T.dest_variable t2 = v'
			       end handle _ => (case T.lookup env1 v of
						    SOME (t,e) => aux renamings' ([],t) e ([],t2) env2
						  | NONE => raise Fail "alpha_equal_closure_terms")
			    end
		       else if op2 = "variable"
		       then let val v = T.dest_variable t2
			    in (op1 = "variable"
				andalso
				apply_ren renamings' (T.dest_variable t1) = v)
			       handle _ => (case T.lookup env2 v of
						SOME (t,e) => aux renamings' ([],t1) env1 ([],t) e
					      | NONE => raise Fail "alpha_equal_closure_terms")
			    end
		       else op1 = op2
			    andalso B.all2 T.equal_parameters (T.parameters_of_term t1) (T.parameters_of_term t2)
			    andalso B.all2 (fn x => fn y => aux renamings' x env1 y env2) (T.brterms_of_term t1) (T.brterms_of_term t2)
		    end
	    end
    in aux MAP.empty ([],v1) e1 ([],v2) e2
    end handle _ => false

val set_int_op  = SET.addList (SET.empty, ["add", "subtract", "multiply", "divide", "remainder"])
val set_comp_op = SET.addList (SET.empty, ["less", "int_eq"])
val set_is_op   = SET.addList (SET.empty, ["isinr", "isinl", "ispair", "isint", "islambda", "isatom2"])

fun member_int_op  element = SET.member (set_int_op,  element)
fun member_comp_op element = SET.member (set_comp_op, element)
fun member_is_op   element = SET.member (set_is_op,   element)

fun NextStepEval2 _ cls lib t principals non_principals env =
    let val opid = T.opid_of_term t
	(*val _ = print (opid ^ "\n")*)

    in if member_int_op opid
       then let val ((v1,e1),(v2,e2)) = B.get2 principals
	    in M.decr (T.do_primitive_int_op opid v1 v2, empty_env, false)
	    end

       else if opid = "minus"
       then let val (v,e) = B.get1 principals
	    in if T.is_nuprl_term "natural_number" v
	       then M.unit (T.mk_nuprl_minus_term v, empty_env, false)
	       else M.decr (T.do_primitive_minus v, env, false)
	    end

       else if member_comp_op opid
       then let val ((v1,e1),(v2,e2)) = B.get2 principals
		val (t3,t4) = B.get2_0bound non_principals
	    in if T.do_primitive_cmp opid v1 v2
	       then M.decr (t3, env, true)
	       else M.decr (t4, env, true)
	    end

       else if opid = "atom_eq"
       then let val n = (T.firstnat t) handle _ => 0
		val ((v1,e1),(v2,e2)) = B.get2 principals
		val (t3,t4) = B.get2_0bound non_principals
	    in if T.compare_atomn n v1 v2
	       then M.decr (t3, env, true)
	       else M.decr (t4, env, true)
	    end

       else if opid = "eq_term"
       then let val ((v1,e1),(v2,e2)) = B.get2 principals
	    in if P.is_complete_primitive_value v1
		  andalso
		  P.is_complete_primitive_value v2
	       then if alpha_equal_closure_terms v1 e1 v2 e2
		    then M.decr (T.mk_inl_term T.mk_nuprl_axiom_term, empty_env, false)
		    else M.decr (T.mk_inr_term T.mk_nuprl_axiom_term, empty_env, false)
	       else raise Fail ("eq_term(" ^ T.opid_of_term v1 ^ "," ^ T.opid_of_term v2 ^ ")")
	    end

       else if member_is_op opid
       then let val (v1,e1) = B.get1 principals
		val (t2,t3) = B.get2_0bound non_principals
	    in if P.do_primitive_test opid v1
	       then M.decr (t2, env, true)
	       else M.decr (t3, env, true)
	    end

       else if opid = "spread"
       then let val (v1,e1) = B.get1 principals
		val (x,y,B) = B.get1_2bound non_principals
		val (a, b)  = (T.dest_pair 5 v1)
		    handle _ => raise Fail "spread" (*(T.toStringTerm t)*)
	    in M.decr (B, T.add_env_bindings env [(y,b,e1),(x,a,e1)], true)
	    end

       else if opid = "decide"
       then let val (v1,e1)   = B.get1 principals
		val (x,A,y,B) = B.get2_1bound non_principals
	    in if T.is_nuprl_term "inl" v1
	       then M.decr (A, T.add_env_bindings env [(x, T.subtermn 1 v1, e1)], true)
	       else if T.is_nuprl_term "inr" v1
	       then M.decr (B, T.add_env_bindings env [(y, T.subtermn 1 v1, e1)], true)
	       else raise Fail "decide"
	    end

       else if opid = "apply"
       then if List.null principals
	    then let val (yc,arg) = B.get2_0bound non_principals
		 in if T.opid_of_term yc = "ycomb"
		    then M.decr (T.mk_apply_term arg t, env, true)
		    else raise Fail "apply"
		 end
	    else let val (f,fe) = B.get1 principals
		     val arg    = B.get1_0bound non_principals
		     (*val _ = print ("app:" ^ T.opid_of_term f ^ "," ^ T.opid_of_term arg ^ "\n")*)
		     val (x, B) = T.dest_lambda 1 f
		 in M.decr (B, T.add_env_bindings fe [(x, arg, env)], true)
		 end

       else if opid = "callbyvalue"
       then let val (q,e) = B.get1 principals
		val (x,B) = B.get1_1bound non_principals
	    in if P.is_primitive_value q
	       then M.decr (B, T.add_env_bindings env [(x, q, e)], true)
	       else raise Fail "callbyvalue"
	    end

       else if opid = "callbyvalueall"
       then let val (q,e) = B.get1 principals
		val (x,B) = B.get1_1bound non_principals
	    in if P.is_complete_primitive_value q
	       then M.decr (B, T.add_env_bindings env [(x, q, e)], true)
	       else raise Fail ("callbyvalueall:(" ^ T.opid_of_term q ^ ")")
	    end

       else if opid = "list_ind"
       then let val (q,e) = B.get1 principals
		val (nilcase,x,xs,r,conscase) = B.get2_03bound non_principals
	    in if T.is_nuprl_term "nil" q
	       then M.decr (nilcase, env, true)
	       else if T.is_nuprl_term "cons" q
	       then let val (qa,qb) = T.dest_cons q
			val qb' = mct (qb,e)
			val t2  = T.mk_list_ind_term qb' nilcase (x,xs,r,conscase)
			val sub = [(x,qa,e),(xs,qb,e),(r,t2,env)]
		    in M.decr (conscase, T.add_env_bindings env sub, true)
		    end
	       else raise Fail "list_ind"
	    end

       else if opid = "ind"
       then let val (q,e) = B.get1 principals
		val (x,rd,downcase,basecase,y,ru,upcase) = B.get3_202bound non_principals
		val ord = T.is_zero q
		val (t',e') =
		    if ord = EQUAL then (basecase,env)
		    else let val (p,r,w,c) =
				 if ord = GREATER
				 then (T.dec_integer q,ru,y,upcase)
				 else (T.inc_integer q,rd,x,downcase)
			     val t2 = T.mk_nuprl_ind_term p (x,rd,downcase) basecase (y,ru,upcase)
			 in (c, T.add_env_bindings env [(w,q,e),(r,t2,env)])
			 end
	    in M.decr (t', e', true)
	    end

       else if opid = "rec_ind"
       then let val (arg,f,x,B) = B.get2_02bound non_principals
		val B' = T.mk_nuprl_rec_ind_term (T.mk_variable_term x) (f,x,B)
		val function = T.mk_lambda_term x B'
	    in M.decr (B, T.add_env_bindings env [(x,arg,env),(f,function,env)], true)
	    end

       else if opid = "variable"
       then case T.lookup_binding env (T.dest_variable t) of
		SOME (a,e) => M.unit (a, e, true)
	      | NONE => raise Fail ("variable " ^ T.toStringTerm t)

       else if opid = "!closure"
       then let val (u,e) = B.get2_0bound non_principals
	    in M.unit (u, e, true)
	    end

       else if opid = "!abstraction"
       then let val ((v1,u1),(v2,u2),(v3,u3)) = B.get3 principals
	    in M.unit (T.mk_nuprl_iabstraction_term v2 v3, env, false)
	    end

       else if opid = "!library"
       then let val (q,u) = B.get2_0bound non_principals
	    in upd_lib u (q, env, true)
	    end

       else if E.is_termof_term lib t
       then M.decr (E.unfold_tof t, env, true)

       else if E.is_abstraction_term lib t
       then let val ope = if cls then SOME env else NONE
	    in upd_get_found_user (E.unfold_abs ope t, env, true)
	    end

       else if List.null (T.bterms_of_term t)
       then M.unit (t, empty_env, false)

       else M.unit (t, env, false)

    end

(*fun is_ycomb term =
    let val (f,B) = T.dest_lambda 2 term
	(*val _ = if f = "f"
		then print (T.toStringTerm term ^ "\n")
		else ()*)
	val (t1,t2) = T.dest_apply B
	fun dest_in_lam t =
	    let val (x,B) = T.dest_lambda 3 t
		val (g,arg) = T.dest_apply B
		val (x1,x2) = T.dest_apply arg
	    in f = T.dest_variable g
	       andalso
	       x = T.dest_variable x1
	       andalso
	       x = T.dest_variable x2
	    end
    in dest_in_lam t1 andalso dest_in_lam t2
    end handle _ => false*)

(*fun RefNextStepEval2 cls lib t principals non_principals env =
    let val opid = T.opid_of_term t
	(*val _ = print (opid ^ "\n")*)

    in if member_int_op opid
       then let val ((v1,e1),(v2,e2)) = B.get2 principals
	    in M.decr (T.do_primitive_int_op opid v1 v2, empty_env, false)
	    end

       else if opid = "minus"
       then let val (v,e) = B.get1 principals
	    in if T.is_nuprl_term "natural_number" v
	       then M.unit (T.mk_nuprl_minus_term v, empty_env, false)
	       else M.decr (T.do_primitive_minus v, empty_env, false)
	    end

       else if member_comp_op opid
       then let val ((v1,e1),(v2,e2)) = B.get2 principals
		val (([],t3),([],t4)) = B.get2 non_principals
	    in if T.do_primitive_cmp opid v1 v2
	       then M.decr (T.rterm2term t3, env, true)
	       else M.decr (T.rterm2term t4, env, true)
	    end

       else if opid = "atom_eq"
       then let val n = (T.firstnat t) handle _ => 0
		val ((v1,e1),(v2,e2)) = B.get2 principals
		val (([],t3),([],t4)) = B.get2 non_principals
	    in if T.compare_atomn n v1 v2
	       then M.decr (T.rterm2term t3, env, true)
	       else M.decr (T.rterm2term t4, env, true)
	    end

       else if opid = "eq_term"
       then let val ((v1,e1),(v2,e2)) = B.get2 principals
	    in if P.is_complete_primitive_value v1
		  andalso
		  P.is_complete_primitive_value v2
	       then if alpha_equal_closure_terms v1 e1 v2 e2
		    then M.decr (T.mk_inl_term T.mk_nuprl_axiom_term, empty_env, false)
		    else M.decr (T.mk_inr_term T.mk_nuprl_axiom_term, empty_env, false)
	       else raise Fail ("eq_term(" ^ T.opid_of_term v1 ^ "," ^ T.opid_of_term v2 ^ ")")
	    end

       else if member_is_op opid
       then let val (v1,e1) = B.get1 principals
		val (([],t2),([],t3)) = B.get2 non_principals
	    in if P.do_primitive_test opid v1
	       then M.decr (T.rterm2term t2, env, true)
	       else M.decr (T.rterm2term t3, env, true)
	    end

       else if opid = "spread"
       then let val (v1,e1) = B.get1 principals
		val ([x,y],B) = B.get1 non_principals
		val (a, b) = (T.dest_pair 5 v1)
		    handle _ => raise Fail "spread" (*(T.toStringTerm t)*)
	    in M.decr (T.rterm2term B, T.add_env_bindings env [(y,b,e1),(x,a,e1)], true)
	    end

       else if opid = "decide"
       then let val (v1,e1) = B.get1 principals
		val (([x],A),([y],B)) = B.get2 non_principals
	    in if T.is_nuprl_term "inl" v1
	       then M.decr (T.rterm2term A, T.add_env_bindings env [(x, T.subtermn 1 v1, e1)], true)
	       else if T.is_nuprl_term "inr" v1
	       then M.decr (T.rterm2term B, T.add_env_bindings env [(y, T.subtermn 1 v1, e1)], true)
	       else raise Fail "decide"
	    end

       else if opid = "apply"
       then if List.null principals
	    then let val (([],yc),([],arg)) = B.get2 non_principals
		 in if T.opid_of_term (T.rterm2term yc) = "ycomb"
		    then M.decr (T.mk_apply_ref_term arg (T.mk_rterm t), env, true)
		    else raise Fail "apply"
		 end
	    else let val (f,fe)   = B.get1 principals
		     val ([],arg) = B.get1 non_principals
		     val (x, B)   = T.dest_lambda 4 f
		 in M.decr (B, T.add_env_bindings fe [(x, T.rterm2term arg, env)], true)
		 end

       else if opid = "callbyvalue"
       then let val (q,e) = B.get1 principals
		val ([x],B) = B.get1 non_principals
	    in if P.is_primitive_value q
	       then M.decr (T.rterm2term B, T.add_env_bindings env [(x, q, e)], true)
	       else raise Fail "callbyvalue"
	    end

       else if opid = "callbyvalueall"
       then let val (q,e) = B.get1 principals
		val ([x],B) = B.get1 non_principals
	    in if P.is_complete_primitive_value q
	       then M.decr (T.rterm2term B, T.add_env_bindings env [(x, q, e)], true)
	       else raise Fail ("callbyvalueall:(" ^ T.opid_of_term q ^ ")")
	    end

       else if opid = "list_ind"
       then let val (q,e) = B.get1 principals
		val (([],nilcase),([x,xs,r],conscase)) = B.get2 non_principals
		val opq = T.opid_of_term q
	    in if opq = "nil"
	       then M.decr (T.rterm2term nilcase, env, true)
	       else if opq = "cons"
	       then let val (qa,qb) = T.dest_cons q
			val qb' = mct (qb,e)
			val t2  = T.mk_list_ind_ref_term qb' nilcase (x,xs,r,conscase)
			val sub = [(x,qa,e),(xs,qb,e),(r,t2,env)]
		    in M.decr (T.rterm2term conscase, T.add_env_bindings env sub, true)
		    end
	       else raise Fail ("list_ind(" ^ T.toStringTerm t ^ ")")
	    end

       else if opid = "ind"
       then let val (q,e) = B.get1 principals
		val (([x,rd],downcase),([],basecase),([y,ru],upcase)) = B.get3 non_principals
		val ord = T.is_zero q
		val (t',e') =
		    if ord = EQUAL then (basecase,env)
		    else let val (p,r,w,c) =
				 if ord = GREATER
				 then (T.dec_integer q,ru,y,upcase)
				 else (T.inc_integer q,rd,x,downcase)
			     val t2 = T.mk_nuprl_ind_ref_term p (x,rd,downcase) basecase (y,ru,upcase)
			 in (c, T.add_env_bindings env [(w,q,e),(r,t2,env)])
			 end
	    in M.decr (T.rterm2term t', e', true)
	    end

       else if opid = "rec_ind"
       then let val (([],arg),([f,x],B)) = B.get2 non_principals
		val B' = T.mk_nuprl_rec_ind_ref_term (T.mk_variable_term x) (f,x,B)
		val function = T.mk_lambda_term x B'
	    in M.decr (T.rterm2term B, T.add_env_bindings env [(x,T.rterm2term arg,env),(f,function,env)], true)
	    end

       else if opid = "variable"
       then case T.lookup_binding env (T.dest_variable t) of
		SOME (a,e) => M.unit (a, e, true)
	      | NONE => raise Fail ("variable " ^ T.toStringTerm t)

       else if opid = "!closure"
       then let val (([],u),([],e)) = B.get2 non_principals
	    in M.unit (T.rterm2term u, T.rterm2term e, true)
	    end

       else if opid = "!abstraction"
       then let val ((v1,u1),(v2,u2),(v3,u3)) = B.get3 principals
	    in M.unit (T.mk_nuprl_iabstraction_term v2 v3, env, false)
	    end

       else if opid = "!library"
       then let val (([],q),([],u)) = B.get2 non_principals
	    in upd_lib (T.rterm2term u) (T.rterm2term q, env, true)
	    end

       else if E.is_termof_term lib t
       then M.decr (E.unfold_tof t, env, true)

       else if E.is_abstraction_term lib t
       then let val env = if List.null non_principals then empty_env else env
		val ope = if cls then SOME env else NONE
	    in upd_get_found_user (E.unfold_abs ope t, env, true)
	    end

       else if List.null (T.bterms_of_term t)
       then M.unit (t, empty_env, false)

       else M.unit (t, env, false)

    end*)

fun decr x s =
    let val (x',s') = M.decr x s
    in (x',s')
    end

fun unit x s =
    let val (x',s') = M.unit x s
    in (x',s')
    end

fun unit' v x s =
    let val (x',s') = M.unit x s
    in (x',s')
    end

val upd_get_found_user =
 fn x =>
 fn s =>
    let val (x',s') = upd_get_found_user x s
    in (x',s')
    end

val upd_lib =
 fn t =>
 fn x =>
 fn s =>
    let val (x',s') = upd_lib t x s
    in (x',s')
    end

fun ClosNextStepEval2 cls lib t principals non_principals env =
    let val opid = T.opid_of_term t
	(*val _ = print (opid ^ "\n")*)

    in if member_int_op opid
       then let val ((v1,_),(v2,_)) = B.get2 principals
	    in decr (T.do_primitive_int_op opid v1 v2, em_env, false)
	    end

       else if opid = "minus"
       then let val (v,_) = B.get1 principals
	    in if T.is_nuprl_term "natural_number" v
	       then unit (T.mk_nuprl_minus_term v, em_env, false)
	       else decr (T.do_primitive_minus v, em_env, false)
	    end

       else if member_comp_op opid
       then let val ((v1,_),(v2,_)) = B.get2 principals
		val (t3,t4) = B.get2_0bound non_principals
	    in if T.do_primitive_cmp opid v1 v2
	       then decr (T.rterm2term t3, env, true)
	       else decr (T.rterm2term t4, env, true)
	    end

       else if opid = "atom_eq"
       then let val n = (T.firstnat t) handle _ => 0
		val ((v1,_),(v2,_)) = B.get2 principals
		val (t3,t4) = B.get2_0bound non_principals
	    in if T.compare_atomn n v1 v2
	       then decr (T.rterm2term t3, env, true)
	       else decr (T.rterm2term t4, env, true)
	    end

       else if opid = "eq_term"
       then let val ((v1,e1),(v2,e2)) = B.get2 principals
	    in if P.is_complete_primitive_value v1
	       then if P.is_complete_primitive_value v2
		    then if ct_alpha_equal_closure_terms v1 e1 v2 e2
			 then decr (T.mk_inl_term T.mk_nuprl_axiom_term, em_env, false)
			 else decr (T.mk_inr_term T.mk_nuprl_axiom_term, em_env, false)
		    else raise Fail ("eq_term(2," ^ T.opid_of_term v2 ^ "," ^ T.toStringTerm v2 ^ ")")
	       else raise Fail ("eq_term(1," ^ T.opid_of_term v1 ^ "," ^ T.toStringTerm v1 ^ ")")
	    end

       else if member_is_op opid
       then let val (v1,_) = B.get1 principals
		val (t2,t3) = B.get2_0bound non_principals
	    in if P.do_primitive_test opid v1
	       then decr (T.rterm2term t2, env, true)
	       else decr (T.rterm2term t3, env, true)
	    end

       else if opid = "spread"
       then let val (v1,e1) = B.get1 principals
		val (x,y,B) = B.get1_2bound non_principals
		val (a, b)  = (T.dest_pair 5 v1)
		    handle _ => ((*print (T.toStringTerm t  ^ "\n---\n");
				 print (T.toStringTerm v1 ^ "\n---\n");
				 print (T.toStringEnv  e1 ^ "\n---\n");*)
				 raise Fail ("spread(" ^ T.opid_of_term v1 ^ ")"))
	    in decr (T.rterm2term B, T.add2env env [(y,b,e1),(x,a,e1)], true)
	    end

       else if opid = "decide"
       then let val (v1,e1)   = B.get1 principals
		val (x,A,y,B) = B.get2_1bound non_principals
	    in if T.is_nuprl_term "inl" v1
	       then decr (T.rterm2term A, T.add2env env [(x, T.subtermn 1 v1, e1)], true)
	       else if T.is_nuprl_term "inr" v1
	       then decr (T.rterm2term B, T.add2env env [(y, T.subtermn 1 v1, e1)], true)
	       else raise Fail ("decide(" ^ T.opid_of_term v1 ^ ")")
	    end

       else if opid = "apply"
       then if List.null principals (* then the function is the Y combinator *)
	    then let val (yc,arg) = B.get2_0bound non_principals
		 in if T.opid_of_term (T.rterm2term yc) = "ycomb"
		    then decr (T.mk_apply_ref_term arg (T.mk_rterm t), env, true)
		    else raise Fail "apply"
		 end
	    else let val (f,fe) = B.get1 principals
		     val arg    = B.get1_0bound non_principals
		     val (x, B) = T.dest_lambda 5 f
		 in decr (B, T.add2env fe [(x, T.rterm2term arg, env)], true)
		 end

       else if opid = "fix"
       then let val f = B.get1_0bound non_principals
	    in decr (T.mk_apply_term (T.rterm2term f) t, env, true)
	    end

       else if opid = "!wait"
       then let val (t,_) = B.get1 principals
		val w     = B.get1_0bound non_principals
	    in decr (T.do_primitive_wait t (T.rterm2term w), env, true)
	    end

       else if opid = "callbyvalue"
       then let val (q,e) = B.get1 principals
		val (x,B) = B.get1_1bound non_principals
	    in if P.is_primitive_value q
	       then decr (T.rterm2term B, T.add2env env [(x, q, e)], true)
	       else raise Fail "callbyvalue"
	    end

       else if opid = "callbyvalueall"
       then let val (q,e) = B.get1 principals
		val (x,B) = B.get1_1bound non_principals
	    in if P.is_complete_primitive_value q
	       then decr (T.rterm2term B, T.add2env env [(x, q, e)], true)
	       else raise Fail ("callbyvalueall:(" ^ T.opid_of_term q ^ ")")
	    end

       else if opid = "list_ind"
       then let val (q,e) = B.get1 principals
		val (nilcase,x,xs,r,conscase) = B.get2_03bound non_principals
		val opq = T.opid_of_term q
	    in if opq = "nil"
	       then decr (T.rterm2term nilcase, env, true)
	       else if opq = "cons"
	       then let val (qa,qb) = T.dest_cons q
			val qb' = mk_rct (qb,e)
			val t2  = T.mk_list_ind_ref_term (T.mk_rterm qb') nilcase (x,xs,r,conscase)
			val sub = [(x,qa,e),(xs,qb,e),(r,t2,env)]
		    in decr (T.rterm2term conscase, T.add2env env sub, true)
		    end
	       else raise Fail ("list_ind(" ^ T.toStringTerm t ^ ")")
	    end

       else if opid = "ind"
       then let val (q,e) = B.get1 principals
		val (x,rd,downcase,basecase,y,ru,upcase) = B.get3_202bound non_principals
		val ord = T.is_zero q
		val (t',e') =
		    if ord = EQUAL then (basecase,env)
		    else let val (p,r,w,c) =
				 if ord = GREATER
				 then (T.dec_integer q,ru,y,upcase)
				 else (T.inc_integer q,rd,x,downcase)
			     val t2 = T.mk_nuprl_ind_ref_term p (x,rd,downcase) basecase (y,ru,upcase)
			 in (c, T.add2env env [(w,q,e),(r,t2,env)])
			 end
	    in decr (T.rterm2term t', e', true)
	    end

       else if opid = "rec_ind"
       then let val (arg,f,x,B) = B.get2_02bound non_principals
		val B' = T.mk_nuprl_rec_ind_ref_term (T.mk_variable_term x) (f,x,B)
		val function = T.mk_lambda_term x B'
	    in decr (T.rterm2term B, T.add2env env [(x,T.rterm2term arg,env),(f,function,env)], true)
	    end

       else if opid = "variable"
       then let val v = T.dest_variable t
	    in case T.lookup env v of
		   SOME (a,e) => unit' v (a, e, true)
		 | NONE => raise Fail ("variable " ^ T.toStringTerm t)
	    end

       else if opid = "!closure"
       then raise Fail "closure" (*let val (([],u),([],e)) = B.get2 non_principals
	    in unit (T.rterm2term u, T.rterm2env e, true)
	    end*)

       else if opid = "!abstraction"
       then let val ((v1,u1),(v2,u2),(v3,u3)) = B.get3 principals
	    in unit (T.mk_nuprl_iabstraction_term v2 v3, env, false)
	    end

       else if opid = "!library"
       then let val (q,u) = B.get2_0bound non_principals
	    in upd_lib (T.rterm2term u) (T.rterm2term q, env, true)
	    end

       else if E.is_termof_term lib t
       then decr (E.unfold_tof t, env, true)

       else if E.is_abstraction_term lib t
       then let val env = if List.null non_principals then em_env else env
		val ope = if cls then SOME env else NONE
	    in upd_get_found_user (E.ct_unfold_abs ope t, env, true)
	    end

       else if List.null (T.bterms_of_term t)
       then unit (t, em_env, false)

       else unit (t, env, false)

    end

fun m_num_principals opid subterms (state as (steps,_)) =
    if steps < 0
       andalso opid = "apply"
       andalso T.is_nuprl_term "ycomb" (T.subterms_n 1 subterms)
    then (0, state)
    else (E.num_principals opid, state)

fun clos_lst lst = map (fn c => ([], mct c)) lst

fun clos_ref_lst lst = map (fn c => ([], T.mk_rterm (mk_rct c))) lst

fun clos_refs lst = map (fn c => ([], T.mk_rterm (mk_rct c))) lst

fun printDebug term1 term2 env timer n m =
    if m < n andalso m mod 1000 = 0
    then let val time  = IntInf.toString (B.getMilliTime timer)
	     (*val size1 = T.size term1
	     val size2 = T.size term2
	     val size3 = T.size env*)
	     val tail  = "[time:"    ^ time ^
			 (*",size-t1:" ^ Int.toString size1 ^
			 ",size-t2:" ^ Int.toString size2 ^
			 ",size-e:"  ^ Int.toString size3 ^*)
			 "]"
	 in print (Int.toString m ^ tail ^ "\n")
	 end
    else ()

(*
(* EVALUATOR2 - closure conversion -- monadized *)
fun Evaluator2' term =

    let val timer = B.startTimer ()

	fun EvalList cbva [] env = M.unit []
	  | EvalList cbva ((vars,rterm)::rest) env =
	    (Eval (T.rterm2term rterm,env))
		>>=
		(fn p =>
		    ((if cbva then EvalAll else M.unit) p)
			>>=
			(fn q => (EvalList cbva rest env)
				     >>=
				     (fn vs => M.unit (q :: vs))))

	and Eval (t, env) =
	    let val (opr as (opid,params),subterms) = T.dest_term t
		(*val _ = (print (opid ^ "- "); app (fn (_,t) => print (" " ^ (if T.is_nuprl_variable_term t then T.toStringTerm t else T.opid_of_term t))) subterms; print "\n")*)
		(*val _ = if opid = "int_eq"
			then (* print ("\n----\n" ^ T.toStringTerm t ^ "\n----\n" ^ ListFormat.fmt {init = "[", sep = ",", final = "]", fmt = fn x => x} (domain env) ^ "\n-----\n")*)
			    print ("\n----\n" ^ T.toStringTerm t ^ "\n----\n" ^ print_first_env env ^ "\n-----\n")
			else ()*)
	    in (m_num_principals opid subterms)
		   >>=
		   (fn n =>
		       let val (p,np) = B.split n subterms
		       in (EvalList (E.is_eval_all opid) p env)
			      >>=
			      (fn c =>
			       fn (state as (n,(lib,cls))) =>
				  let (*val np = map (fn (vars, rterm) => (vars, T.rterm2term rterm)) np*)
				      val ((t',e',ev),state' as (n',_)) = RefNextStepEval2 cls lib t c np env state

				      (*val _ = print ("[size: " ^ Int.toString (T.size t') ^ "]\n")
				      val _ = print ("[size-env: " ^ Int.toString (T.size e') ^ "]\n")*)

				      (*val _ = printDebug t t' e' timer n n'*)
				      (*val _ = print (opid ^ ":" ^ Bool.toString ev ^ "," ^ T.opid_of_term t' ^ "\n")*)
				  in if ev then Eval (t',e') state' else ((t',e'),state')
				  end (*handle _ => ((T.mk_nuprl_ref_term opr ((clos_ref_lst c) @ np), env), state)*))
		       end)
	    end

	and EvalAll (t, env) =
	    let val (opr as (opid,params),subterms) = T.dest_term t
 		(*val _ = (print (opid ^ "+ "); app (fn (_,t) => print (" " ^ T.opid_of_term t)) subterms; print "\n")*)
		val (principals,nprincipals) = B.split (E.num_principal_all opid) subterms
		val env' = if List.null nprincipals then empty_env else env
	    in (EvalList true principals env)
		   >>=
		   (fn c => M.unit (T.mk_nuprl_ref_term opr ((clos_ref_lst c) @ nprincipals), env'))
	    end

    in if T.is_nuprl_iclosure_term term
       then Eval (T.dest_iclosure term)
       else Eval (term, empty_env)
    end

fun Evaluator2 cls lib steps term =
    let val _ = print "[starting evaluation]\n"
	val ((t',e'),(n,_)) = Evaluator2' term (steps,(lib,cls))
	(*val _ = print (":" ^ Int.toString n ^ "," ^ T.opid_of_term t' ^  "\n")*)
	val answer =
	    if cls andalso T.is_nuprl_pair_term t'
	    then let val (s,msgs) = T.dest_pair 8 t'
		     val msgs' = T.closure2term msgs e'
		 in T.mk_pair_term (T.mk_nuprl_iclosure_term s e') msgs'
		 end
	    else T.closure2term t' e'
	val _ = print "[evaluation done]\n"
    in (answer, steps - n)
    end
*)

(* EVALUATOR2 - closure conversion -- no monad *)
fun CEvaluator2' term state =

    let val timer = B.startTimer ()

	fun EvalList cbva [] env state = ([], state)
	  | EvalList cbva ((vars,rterm)::rest) env state =
	    let val term    = T.rterm2term rterm
		val (p,s1)  = Eval (term,env) state
		val (q,s2)  = if cbva then EvalAll p s1 else (p,s1)
		(*val _       = if T.is_nuprl_iclosure_term term
			      then let val clos = mct q
				       val _ = print ("[set:" ^ Int.toString (T.size term) ^ "->" ^ Int.toString (T.size clos) ^ "]\n")
				   in T.set_rterm rterm clos
				   end
			      else ()*)
		val (vs,s3) = EvalList cbva rest env s2
	    in (q::vs,s3)
	    end

	and Eval (t, env) state =
	    if T.is_ct t
	    then Eval (T.dest_ct t) state
	    else let val (opr as (opid,params),subterms) = T.dest_term t
		     val (n,s1) = m_num_principals opid subterms state
		     val (p,np) = B.split n subterms
		     val (c,s2 as (_,(lib,cls))) = EvalList (E.is_eval_all opid) p env s1
		     (*val _ = print ("[----" ^ opid ^ "----]\n")*)
		 in let  val ((t',e',ev),s3) = ClosNextStepEval2 cls lib t c np env s2
		    (*val _ = print ("[size-1: "     ^ Int.toString (T.size t)       ^ "]\n")
		      val _ = print ("[size-env-1: " ^ Int.toString (T.size_env env) ^ "]\n")
		      val _ = print ("[size-2: "     ^ Int.toString (T.size t')      ^ "]\n")
		      val _ = print ("[size-env-2: " ^ Int.toString (T.size_env e')  ^ "]\n")*)
		    in if ev
		       then Eval (t',e') s3
		       else ((t',e'),s3)
		    end (*handle _ => ((T.mk_nuprl_ref_term opr ((clos_ref_lst c) @ np), env), s2)*)
		 end

	and EvalAll (t, env) state =
	    if T.is_ct t
	    then EvalAll (T.dest_ct t) state
	    else let val (opr as (opid,params),subterms) = T.dest_term t
		     val (principals,nprincipals) = B.split (E.num_principal_all opid) subterms
		     val env' = if List.null nprincipals then em_env else env
		     val (c,s) = EvalList true principals env state
		 in ((T.mk_nuprl_ref_term opr ((clos_refs c) @ nprincipals), env'),s)
		 end

    in if T.is_ct term
       then Eval (T.dest_ct term) state
       else Eval (term, em_env) state
    end

fun CEvaluator2 cls lib steps term =
    let val _ = print "[starting evaluation]\n"
	(*val _ = print (T.toStringTerm term ^ "\n")*)
	val ((t',e'),(n,_)) = CEvaluator2' term (steps,(lib,cls))
	(*val _ = print "[closing]\n"*)
	(*val _ = print (":" ^ Int.toString n ^ "," ^ T.opid_of_term t' ^  "\n")*)
	val answer =
	    if cls andalso T.is_nuprl_pair_term t'
	    then let val (s,msgs) = T.dest_pair 8 t'
		     val msgs' = T.close msgs e'
		 in T.mk_pair_term (T.mk_rct (s, e')) msgs'
		 end
	    else T.close t' e'
	val _ = print "[evaluation done]\n"
    in (answer, steps - n)
    end

val Evaluator2 = CEvaluator2

end
