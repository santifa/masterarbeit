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
 *  o File name:   EvaluatorEnv2.sml
 *  o Description: uses closures.
 *)


structure EvaluatorEnv2 = struct

structure B = Tools
structure T = NuprlTerms
structure P = Primitive
structure E = EvalProperties
structure M = Monad

val >>= = M.bind
infix >>=

structure ENV = SplayMapFn(type ord_key = string val compare = String.compare)
datatype env = ENV of (T.nuprl_term * env) ENV.map

structure MAP = SplayMapFn(type ord_key = int val compare = Int.compare)
type map = env MAP.map

val em_env = ENV ENV.empty

fun ex_one_env (ENV env) (x, t, e) = ENV (ENV.insert (env, x ,(t, e)))
fun ex_env env lst = foldr (fn (v, env) => ex_one_env env v) env lst

fun lkup_env (ENV env) v = ENV.find (env, v)

val eval_map = ref (MAP.empty : map)
val id_map = ref 0

fun reset_eval_map () = (eval_map := MAP.empty)
fun reset_id_map   () = id_map := 0
fun reset          () = (reset_eval_map (); reset_id_map ())

fun set_eval_map id env = eval_map := MAP.insert (!eval_map, id, env)

fun next_id_map () =
    let val x = !id_map
	val _ = id_map := x + 1
    in x
    end

fun mk_closure term env =
    let val id  = next_id_map ()
	val tid = T.mk_nuprl_small_integer_term id
	val _   = set_eval_map id env
    in T.mct (term, tid)
    end

fun get_eval_map e =
    let val n = T.dest_small_integer e
    in case MAP.find (!eval_map, n) of
	   SOME env => env
	 | NONE => raise Fail "get_eval_map"
    end

fun rm_eval_map e =
    let val n = T.dest_small_integer e
	val (map, env) = MAP.remove (!eval_map, n)
	val _ = eval_map := map
    in env
    end handle _ =>
	       let val _ = print (T.toStringTerm e)
	       in raise Fail "rm_eval_map"
	       end

val rm_eval_map = get_eval_map

fun upd_lib user' x (n,((map,user),cls)) = (x, (n,((map,user'),cls)))

fun upd_get_found_user x (n,((map,user),cls)) =
    (x, (B.decr_steps n, ((map,E.get_found_user user),cls)))

fun apply_ren ren (var : T.variable) =
    case List.find (fn (x,_) => x = var) ren of
	SOME (v,v') => v'
      | NONE => raise Fail "apply_ren"

fun alpha_equal_closure_terms_map v1 e1 v2 e2 =
    let fun aux renamings (vs1,t1) env1 (vs2,t2) env2 =
	    let val renamings' = B.accumulate2 (fn r => fn u => fn v => (u,v) :: r) renamings vs1 vs2
		val ((op1,parms1),bts1) = T.full_dest_term t1
	    in if op1 = "!closure"
	       then let val (t, e) = T.dest_iclosure t1
			val e' = rm_eval_map e
		    in aux renamings' ([],t) e' ([],t2) env2
		    end
	       else let val ((op2,parms2),bts2) = T.full_dest_term t2
		    in if op2 = "!closure"
		       then let val (t, e) = T.dest_iclosure t2
				val e' = rm_eval_map e
			    in aux renamings' ([],t1) env1 ([],t) e'
			    end
		       else if op1 = "variable"
		       then let val v = T.dest_variable t1
			    in let val v' = apply_ren renamings' v
			       in op2 = "variable" andalso T.dest_variable t2 = v'
			       end handle _ => (case lkup_env env1 v of
						    SOME (t,e) => aux renamings' ([],t) e ([],t2) env2
						  | NONE => raise Fail "alpha_equal_closure_terms_map")
			    end
		       else if op2 = "variable"
		       then let val v = T.dest_variable t2
			    in (op1 = "variable"
				andalso
				apply_ren renamings' (T.dest_variable t1) = v)
			       handle _ => (case lkup_env env2 v of
						SOME (t,e) => aux renamings' ([],t1) env1 ([],t) e
					      | NONE => raise Fail "alpha_equal_closure_terms_map")
			    end
		       else op1 = op2
			    andalso B.all2 T.equal_parameters parms1 parms2
			    andalso B.all2 (fn x => fn y => aux renamings' x env1 y env2) bts1 bts2
		    end
	    end
    in aux [] ([],v1) e1 ([],v2) e2
    end handle _ => false

fun member (element : string) list =
    List.exists (fn v => v = element) list

fun NextStepEvalEnv2 cls lib t principals non_principals env =
    let val opid = T.opid_of_term t
	(*val _ = print (opid ^ "\n")*)

    in if member opid ["add", "subtract", "multiply", "divide", "remainder"]
       then let val ((v1,_),(v2,_)) = B.get2 principals
	    in M.decr (T.do_primitive_int_op opid v1 v2, em_env, false)
	    end

       else if opid = "minus"
       then let val (v,_) = B.get1 principals
	    in if T.is_nuprl_term "natural_number" v
	       then M.unit (T.mk_nuprl_minus_term v, em_env, false)
	       else M.decr (T.do_primitive_minus v, env, false)
	    end

       else if member opid ["less", "int_eq"]
       then let val ((v1,_),(v2,_)) = B.get2 principals
		val (t3,t4) = B.get2_0bound non_principals
	    in if T.do_primitive_cmp opid v1 v2
	       then M.decr (t3, env, true)
	       else M.decr (t4, env, true)
	    end

       else if opid = "atom_eq"
       then let val n = (T.firstnat t) handle _ => 0
		val ((v1,_),(v2,_)) = B.get2 principals
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
	       then if alpha_equal_closure_terms_map v1 e1 v2 e2
		    then M.decr (T.mk_inl_term T.mk_nuprl_axiom_term, em_env, false)
		    else M.decr (T.mk_inr_term T.mk_nuprl_axiom_term, em_env, false)
	       else raise Fail "eq_term"
	    end

       else if member opid ["isinr", "isinl", "ispair", "isint", "islambda", "isatom2"]
       then let val (v1,_) = B.get1 principals
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
		val env' = ex_env env [(y,b,e1),(x,a,e1)]
	    in M.decr (B, env', true)
	    end

       else if opid = "decide"
       then let val (v1,e1)   = B.get1 principals
		val (x,A,y,B) = B.get2_1bound non_principals
	    in if T.is_nuprl_term "inl" v1
	       then let val env' = ex_one_env env (x, T.subtermn 1 v1, e1)
		    in M.decr (A, env', true)
		    end
	       else if T.is_nuprl_term "inr" v1
	       then let val env' = ex_one_env env (y, T.subtermn 1 v1, e1)
		    in M.decr (B, env', true)
		    end
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
		     val (x, B) = T.dest_lambda 7 f
		     val env' = ex_one_env fe (x, arg, env)
		 in M.decr (B, env', true)
		 end

       else if opid = "callbyvalue"
       then let val (q,e) = B.get1 principals
		val (x,B) = B.get1_1bound non_principals
		val env' = ex_one_env env (x, q, e)
	    in if P.is_primitive_value q
	       then M.decr (B, env', true)
	       else raise Fail "callbyvalue"
	    end

       else if opid = "callbyvalueall"
       then let val (q,e) = B.get1 principals
		val (x,B) = B.get1_1bound non_principals
		val env' = ex_one_env env (x, q, e)
	    in if P.is_complete_primitive_value q
	       then M.decr (B, env', true)
	       else raise Fail ("callbyvalueall:(" ^ T.opid_of_term q ^ ")")
	    end

       else if opid = "list_ind"
       then let val (q,e) = B.get1 principals
		val (nilcase,x,xs,r,conscase) = B.get2_03bound non_principals
	    in if T.is_nuprl_term "nil" q
	       then M.decr (nilcase, env, true)
	       else if T.is_nuprl_term "cons" q
	       then let val (qa,qb) = T.dest_cons q
			val qb'  = mk_closure qb e
			val t2   = T.mk_list_ind_term qb' nilcase (x,xs,r,conscase)
			val sub  = [(x,qa,e),(xs,qb,e),(r,t2,env)]
			val env' = ex_env env sub
		    in M.decr (conscase, env', true)
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
			     val t2   = T.mk_nuprl_ind_term p (x,rd,downcase) basecase (y,ru,upcase)
			     val env' = ex_env env [(w,q,e),(r,t2,env)]
			 in (c, env')
			 end
	    in M.decr (t', e', true)
	    end

       else if opid = "rec_ind"
       then let val (arg,f,x,B) = B.get2_02bound non_principals
		val B'   = T.mk_nuprl_rec_ind_term (T.mk_variable_term x) (f,x,B)
		val func = T.mk_lambda_term x B'
		val env' = ex_env env [(x,arg,env),(f,func,env)]
	    in M.decr (B, env', true)
	    end

       else if opid = "variable"
       then case lkup_env env (T.dest_variable t) of
		SOME (a,e) => M.unit (a, e, true)
	      | NONE => raise Fail ("variable " ^ T.toStringTerm t)

       else if opid = "!closure"
       then let val (u,e) = B.get2_0bound non_principals
		val env' = rm_eval_map e
	    in M.unit (u, env', true)
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
       then let val ope = (*if cls then SOME env else*) NONE
	    in upd_get_found_user (E.unfold_abs ope t, env, true)
	    end

       else if List.null (T.bterms_of_term t)
       then M.unit (t, em_env, false)

       else M.unit (t, env, false)

    end

fun m_num_principals opid term (state as (steps,_)) =
    if steps < 0
       andalso opid = "apply"
       andalso T.is_nuprl_term "ycomb" (#1 (T.dest_apply term))
    then (0, state)
    else (E.num_principals opid, state)

fun clos_lst lst = map (fn (t, e) => ([], mk_closure t e)) lst

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

(* EVALUATOR2 - closure conversion *)
fun Evaluator2' term =

    let val timer = B.startTimer ()

	fun EvalList cbva [] env = M.unit []
	  | EvalList cbva ((vars,t)::rest) env =
	    (Eval (t,env))
		>>=
		(fn p => ((if cbva then EvalAll else M.unit) p)
			     >>=
			     (fn q => (EvalList cbva rest env)
					  >>=
					  (fn vs => M.unit (q :: vs))))

	and Eval (t, env) =
	    let val (opr as (opid,params),subterms) = T.full_dest_term t
	    in (m_num_principals opid t)
		   >>=
		   (fn n =>
		       let val (p,np) = B.split n subterms
		       in (EvalList (E.is_eval_all opid) p env)
			      >>=
			      (fn c =>
			       fn (state as (n,(lib,cls))) =>
				  let (*val _ = print (":" ^ T.opid_of_term t ^ "\n")*)
				      val ((t',e',ev),state' as (n',_)) = NextStepEvalEnv2 cls lib t c np env state
				      val _ = printDebug t t' e' timer n n'
				  in if ev then Eval (t',e') state' else ((t',e'),state')
				  end (*handle _ => ((T.mk_nuprl_term opr ((clos_lst c) @ np), env), state)*))
		       end)
	    end

	and EvalAll (t, env) =
	    let val (opr as (opid,params),subterms) = T.full_dest_term t
		val (principals,nprincipals) = B.split (E.num_principal_all opid) subterms
		val env' = if List.null nprincipals then em_env else env
	    in (EvalList true principals env)
		   >>=
		   (fn c => M.unit (T.mk_nuprl_term opr ((clos_lst c) @ nprincipals), env'))
	    end

    in if T.is_nuprl_iclosure_term term
       then let val (t,e) = T.dest_iclosure term
	    in Eval (t, rm_eval_map e)
	    end
       else Eval (term, em_env)
    end

fun Evaluator2 cls lib steps term =
    let val ((t',e'),(n,_)) = Evaluator2' term (steps,(lib,cls))
	val answer = t'
	    (*if cls andalso T.is_nuprl_pair_term t'
	    then let val (s,msgs) = T.dest_pair 8 t'
		     val msgs' = T.closure2term msgs e'
		 in T.mk_nuprl_pair_term (T.mk_nuprl_iclosure_term s e') msgs'
		 end
	    else T.closure2term t' e'*)
    in (answer, steps - n)
    end

end
