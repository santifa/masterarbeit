module B = Tools
module T = NuprlTerms
module P = Primitive
module E = EvalProperties
module M = Monad

let null lst = (try List.hd lst; false with _ -> true)

let empty_env = T.mk_nuprl_empty_env_term

let mct = T.mct
let mk_ct = T.mk_ct
let mk_rct = T.mk_rct
let em_env = T.em_env

let upd_lib user' x (n,((map,user),cls)) = (x, (n,((map,user'),cls)))

let upd_get_found_user x (n,((map,user),cls)) =
  (x, (B.decr_steps n, ((map,E.get_found_user user),cls)))

module KEY = struct type t = string let compare = String.compare end
module SET = Set.Make(KEY)
module MAP = Map.Make(KEY)

let addListSET lst set = List.fold_right SET.add lst set

let apply_ren ren (var : T.variable) =
  try MAP.find var ren with _ -> failwith "apply_ren"

let update_ren ren vars1 vars2 =
  B.accumulate2
    (fun ren u v -> MAP.add u v ren)
    ren
    vars1
    vars2

let ct_alpha_equal_closure_terms v1 e1 v2 e2 =
  let rec aux renamings (vs1,t1) env1 (vs2,t2) env2 =
    let renamings' = update_ren renamings vs1 vs2 in
    let op1 = T.opid_of_term t1 in
    if op1 = "!!closure"
    then let (t, e) = T.dest_ct t1 in aux renamings' ([],t) e ([],t2) env2
    else
      let op2 = T.opid_of_term t2 in
      if op2 = "!!closure"
      then let (t, e) = T.dest_ct t2 in aux renamings' ([],t1) env1 ([],t) e
      else if op1 = "variable"
      then
	let v = T.dest_variable t1 in
	try
	  let v' = apply_ren renamings' v in
	  op2 = "variable" && T.dest_variable t2 = v'
	with _ ->
	  (match T.lookup env1 v with
	    Some (t,e) -> aux renamings' ([],t) e ([],t2) env2
	  | None -> failwith "alpha_equal_closure_terms")
      else if op2 = "variable"
      then
	let v = T.dest_variable t2 in
	try
	  (op1 = "variable"
	     &&
	   apply_ren renamings' (T.dest_variable t1) = v)
	with _ ->
	  (match T.lookup env2 v with
	    Some (t,e) -> aux renamings' ([],t1) env1 ([],t) e
	  | None -> failwith "alpha_equal_closure_terms")
      else
	op1 = op2
	  && B.all2 T.equal_parameters (T.parameters_of_term t1) (T.parameters_of_term t2)
	  && B.all2 (fun x y -> aux renamings' x env1 y env2) (T.brterms_of_term t1) (T.brterms_of_term t2)
  in
  try aux MAP.empty ([],v1) e1 ([],v2) e2
  with _ -> false

let set_int_op  = addListSET ["add"; "subtract"; "multiply"; "divide"; "remainder"] SET.empty
let set_comp_op = addListSET ["less"; "int_eq"] SET.empty
let set_is_op   = addListSET ["isinr"; "isinl"; "ispair"; "isint"; "islambda"; "isatom2"] SET.empty

let member_int_op  element = SET.mem element set_int_op
let member_comp_op element = SET.mem element set_comp_op
let member_is_op   element = SET.mem element set_is_op

let closNextStepEval2 cls lib t principals non_principals env =
  let opid = T.opid_of_term t in
(*val _ = print (opid ^ "\n")*)

  if member_int_op opid
  then
    let ((v1,_),(v2,_)) = B.get2 1 principals in
    M.decr (T.do_primitive_int_op opid v1 v2, em_env, false)

  else if opid = "minus"
  then
    let (v,_) = B.get1 1 principals in
    if T.is_nuprl_term "natural_number" v
    then M.unit (T.mk_nuprl_minus_term v, em_env, false)
    else M.decr (T.do_primitive_minus v, em_env, false)

  else if member_comp_op opid
  then
    let ((v1,_),(v2,_)) = B.get2 2 principals in
    let (t3,t4) = B.get2_0bound 3 non_principals in
    if T.do_primitive_cmp opid v1 v2
    then M.decr (T.rterm2term t3, env, true)
    else M.decr (T.rterm2term t4, env, true)

  else if opid = "atom_eq"
  then
    let n = try T.firstnat t with _ -> 0 in
    let ((v1,_),(v2,_)) = B.get2 4 principals in
    let (t3,t4) = B.get2_0bound 5 non_principals in
    if P.compare_atomn n v1 v2
    then M.decr (T.rterm2term t3, env, true)
    else M.decr (T.rterm2term t4, env, true)

  else if opid = "eq_term"
  then
    let ((v1,e1),(v2,e2)) = B.get2 6 principals in
    if P.is_complete_primitive_value v1
	&&
      P.is_complete_primitive_value v2
    then
      if ct_alpha_equal_closure_terms v1 e1 v2 e2
      then M.decr (T.mk_inl_term T.mk_nuprl_axiom_term, em_env, false)
      else M.decr (T.mk_inr_term T.mk_nuprl_axiom_term, em_env, false)
    else failwith "eq_term"

  else if member_is_op opid
  then
    let (v1,_) = B.get1 7 principals in
    let (t2,t3) = B.get2_0bound 8 non_principals in
    if P.do_primitive_test opid v1
    then M.decr (T.rterm2term t2, env, true)
    else M.decr (T.rterm2term t3, env, true)

  else if opid = "spread"
  then
    let (v1,e1) = B.get1 9 principals in
    let (x,y,b) = B.get1_2bound 10 non_principals in
    let (a1, a2) =
      try T.dest_pair 5 v1
      with _ -> failwith ("spread(" ^ T.opid_of_term v1 ^ ")") in
    M.decr (T.rterm2term b, T.add2env env [(y,a2,e1);(x,a1,e1)], true)

  else if opid = "decide"
  then
    let (v1,e1) = B.get1 11 principals in
    let (x,a,y,b) = B.get2_1bound 12 non_principals in
    if T.is_nuprl_term "inl" v1
    then M.decr (T.rterm2term a, T.add2env env [(x, T.subtermn 1 v1, e1)], true)
    else if T.is_nuprl_term "inr" v1
    then M.decr (T.rterm2term b, T.add2env env [(y, T.subtermn 1 v1, e1)], true)
    else failwith "decide"

  else if opid = "apply"
  then
    if null principals
    then
      (*let _ = print_endline (T.toStringTerm t) in*)
      let (yc,arg) = B.get2_0bound 13 non_principals in
      if T.opid_of_term (T.rterm2term yc) = "ycomb"
      then M.decr (T.mk_apply_ref_term arg (T.mk_rterm t), env, true)
      else failwith "apply"
    else
      let (f,fe) = B.get1 14 principals in
      let arg    = B.get1_0bound 15 non_principals in
      let (x, b) = T.dest_lambda 1 f in
      M.decr (b, T.add2env fe [(x, T.rterm2term arg, env)], true)

  else if opid = "fix"
  then
    let f = B.get1_0bound 16 non_principals in
    M.decr (T.mk_apply_term (T.rterm2term f) t, env, true)

  else if opid = "!wait"
  then
    let (t,_) = B.get1 17 principals in
    let w     = B.get1_0bound 18 non_principals in
    M.decr (T.do_primitive_wait t (T.rterm2term w), env, true)

  else if opid = "callbyvalue"
  then
    let (q,e) = B.get1 19 principals in
    let (x,b) = B.get1_1bound 20 non_principals in
    if P.is_primitive_value q
    then M.decr (T.rterm2term b, T.add2env env [(x, q, e)], true)
    else failwith "callbyvalue"

  else if opid = "callbyvalueall"
  then
    let (q,e) = B.get1 21 principals in
    let (x,b) = B.get1_1bound 22 non_principals in
    if P.is_complete_primitive_value q
    then M.decr (T.rterm2term b, T.add2env env [(x, q, e)], true)
    else failwith ("callbyvalueall:(" ^ T.opid_of_term q ^ ")")

  else if opid = "list_ind"
  then
    let (q,e) = B.get1 23 principals in
    let (nilcase,x,xs,r,conscase) = B.get2_03bound 24 non_principals in
    let opq = T.opid_of_term q in
    if opq = "nil"
    then M.decr (T.rterm2term nilcase, env, true)
    else if opq = "cons"
    then
      let (qa,qb) = T.dest_cons q in
      let qb' = mk_rct (qb,e) in
      let t2  = T.mk_nuprl_list_ind_ref_term qb' nilcase (x,xs,r,conscase) in
      let sub = [(x,qa,e);(xs,qb,e);(r,t2,env)] in
      M.decr (T.rterm2term conscase, T.add2env env sub, true)
    else failwith ("list_ind(" ^ T.toStringTerm t ^ ")\n---")

  else if opid = "ind"
  then
    let (q,e) = B.get1 25 principals in
    let (x,rd,downcase,basecase,y,ru,upcase) = B.get3_202bound 26 non_principals in
    let ord = T.is_zero q in
    let (t',e') =
      if ord = 0
      then (basecase,env)
      else
	let (p,r,w,c) =
	  if ord > 0
	  then (T.dec_integer q,ru,y,upcase)
	  else (T.inc_integer q,rd,x,downcase) in
	let t2 = T.mk_nuprl_ind_ref_term p (x,rd,downcase) basecase (y,ru,upcase) in
	(c, T.add2env env [(w,q,e);(r,t2,env)]) in
    M.decr (T.rterm2term t', e', true)

  else if opid = "rec_ind"
  then
    let (arg,f,x,b) = B.get2_02bound 27 non_principals in
    let b' = T.mk_nuprl_rec_ind_ref_term (T.mk_variable_term x) (f,x,b) in
    let func = T.mk_lambda_term x b' in
    M.decr (T.rterm2term b, T.add2env env [(x,T.rterm2term arg,env);(f,func,env)], true)

  else if opid = "variable"
  then
    match T.lookup env (T.dest_variable t) with
      Some (a,e) -> M.unit (a, e, true)
    | None -> failwith ("variable " ^ T.toStringTerm t)

  else if opid = "!closure"
  then failwith "closure"

  else if opid = "!abstraction"
  then
    let ((v1,u1),(v2,u2),(v3,u3)) = B.get3 28 principals in
    M.unit (T.mk_nuprl_iabstraction_term v2 v3, env, false)

  else if opid = "!library"
  then
    let (q,u) = B.get2_0bound 29 non_principals in
    upd_lib (T.rterm2term u) (T.rterm2term q, env, true)

  else if E.is_termof_term lib t
  then M.decr (E.unfold_tof t, env, true)

  else if E.is_abstraction_term lib t
  then
    let env = if null non_principals then em_env else env in
    let ope = if cls then Some env else None in
    upd_get_found_user (E.ct_unfold_abs ope t, env, true)

  else if null (T.bterms_of_term t)
  then M.unit (t, em_env, false)

  else M.unit (t, env, false)

let m_num_principals opid subterms ((steps,_) as state) =
  if steps < 0
      && opid = "apply"
      && T.is_nuprl_term "ycomb" (T.subterms_n 1 subterms)
  then (0, state)
  else (E.num_principals opid, state)

let clos_lst lst = List.map (fun c -> ([], mct c)) lst

let clos_ref_lst lst = List.map (fun c -> ([], T.mk_rterm (mct c))) lst

let clos_refs lst = List.map (fun c -> ([], T.mk_rterm (mk_rct c))) lst

(* EVALUATOR2 - closure conversion -- no monad *)
let evaluator2' term state =

  let rec evalList cbva lst env state =
    match lst with
      [] -> ([], state)
    | (vars,rterm)::rest ->
	let term    = T.rterm2term rterm in
	let (p,s1)  = eval (term, env) state in
	let (q,s2)  = if cbva then evalAll p s1 else (p,s1) in
	let (vs,s3) = evalList cbva rest env s2 in
	(q::vs,s3)

  and eval (t, env) state =
    if T.is_ct t
    then eval (T.dest_ct t) state
    else
      (*let _ = print_endline ("[------" ^ T.opid_of_term t ^ "------]") in*)
      let ((opid,params),subterms) = T.dest_term t in
      let (n,s1) = m_num_principals opid subterms state in
      let (p,np) = B.split n subterms in
      (*let _ = print_endline ("[------"
			     ^ T.opid_of_term t
			     ^ "--"
			     ^ string_of_int (List.length p)
			     ^ "--"
			     ^ string_of_int (List.length np)
			     ^ "------]") in*)
      let (c,((_,(lib,cls)) as s2)) = evalList (E.is_eval_all opid) p env s1 in
      let ((t',e',ev),s3) = closNextStepEval2 cls lib t c np env s2 in
      if ev
      then eval (t',e') s3
      else ((t',e'),s3)

  and evalAll (t, env) state =
    if T.is_ct t
    then evalAll (T.dest_ct t) state
    else
      let ((opid,params) as opr,subterms) = T.dest_term t in
      let (principals,nprincipals) = B.split (E.num_principal_all opid) subterms in
      let env' = if null nprincipals then em_env else env in
      let (c,s) = evalList true principals env state in
      ((T.mk_nuprl_ref_term opr ((clos_refs c) @ nprincipals), env'),s)

  in
  if T.is_ct term
  then eval (T.dest_ct term) state
  else eval (term, em_env) state

let evaluator2 cls lib steps term =
  let _ = print_endline "[starting evaluation]" in
  let ((t',e'),(n,_)) = evaluator2' term (steps,(lib,cls)) in
  let answer =
    if cls && T.is_nuprl_pair_term t'
    then
      let (s,msgs) = T.dest_pair 8 t' in
      let msgs' = T.close msgs e' in
      T.mk_pair_term (T.mk_rct (s, e')) msgs'
    else T.close t' e' in
  let _ = print_endline "[evaluation done]" in
  (answer, steps - n)
