open Prelude
open PbReplicaEx
open Core
open Test

(* create a new replica *)
let to_replica n =
  { id = Obj.magic n; replica = local_replica (Obj.magic n) }

let node2string node =  coq2string (name2string node)

let s2string state = coq2string (state2string (sm_state state))

let msgs2string msgs = coq2string (directedMsgs2string msgs)

let response (msg : directedMsg) : bool =
  match msg.dmDst with
  | [] -> false
  | dst :: _ ->
    match (Obj.magic dst) with
    | PBc -> true
    | _ -> false

(* implement the virtual simulator *)
class ['a, 'b, 'c, 'd] pb c t = object(self)
  inherit ['a, 'b, 'c, 'd] test_simulator c t

  (* create the replication system with one primary and three backups *)
  method create_replicas =
    replicas#set_replicas [to_replica PBprimary; to_replica PBbackup]

  method msgs2string (msgs : directedMsgs) : string = msgs2string msgs

  method change_dst dm ids =
    { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay }

  method get_dsts dm = dm.dmDst

  method is_response dm = response dm

  method run_sm dm rep =
    log_state ((node2string (Obj.magic rep.id)) ^ "(old)") (s2string rep.replica);
    let (rep', dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
    log_state ((node2string (Obj.magic rep.id)) ^ "(new)") (s2string rep');
    (rep', dmsgs)
end

let response_eq responses =
  match responses with
  | [] ->
    (* create a simple PNinput request *)
    let req = PBinput 10 in
    (* create a message list with the primary as destination *)
    [{ dmMsg = Obj.magic req; dmDst = [Obj.magic PBprimary]; dmDelay = 0 }]
  | rsp :: rsps ->
    match (Obj.magic rsp.dmMsg) with
    | PBreply 10 ->  log_test_success "The primary node returned the correct result";
      []
    | _ ->   log_test_failed "Should be 10" (msgs2string [rsp]);
      [] (* do nothing if we recieve some result *)

let response_uneq responses =
  match responses with
  | [] ->
    (* create a simple PNinput request *)
    let req = PBinput 9 in
    (* create a message list with the primary as destination *)
    [{ dmMsg = Obj.magic req; dmDst = [Obj.magic PBprimary]; dmDelay = 0 }]
  | rsp :: rsps ->
    match (Obj.magic rsp.dmMsg) with
    | PBreply 10 ->  log_test_success "The network returned the correct result";
      []
    | _ ->   log_test_failed "Should be 10" (msgs2string [rsp]);
      [] (* do nothing if we recieve some result *)

let _ =
  (* create a new primary backup simulation *)
  let t = [response_eq; response_uneq] in
  let c = new pb {
    version = "1.0";
    protocol = "PB";
    client_id = 0;
    private_key = Obj.magic 0(* ignore this one *);
    primary = Obj.magic PBprimary; (* type: name *)
    timer = 1;
  } t in
  c#run 
