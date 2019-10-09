open Colors
open Prelude
open RaftReplicaEx
open RsaKeyFun
open Core
open Test
(* define the basics for the protocol *)

(* generate number between 150 and 300 *)
let rand n =
  Random.init n;
  150 + Random.int 150

(* convert internals to strings *)
let s2string state = coq2string (state2string (sm_state state))

let msgs2string msgs = coq2string (directedMsgs2string msgs)

let node2string name = coq2string (name2string name)

(* create a leader node for tests *)
let to_leader n =
  let node = leader_replica (Obj.magic n) in
  let timer = Timer_msg timer0 in
  let (node', d) = lrun_sm  node (Obj.magic timer) in
  log_msgs "Leader" (msgs2string d);
  (* let msg = { dmMsg = Obj.magic timer; dmDst = [d]; dmDelay = 0 } in *)
  ({ id = Obj.magic (Replica (Obj.magic n)); replica = node' }, d)

(* create a normal node without any initialization *)
let to_replica n =
  let node = local_replica (Obj.magic n) in
  (* let init = Init_msg (rand n) in
   * let (node', d) = lrun_sm (node (Obj.magic n)) (Obj.magic init) in
   * log_msgs "Main" (msgs2string d); *)
  { id = Obj.magic (Replica (Obj.magic n)); replica = node }

let mk_init n =
  let init = Init_msg (rand n) in
  { dmMsg = Obj.magic init; dmDst = [Obj.magic (Replica (Obj.magic n))]; dmDelay = 0 }

(* create a normal node with initialization message *)
let to_replica_w_init n =
  let node = local_replica (Obj.magic n) in
  let init = mk_init n in
  (* let (node', d) = lrun_sm node (Obj.magic init) in *)
  (* log_msgs "Main" (msgs2string d); *)
  ({ id = Obj.magic (Replica (Obj.magic n)); replica = node }, [init])

(* test if the first message is a client message *)
let response (msg : directedMsg) : bool =
  match msg.dmDst with
  | [] -> false
  | dst :: _ ->
    match (Obj.magic dst) with
    | Client _ -> true
    | _ -> false

let cdest dm ids = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay }

let rsm dm rep =
  let (rep', dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
  log_state ((node2string (Obj.magic rep.id)) ^ "(new)") (s2string rep');
  (rep', dmsgs)
