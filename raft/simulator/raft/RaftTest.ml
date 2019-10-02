open Colors
open Prelude
open RaftReplicaEx
open RsaKeyFun
open Core
open Test

let s2string state = coq2string (state2string (sm_state state))

let msgs2string msgs = coq2string (directedMsgs2string msgs)

let node2string name = coq2string (name2string name)

let to_replica n =
  let node = local_replica in
  let init = Init_msg n in
  let (node', d) = lrun_sm (node (Obj.magic n)) (Obj.magic init) in
  log_msgs "Main" (msgs2string d);
  ({ id = Obj.magic (Replica (Obj.magic n)); replica = node' }, d)

(* let to_leader n = { id = Obj.magic (Replica (Obj.magic n));
 *                      replica = local_replica true (Obj.magic n) } *)

let response (msg : directedMsg) : bool =
  match msg.dmDst with
  | [] -> false
  | dst :: _ ->
    match (Obj.magic dst) with
    | Client _ -> true
    | _ -> false

class ['a, 'b, 'c, 'd] raft c t = object(self)
  inherit ['a, 'b, 'c, 'd] test_simulator c t

  method create_replicas =
    let (r, msg) = to_replica 0 in
    let (r', msg') = to_replica 1 in
    let (r'', msg'') = to_replica 2 in
    let (r''', msg''') = to_replica 3 in
    replicas#set_replicas [r; r'; r''; r'''];
    msg @ msg' @ msg'' @ msg'''

  method get_dsts dm = dm.dmDst

  method change_dst dm ids = 
    { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay }

  method msgs2string (msgs : directedMsgs) : string = msgs2string msgs

  method is_response dm = response dm

  method run_sm dm rep =
    log_state ((node2string (Obj.magic rep.id)) ^ "(old)") (s2string rep.replica);
    let (rep', dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
    log_state ((node2string (Obj.magic rep.id)) ^ "(new)") (s2string rep');
    (rep', dmsgs)
end

let init (responses : directedMsgs) : directedMsgs =
  match responses with
  | [] -> log_test_failed "Initialitation failed." "Empty queue"; []
  | dm :: msgs ->
    match (Obj.magic dm.dmMsg) with
    | _ ->
      let register = Register_msg (Obj.magic 0) in
      responses @ ({ dmMsg = Obj.magic register; dmDst = [Obj.magic (Replica (Obj.magic 0))]; dmDelay = 0 } :: [])

let _ =
  let t = [init] in
  let c = new raft {
    version = "1.0";
    protocol = "Raft";
    client_id = 0;
    private_key = (* lookup_client_sending_key *) (Obj.magic 0);
    primary = Obj.magic (Replica (Obj.magic 0)) (* type: name *);
    timer = 1;
  } t in
  c#run
