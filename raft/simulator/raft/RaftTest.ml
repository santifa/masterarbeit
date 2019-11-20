open Colors
open Prelude
open RaftReplicaEx
open RsaKeyFun
open Core
open Test
open Raft

(* The file contains basic tests which need a faked
 * leader state *)
class ['a, 'b, 'c, 'd] raft c t = object(self)
  inherit ['a, 'b, 'c, 'd] test_simulator c t

  method create_replicas =
    let (r, msg) = to_leader 0 in
    replicas#set_replicas [r; to_replica 1; to_replica 2; to_replica 3];
    msg

  method get_dsts dm = dm.dmDst

  method change_dst dm ids =
    { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay }

  method msgs2string (msgs : directedMsgs) : string = msgs2string msgs

  method is_response dm = response dm

  method run_sm dm rep = rsm dm rep
end

(* test that a client can register itself at the network *)
let test_register (responses : directedMsgs) : directedMsgs =
  match responses with
  | [] -> log_test_failed "No response" ""; []
  | dm :: msgs ->
    match (Obj.magic dm.dmMsg) with
    (* | Timer_msg _ -> responses *)
    | Register_result_msg res ->
      log_test_success ("Register " ^ (coq2string (result2string res))); []
    | Append_entries_msg (Heartbeat (_, _, _, _, _)) ->
      let dest = [Obj.magic (Replica (Obj.magic 0))] in
      let register = Register_msg (Obj.magic 0) in
      ({ dmMsg = Obj.magic register; dmDst = dest; dmDelay = 0 } :: [])
    | _ -> log_test_failed "Wrong response" ""; []

let request s = Client_request ((Obj.magic 0), (Obj.magic s), (Obj.magic 1), (Obj.magic 1))
(* A request should be dropped if the session is not valid
 * Since nothing is returned the method can not check anything *)
let test_unregistered (responses : directedMsgs) : directedMsgs =
  match responses with
  | _ ->
    let request_msg = Request_msg (request 0) in
    let dest = [Obj.magic (Replica (Obj.magic 0))] in
    ({ dmMsg = Obj.magic request_msg; dmDst = dest; dmDelay = 0 } :: [])

let test_replication (responses : directedMsgs) : directedMsgs =
  match responses with
  | [] -> log_test_failed "No response" ""; []
  | dm :: msgs ->
    match (Obj.magic dm.dmMsg) with
    (* register client *)
    | Append_entries_msg (Heartbeat (_, _, _, _, _)) ->
      let dest = [Obj.magic (Replica (Obj.magic 0))] in
      let register = Register_msg (Obj.magic 0) in
      ({ dmMsg = Obj.magic register; dmDst = dest; dmDelay = 0 } :: [])
    (* upon register result send request *)
    | Register_result_msg (Register_client_res (r, s, l)) ->
      if r then begin
        let request_msg = Request_msg (request s) in
        let dest = [Obj.magic l] in
        msgs @ ({ dmMsg = Obj.magic request_msg; dmDst = dest; dmDelay = 0 } :: [])
      end else begin log_test_failed "Registering failed" ""; [] end
    | Register_result_msg (Client_res (r, s)) ->
      log_test_success ("Result is " ^ (Int.to_string (Obj.magic s))); []
    | _ -> log_test_failed "Request failed" ""; []

let _ =
  let t = [("Test Register", test_register);
           ("Test if unregistered", test_unregistered);
           ("Test log replication", test_replication)] in
  let c = new raft {
    version = "1.0";
    protocol = "Raft";
    client_id = 0;
    private_key = (* lookup_client_sending_key *) (Obj.magic 0);
    primary = Obj.magic (Replica (Obj.magic 0)) (* type: name *);
    timer = 1;
  } t in
  c#run
