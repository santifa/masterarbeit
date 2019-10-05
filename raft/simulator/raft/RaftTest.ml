open Colors
open Prelude
open RaftReplicaEx
open RsaKeyFun
open Core
open Test

(* generate number between 150 and 300 *)
let rand n =
  Random.init n;
  150 + Random.int 150

let s2string state = coq2string (state2string (sm_state state))

let msgs2string msgs = coq2string (directedMsgs2string msgs)

let node2string name = coq2string (name2string name)

let to_leader n =
  let node = leader_replica (Obj.magic n) in
  let dest = [Obj.magic (Replica (Obj.magic 1));
              Obj.magic (Replica (Obj.magic 2));
              Obj.magic (Replica (Obj.magic 3))] in
  let heartbeat = Append_entries_msg Heartbeat in
  let msg = { dmMsg = Obj.magic heartbeat; dmDst = dest; dmDelay = 0 } in
  ({ id = Obj.magic (Replica (Obj.magic n)); replica = node }, [msg])

let to_replica n =
  let node = local_replica (Obj.magic n) in
  (* let init = Init_msg (rand n) in
   * let (node', d) = lrun_sm (node (Obj.magic n)) (Obj.magic init) in
   * log_msgs "Main" (msgs2string d); *)
  ({ id = Obj.magic (Replica (Obj.magic n)); replica = node }, [])

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
    let (r, msg) = to_leader 0 in
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
    (* log_state ((node2string (Obj.magic rep.id)) ^ "(old)") (s2string rep.replica); *)
    let (rep', dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
    log_state ((node2string (Obj.magic rep.id)) ^ "(new)") (s2string rep');
    (rep', dmsgs)
end

(* let init (responses : directedMsgs) : directedMsgs =
 *   match responses with
 *   | [] -> log_test_failed "Initialitation failed." "Empty queue"; []
 *   | dm :: msgs ->
 *     match (Obj.magic dm.dmMsg) with
 *     | Timer_msg _ -> responses
 *     | _ ->
 *       let register = Register_msg (Obj.magic 0) in
 *       responses @ ({ dmMsg = Obj.magic register; dmDst = [Obj.magic (Replica (Obj.magic 0))]; dmDelay = 0 } :: []) *)

(* test that a client can register itself at the network *)
let test_register (responses : directedMsgs) : directedMsgs =
  match responses with
  | [] -> log_test_failed "No response" ""; []
  | dm :: msgs ->
    match (Obj.magic dm.dmMsg) with
    | Register_result_msg res ->
      log_test_success ("Register " ^ (coq2string (result2string res))); []
    | Append_entries_msg (Heartbeat) ->
      let dest = [Obj.magic (Replica (Obj.magic 0))] in
      let register = Register_msg (Obj.magic 0) in
      responses @ ({ dmMsg = Obj.magic register; dmDst = dest; dmDelay = 0 } :: [])
    | _ -> log_test_failed "Wrong response" ""; []

let request s = Client_request ((Obj.magic 0), (Obj.magic s), (Obj.magic 1), (Obj.magic 1))
(* A request should be dropped if the session is not valid *)
let test_unregistered (responses : directedMsgs) : directedMsgs =
  match responses with
  | _ ->
    let request_msg = Request_msg (request 0) in
    let dest = [Obj.magic (Replica (Obj.magic 0))] in
    responses @ ({ dmMsg = Obj.magic request_msg; dmDst = dest; dmDelay = 0 } :: [])

let test_replication (responses : directedMsgs) : directedMsgs =
  match responses with
  | [] -> log_test_failed "No response" ""; []
  | dm :: msgs ->
    match (Obj.magic dm.dmMsg) with
    (* register client *)
    | Append_entries_msg (Heartbeat) ->
      let dest = [Obj.magic (Replica (Obj.magic 0))] in
      let register = Register_msg (Obj.magic 0) in
      responses @ ({ dmMsg = Obj.magic register; dmDst = dest; dmDelay = 0 } :: [])
    (* upon register result send request *)
    | Register_result_msg (Register_client_res (r, s, l)) ->
      if r then begin
        let request_msg = Request_msg (request s) in
        let dest = [Obj.magic l] in
        msgs @ ({ dmMsg = Obj.magic request_msg; dmDst = dest; dmDelay = 0 } :: [])
      end else begin log_test_failed "Registering failed" ""; [] end
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
