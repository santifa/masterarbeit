open Colors
open Prelude
open RaftReplicaEx
open RsaKeyFun
open Core
open Test
open Raft
(* test the boot up of the system and the first leader election*)

(* reorder the queue that timer messages put to the back *)
let rec reorder (msgs : directedMsgs) : directedMsgs =
  match msgs with
  | [] -> []
  | x :: xs ->
    match (Obj.magic x.dmMsg), (Obj.magic x.dmDelay) with
    | Timer_msg _, 50 -> x :: xs
    | Timer_msg _, _ -> xs @ [x]
    | _ -> x :: reorder xs

class ['a, 'b, 'c, 'd] raft c t = object(self)
  inherit ['a, 'b, 'c, 'd] test_simulator c t

  method create_replicas =
    let (r, msg) = to_replica_w_init 0 in
    let (r', msg') = to_replica_w_init 1 in
    let (r'', msg'') = to_replica_w_init 2 in
    let (r''', msg''') = to_replica_w_init 3 in
    replicas#set_replicas [r; r'; r''; r'''];
    msg @ msg' @ msg'' @ msg'''

  method get_dsts dm = dm.dmDst

  method change_dst dm ids =
    { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay }

  method msgs2string (msgs : directedMsgs) : string = msgs2string msgs

  method is_response dm = response dm

  method run_sm dm rep = rsm dm rep

  method run_replicas (inflight : 'c list) : ('c list * 'c list) =
  (* check if there is some message in queue *)
  match inflight with
  | [] ->
    log_info "Main" "All messages processed stopping";
    ([], []) (* we reached the end of the simulation round *)
  | dm :: dms ->
    (* we have some message and now we iterate through all its destinations *)
    match (self#get_dsts dm)(* dm.dmDst *) with
    (* restart loop if there a no destinations *)
    | [] -> self#run_replicas dms
    | id :: ids ->
      log_msgs "Procesing" (self#msgs2string [dm]) (* ((print_dmsgs [dm]) "") *);
      (* create a new message without the taken id *)
      let dm' = self#change_dst dm ids (* { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } *) in
      (* find the replica mathing the id *)
      match replicas#find_replica id with
      | None ->
        let failed_to_deliver = self#change_dst dm [id] in
        let resp = self#get_response [failed_to_deliver] in
        (* requeue message which failed to deliver ? *)
        let (response, failed) = self#run_replicas (dm' :: dms) in
        (match resp with
         | None -> (response, failed_to_deliver :: failed)
         | Some resp' -> (resp' :: response, failed))

      | Some rep ->
        (* we have found the replica *)
        (* run the state machine on the message input *)
        let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
        (* *          let (rep',dmsgs) = self#run_sm dm rep (* (Obj.magic dm.dmMsg) *) in *)
        log_state (coq2string (name2string id)) (coq2string (state2string rep'.sm_state));
        replicas#replace_replica id rep';
        (* (message without current replica) :: (next messages) @ (newly created messages) *)
        let f' = reorder (dmsgs @ dm' :: dms) in
        let (response, failed) = self#run_replicas f' in
        (response, failed)
end

(* This runs forever so run with $ ... | head -n 100 to see the heartbeat *)
let init (responses : directedMsgs) : directedMsgs =
  match responses with
  | [] -> log_test_failed "Initialitation failed." "Non-empty queue"; []
  | dm :: msgs ->
    match (Obj.magic dm.dmMsg) with
    | Init_msg _ -> responses
    | Timer_msg _ -> responses
    | _ -> log_test_failed "The initialitation failed" "Wrong messages"; []

let _ =
  let t = [("Test Init", init)] in
  let c = new raft {
    version = "1.0";
    protocol = "Raft";
    client_id = 0;
    private_key = (* lookup_client_sending_key *) (Obj.magic 0);
    primary = Obj.magic (Replica (Obj.magic 0)) (* type: name *);
    timer = 1;
  } t in
  c#run
