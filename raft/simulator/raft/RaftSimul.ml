open Colors
open Prelude
open RsaKeyFun
open Core
open Simulator
open RaftReplicaEx

(* generate number between 150 and 300 *)
let rand n =
  Random.init n;
  150 + Random.int 150

let print_state state = coq2string (state2string (sm_state state))

let to_replica n =
  let init = Init_msg (rand n) in
  let (node', d) = lrun_sm (local_replica (Obj.magic n)) (Obj.magic init) in
  ({ id = Obj.magic (Replica (Obj.magic n)); replica = node' }, d)

(* let destination2string (n : name) : string =
 *   match Obj.magic n with
 *   | Replica r -> "R(" ^ string_of_int (Obj.magic r) ^ ")"
 *   | Client c -> "C(" ^ string_of_int (Obj.magic c) ^ ")";; *)

let mk_request id request =
  let cmd = 12 in
  let client = Obj.magic id in
  Request_msg (Client_request (client, 1, request, (Obj.magic cmd)))

let is_response (msg : directedMsg) : bool =
  match msg.dmDst with
  | [] -> false
  | dst :: _ ->
    match (Obj.magic dst) with
    | Client _ -> true
    | _ -> false

let get_response (msgs : directedMsgs) : directedMsg option =
  match msgs with
  | [] -> None
  | msg :: _ ->
    if is_response msg then Some msg else None

(* reorder the queue that timer messages put to the back *)
let rec reorder (msgs : directedMsgs) : directedMsgs =
  match msgs with
  | [] -> []
  | x :: xs ->
    match (Obj.magic x.dmMsg) with
    | Timer_msg _ -> xs @ [x]
    | _ -> x :: reorder xs

class ['a, 'b, 'c, 'd] raft c = object(self)
  inherit ['a, 'b, 'c, 'd] simulator c

  method create_replicas =
    let (n0, d0) = to_replica 0 in
    let (n1, d1) = to_replica 1 in
    let (n2, d2) = to_replica 2 in
    let (n3, d3) = to_replica 3 in
    replicas#set_replicas [n0; n1; n2; n3];
    d0 @ d1 @ d2 @ d3

  method msgs2string msgs = coq2string (directedMsgs2string msgs)

  method run_replicas (inflight : directedMsgs) : (directedMsgs * directedMsgs) =
    (* log_msgs "Queue" (coq2string (directedMsgs2string inflight)); *)
    match inflight with
  | [] ->
    log_info "Main" "All messages processed stopping";
    ([], []) (* we reached the end of the simulation round *)
  | dm :: dms ->
    (* we have some message and now we iterate through all its destinations *)
    match dm.dmDst(* dm.dmDst *) with
    (* restart loop if there a no destinations *)
    | [] -> self#run_replicas dms
    | id :: ids ->
      log_msgs "Procesing" (self#msgs2string [dm]) (* ((print_dmsgs [dm]) "") *);
      (* create a new message without the taken id *)
      let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
      (* find the replica mathing the id *)
      match replicas#find_replica id with
      | None ->
        let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
        let resp = get_response [failed_to_deliver] in
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
(* match inflight with
 *     | [] -> ([], [])
 *     | dm :: dms ->
 *       match dm.dmDst with
 *       | [] -> self#run_replicas dms
 *       | id :: ids ->
 *         log_msgs "Procesing" (coq2string (directedMsg2string dm));
 *         let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
 *         match replicas#find_replica id with
 *         | Some rep ->
 *           log_info (destination2string id ^ " | Input message")
 *             (coq2string (msg2string (Obj.magic dm.dmMsg)));
 *           (* log_state "Main" (coq2string (state2string rep.replica.sm_state)); *)
 *           let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
 *           (* print_info (kCYN) "Done" ""; *)
 *           replicas#replace_replica id rep';
 *           log_state "Main" (coq2string (state2string rep'.sm_state));
 *           self#run_replicas (dm' :: dms @ dmsgs)
 *         | None ->
 *           log_err  "Main" ("Couldn't find id " ^ destination2string id);
 *           let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
 *           ([], [failed_to_deliver]) :: self#run_replicas (dm' :: dms) *)

  method client (responses : directedMsgs) : directedMsgs =
    log_msgs "Client" (coq2string (directedMsgs2string responses));
    match responses with
    | [] -> []
    | x :: xs ->
      match (Obj.magic x.dmMsg) with
      | Init_msg _ -> responses (* return if the system still boots up *)
      | Timer_msg _ -> responses (* ignore timer messages for nodes *)
      | _ -> []

  (* method run_client timestamp max avg printing_period =
   *   (* register some client *)
   *   let register = Register_msg (Obj.magic conf.client_id) in
   *   let inflight = [{ dmMsg = Obj.magic register; dmDst = [c.primary]; dmDelay = 0 }] in
   *   print_info (kBLU) "Start" (char_list2string (directedMsgs2string inflight));
   *   let failed_to_deliver = self#run_replicas inflight in
   *   (* execute some request **)
   *   let req = self#mk_request (Obj.magic timestamp) 17 in
   *   let inflight = [{ dmMsg = Obj.magic req; dmDst = [c.primary]; dmDelay = 0 }] in
   *   let t = Prelude.Time.get_time () in
   *   print_info (kBLU) "Start" (char_list2string (directedMsgs2string inflight));
   *   let failed_to_deliver = failed_to_deliver @ (self#run_replicas inflight) in
   *   let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
   *   let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
   *   (match failed_to_deliver with
   *    | [] -> ()
   *    | s' -> print_err (char_list2string (directedMsgs2string s')) ~case:"Failed to deliver: " ());
   *   (if timestamp mod printing_period = 0 then
   *      print_res timestamp d new_avg
   *    else ());
   *   if timestamp < max then
   *     self#run_client (timestamp + 1) max new_avg printing_period
   *   else () *)
end

let _ =
  let c = new raft {
    version = "1.0";
    protocol = "Raft";
    client_id = 0;
    private_key = lookup_client_sending_key (Obj.magic 0);
    primary = Obj.magic (Replica (Obj.magic 0)) (* type: name *);
    timer = 1;
  } in
  c#run
