open Prelude
open PbReplicaEx
open Core
open Simulator

(* convert the node name to string *)
let node2string n =
  match (Obj.magic n) with
  | PBprimary -> "Primary "
  | PBbackup -> "Backup "
  | PBc -> "Client "

(* create a new replica *)
let to_replica n =
  log_info "Main" ("Starting " ^ (String.of_char_list (name2string n)));
  { id = Obj.magic n; replica = local_replica (Obj.magic n) }

let print_dmsgs msgs =
  List.fold_right ~f:(fun acc x -> x ^ ":" ^ acc)
    (List.map ~f:(fun x -> (String.of_char_list (directedMsg2string x))) msgs)

let print_msg msg = String.of_char_list (msg2string (Obj.magic msg))

let print_node node = node2string node

let print_state state = String.of_char_list (state2string (sm_state state))

let get_response (msgs : directedMsgs) : directedMsgs =
  match msgs with
  | [] -> []
  (* only check the first msg *)
  | msg :: _ ->
    match msg.dmDst with
    | [] -> []
    | dst :: _ ->
      match (Obj.magic dst) with
      | PBc -> [msg]
      | _ -> []

(* implement the virtual simulator *)
class ['a, 'b, 'c, 'd] pb c = object(self)
  inherit ['a, 'b, 'c, 'd] simulator c

  (* create the replication system with one primary and three backups *)
  method create_replicas =
    replicas#set_replicas [to_replica PBprimary; to_replica PBbackup]

  method msgs2string (msgs : directedMsgs) : string = print_dmsgs msgs ""

  method run_replicas (inflight : directedMsgs) : (directedMsgs * directedMsgs) =
  (* check if there is some message in queue *)
  match inflight with
  | [] ->
    log_info "Main" "All messages processed stopping";
    ([], []) (* we reached the end of the simulation round *)
  | dm :: dms ->
    (* we have some message and now we iterate through all its destinations *)
    match dm.dmDst with
    (* restart loop if there a no destinations *)
    | [] -> self#run_replicas dms
    | id :: ids ->
      log_msgs "Procesing" ((print_dmsgs [dm]) "");
      (* create a new message without the taken id *)
      let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
      (* find the replica mathing the id *)
      match replicas#find_replica id with
      | None ->
        let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
        let resp = get_response [failed_to_deliver] in
        (* requeue message which failed to deliver ? *)
        let (response, failed) = self#run_replicas (dm' :: dms) in
        if List.is_empty resp then begin
          log_err "Main" ("Couldn't find id " ^ print_node id);
          (response, failed_to_deliver :: failed)
        end else (resp @ response, failed)

      | Some rep ->
        (* we have found the replica *)
        log_msgs ((print_node rep.id) ^ "got") (print_msg dm.dmMsg);
        (* run the state machine on the message input *)
        let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
        log_state (print_node id ^ "State transistion completed")
          ("Send " ^ ((print_dmsgs dmsgs) ""));
        (* let resp = get_response dmsgs in *)
        (* replace the state machine of the replica *)
        log_state (print_node id) (print_state rep');
        replicas#replace_replica id rep';
        (* (message without current replica) :: (next messages) @ (newly created messages) *)
        let (response, failed) = self#run_replicas (dm' :: dms @ dmsgs) in
        (response, failed)

  method client (response : directedMsgs) : directedMsgs =
    match response with
    | [] ->
    (* create a simple PNinput request *)
    let req = PBinput 10 in
    (* create a message list with the primary as destination *)
    [{ dmMsg = Obj.magic req; dmDst = [c.primary]; dmDelay = 0 }]
    | rsp :: rsps ->
      match (Obj.magic rsp.dmMsg) with
      | PBreply 10 ->  log_test "correct" "The primary node returned the correct result";
        []
      | _ ->   log_err "failed" ("Got the wrong result" ^ self#msgs2string [rsp]);
        [] (* do nothing if we recieve some result *)
end

let _ =
  (* create a new primary backup simulation *)
  let c = new pb {
    version = "1.0";
    protocol = "PB";
    client_id = 0;
    private_key = Obj.magic 0(* ignore this one *);
    primary = Obj.magic PBprimary; (* type: name *)
    timer = 1;
  } in
  c#run
