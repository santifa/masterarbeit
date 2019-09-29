open Colors
open Prelude
open PbReplicaEx
open RsaKeyFun
open Core
open Simulator

(* create a new replica *)
let to_replica n =
  (* log_info "Main" ("Starting " ^ (String.of_char_list (name2string n))); *)
  { id = Obj.magic n; replica = local_replica (Obj.magic n) }

let node2string node =  coq2string (name2string node)

let s2string state = coq2string (state2string (sm_state state))

let msgs2string msgs = coq2string (directedMsgs2string msgs)

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

  method msgs2string (msgs : directedMsgs) : string = msgs2string msgs

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
      log_msgs "Procesing" (self#msgs2string [dm]);
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
          log_err "Main" ("Couldn't find id " ^ node2string (Obj.magic id));
          (response, failed_to_deliver :: failed)
        end else (resp @ response, failed)

      | Some rep ->
        (* we have found the replica *)
        (* log_msgs ((node2string (Obj.magic rep.id)) ^ "got") (msgs2string [dm.dmMsg]); *)
        (* run the state machine on the message input *)
        let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
        log_state ((node2string (Obj.magic id)) ^ "State transistion completed")
          ("Send " ^ (msgs2string dmsgs));
        (* let resp = get_response dmsgs in *)
        (* replace the state machine of the replica *)
        log_state (node2string (Obj.magic id)) (s2string rep');
        replicas#replace_replica id rep';
        (* (message without current replica) :: (next messages) @ (newly created messages) *)
        let (response, failed) = self#run_replicas (dm' :: dms @ dmsgs) in
        (response, failed)

  method client (response : directedMsgs) : directedMsgs =
    match response with
    | [] ->
      (* generate request number *)
      let rand = Random.int 20 in
      (* create a simple PNinput request *)
      let req = PBinput rand in
      (* create a message list with the primary as destination *)
      [{ dmMsg = (Obj.magic req); dmDst = [c.primary]; dmDelay = 0 }]
    | _ ->
      []
end

let _ =
  (* create a new primary backup simulation *)
  let c = new pb {
    version = "1.0";
    protocol = "PB";
    client_id = 0;
    private_key = lookup_client_sending_key (Obj.magic 0);
    primary = Obj.magic PBprimary; (* type: name *)
    timer = 1;
  } in
  c#run
