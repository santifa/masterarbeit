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
  List.fold_right ~f:(fun acc x -> x ^ ":" ^ acc) (List.map ~f:(fun x -> (String.of_char_list (directedMsg2string x))) msgs)

let print_msg msg =
  String.of_char_list (msg2string (Obj.magic msg))

let print_node node =
  node2string node

let print_state state =
  String.of_char_list (state2string (sm_state state))

(* implement the virtual simulator *)
class ['a, 'b, 'c, 'd] pb c = object(self)
  inherit ['a, 'b, 'c, 'd] simulator c

  (* create the replication system with one primary and three backups *)
  method create_replicas =
    replicas#set_replicas [to_replica PBprimary; to_replica PBbackup]

  (* create a client request *)
  method mk_request (timestamp : int) (request : int) =
    PBinput request

  method run_replicas (inflight : directedMsgs) : directedMsgs =
  log_msgs "Queue" ((print_dmsgs inflight) "");
  (* check if there is some message in queue *)
  match inflight with
  | [] ->
    log_info "Main" "All messages processed stopping";
    []
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
        log_err "Main" ("Couldn't find id " ^ print_node id);
        let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
        (* requeue message which failed to deliver ? *)
        failed_to_deliver :: self#run_replicas (dm' :: dms)
      | Some rep ->
        (* we have found the replica *)
        log_msgs ((print_node rep.id) ^ "got") (print_msg dm.dmMsg);
        (* run the state machine on the message input *)
        let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
        log_state (print_node id ^ "State transistion completed") ("Send " ^ ((print_dmsgs dmsgs) ""));
        (* replace the state machine of the replica *)
        log_state (print_node id) (print_state rep');
        replicas#replace_replica id rep';
        (* (message without current replica) :: (next messages) @ (newly created messages) *)
        self#run_replicas (dm' :: dms @ dmsgs)

  (* run the client recursively
   * timestamp - is the current term and gets inc every round
   * max - the maximum rounds to go
   * avg - an ongoing calculated average
   * printing_period - the number of timestamps before printing some results *)
  method run_client timestamp max avg printing_period =
    (* generate request number *)
    let rand = Random.int 20 in
    (* create a simple PNinput request *)
    let req = self#mk_request (Obj.magic timestamp) rand in
    (* create a message list with the primary as destination *)
    let inflight = [{ dmMsg = Obj.magic req; dmDst = [c.primary]; dmDelay = 0 }] in
    (* start monitoring the system time *)
    log_info "Client sends" (String.of_char_list (directedMsgs2string inflight));
    let t = Prelude.Time.get_time () in
    (* deliver the messages *)
    let failed_to_deliver = self#run_replicas inflight in
    (* stop monitoring the system *)
    let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
    (* calculate the average *)
    let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
    (* print the messages which failed to deliver as string *)
    let s = Batteries.String.of_list (directedMsgs2string failed_to_deliver) in
    (match s with
     | "" -> ()
     | s' -> log_err "Main" ("Failed to deliver " ^ s'));
    (* print some results if the time is right *)
    (if timestamp mod printing_period = 0 then
       log_res "Main" timestamp d new_avg
     else ());
    (* restart the client if there are more rounds to go *)
    if timestamp < max then
      self#run_client (timestamp + 1) max new_avg printing_period
    else ()
end

let _ =
  (* create a new primary backup simulation *)
  let c = new pb {
    version = "1.0";
    protocol = "PB";
    client_id = 0;
    private_key = Obj.magic 0(* lookup_client_sending_key (Obj.magic 0) *);
    primary = Obj.magic PBprimary; (* type: name *)
    timer = 1;
  } in
  c#run
