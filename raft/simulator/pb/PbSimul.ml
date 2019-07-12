open Colors
open Prelude
open PbReplicaEx
open RsaKeyFun
open Core
open Simulator

(* turn this to false if you don't want to sign messages *)
let signing : bool ref = ref true

(* convert the node name to string *)
let node2string n =
  match (Obj.magic n) with
  | PBprimary -> "Primary "
  | PBbackup -> "Backup "
  | _ -> "Other "

(* create a new replica *)
let to_replica n =
  print_info (kBLU) "Main" ("Starting " ^ (String.of_char_list (name2string n)));
  { id = Obj.magic n; replica = local_replica (Obj.magic n) }

(* init the replicas object *)
let r = new replicas

let sign_request breq priv =
  let o  = Obj.magic (PBinput breq) in
  sign_one o priv

(* build the request destination *)
(* let destination2string (n : name) : string =
 *   match Obj.magic n with
 *   | PBprimary -> "P(" ^ string_of_int (Obj.magic 0) ^ ")"
 *   | PBbackup -> "B(" ^ string_of_int (Obj.magic 0) ^ ")"
 *   | PBc -> "C(" ^ string_of_int (Obj.magic 0) ^ ")" ;; *)

let print_msgs msgs =
  List.fold_right ~f:(fun acc x -> acc ^ ";" ^ x) (List.map ~f:(fun x -> (String.of_char_list (directedMsg2string x))) msgs)

(* run the replicas on some input *)
let rec run_replicas_on_inputs (inflight : directedMsgs) : directedMsgs =
  print_info (kMAG) "Queue" ((print_msgs inflight) "");
  (* check if there is some message in queue *)
  match inflight with
  | [] ->
    print_info (kBLU) "Main" "All messages processed stopping";
    []
  | dm :: dms ->
    (* we have some message and now we iterate through all its destinations *)
    match dm.dmDst with
    (* restart loop if there a no destinations *)
    | [] -> run_replicas_on_inputs dms
    | id :: ids ->
      print_info (kCYN) "Procesing" ((String.of_char_list (directedMsg2string dm)));
      (* create a new message without the taken id *)
      let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
      (* find the replica mathing the id *)
      match r#find_replica id with
      | None ->
        print_err ("Couldn't find id " ^ node2string id);
        let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
        (* requeue message which failed to deliver ? *)
        failed_to_deliver :: run_replicas_on_inputs (dm' :: dms)
      | Some rep ->
        (* we have found the replica *)
        print_info (kGRN) ((node2string rep.id) ^ "got") (String.of_char_list (msg2string (Obj.magic dm.dmMsg)));
        (* run the state machine on the message input *)
        let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
        print_info (kCYN) (node2string id ^ "State transistion completed") ("Return " ^ (String.of_char_list (directedMsgs2string dmsgs)));
        (* replace the state machine of the replica *)
        print_info (kCYN) (node2string id) (Obj.magic rep.replica);
        r#replace_replica id rep';
        (* (message without current replica) :: (next messages) @ (newly created messages) *)
        run_replicas_on_inputs (dm' :: dms @ dmsgs)

(* implement the virtual simulator *)
class ['a, 'b] pb c = object(self)
  inherit ['a, 'b] runner c

  (* create the replication system with one primary and three backups *)
  method create_replicas =
    r#set_replicas [to_replica PBprimary; to_replica PBbackup]

  (* create a client request *)
  method mk_request (timestamp : int) (request : int) =
    PBinput request
    (* let opr       = Obj.magic (Opr_add request) in
     * let breq      = Bare_req (opr,timestamp,(Obj.magic c.client_id)) in
     * let tokens    = [ (if !signing then Obj.magic (sign_request breq c.private_key) else Obj.magic()) ] in
     * PBFTrequest (Req(breq,tokens)) *)


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
    print_info (kWHT) "Client sends" (String.of_char_list (directedMsgs2string inflight));
    let t = Prelude.Time.get_time () in
    (* deliver the messages *)
    let failed_to_deliver = run_replicas_on_inputs inflight in
    (* stop monitoring the system *)
    let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
    (* calculate the average *)
    let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
    (* print the messages which failed to deliver as string *)
    let s = Batteries.String.of_list (directedMsgs2string failed_to_deliver) in
    (match s with
     | "" -> ()
     | s' -> print_err s');
    (* print some results of the time is right *)
    (if timestamp mod printing_period = 0 then
       print_res timestamp d new_avg
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
    private_key = lookup_client_sending_key (Obj.magic 0);
    primary = Obj.magic PBprimary (* type: name *)
  } in
  c#run

(* let _ = Command.run ~version:"1.0" ~build_info:"PBFT" command *)
