open Colors
open Prelude
open RsaKeyFun
open Core
open Simulator
open RaftReplicaEx

let char_list2string l = Batteries.String.of_list l

let print_state state = char_list2string (state2string (sm_state state))

let to_replica n = { id = Obj.magic (Replica (Obj.magic n));
                     replica = local_replica false (Obj.magic n) }

let to_leader n = { id = Obj.magic (Replica (Obj.magic n));
                     replica = local_replica true (Obj.magic n) }

let get_session msg =
  match 

let destination2string (n : name) : string =
  match Obj.magic n with
  | Replica r -> "R(" ^ string_of_int (Obj.magic r) ^ ")"
  | Client c -> "C(" ^ string_of_int (Obj.magic c) ^ ")";;

class ['a, 'b, 'c, 'd] raft c = object(self)
  inherit ['a, 'b, 'c, 'd] simulator c

  method create_replicas =
    replicas#set_replicas [to_leader 0; to_replica 1; to_replica 2; to_replica 3];

  method mk_request (timestamp : int) (request : int) =
    let cmd = 12 in
    let term = 0 in
    let client = Obj.magic conf.client_id in
    Request_msg (Client_request (client, conf.session, request, (Obj.magic cmd)))

  method run_replicas (inflight : directedMsgs) : directedMsgs =
    match inflight with
    | [] -> []
    | dm :: dms ->
      match dm.dmDst with
      | [] -> self#run_replicas dms
      | id :: ids ->
        print_info (kCYN) "Procesing" (char_list2string (directedMsg2string dm));
        let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
        match replicas#find_replica id with
        | Some rep ->
          print_info (kGRN) (destination2string id ^ " | Input message")
            (char_list2string (msg2string (Obj.magic dm.dmMsg)));
          print_endline (char_list2string (state2string rep.replica.sm_state));
          let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
          print_info (kCYN) "Done" "";
          replicas#replace_replica id rep';
          print_endline (char_list2string (state2string rep'.sm_state));
          self#run_replicas (dm' :: dms @ dmsgs)
        | None ->
          print_err  ("Couldn't find id " ^ destination2string id) ();
          let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
          failed_to_deliver :: self#run_replicas (dm' :: dms)
       
  method run_client timestamp max avg printing_period =
    (* register some client *)
    let register = Register_msg (Obj.magic conf.client_id) in
    let inflight = [{ dmMsg = Obj.magic register; dmDst = [c.primary]; dmDelay = 0 }] in
    print_info (kBLU) "Start" (char_list2string (directedMsgs2string inflight));
    let failed_to_deliver = self#run_replicas inflight in
    (* execute some request **)
    let req = self#mk_request (Obj.magic timestamp) 17 in
    let inflight = [{ dmMsg = Obj.magic req; dmDst = [c.primary]; dmDelay = 0 }] in
    let t = Prelude.Time.get_time () in
    print_info (kBLU) "Start" (char_list2string (directedMsgs2string inflight));
    let failed_to_deliver = failed_to_deliver @ (self#run_replicas inflight) in
    let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
    let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
    (match failed_to_deliver with
     | [] -> ()
     | s' -> print_err (char_list2string (directedMsgs2string s')) ~case:"Failed to deliver: " ());
    (if timestamp mod printing_period = 0 then
       print_res timestamp d new_avg
     else ());
    if timestamp < max then
      self#run_client (timestamp + 1) max new_avg printing_period
    else ()
end

let _ =
  let c = new raft {
    version = "1.0";
    protocol = "Raft";
    client_id = 0;
    private_key = lookup_client_sending_key (Obj.magic 0);
    primary = Obj.magic (Replica (Obj.magic 0)) (* type: name *);
    session = 1;
  } in
  c#run
