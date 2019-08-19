open Colors
open Prelude
open RsaKeyFun
open Core
open Simulator
open RaftReplicaEx

let to_replica n = { id = Obj.magic (Raftreplica (Obj.magic n));
                     replica = local_replica (Obj.magic n) }

let destination2string (n : name) : string =
  match Obj.magic n with
  | Raftreplica r -> "R(" ^ string_of_int (Obj.magic r) ^ ")"
  | Raftclient c -> "C(" ^ string_of_int (Obj.magic c) ^ ")";;

class ['a, 'b, 'c, 'd] raft c = object(self)
  inherit ['a, 'b, 'c, 'd] simulator c

  method create_replicas =
    replicas#set_replicas [to_replica 0; to_replica 1; to_replica 2; to_replica 3];

  method mk_request (timestamp : int) (request : int) =
    let cmd = 0 in
    let term = 0 in
    let client = Obj.magic conf.client_id in
    RequestMsg (Req(client, cmd, term))

  method run_replicas (inflight : directedMsgs) : directedMsgs =
    match inflight with
    | [] -> []
    | dm :: dms ->
      print_info (kCYN) "Procesing" (Batteries.String.of_list (directedMsg2string dm));
      match dm.dmDst with
      | [] -> self#run_replicas dms
      | id :: ids ->
        let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
        match replicas#find_replica id with
        | None ->
          print_err  ("Couldn't find id " ^ destination2string id) ();
          let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
          failed_to_deliver :: self#run_replicas (dm' :: dms)
        | Some rep ->
          print_info (kGRN) "Input message"
            (Batteries.String.of_list(msg2string (Obj.magic dm.dmMsg)));
          let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
          print_info (kCYN) "Done" "";
          replicas#replace_replica id rep';
          self#run_replicas (dm' :: dms @ dmsgs)

  method run_client timestamp max avg printing_period =
    let req = self#mk_request (Obj.magic timestamp) 17 in
    let inflight = [{ dmMsg = Obj.magic req; dmDst = [c.primary]; dmDelay = 0 }] in
    let t = Prelude.Time.get_time () in
    print_endline (Batteries.String.of_list (directedMsgs2string inflight));
    let failed_to_deliver = self#run_replicas inflight in
    let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
    let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
    let s = Batteries.String.of_list (directedMsgs2string failed_to_deliver) in
    (match s with
     | "" -> ()
     | s' -> print_err s' ~case:"Failed to deliver: " ());
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
    primary = Obj.magic (Raftreplica (Obj.magic 0)) (* type: name *)
  } in
  c#run
