open Colors
open Prelude
open PbftReplicaEx
open RsaKeyFun
open Core
open Simulator

(* turn this to false if you don't want to sign messages *)
let signing : bool ref = ref true

let sign_request breq priv =
  let o  = Obj.magic (PBFTmsg_bare_request breq) in
  sign_one o priv

let destination2string (n : name) : string =
  match Obj.magic n with
  | PBFTreplica r -> "R(" ^ string_of_int (Obj.magic r) ^ ")"
  | PBFTclient  c -> "C(" ^ string_of_int (Obj.magic c) ^ ")" ;;

class ['a, 'b, 'c, 'd] pbft c = object(self)
  inherit ['a, 'b, 'c, 'd] simulator c

  method create_replicas =
    replicas#set_replicas
      [{ id = Obj.magic (PBFTreplica (Obj.magic 0)); replica = local_replica (Obj.magic 0) };
       { id = Obj.magic (PBFTreplica (Obj.magic 1)); replica = local_replica (Obj.magic 1) };
       { id = Obj.magic (PBFTreplica (Obj.magic 2)); replica = local_replica (Obj.magic 2) };
       { id = Obj.magic (PBFTreplica (Obj.magic 3)); replica = local_replica (Obj.magic 3) }]

  method mk_request (timestamp : int) (request : int) =
    let opr       = Obj.magic (Opr_add request) in
    let client    = conf.client_id in
    let breq      = Bare_req (opr, timestamp, (Obj.magic client)) in
    let tokens    = [ (if !signing then Obj.magic (sign_request breq conf.private_key) else Obj.magic()) ] in
    PBFTrequest (Req(breq,tokens))

  method run_replicas (inflight : directedMsgs) : directedMsgs =
    match inflight with
    | [] -> []
    | dm :: dms ->
      print_endline (kCYN ^ "[processsing: " ^ Batteries.String.of_list (directedMsg2string dm) ^ "]" ^ kNRM);
      match dm.dmDst with
      | [] -> self#run_replicas dms
      | id :: ids ->
        let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
        match replicas#find_replica id with
        | None ->
           print_endline (kBRED ^ "[couldn't find id " ^ destination2string id ^ "]" ^ kNRM);
           let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
           failed_to_deliver :: self#run_replicas (dm' :: dms)
        | Some rep ->
           print_endline (kGRN ^ "[input message: " ^ Batteries.String.of_list (msg2string (Obj.magic dm.dmMsg)) ^ "]" ^ kNRM);
           let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
           print_endline ("[done]");
           print_endline (String.of_char_list (pbft_state2string (sm_state rep')));
           replicas#replace_replica id rep';
           self#run_replicas (dm' :: dms @ dmsgs)

  method run_client timestamp max avg printing_period =
  let req = self#mk_request timestamp 17 in
  let inflight = [{ dmMsg = Obj.magic req; dmDst = [conf.primary]; dmDelay = 0 }] in
  let t = Prelude.Time.get_time () in
  let failed_to_deliver = self#run_replicas inflight in
  let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
  let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
  let s = Batteries.String.of_list (directedMsgs2string failed_to_deliver) in
  (if timestamp mod printing_period = 0 then
     print_endline (kMAG
                    ^ "[timestamp: " ^ string_of_int timestamp
                    ^ "; elapsed time: " ^ Batteries.String.of_list (Prelude.Time.time2string d)
                    ^ "; average: " ^ Batteries.String.of_list (Prelude.Time.time2string new_avg)
                    ^ "; non delievered messages: " ^ s
                    ^ "]"
                    ^ kNRM)
   else ());
  if timestamp < max then
    self#run_client (timestamp + 1) max new_avg printing_period
  else ()
end

let _ =
  (* create pbft simulation *)
  let c = new pbft {
    version = "1.0";
    protocol = "PBFT";
    client_id = 0;
    private_key = lookup_client_sending_key (Obj.magic 0);
    primary = Obj.magic (PBFTreplica (Obj.magic 0)) (* type: name *)
  } in
  c#run
