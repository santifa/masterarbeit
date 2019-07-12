open Colors
open Prelude
open RsaKeyFun
open Core
open Simulator
open RaftReplicaEx

(* turn this to false if you don't want to sign messages *)
let signing : bool ref = ref true

let to_replica n = { id = Obj.magic (Replica (Obj.magic n));
                     replica = local_replica (Obj.magic n) }
let r = new replicas


(* let sign_request breq priv =
 *   let o  = Obj.magic (PBFTmsg_bare_request breq) in
 *   sign_one o priv *)

let destination2string (n : name) : string =
  match Obj.magic n with
  | Replica r -> "R(" ^ string_of_int (Obj,magic r) ^ ")"
  | Client c -> "C(" ^ string_of_int (Obj.magic c) ^ ")";;

let rec run_replicas_on_inputs (inflight : directedMsgs) : directedMsgs =
  match inflight with
  | [] -> []
  | dm :: dms ->
    (* print_info (kCYN) "Procesing" (directedMsg2string dm); *)
    match dm.dmDst with
    | [] -> run_replicas_on_inputs dms
    | id :: ids ->
      let dm' = { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } in
      match r#find_replica id with
      | None ->
        print_err ("Couldn't find id " ^ destination2string id);
        let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in
        failed_to_deliver :: run_replicas_on_inputs (dm' :: dms)
      | Some rep ->
        (* print_info (kGRN) "Input message" (msg2string (Obj.magic dm.dmMsg)); *)
        let (rep',dmsgs) = lrun_sm rep.replica (Obj.magic dm.dmMsg) in
        print_info (kCYN) "Done" [];
        r#replace_replica id rep';
        run_replicas_on_inputs (dm' :: dms @ dmsgs)

class ['a, 'b] pbft c = object(self)
  inherit ['a, 'b] runner c

  method create_replicas =
    r#set_replicas [to_replica 0; to_replica 1; to_replica 2; to_replica 3];

  method mk_request (timestamp : int) (request : int) =
    let opr       = Obj.magic request in
    (* let breq      = Bare_req (opr,timestamp,(Obj.magic c.client_id)) in *)
    let tokens    = Obj.magic() (* [ (if !signing then Obj.magic (sign_request breq c.private_key) else Obj.magic()) ] *) in
    Command (request)


  method run_client timestamp max avg printing_period =
    let req = self#mk_request (Obj.magic timestamp) 17 in
    let inflight = [{ dmMsg = Obj.magic req; dmDst = [c.primary]; dmDelay = 0 }] in
    let t = Prelude.Time.get_time () in
    let failed_to_deliver = run_replicas_on_inputs inflight in
    let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
    let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
    (*let s = Batteries.String.of_list (directedMsgs2string failed_to_deliver) in*)
    (if timestamp mod printing_period = 0 then
       print_res timestamp d new_avg
     else ());
    if timestamp < max then
      self#run_client (timestamp + 1) max new_avg printing_period
    else ()
end

let _ =
  let c = new pbft {
    version = "1.0";
    protocol = "PBFT";
    client_id = 0;
    private_key = lookup_client_sending_key (Obj.magic 0);
    primary = Obj.magic (Replica (Obj.magic 0)) (* type: name *)
  } in
  c#run

(* let _ = Command.run ~version:"1.0" ~build_info:"PBFT" command *)
