open Prelude
open PbReplicaEx
open Core
open Test

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
class ['a, 'b, 'c, 'd] pb c t = object(self)
  inherit ['a, 'b, 'c, 'd] simulator c t

  (* create the replication system with one primary and three backups *)
  method create_replicas =
    replicas#set_replicas [to_replica PBprimary; to_replica PBbackup]

  method msgs2string (msgs : directedMsgs) : string = print_dmsgs msgs ""

  method change_dst dm ids =
    { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay }

  method get_dsts dm = dm.dmDst

  method get_response dms = get_response dms

  method run_sm dm rep = lrun_sm rep (Obj.magic dm.dmMsg)
end

class ['c] response_eq = object
  method request (resp: directedMsgs) : directedMsgs =
    match resp with
    | [] ->
      (* create a simple PNinput request *)
      let req = PBinput 10 in
      (* create a message list with the primary as destination *)
      [{ dmMsg = Obj.magic req; dmDst = [Obj.magic PBprimary]; dmDelay = 0 }]
    | rsp :: rsps ->
      match (Obj.magic rsp.dmMsg) with
      | PBreply 10 ->  log_test "correct" "The primary node returned the correct result";
        []
      | _ ->   log_err "failed" ("Got the wrong result" ^ (print_msg rsp));
        [] (* do nothing if we recieve some result *)
end

class ['c] resp_uneq = object
  method request (resp: directedMsgs) : directedMsgs =
    match resp with
    | [] ->
      (* create a simple PNinput request *)
      let req = PBinput 9 in
      (* create a message list with the primary as destination *)
      [{ dmMsg = Obj.magic req; dmDst = [Obj.magic PBprimary]; dmDelay = 0 }]
    | rsp :: rsps ->
      match (Obj.magic rsp.dmMsg) with
      | PBreply 10 ->  log_test "correct" "The primary node returned the correct result";
        []
      | _ ->   log_test "failed" ("Got the wrong result" ^ (print_dmsgs [rsp] ""));
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
  } [(new response_eq); (new resp_uneq)] in
  c#run 
