open Core
include Log

(* This module defines the abstract type classes and basic functions
   to easily implement a simulator for some protocol.
   Maybe it would be usefull to provide an .mli file

   The classes uses generic types which can lead to confusions
   or maybe inappropriate in complex cases.

   The rough method is to implement the virtual methods of the simulator class
   which should be sufficient for ocaml to guess the types and run the simulation.
*)

(* The basic record which connects an id with some replica.
   The semantic is mostly that the id the the node name and
   the replica is some sort of current state. *)
type ('a, 'b) idrep = { id : 'a ; replica : 'b }

(* This is the basic object for working with replicas. *)
class ['a, 'b] replicas = object(self)
  val mutable r : ('a, 'b) idrep list ref = ref []

  (* assign a list of replicas *)
  method set_replicas (l : ('a, 'b) idrep list) =
    r := l

  (* get all replicas *)
  method get_replicas : ('a, 'b) idrep list =
    !r

  (* return some replica iff the id is found *)
  method find_replica id : ('a, 'b) idrep option =
    List.find ~f:(fun x -> id = x.id) !r

  (* replace the current replica with a new one *)
  method replace_replica id rep : unit =
    r := List.map ~f:(fun x -> if id = x.id then { id = id; replica = rep } else x) !r
end

(* A basic run configuration *)
type ('a) run_conf = {
  version : string;
  protocol : string;
  client_id : int;
  private_key : Nocrypto.Rsa.priv;
  primary : 'a;
  timer : int;
}


class virtual ['c] client = object
  (** specify the client implementation. The client get initial an empty list of responses. **)
  method virtual request : 'c list  -> 'c list
end

(* the abstract simulator provides convient functions to implement a new protocol.
   Inherit and implement the virtual methods. See PbSimul.ml and PbftSimul.ml as reference
   'a -> Nodename ; 'b -> protocol message ; 'c -> directed message type ; 'd -> state machine *)
class virtual ['a, 'b, 'c, 'd] simulator c t = object(self)
  val mutable conf : ('a) run_conf = c
  val mutable replicas : ('a, 'd) replicas = new replicas
  val mutable tests : ('c) client list = t

  (** create all the replicas **)
  method virtual create_replicas : unit

  (** Convert a list of mesgs to a string **)
  method virtual msgs2string : 'c list -> string

  (** specify how the replica handles input messages **)
  method virtual run_replicas : 'c list -> ('c list * 'c list)

  method virtual change_dst : 'c -> 'a list -> 'c

  method virtual get_dsts : 'c -> 'a list

  method virtual get_response : 'c list -> 'c list

  method virtual run_sm : 'c -> 'b

  method run_replicas (inflight : 'c list) : ('c list * 'c list) =
  (* check if there is some message in queue *)
  match inflight with
  | [] ->
    log_info "Main" "All messages processed stopping";
    ([], []) (* we reached the end of the simulation round *)
  | dm :: dms ->
    (* we have some message and now we iterate through all its destinations *)
    match (self#get_dsts dm)(* dm.dmDst *) with
    (* restart loop if there a no destinations *)
    | [] -> self#run_replicas dms
    | id :: ids ->
      log_msgs "Procesing" (self#msgs2string [dm]) (* ((print_dmsgs [dm]) "") *);
      (* create a new message without the taken id *)
      let dm' = self#change_dst dm ids (* { dmMsg = dm.dmMsg; dmDst = ids; dmDelay = dm.dmDelay } *) in
      (* find the replica mathing the id *)
      match replicas#find_replica id with
      | None ->
        (* let failed_to_deliver = { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } in *)
        let failed_to_deliver = self#change_dst dm [id] (* { dmMsg = dm.dmMsg; dmDst = [id]; dmDelay = dm.dmDelay } *) in
        let resp = self#get_response [failed_to_deliver] in
        (* requeue message which failed to deliver ? *)
        let (response, failed) = self#run_replicas (dm' :: dms) in
        if List.is_empty resp then begin
          (* log_err "Main" ("Couldn't find id " ^ print_node id); *)
          (response, failed_to_deliver :: failed)
        end else (resp @ response, failed)

      | Some rep ->
        (* we have found the replica *)
        (* log_msgs ((print_node rep.id) ^ "got") (print_msg dm.dmMsg); *)
        (* run the state machine on the message input *)
        let (rep',dmsgs) = self#run_sm dm rep.replica(* (Obj.magic dm.dmMsg) *) in
        (* log_state (print_node id ^ "State transistion completed")
         *   ("Send " ^ self#msgs2string dmsgs (\* ((print_dmsgs dmsgs) "") *\)); *)
        (* let resp = get_response dmsgs in *)
        (* replace the state machine of the replica *)
        (* log_state (print_node id) (print_state rep'); *)
        replicas#replace_replica id rep';
        (* (message without current replica) :: (next messages) @ (newly created messages) *)
        let (response, failed) = self#run_replicas (dm' :: dms @ dmsgs) in
        (response, failed)

  (** Run the simulation and handle client server interaction **)
  method run_simulation (queue : 'c list) t : 'c list =
    let request = t#request queue in
    if List.is_empty request then [] (* return if no more request are produced *)
    else begin
      log_info "Input queue" (self#msgs2string request);
      let (responses, failed_to_deliver) = self#run_replicas request in
      log_info "Response queue" (self#msgs2string responses);
      if List.is_empty responses then failed_to_deliver else
        failed_to_deliver @ self#run_simulation responses t
    end

  method run_tests (t : ('c) client list) : unit =
    match t with
    | [] -> ()
    | t' :: tt ->
      let failed = self#run_simulation [] t' in
      let s = self#msgs2string failed in
      (match s with
       | "" -> ()
       | s' -> log_err "Main" ("Test failed" ^ s'));
      self#run_tests tt

  (* maybe this could be more generalized *)
  (** An implementation should catch the spec args <max> <printing_period> initialize the crypto;
      set the replicas and at last call run_client **)
  method callback : int -> int -> bool -> unit -> unit =
    (fun max printing_period debug () ->
       log_info "Main" "Initialize random generator";
       let () = Nocrypto_entropy_unix.initialize () in

       log_info "Main" "Start system";
       self#create_replicas;

       log_info "Main" "Fire up test client";
       self#run_tests tests)


  (** the default cli specification **)
  method spec : Command.t =
    let () = Nocrypto_entropy_unix.initialize () in
    let () = Random.self_init () in
    Command.basic_spec
      ~summary:"Start a client"
      Command.Spec.(
        empty
        +> flag "-max" (optional_with_default 10 int)
          ~doc:" Number of messages to send (default 10)"

        +> flag "-printing-period" (optional_with_default 10 int)
          ~doc:" Number of messages till a summary is printed (default 10)"
        +> flag "-debug" (optional_with_default true bool)
          ~doc: "Verbose output (default true)"
      )
      self#callback

  (** run a simulator with some specified configuration **)
  method run =
    log_info "Main" ("Running simulator for " ^ conf.protocol
                              ^ " Version: " ^ conf.version);
    Command.run ~version:conf.version ~build_info:conf.protocol self#spec
end
