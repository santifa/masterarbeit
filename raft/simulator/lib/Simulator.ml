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

(* the abstract simulator provides convient functions to implement a new protocol.
   Inherit and implement the virtual methods. See PbSimul.ml and PbftSimul.ml as reference
   'a -> Nodename ; 'b -> protocol message ; 'c -> directed message type ; 'd -> state machine *)
class virtual ['a, 'b, 'c, 'd] simulator c = object(self)
  val mutable conf : ('a) run_conf = c
  val mutable replicas : ('a, 'd) replicas = new replicas
  val mutable queue : 'c list ref = ref []

  method add_to_queue (msg : 'c list) : unit = queue := msg

  (** create all the replicas **)
  method virtual create_replicas : 'c list

  (** Convert a list of mesgs to a string **)
  method virtual msgs2string : 'c list -> string

  (** specify how the replica handles input messages **)
  method virtual run_replicas : 'c list -> ('c list * 'c list)

  (** specify the client implementation. The client get initial an empty list of responses. **)
  method virtual client : 'c list  -> 'c list

  (** Run the simulation and handle client server interaction **)
  method run_simulation (queue : 'c list) : 'c list =
    let request = self#client queue in
    if List.is_empty request then [] (* return if no more request are produced *)
    else begin
      log_info "Input queue" (self#msgs2string request);
      let (responses, failed_to_deliver) = self#run_replicas request in
      log_info "Response queue" (self#msgs2string responses);
      if List.is_empty responses then failed_to_deliver else
        failed_to_deliver @ self#run_simulation responses
    end

  (** This method handles the basic benchmarking code and reports failed messages
   ** every round is a full simulation between client and replicas **)
  method benchmark (timestamp : int) (max : int) (avg : Prelude.Time.t) (period : int) =
    (* start monitoring the system time *)
    let t = Prelude.Time.get_time () in
    (* run the system *)
    let failed_to_deliver = self#run_simulation !queue in
    (* stop monitoring the system *)
    let d = Prelude.Time.sub_time (Prelude.Time.get_time ()) t in
    (* calculate the average *)
    let new_avg = Prelude.Time.div_time (Prelude.Time.add_time (Prelude.Time.mul_time avg  (timestamp - 1)) d) timestamp in
    (* print the messages which failed to deliver as string *)
    let s = self#msgs2string failed_to_deliver in
    (match s with
     | "[]" -> ()
     | s' -> log_err "Main" ("Failed to deliver" ^ s'));
    (* print some results if the time is right *)
    (if timestamp mod period = 0 then
       log_res "Main" timestamp d new_avg
     else ());
    (* restart the client if there are more rounds to go *)
    if timestamp < max then
      self#benchmark (timestamp + 1) max new_avg period
    else ()

  (* maybe this could be more generalized *)
  (** An implementation should catch the spec args <max> <printing_period> initialize the crypto;
      set the replicas and at last call run_client **)
  method callback : int -> int -> bool -> unit -> unit =
    (fun max printing_period debug () ->
       log_info "Main" "Initialize random generator";
       let () = Nocrypto_entropy_unix.initialize () in

       log_info "Main" "Start replicas";
       self#add_to_queue(self#create_replicas);


       log_info "Main" "Fire up client";
       let initial_avg       = Prelude.Time.mk_time 0. in
       self#benchmark conf.timer max initial_avg printing_period)


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
