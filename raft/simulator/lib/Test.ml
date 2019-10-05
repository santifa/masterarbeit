open Core
include Simulator
(* This module defines the abstract type classes and basic functions
   to easily implement test cases for some protocol.
   Maybe it would be usefull to provide an .mli file

   The classes uses generic types which can lead to confusions
   or maybe inappropriate in complex cases.

   The rough method is to implement the virtual methods of the simulator class
   which should be sufficient for ocaml to guess the types and run the simulation.
*)

(* the abstract simulator provides convient functions to implement a new protocol.
   Inherit and implement the virtual methods. See PbSimul.ml and PbftSimul.ml as reference
   'a -> Nodename ; 'b -> protocol message ; 'c -> directed message type ; 'd -> state machine *)
class virtual ['a, 'b, 'c, 'd] test_simulator c t = object(self)
  inherit ['a, 'b, 'c, 'd] simulator c
  (* a test is function which takes a list of response messages and returns a new set of request messages *)
  val mutable tests : (string * ('c list -> 'c list)) list = t

  (** change the destination of a message **)
  method virtual change_dst : 'c -> 'a list -> 'c

  (** extract a list of destinations **)
  method virtual get_dsts : 'c -> 'a list

  (** return wether the message is a response to the client or not **)
  method virtual is_response : 'c -> bool

  (** run the replica on some input message **)
  method virtual run_sm : 'c -> ('a, 'b) idrep -> ('b * 'c list)

  (** Take a list of messages and return the first if it's a response message **)
  method get_response (msgs : 'c list) : 'c option =
    match msgs with
    | [] -> None
    | msg :: _ ->
      if self#is_response msg then Some msg else None

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
        let failed_to_deliver = self#change_dst dm [id] in
        let resp = self#get_response [failed_to_deliver] in
        (* requeue message which failed to deliver ? *)
        let (response, failed) = self#run_replicas (dm' :: dms) in
        (match resp with
         | None -> (response, failed_to_deliver :: failed)
         | Some resp' -> (resp' :: response, failed))

      | Some rep ->
        (* we have found the replica *)
        (* run the state machine on the message input *)
        let (rep',dmsgs) = self#run_sm dm rep (* (Obj.magic dm.dmMsg) *) in
        replicas#replace_replica id rep';
        (* (message without current replica) :: (next messages) @ (newly created messages) *)
        let (response, failed) = self#run_replicas (dmsgs @ dm' :: dms) in
        (response, failed)

  (** Run the simulation and handle client server interaction **)
  method run_test (queue : 'c list) t : 'c list =
    let request = t queue in
    if List.is_empty request then [] (* return if no more request are produced *)
    else begin
      log_info "Input queue" (self#msgs2string request);
      let (responses, failed_to_deliver) = self#run_replicas request in
      log_info "Response queue" (self#msgs2string responses);
      if List.is_empty responses then failed_to_deliver else
        failed_to_deliver @ self#run_test responses t
    end

  method run_tests (t : (string * ('c list -> 'c list)) list) : unit =
    match t with
    | [] -> ()
    | t' :: tt ->
      print_endline " ";
      log_info "Running test" (fst t');
      let i = self#create_replicas in
      let failed = self#run_test i (snd t') in
      (match failed with
       | [] -> ()
       | s -> log_err "Main" (" Test failed " ^ (self#msgs2string s)));
      self#run_tests tt

  (* maybe this could be more generalized *)
  (** An implementation should catch the spec args <max> <printing_period> initialize the crypto;
      set the replicas and at last call run_client **)
  method callback : int -> int -> bool -> unit -> unit =
    (fun max printing_period debug () ->
       log_info "Main" "Initialize random generator";
       let () = Nocrypto_entropy_unix.initialize () in

       log_info "Main" "Fire up test clients";
       self#run_tests tests)

  method benchmark timestamp max avg period = ()

  method run_simulation queue = []

  method client msgs = []
end
