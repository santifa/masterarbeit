open Colors
open Prelude
open RsaKeyFun
open Core

(* the generic type *)
type ('a, 'b) idrep = { id : 'a ; replica : 'b }

(* create a list of replicas *)
class ['a, 'b] replicas = object(self)
  val mutable r : ('a, 'b) idrep list ref = ref []

  (* assign replicas *)
  method set_replicas (l : ('a, 'b) idrep list) =
    r := l

  method get_replicas : ('a, 'b) idrep list =
    !r

  method find_replica id : ('a, 'b) idrep option =
    List.find ~f:(fun x -> id = x.id) !r

  method replace_replica id rep : unit =
    r := List.map ~f:(fun x -> if id = x.id then { id = id; replica = rep } else x) !r
end

(* print error messages *)
let print_err msg =
  print_endline (kBRED ^ "Error:\t[" ^ msg ^ "]" ^ kNRM)

(* print info messages with c - color; t - message type; msg - message *)
let print_info c t msg =
  print_endline (c ^ "Info:\t{" ^ t ^ ": " ^ msg ^ "}" ^ kNRM)

(* print results t - timestamp; d - elapsed time; avg - average *)
let print_res t d avg  =
  print_endline (kMAG ^ "Result:\t[Timestamp: " ^ string_of_int t
                 ^ "; elapsed time: " ^ (Batteries.String.of_list (Prelude.Time.time2string d))
                 ^ "; average: " ^ Batteries.String.of_list (Prelude.Time.time2string avg)
                 ^ "]" ^ kNRM)


type ('a) run_conf = {
  version : string;
  protocol : string;
  client_id : int;
  private_key : Nocrypto.Rsa.priv;
  primary : 'a;
}

class virtual ['a, 'b] runner c = object(self)
  val mutable conf : ('a) run_conf = c

  (** create all the replicas **)
  method virtual create_replicas : unit

  (** specify how some client request is made **)
  method virtual mk_request : int -> int -> 'b

  (** specify the client **)
  method virtual run_client : int -> int -> Prelude.Time.t -> int -> unit

  (* maybe this could be more generalized *)
  (** An implementation should catch the spec args <max> <printing_period> initialize the crypto;
      set the replicas and at last call run_client **)
  method callback : int -> int -> unit -> unit =
    (fun max printing_period () ->
       print_info (kBLU) "Main" "Initialize random generator";
       let () = Nocrypto_entropy_unix.initialize () in

       print_info (kBLU) "Main" "Start replicas";
       self#create_replicas;

       print_info (kBLU) "Main" "Fire up client";
       let initial_timestamp = 1 in
       let initial_avg       = Prelude.Time.mk_time 0. in
       self#run_client initial_timestamp max initial_avg printing_period)


  (** the default cli specification **)
  method spec : Command.t =
    let () = Nocrypto_entropy_unix.initialize () in
    Command.basic_spec
      ~summary:"Start a client"
      Command.Spec.(
        empty
        +> flag "-max" (optional_with_default 10 int)
          ~doc:" Number of messages to send (default 10)"

        +> flag "-printing-period" (optional_with_default 10 int)
          ~doc:" Number of messages till a summary is printed (default 10)"
      )
      self#callback

  (** run a simulator with some specified configuration **)
  method run =
    print_info (kWHT) "Main" ("Running simulator for " ^ conf.protocol
                              ^ " Version: " ^ conf.version);
    Command.run ~version:conf.version ~build_info:conf.protocol self#spec
end
