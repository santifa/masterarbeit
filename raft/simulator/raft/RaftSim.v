(*!
 * This file defines an instance of the raft protocol
 * and extracts the code necessary to use the simulator and runtime
 * from ocaml.
 !*)

Require Export Simulator.
Require Export Protocols.Raft.Raft.
Require Export Ascii String.

(** This section defines a real instance of the previously defined
 ** raft protocol. **)
Section RaftInstance.

  (* ================== TIME ================== *)
  (*! Define timing stuff !*)
  Definition time_I_type : Set := unit.

  Definition time_I_get_time : unit -> time_I_type := fun _ => tt.

  Definition time_I_sub : time_I_type -> time_I_type -> time_I_type := fun _ _ => tt.

  Definition time_I_2string : time_I_type -> string := fun _ => "".

  Global Instance TIME_I : Time.
  Proof.
    exists time_I_type.
    { exact time_I_get_time. }
    { exact time_I_sub. }
    { exact time_I_2string. }
  Defined.

  (*! Commen context definitions !*)
  (** The total number of faults the system should survive.  **)
  Definition F := 1.

  (** Define the total number of clients which is c + 1. **)
  Definition C := 0.

  (** Define the number of replicas as 3 time the number of faults happening plus one. **)
  Definition num_replicas (F : nat) : nat := 3 * F + 1.

  (** Declare the set of replicas as map between num and replica. **)
  Definition replica (F : nat) : Set := nat_n (num_replicas F).

  (** Replicas have decidable equality. **)
  Lemma replica_deq (F : nat) : Deq (replica F).
  Proof.
    apply nat_n_deq.
  Defined.

  (** Convert between the replicas and the numbers indicating the replica **)
  Definition reps2nat (F : nat) : replica F -> nat_n (num_replicas F) := fun n => n.

  (** Show that the function is bijective. **)
  Lemma bijective_reps2nat (F : nat) : bijective (reps2nat F).
  Proof.
    exists (fun n : nat_n (num_replicas F) => n); introv; unfold reps2nat; auto.
  Defined.

  (** Return the number of clients needed for a given amount. **)
  Definition nclients (C : nat) : nat := S C.

  (** Create the map of clients and it's natural representation. **)
  Definition client (C : nat) : Set := nat_n (nclients C).

  (** Proof that the definition client holds for one client. **)
  Definition client0 (C : nat) : client C.
  Proof.
    exists 0.
    apply leb_correct.
    unfold nclients.
    omega.
  Defined.

  (** Proof that proposed clients have decidable equality. **)
  Lemma client_deq (C : nat) : Deq (client C).
  Proof.
    apply nat_n_deq.
  Defined.

  (** Convert between clients and their numeral representations. **)
  Definition clients2nat (C : nat) : client C -> nat_n (nclients C) := fun n => n.

  (** Proof that the conversion is bijective. **)
  Lemma bijective_clients2nat (C : nat) : bijective (clients2nat C).
  Proof.
    exists (fun n : nat_n (nclients C) => n); introv; unfold clients2nat; auto.
  Defined.

  (** Define the state machines type **)
  Definition smState : Set := nat.

  (** Initialize the global context **)
  Global Instance Raft_I_context : RaftContext :=
    MkRaftContext
      F (* faults *)
      (replica F) (* replica type *)
      (replica_deq F) (* replica decidability *)
      (reps2nat F)  (* replica 2 nat conversion *)
      (bijective_reps2nat F) (* proof that conversion is bijective *)

      (nclients C) (* number of clients *)
      (client C) (* client type *)
      (client_deq C) (* client decidability *)
      (clients2nat C) (* client 2 nat conversion *)
      (bijective_clients2nat C) (* proof that conversion is bijective *)
      smState (* state machine type *)
      0 (* initial state *)
      1000. (* timeout in ms *)

  (*! Pretty printing !*)
  (** concat a list of string to one string. **)
  Fixpoint str_concat (l : list String.string) : String.string :=
    match l with
    | [] => ""
    | s :: ss => String.append s (str_concat ss)
    end.

  (* FIX: to replace when extracting *)
  (** The next three functions are placeholder functions which are later
   ** replaced by real ocaml function within the extraction process. **)
  (** carriage return **)
  Definition CR : string := String (ascii_of_nat 13) "".
  Definition print_endline : string -> unit := fun _ => tt.
  Definition nat2string (n : nat) : string := "-".

  (* Fix: there's only one client anyway *)
  (** Name the client **)
  Definition client2string (c : client C) : string := str_concat ["Client: ", nat2string C].

  Definition nat_n2string {m} (n : nat_n m) : string := nat2string (proj1_sig n).
  (** Fetch the replica number from the map **)
  Definition replica2string (r : replica F) : string := str_concat ["Replica: ", nat_n2string r].

  (** The following defintions convert the basic types used within the protocol to strings **)
  Definition term2string (t : Term) : string :=
    match t with
    | term n => str_concat ["Term: ", nat2string n]
    end.

  Definition request2string (r : Request) : string :=
    match r with
    | Req client c t => str_concat ["Request: (",
                                   client2string client, ", ",
                                   "Cmd: ", nat2string c, ", ",
                                   term2string t, ")"]
    end.

  Fixpoint log_list2string (l : list nat) : string :=
    match l with
    | [] => ""
    | x :: xs => str_concat [nat2string x, " ", log_list2string xs]
    end.

  Definition append_entries2string (a : AppendEntries) : string :=
    match a with
    | Heartbeat => "Heartbeat"
    | Replicate t r lli llt ci e => str_concat ["Replicate: (",
                                               term2string t,
                                               replica2string r,
                                               "Last_log_index: ", nat2string lli,
                                               "Last_log_term: ", nat2string llt,
                                               "Commit_index: ", nat2string ci,
                                               "Entries: ", log_list2string e, ")"]
    end.

  Definition request_vote2string (r : RequestVote) : string :=
    match r with
    | Vote t c lli llt => str_concat ["RequestVote: (",
                                     term2string t,
                                     replica2string c,
                                     "Last_log_index: ", nat2string lli,
                                     "Last_log_term: ", nat2string llt, ")"]
    end.

  Definition bool2string (b : bool) : string :=
    match b with
    | true => "true"
    | false => "false"
    end.

  Definition result2string (r : Result) : string :=
    match r with
    | ClientRes res => str_concat ["ClientResult: ", nat2string res]
    | AppendEntriesRes s t => str_concat ["AppendEntriesResult: (",
                                         "Success: ", bool2string s,
                                         term2string t, ")"]
    | RequestVoteRes v t => str_concat ["RequestVoteResult: (",
                                       "Vote_granted: ", bool2string v,
                                       term2string t, ")"]
    end.

  Definition msg2string (m : Raftmsg) : string :=
    match m with
    | RequestMsg r => request2string r
    | ResponseMsg r => result2string r
    | AppendEntriesMsg r => append_entries2string r
    | AppendEntriesResultMsg r => result2string r
    | RequestVoteMsg r => request_vote2string r
    | ResponseVoteMsg r => result2string r
    end.

  (* convert the node types to names *)
  Definition name2string (n : name) : string :=
    match n with
    | Raftreplica r => replica2string r
    | Raftclient c => client2string c
    end.

  Fixpoint names2string (l : list name) : string :=
    match l with
    | [] => ""
    | [n] => name2string n
    | n :: ns => str_concat [name2string n, "|", names2string ns]
    end.

  (** A direct message as some sort of possible delay **)
  Definition delay2string (delay : nat) : string := nat2string delay.

  (** convert a message which is send directly to the nodes into a string **)
  Definition DirectedMsg2string (dm : DirectedMsg) : string :=
    match dm with
    | MkDMsg msg dst delay =>
      str_concat ["Msg:", msg2string msg, " Dst:{", names2string dst, "}, Delay:", delay2string delay]
    end.

  Fixpoint DirectedMsgs2string (l : DirectedMsgs) : string :=
    match l with
    | [] => ""
    | [dm] =>  DirectedMsg2string dm
    | dm :: dmsgs => str_concat  [DirectedMsg2string dm, CR, DirectedMsgs2string dmsgs]
    end.

  (*
  Definition TimedDirectedMsg2string (m : TimedDirectedMsg) : string :=
    match m with
    | MkTimedDMsg dm time => str_concat [DirectedMsg2string dm, ":", time_I_2string time]
    end.

  Fixpoint TimedDirectedMsgs2string (l : TimedDirectedMsgs) : string :=
    match l with
    | [] => ""
    | [dm] => TimedDirectedMsg2string dm
    | dm :: dmsgs => str_concat [TimedDirectedMsg2string dm, CR, TimedDirectedMsgs2string dmsgs]
    end.
*)
(*   Definition MonoSimulationState2string (s : MonoSimulationState) : string := *)
(*     match s with *)
(*     | MkMonoSimState ty sys step out_inflight in_inflight delivered => *)
(*       concat *)
(*         [CR, *)
(*           "====== STEP ======", *)
(*           CR, *)
(*           nat2string step, *)
(*           CR, *)
(*           "====== IN FLIGHT (from outside the system) ======", *)
(*           CR, *)
(*           (*DirectedMsgs2string out_inflight,*) *)
(*           CR, *)
(*           "====== IN FLIGHT (from inside the system) ======", *)
(*           CR, *)
(*           (*DirectedMsgs2string in_inflight,*) *)
(*           CR, *)
(*           "====== DELIVERED ======" *)
(* (*CR, *)
(*          TimedDirectedMsgs2string delivered, *)
(*          CR*) *)
(*         ] *)
(*     end. *)


  Definition state2string (s : RaftState) :=
      str_concat
        ["(Raft state:", CR,
         term2string (current_term s), ")"
        ].

  (*! System definition !*)
  Definition dummy_initial_state : RaftState :=
    Build_State
      initial_term
      None
      []
      0
      0
      5
      RaftSM_initial_state
      initial_leader_state.

  Definition RaftdummySM : MStateMachine RaftState :=
    MhaltedSM dummy_initial_state.

  Definition Raftmono_sys : NMStateMachine RaftState :=
    fun name =>
      match name with
      | Raftreplica n => RaftreplicaSM n
      | _ => MhaltedSM dummy_initial_state
      end.

  (* Definition mk_request_to (rep : Rep) (ts : nat) (opr : nat) : DirectedMsg := *)
  (*   let ts   := time_stamp ts in *)
  (*   let breq := bare_req (opr_add opr) ts (client0 C) in *)
  (*   let dst  := PBFTreplica rep in (* the leader *) *)
  (*   let toks := [ pbft_token_stub ] : Tokens in (* we just send empty lists here to authenticate messages *) *)
  (*   let req  := req breq toks in *)
  (*   let msg  := PBFTrequest req in *)
  (*   MkDMsg msg [dst] 0. *)

  (* Definition mk_request (ts : nat) (opr : nat) : DirectedMsg := *)
  (*   mk_request_to (PBFTprimary initial_view) ts opr. *)

  (* (* n request starting with number start *) *)
  (* Fixpoint mk_requests_start (n start opr : nat) : DirectedMsgs := *)
  (*   match n with *)
  (*   | 0 => [] *)
  (*   | S m => List.app (mk_requests_start m start opr) [mk_request (n + start) opr] *)
  (*   end. *)

  (* Definition mk_requests (n opr : nat) : DirectedMsgs := *)
  (*   mk_requests_start n 0 opr. *)

  (* Record InitRequests := *)
  (*   MkInitRequests *)
  (*     { *)
  (*       num_requests     : nat; *)
  (*       starting_seq_num : nat; *)
  (*       req_operation    : nat; *)
  (*     }. *)

  Definition Raftinit_msgs (msgs : DirectedMsgs) : MonoSimulationState :=
    MkInitMonoSimState Raftmono_sys msgs.

  (* Definition PBFTinit (init : InitRequests) : MonoSimulationState := *)
  (*   Raftinit_msgs *)
  (*     (mk_requests_start *)
  (*        (num_requests init) *)
  (*        (starting_seq_num init) *)
  (*        (req_operation init)). *)

  (* Definition PBFTsimul_list (init : InitRequests) (L : list nat) : MonoSimulationState := *)
  (*   mono_run_n_steps L (PBFTinit init). *)

  (* Definition PBFTsimul_list_msgs (msgs : DirectedMsgs) (L : list nat) : MonoSimulationState := *)
  (*   mono_run_n_steps L (PBFTinit_msgs msgs). *)

  (* (* [switch] is the list of steps at which we want to switch to sending messages *)
  (*  coming from the outside (from clients) instead of keeping on sending messages *)
  (*  coming from the inside (from replicas). *) *)
  (* Definition PBFTsimul_n *)
  (*            (init     : InitRequests) (* This is to generate an initial list of requests *) *)
  (*            (rounds   : Rounds) *)
  (*            (switches : Switches) : MonoSimulationState := *)
  (*   mono_iterate_n_steps rounds switches (PBFTinit init). *)

  (* Definition PBFTsimul_n_msgs *)
  (*            (msgs     : DirectedMsgs) *)
  (*            (rounds   : Rounds) *)
  (*            (switches : Switches) : MonoSimulationState := *)
  (*   mono_iterate_n_steps rounds switches (PBFTinit_msgs msgs). *)

End RaftInstance.


(* ================== EXTRACTION ================== *)


Extraction Language Ocaml.

(* printing stuff *)
Extract Inlined Constant print_endline => "Prelude.print_coq_endline".
Extract Inlined Constant nat2string    => "Prelude.char_list_of_int".

(* numbers *)
Extract Inlined Constant Nat.modulo    => "(mod)".

(* lists *)
Extract Inlined Constant forallb => "List.for_all".
Extract Inlined Constant existsb => "List.exists".
Extract Inlined Constant length  => "List.length".
Extract Inlined Constant app     => "List.append".
Extract Inlined Constant map     => "List.map".
Extract Inlined Constant filter  => "List.filter".

(* timing stuff *)
Extract Inlined Constant time_I_type     => "float".
Extract Inlined Constant time_I_get_time => "Prelude.Time.get_time".
Extract Inlined Constant time_I_sub      => "Prelude.Time.sub_time".
Extract Inlined Constant time_I_2string  => "Prelude.Time.time2string".


(* == crypto stuff == *)
(* === COMMENT OUT THIS PART IF YOU DON'T WANT TO USE KEYS === *)
(* Extract Inlined Constant raft_sending_key   => "Nocrypto.Rsa.priv". *)
(* Extract Inlined Constant raft_receiving_key => "Nocrypto.Rsa.pub". *)
(* Extract Inlined Constant raft_lookup_replica_sending_key   => "RsaKeyFun.lookup_replica_sending_key". *)
(* Extract Inlined Constant raft_lookup_replica_receiving_key => "RsaKeyFun.lookup_replica_receiving_key". *)
(* Extract Inlined Constant raft_lookup_client_receiving_key  => "RsaKeyFun.lookup_client_receiving_key". *)

(* Extract Inlined Constant raft_create_signature => "RsaKeyFun.sign_list". *)
(* Extract Inlined Constant raft_verify_signature => "RsaKeyFun.verify_one". *)
(* Extract Inlined Constant raft_token => "Cstruct.t". *)
(* Extract Inlined Constant raft_token_deq => "(=)". *)
(* === --- === *)


(* == hashing stuff == *)
(* Extract Inlined Constant raft_digest => "Cstruct.t". *)
(* Extract Inlined Constant raft_digest_deq => "(=)". *)
(* Extract Inlined Constant raft_simple_create_hash_messages => "Obj.magic (Hash.create_hash_objects)". *)
(* Extract Inlined Constant raft_simple_verify_hash_messages => "Obj.magic (Hash.verify_hash_objects)". *)
(* Extract Inlined Constant raft_simple_create_hash_state_last_reply => "Obj.magic (Hash.create_hash_pair)". *)
(* Extract Inlined Constant raft_simple_verify_hash_state_last_reply => "Obj.magic (Hash.verify_hash_pair)". *)
(* === --- === *)

Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.

Definition local_replica (*(F C : nat)*) :=
  @RaftreplicaSM (@Raft_I_context).

Extraction "RaftReplicaEx.ml" state2string lrun_sm RaftdummySM local_replica DirectedMsgs2string.
