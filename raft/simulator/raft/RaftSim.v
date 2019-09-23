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

  (*! notations !*)
  Notation Log := (list Entry).
  Notation Sessions := (list (SessionId * Client)).

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
  Definition raft_replica (F : nat) : Set := nat_n (num_replicas F).

  (** Replicas have decidable equality. **)
  Lemma replica_deq (F : nat) : Deq (raft_replica F).
  Proof.
    apply nat_n_deq.
  Defined.

  (** Convert between the replicas and the numbers indicating the replica **)
  Definition reps2nat (F : nat) : raft_replica F -> nat_n (num_replicas F) := fun n => n.

  (** Show that the function is bijective. **)
  Lemma bijective_reps2nat (F : nat) : bijective (reps2nat F).
  Proof.
    exists (fun n : nat_n (num_replicas F) => n); introv; unfold reps2nat; auto.
  Defined.

  (** Return the number of clients needed for a given amount. **)
  Definition nclients (C : nat) : nat := S C.

  (** Create the map of clients and it's natural representation. **)
  Definition raft_client (C : nat) : Set := nat_n (nclients C).

  (** Proof that the definition client holds for one client. **)
  Definition client0 (C : nat) : raft_client C.
  Proof.
    exists 0.
    apply leb_correct.
    unfold nclients.
    omega.
  Defined.

  (** Proof that proposed clients have decidable equality. **)
  Lemma client_deq (C : nat) : Deq (raft_client C).
  Proof.
    apply nat_n_deq.
  Defined.

  (** Convert between clients and their numeral representations. **)
  Definition clients2nat (C : nat) : raft_client C -> nat_n (nclients C) := fun n => n.

  (** Proof that the conversion is bijective. **)
  Lemma bijective_clients2nat (C : nat) : bijective (clients2nat C).
  Proof.
    exists (fun n : nat_n (nclients C) => n); introv; unfold clients2nat; auto.
  Defined.

  (** Define the state machines type **)
  Definition smState : Set := nat.
  Definition result : Set := nat.
  Definition content : Set := nat.

  Definition update_sm (s : smState) (c : content) :=
    let s' := s + c in
    (s', s').

  (* Convert a natural number to a string. use the ocaml fn
   * Predefined for usage in the context. *)
  Definition nat2string (n : nat) : string := "-".

  (** Initialize the global context **)
  Global Instance Raft_I_context : RaftContext :=
    MkRaftContext
      F (* faults *)
      (raft_replica F) (* replica type *)
      (replica_deq F) (* replica decidability *)
      (reps2nat F)  (* replica 2 nat conversion *)
      (bijective_reps2nat F) (* proof that conversion is bijective *)

      (nclients C) (* number of clients *)
      (raft_client C) (* client type *)
      (client_deq C) (* client decidability *)
      (clients2nat C) (* client 2 nat conversion *)
      (bijective_clients2nat C) (* proof that conversion is bijective *)
      1000 (* timeout in ms *)
      content (* content type *)
      nat2string (* content -> string *)
      result (* result type *)
      smState (* state machine type *)
      0 (* initial state *)
      update_sm.

  Check MkEntry (term 0) 0.

  (** Some examples **)
  Definition l : Log := [new_entry (term 0) 0, new_entry (term 1) 1].
  Definition l2 : Log := [new_entry (term 0) 0, new_entry (term 1) 3].
  Compute(get_last_log_term l).
  Compute (get_last_log_index l2).
  Compute (check_last_log 2 (term 1) l).
  Compute (check_last_log 1 (term 0) []).
  Compute (check_last_log 3 (term 2) l).
  Compute (take_from_log 0 l).
  Compute (take_from_log 1 l).


  (*! Pretty printing !*)
  (** Rules for pretty printing:
   ** - Every inductive type should get a string representation for all cases.
   ** - For a type it should be "<Name>: " and
   **   - if there is only one parameter, the parameter as string
   **   - if there are multiple parameter, a tuple of the string representations like
   **     "{<Name1>: <p1>, <Name2>: <p2>}"
   ** - Records are handled likewise
   ** - list are surrounded by brackets "[<entry1>, <entry2>]" **)

  (** concat a list of string to one string. **)
  Fixpoint str_concat (l : list String.string) : String.string :=
    match l with
    | [] => ""
    | s :: ss => String.append s (str_concat ss)
    end.

  (** auxilary function which converts a list of some type to its representation. **)
  Fixpoint list2string_aux {A : Type} (l : list A) (s : A -> string) : string :=
    match l with
    | [] => ""
    | [x] => s x
    | x :: xs => str_concat [s x, ", ", list2string_aux xs s]
    end.

  (** Convert a list to a string according the rules. **)
  Definition list2string {A : Type} (l : list A) (s : A -> string) : string :=
    str_concat ["[", list2string_aux l s, "]"].

  (* FIX: to replace when extracting *)
  (** The next three functions are placeholder functions which are later
   ** replaced by real ocaml function within the extraction process. **)
  (** line feed **)
  Definition LF : string := String (ascii_of_nat 10) "".
  Definition print_endline : string -> unit := fun _ => tt.

  Fixpoint record_concat (n : string) (l : list String.string) : string :=
    str_concat [n, ": {", list2string_aux l (fun x => x), "}"].

  (** Use this to get convert a named number to a string. **)
  Definition number2string (name : string) (i : nat) : string :=
    str_concat [name, ": ", nat2string i].

  (* Fix: there's only one client anyway *)
  (** Name the client **)
  Definition client2string (c : raft_client C) : string := str_concat ["Client: ", nat2string C].

  Definition nat_n2string {m} (n : nat_n m) : string := nat2string (proj1_sig n).
  (** Fetch the replica number from the map **)

  Definition replica2string (r : raft_replica F) : string :=
    str_concat ["Replica: ", nat_n2string r].

  Definition replica_option2string (r : option Rep) : string :=
    match r with
    | None => "None"
    | Some r => replica2string r
    end.

  (** The following defintions convert the basic types according the rules. **)
  Definition term2string (t : Term) : string :=
    match t with
    | term n => number2string "Term" n
    end.

  Definition session_id2string (s : SessionId) :=
    match s with
    | session_id i => number2string "Session" i
    end.

  Definition session2string (s : (SessionId * Client)) : string :=
    match s with
    | (sid, c) => record_concat "Session" [session_id2string sid, client2string c]
    end.

  Definition register_client2string (r : RegisterClient) :=
    match r with
    | register_client c => str_concat ["Register: ", client2string c]
    end.

  Definition request_id2string (r : RequestId) :=
    match r with
    | request_id i => number2string "Request" i
    end.

  Definition cmd2string (c : nat) : string := number2string "Cmd" c.

  Definition request2string (r : ClientRequest) : string :=
    match r with
    | client_request cl sid rid c =>
      record_concat "Request" [client2string cl, session_id2string sid,
                               request_id2string rid, cmd2string c]
    end.

  Definition entry2string (e : Entry) : string :=
    match e as e' with
    | MkEntry t content =>
      record_concat "Entry" [term2string t, content2string content]
    end.

  Definition log2string (l : list Entry) : string :=
    str_concat ["Log: ", list2string l entry2string].

  Definition committed2string (l : list Entry) : string :=
    str_concat ["Committed: ", list2string l entry2string].

  (** Entries are basically the same but are used semantically within append entries messages
   ** and not within the replica states. **)
  Definition entries2string (l : list Entry) : string :=
    str_concat ["Entries: ", list2string l entry2string].

  Definition last_log_index2string (i : nat) : string := number2string "Last_log_index" i.
  Definition last_log_term2string (t : nat) : string := number2string "Last_log_term" t.
  Definition commit_index2string (i : nat) : string := number2string "Commit_index" i.

  Definition append_entries2string (a : AppendEntries) : string :=
    match a with
    | heartbeat => "Heartbeat"
    | replicate t r lli llt ci e =>
      record_concat "Replicate"
                    [term2string t, replica2string r, last_log_index2string lli,
                     last_log_term2string llt, commit_index2string ci, entries2string e]
    end.

  Definition request_vote2string (r : RequestVote) : string :=
    match r with
    | request_vote t c lli llt =>
      record_concat "RequestVote"
                    [term2string t, replica2string c,
                     last_log_index2string lli, last_log_term2string llt]
    end.

  Definition bool2string (b : bool) : string :=
    match b with
    | true => "true"
    | false => "false"
    end.

  Definition result2string (r : Result) : string :=
    match r with
    | client_res res => number2string "ClientResult" res
    | append_entries_res s t =>
      record_concat "AppendEntriesResult"
                    [str_concat ["Success: ", bool2string s], term2string t]
    | request_vote_res v t =>
      record_concat "RequestVoteResult"
                    [str_concat ["Vote_granted: ", bool2string v], term2string t]
    | register_client_res s sid l =>
      record_concat "RegisterClientResult"
                    [str_concat ["Registered:", bool2string s],
                     session_id2string sid, replica_option2string l]
    end.


  Fixpoint msg2string (m : RaftMsg) : string :=
    match m with
    | register_msg m => register_client2string m
    | register_result_msg m => result2string m
    | broadcast_sessions_msg m =>  str_concat ["Broadcast: ", list2string m session2string]
    | request_msg r => request2string r
    | response_msg r => result2string r
    | append_entries_msg r => append_entries2string r
    | append_entries_result_msg r => result2string r
    | request_vote_msg r => request_vote2string r
    | response_vote_msg r => result2string r
    | forward_msg m => str_concat ["Forward: ", msg2string m]
    end.

  (* convert the node types to names *)
  Definition name2string (n : name) : string :=
    match n with
    | replica r => replica2string r
    | client c => client2string c
    end.

  (* maybe wrong name *)
  Definition names2string (l : list name) : string :=
    str_concat ["Dst: ", list2string l name2string].

  (** A direct message as some sort of possible delay **)
  Definition delay2string (delay : nat) : string := str_concat ["Delay: ", nat2string delay].

  (** convert a message which is send directly to the nodes into a string **)
  Definition DirectedMsg2string (dm : DirectedMsg) : string :=
    match dm with
    | MkDMsg msg dst delay =>
      record_concat "message" [msg2string msg, names2string dst, delay2string delay]
    end.

  Definition DirectedMsgs2string (l : DirectedMsgs) : string :=
    str_concat ["Dmsgs: ", list2string l DirectedMsg2string].



  Definition TimedDirectedMsg2string (m : TimedDirectedMsg) : string :=
    match m with
    | MkTimedDMsg dm time => str_concat [DirectedMsg2string dm, ":", time_I_2string time]
    end.

  Definition TimedDirectedMsgs2string (l : TimedDirectedMsgs) :=
    str_concat ["Tdmsgs: ", list2string l TimedDirectedMsg2string].

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


  (** Convert a NextIndex element into a string tuple. **)
  Definition index2string (i : Index) : string :=
    str_concat ["(i: ", nat2string (index2nat i), ", e: ", replica2string (index2rep i), ")"].

  (** This function takes the first list index name and iterates through the list
   ** concatenating the index and entry value as tuple. **)
  Fixpoint indexed_list2string (l : NextIndex) : string :=
    match l with
    | [] => ""
    | [x] => index2string x
    | x :: xs => str_concat [index2string x, ", ", indexed_list2string xs]
    end.

  Definition next_index2string (l : NextIndex) : string :=
    str_concat ["Next_index: [", indexed_list2string l, "]"].

  Definition match_index2string (l : MatchIndex) : string :=
    str_concat ["Match_index: [", indexed_list2string l, "]"].

  (** Give a string representation from the leader state if some **)
  Definition leader_state2string (l : LeaderState) : string :=
      record_concat "Leader" ["yes",
                              next_index2string (next_index l),
                              match_index2string (match_index l)].
  
  Definition current_leader2string (c : option Rep) : string :=
    match c with
    | None => "Current_leader: None"
    | Some n => str_concat ["Current_leader: ", replica2string n]
    end.

  Definition voted_for2string (c : option nat) : string :=
    match c with
    | None => "Voted_for: None"
    | Some n => str_concat ["Voted_for: ", nat2string n]
    end.

  Definition node_state2string (s : NodeState) : string :=
    match s with
    | leader l => leader_state2string l
    | follower => "Follower"
    | candidate => "Candidate"
    end.

    (** Give a string representation of some nodes states **)
  Definition state2string (s : RaftState) : string :=
    record_concat "Replica state"
                  [term2string (current_term s),
                   str_concat ["Sessions: ", list2string (sessions s) session2string],
                   voted_for2string (voted_for s),
                   log2string (log s),
                   commit_index2string (commit_index s),
                   number2string "Last_Applied" (last_applied s),
                   current_leader2string (current_leader s),
                   node_state2string (node_state s)].

  (*! System definition !*)
  (** this is the initial replica state which is used to create
   ** a network of replicas. **)
  (* Definition dummy_initial_state : RaftState := *)
    (* Build_State *)
    (*   initial_term *)
    (*   None *)
    (*   [] *)
    (*   0 *)
    (*   0 *)
    (*   5 *)
    (*   RaftSM_initial_state *)
    (*   no_leader_state. *)

  (** This is a special purpose state, which initiates a leader.
   ** Providing an initial leader is not inteded by the raft protocol.
   ** This state assumes that the network has 3 followers. **)
  Definition dummy_leader_state : RaftState :=
    Build_State
      term0
      []
      None
      []
      0
      0
      5
      RaftSM_initial_state
      (leader (init_leader_state [1, 2, 3]))
      (Some (nat2rep 0))
      [0; 1; 2; 3].

  (** Provide the dummy state machine defined within raft.v **)
  Definition RaftdummySM : MStateMachine RaftState :=
    MhaltedSM state0 (* dummy_initial_state *).

  Definition Raftmono_sys : NMStateMachine RaftState :=
    fun name =>
      match name with
      | replica n => RaftReplicaSM n
      | _ => MhaltedSM state0
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


Definition local_replica (*(F C : nat)*) (leader : bool) :=
  if leader then @RaftLeaderreplicaSM (@Raft_I_context)
  else @RaftReplicaSM (@Raft_I_context).

Extraction "RaftReplicaEx.ml" state2string lrun_sm RaftdummySM local_replica DirectedMsgs2string.
