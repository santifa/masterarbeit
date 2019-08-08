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

  (* define the abstract state machine *)
  Definition smState : Set := nat.

  (* initialize the global raft context *)
  Global Instance Raft_I_context : RaftContext :=
    MkRaftContext
      F
      (replica F)
      (replica_deq F)
      (reps2nat F)
      (bijective_reps2nat F)
  
      (nclients C)
      (client C)
      (client_deq C)
      (clients2nat C)
      (bijective_clients2nat C)
      smState
      0.
  


 
  (* define some client operations *)
  (* Inductive operation := *)
  (* | opr_add (n : nat) *)
  (* | opr_sub (n : nat). *)

  (* Lemma operation_deq : Deq operation. *)
  (* Proof. *)
  (*   introv; destruct x as [n|n], y as [m|m]; prove_dec; *)
  (*     destruct (deq_nat n m); subst; prove_dec. *)
  (* Defined. *)



  (* ================== PRETTY PRINTING ================== *)

    Fixpoint str_concat (l : list String.string) : String.string :=
    match l with
    | [] => ""
    | s :: ss => String.append s (str_concat ss)
    end.

  (* FIX: to replace when extracting *)
  Definition print_endline : string -> unit := fun _ => tt.
  Definition nat2string (n : nat) : string := "-".

  Definition CR : string := String (ascii_of_nat 13) "".

  (* Fix: to finish *)
  (*Definition tokens2string (toks : Tokens) : string := "-".
*)
  (* Fix: to finish *)
  (* Definition digest2string (d : raft_digest) : string := "-". *)

  (* Fix: to finish *)
  (* Definition result2string (r : result) : string := "-". *)

  (* Fix: there's only one client anyway *)
  Definition client2string (c : client C) : string := "-".

  (* Definition timestamp2string (ts : Timestamp) : string := *)
  (*   match ts with *)
  (*   | time_stamp n => nat2string n *)
  (*   end. *)

  (*Definition view2string (v : View) : string :=
    match v with
    | view n => nat2string n
    end.
*)
  (*Definition seq2string (s : SeqNum) : string :=
    match s with
    | seq_num n => nat2string n
    end.
*)
  (* Definition operation2string (opr : operation) : string := *)
  (*   match opr with *)
  (*   | opr_add n => str_concat ["+", nat2string n] *)
  (*   | opr_sub n => str_concat ["-", nat2string n] *)
  (*   end. *)

  Definition nat_n2string {m} (n : nat_n m) : string := nat2string (proj1_sig n).

  Definition replica2string (r : replica F) : string := nat_n2string r.

(*  Definition bare_request2string (br : Bare_Request) : string :=
    match br with
    | null_req => str_concat [ "null_req"]
    | bare_req opr ts c => str_concat [operation2string opr, ",", timestamp2string ts, ",", client2string c]
    end.

  Definition request2string (r : Request) : string :=
    match r with
    | req br a => str_concat ["REQUEST(", bare_request2string br, ",", tokens2string a, ")"]
    end.

  Fixpoint requests2string (rs : list Request) : string :=
    match rs with
    | [] => ""
    | [r] => request2string r
    | r :: rs => str_concat [request2string r, ",", requests2string rs]
    end.

  Definition bare_pre_prepare2string (bpp : Bare_Pre_prepare) : string :=
    match bpp with
    | bare_pre_prepare v s reqs => str_concat [view2string v, ",", seq2string s, ",", requests2string reqs]
    end.

  Definition bare_prepare2string (bp : Bare_Prepare) : string :=
    match bp with
    | bare_prepare v s d i => str_concat [view2string v, ",", seq2string s, ",", digest2string d, ",", replica2string i]
    end.

  Definition bare_commit2string (bc : Bare_Commit) : string :=
    match bc with
    | bare_commit v s d i => str_concat [view2string v, ",", seq2string s, ",", digest2string d, ",", replica2string i]
    end.

  Definition bare_reply2string (br : Bare_Reply) : string :=
    match br with
    | bare_reply v ts c i res => str_concat [view2string v, ",", timestamp2string ts, ",", client2string c, ",", replica2string i, ",", result2string res]
    end.

  Definition pre_prepare2string (pp : Pre_prepare) : string :=
    match pp with
    | pre_prepare b a => str_concat ["PRE_PREPARE(",bare_pre_prepare2string b, ",", tokens2string a, ")"]
    end.

  Definition prepare2string (p : Prepare) : string :=
    match p with
    | prepare bp a => str_concat ["PREPARE(", bare_prepare2string bp, ",", tokens2string a, ")"]
    end.

  Definition commit2string (c : Commit) : string :=
    match c with
    | commit bc a => str_concat ["COMMIT(", bare_commit2string bc, ",", tokens2string a, ")"]
    end.

  Definition reply2string (r : Reply) : string :=
    match r with
    | reply br a => str_concat ["REPLY(", bare_reply2string br, ",", tokens2string a, ")"]
    end.

  Definition debug2string (d : Debug) : string :=
    match d with
    | debug r s => str_concat ["DEBUG(", replica2string r, ",", s, ")"]
    end.

  Definition bare_checkpoint2string (bc : Bare_Checkpoint) : string :=
    match bc with
    | bare_checkpoint v n d i => str_concat [view2string v, ",", seq2string n, ",", digest2string d, ",", replica2string i]
    end.

  Definition checkpoint2string (c : Checkpoint) : string :=
    match c with
    | checkpoint bc a => str_concat ["CHECKPOINT(", bare_checkpoint2string bc, ",", tokens2string a, ")"]
    end.

  Definition check_ready2string (c : CheckReady) : string := "CHECK-READY()".

  Definition check_stable2string (c : CheckStableChkPt) : string := "CHECK-STABLE()".

  Definition start_timer2string (t : StartTimer) : string :=
    match t with
    | start_timer r v => str_concat ["START-TIMER(", bare_request2string r, "," , view2string v, ")"]
    end.

  Definition expired_timer2string (t : ExpiredTimer) : string :=
    match t with
    | expired_timer r v => str_concat ["EXPIRED-TIMER(", bare_request2string r, "," , view2string v, ")"]
    end.

  (* FIX *)
  Definition stable_chkpt2string (stable : StableChkPt) : string := "-".

  (* FIX *)
  Definition checkpoint_cert2string (cert : CheckpointCert) : string := "-".

  (* FIX *)
  Definition prepared_infos2string (l : list PreparedInfo) : string := "-".

  Definition bare_view_change2string (bvc : Bare_ViewChange) : string :=
    match bvc with
    | bare_view_change v n stable cert preps i =>
      str_concat
        [view2string v,
         ",",
         seq2string n,
         ",",
         stable_chkpt2string stable,
         ",",
         checkpoint_cert2string cert,
         ",",
         prepared_infos2string preps,
         ",",
         replica2string i
        ]
    end.

  Definition view_change2string (vc : ViewChange) : string :=
    match vc with
    | view_change bvc a => str_concat ["VIEW-CHANGE(", bare_view_change2string bvc, ",", tokens2string a, ")"]
    end.

  (* FIX *)
  Definition view_change_cert2string (V : ViewChangeCert) : string := "-".

  Fixpoint pre_prepares2string (l : list Pre_prepare) : string :=
    match l with
    | [] => ""
    | [r] => pre_prepare2string r
    | r :: rs => str_concat [pre_prepare2string r, ",", pre_prepares2string rs]
    end.

  Definition bare_new_view2string (bnv : Bare_NewView) : string :=
    match bnv with
    | bare_new_view v V OP NP =>
      str_concat
        [
          view2string v,
          ",",
          view_change_cert2string V,
          ",",
          pre_prepares2string OP,
          ",",
          pre_prepares2string NP
        ]
    end.

  Definition new_view2string (nv : NewView) : string :=
    match nv with
    | new_view bnv a => str_concat ["NEW-VIEW(", bare_new_view2string bnv, ",", tokens2string a, ")"]
    end.

  Definition check_bcast_new_view2string (c : CheckBCastNewView) : string :=
    match c with
    | check_bcast_new_view i => str_concat ["CHECK-BCAST-NEW-VIEW(", nat2string i, ")"]
    end.

  Definition msg2string (m : PBFTmsg) : string :=
    match m with
    | PBFTrequest r              => request2string r
    | PBFTpre_prepare pp         => pre_prepare2string pp
    | PBFTprepare p              => prepare2string p
    | PBFTcommit c               => commit2string c
    | PBFTcheckpoint c           => checkpoint2string c
    | PBFTcheck_ready c          => check_ready2string c
    | PBFTcheck_stable c         => check_stable2string c
    | PBFTcheck_bcast_new_view c => check_bcast_new_view2string c
    | PBFTstart_timer t          => start_timer2string t
    | PBFTexpired_timer t        => expired_timer2string t
    | PBFTview_change v          => view_change2string v
    | PBFTnew_view v             => new_view2string v
    | PBFTdebug d                => debug2string d
    | PBFTreply r                => reply2string r
    end.
*)
  (* Definition name2string (n : name) : string := *)
  (*   match n with *)
  (*   | Raftleader => "leader" *)
  (*   end. *)

  (* Fixpoint names2string (l : list name) : string := *)
  (*   match l with *)
  (*   | [] => "" *)
  (*   | [n] => name2string n *)
  (*   | n :: ns => str_concat [name2string n, ",", names2string ns] *)
  (*   end. *)

  (* Definition delay2string (delay : nat) : string := nat2string delay. *)

  Definition msg2string (m : Raftmsg) : string :=
    match m with
    | Input n => "Command " ++ nat2string n
    | Heartbeat => "Heartbeat"
    (* | _ => "Other msg" *)
    end.

  (* Definition DirectedMsg2strking (dm : DirectedMsg) : string := *)
  (*   match dm with *)
  (*   | MkDMsg msg dst delay =>  *)
  (*     (* concat ["msg", ":", "[", " dest" , "]", ":"] *) *)
  (*   end. *)

  (* Fixpoint DirectedMsgs2string (l : DirectedMsgs) : string := *)
  (*   match l with *)
  (*   | [] => "" *)
  (*   | [dm] => "msg" (* DirectedMsg2string dm *) *)
  (*   | dm :: dmsgs => str_concat ["mutliple msgs"] (* [DirectedMsg2string dm, CR, DirectedMsgs2string dmsgs] *) *)
  (*   end. *)
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
        ["(Raft state:"
         ,")"
        ].

  (* ================== SYSTEM ================== *)

  

  Definition dummy_initial_state : RaftState :=
    Build_State
      initial_term
      RaftSM_initial_state
      5
      false.

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

Extraction "RaftReplicaEx.ml" state2string lrun_sm RaftdummySM local_replica.
