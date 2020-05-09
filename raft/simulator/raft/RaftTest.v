(*! This file is part of the raft implementation in velisarios !*)

(*! Abstract !*)
(** This file implements some tests and utlities used for checking
 ** the logic of the implementation. Defintions with an export flag
 ** in the comments are used in the OCaml code to test the protocol.
 ** This utilizes a dummy implementation of a possible raft state machine
 ** which only uses natural numbers and addition. **)

Require Export Simulator.
Require Export Protocols.Raft.Raft.
Require Export Ascii String.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section RaftTestInstance.

  (*! Define the test instance !*)
  (** Time **)
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

  (*! Realization of the context definitions !*)
  Definition Faults := 1.
  Definition Clients := 0. (* client is c + 1 *)
  (* Numbers of replicas *)
  Definition num_replicas (F : nat) : nat := 3 * F + 1.
  (* The set of replicas based on the replica numbers *)
  Definition raft_replicas (F : nat) : Set := nat_n (num_replicas Faults).
  (* Show decidable equality *)
  Lemma replica_deq (F : nat) : Deq (raft_replicas F).
  Proof.
    apply nat_n_deq.
  Defined.
  (* Mapping between the number of a replica and the replica itself *)
  Definition reps2nat (F : nat) : raft_replicas F -> nat_n (num_replicas Faults) := fun n => n.
  (* proof reps2nat is bijective *)
  Lemma bijective_reps2nat (F : nat) : bijective (reps2nat F).
  Proof.
    exists (fun n : nat_n (num_replicas Faults) => n); introv; unfold reps2nat; auto.
    Defined.
  Definition nclients (C : nat) := S C.
  Definition raft_client (C : nat) : Set := nat_n (nclients C).
  Definition client0 (C : nat) : raft_client C.
  Proof.
    exists 0. apply leb_correct. unfold nclients. omega.
  Defined.
  (* proof client decidability *)
  Lemma client_deq (C : nat) : Deq (raft_client C).
  Proof.
    apply nat_n_deq.
  Defined.
  Definition clients2nat (C : nat) : raft_client C -> nat_n (nclients C) := fun n => n.
  Lemma bijective_clients2nat (C : nat) : bijective (clients2nat C).
  Proof.
    exists (fun n : nat_n (nclients C) => n); introv; unfold clients2nat; auto.
  Defined.

  (*! Raft state machine !*)
  (** A simple state machine which only adds natural numbers **)
  Definition rstate : Set := nat.
  Definition rstate0 : rstate := 0.
  Definition rresult : Set := nat.
  Definition rcontent : Set := nat.
  Definition rupdate (s : rstate) (c : rcontent) : rstate * rresult := (s + c, s + c).
  Definition nat2string (n : nat) : string := "-". (* used in OCaml *)
  Global Instance Raft_I_context : RaftContext :=
    MkRaftContext
      Faults
      (raft_replicas Faults)
      (replica_deq Faults)
      (reps2nat Faults)
      (bijective_reps2nat Faults)
      (nclients Clients)
      (raft_client Clients)
      (client_deq Clients)
      (clients2nat Clients)
      (bijective_clients2nat Clients)
      rcontent
      nat2string
      rresult
      rstate
      rstate0
      rupdate.

  (*! Tests !*)
  (** Some tests for the most important parts of the raft protocol to validaty logical
   ** correctness. Through the number of faults to tolerate we know that there are 4
   ** nodes in the network. Assign the first as one as leader **)
  Definition leader : RaftState := to_leader state0 replica0.

  (*! Test the next and match index !*)
  Print replica0.
  Compute rep_deq replica0 replica0.
  Compute (decrease_next_index (next_index0 replica0 1) replica0).
  Definition leader_inc := (incr_next_index_all leader).
  Compute gni (node_state leader_inc).
  Compute decrease_next_index (gni (node_state leader_inc)) replica0.

  (*! Test the log !*)
  Definition log1 := add2log [] [(new_term_entry term0)].
  Compute log1.
  Definition log2 := add2log log1 [(new_content_entry term0 3), (new_content_entry term0 4)].
  Compute log2.  (* three elements list *)
  Compute  get_log_entry log2 2.
  Definition s := new_session [] (client0 0).
  Definition log3 := add2log log2
                             [(new_term_entry (term 1)),
                              (new_sessions_entry (term 1) (fst s)),
                              (new_content_entry (term 1) 5)].
  Compute log3.
  Compute get_last_entry log3. (* return content entry 5 *)
  Compute last_session log3. (* get the last session *)
  Compute take_from_log log3 2. (* remove last two added entries *)
  Compute check_entry_term log3 6 (term 1). (* check that content entry 5 is valid *)

  (* test fix_log function 5 entries, term 1 *)
  Compute log3.
  Definition l := (update_log leader log3).
  (* the position 5 is free so just add the new content *)
  Compute (log (fix_log l [(new_content_entry (term 1) 6)] 5 (term 1))).
  (* the logs are considered equal since position 4 has term 1 *)
  Compute (log (fix_log l [(new_content_entry (term 1) 6)] 4 (term 1))).
  (* the logs are considered unequal since the position 4 has not term 0 *)
  Compute (log (fix_log l [(new_content_entry (term 1) 6)] 4 (term 0))).
  (* the logs are considered unequal *)
  Compute (log (fix_log l [(new_content_entry (term 1) 6)] 3 (term 0))).

  (*! Test the caching !*)
  Definition cache := add2cache [] session_id0 request_id0 1.
  Compute cache.
  Compute add_result2cache cache 1 3.
  Compute get_cached_result (add_result2cache cache 1 3) session_id0 request_id0. (* returns 3 *)

  (*! Fake states !*)
  (** For some tests it's handy to have faked states.
   ** The resulting network has four nodes, one leader and three followers. **)
  Definition fake_leader : RaftState :=
    to_leader state0 (nat2rep 0).

  Definition RaftLeaderSM : MStateMachine _ :=
    mkSM
      (replica_update (nat2rep 0))
      (to_leader state0 (nat2rep 0)).

  Definition test_leader := @RaftLeaderSM. (* may be error?! *)
  Definition test_replica := @RaftReplicaSM (@Raft_I_context).


End RaftTestInstance.

Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.

Extraction "RaftReplicaTest.ml" test_replica test_leader.
