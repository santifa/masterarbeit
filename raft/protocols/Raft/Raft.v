(*
 * This is the master file for the raft implementation only.
 *)

(* import velisarios *)
Require Export Velisarios.Quorum.
Require Export Velisarios.Process.
Require Export String.
Require Export Peano.
Require Export List.


Section Raft.

  Local Open Scope eo.
  Local Open Scope proc.

  (* define a context configuration for all nodes *)
  Class Raftcontext :=
    MkRaftContext
      {
        (* define the amount of clients and the bijective homomorphism  *)
        clients : nat;
        C : Set;
        client_deq : Deq C;
        clients2nat : C -> nat_n clients;
        clients_bji : bijective clients2nat;

        (* define the amount of replicas by num faults and the bijective homomorphism *)
        F : nat;
        reps := (3 * F) + 1;
        Rep : Set;
        rep_deq : Deq Rep;
        reps2nat : Rep -> nat_n reps;
        reps_bij : bijective reps2nat;
      }.

  Context { raft_context : Raftcontext }.

  (* define the node types *)
  Inductive Raftnode :=
  (* handles client io, issues log replication max 1 *)
  | Replica (n : Rep)
  (* issue state change requests *)
  | Client (n : C).

  (* prove decidable equality for the nodes *)
  Lemma Deq_Raftnode : Deq Raftnode.
  Proof.
    introv; destruct x as [r1|c1], y as [r2|c2].
    + destruct (rep_deq r1 r2); [left|right]; subst; auto.
      intro xx; inversion xx; subst; tcsp.
    + right; intro xx; inversion xx; subst; tcsp.
    + right; intro xx; inversion xx; subst; tcsp.
    + destruct (client_deq c1 c2); [left|right]; subst; auto.
      intro xx; inversion xx; subst; tcsp.
  Qed.

  Global Instance Raft_I_Node : Node := MkNode Raftnode Deq_Raftnode.

  (* define the quorum context *)
  Lemma Replica_inj : injective Replica.
  Proof.
    introv h; ginv; auto.
  Qed.

  Global Instance Raft_I_Quorum : Quorum_context :=
    MkQuorumContext
      Rep
      reps
      rep_deq
      reps2nat
      reps_bij
      Replica
      Replica_inj.

  Definition rep2node := Rep -> node_type.





  Inductive Raftmsg :=
  (* the leader signals it's alive *)
  | Heartbeat
  (* reply the new term number to the client *)
  | Reply (new_term_num : nat) (c : C)
  (* the command issued by the client - here new term number *)
  | Command (term_num : nat).

  Global Instance Raft_I_Msg : Msg := MkMsg Raftmsg.

  Definition Raft_msg_status (m : msg) : msg_status :=
    match m with
    (* flag the heartbeat msg as system internal message *)
    | Heartbeat => MSG_STATUS_INTERNAL
    (* the outgoing reply to the client is set to internal? *)
    | Reply _ _ => MSG_STATUS_INTERNAL
    (* flag the command msg as from outside the system *)
    | Command _ => MSG_STATUS_EXTERNAL
    end.

  Global Instance Raft_I_MsgStatus : MsgStatus := MkMsgStatus Raft_msg_status.

  (* receive a message from the client and extract the number *)
  Definition receive_command (m : Raftmsg) : option nat :=
    match m with
    | Command n => Some n
    | _ => None
    end.

  Definition send_command (n : nat) (names : list name) : DirectedMsg :=
    MkDMsg (Command n) names 0.

  Inductive Raftleader_state :=
    (* the current term of the global network *)
  | Term (term_num : nat).

  (* define the update function of the leader *)
  Definition leader_update : MSUpdate Raftleader_state :=
    fun state input =>
      match state, input with
      (* update the term_num and reply to the client *)
      | Term n, Command m => (Term m, [])
      (* ignore other messages *)
      | _, _ => (state, [])
      end.

  (* initialize the state machines ? *)
  Arguments MkSM      [S] [I] [O] _ _ _.
  Arguments sm_halted [S] [I] [O] _.
  Arguments sm_state  [S] [I] [O] _.
  Arguments sm_update [S] [I] [O] _ _ _.

  (* initialize the leader state machine *)
  Definition RaftleaderSM : MStateMachine Raftleader_state :=
    mkSSM leader_update (Term 0).

  (* link the node name to the state definition *)
  Definition Raftstate (n : name) :=
    match n with
    | Raftleader => Raftleader_state
    end.

  (* link the node name with the state ?? *)
  Definition Raftusys : MUSystem Raftstate :=
    fun name =>
      match name return StateMachine (Raftstate name) msg DirectedMsgs with
      | Raftleader => RaftleaderSM
      end.

  Definition Raftsys : System :=
    fun name =>
      match name with
      | Raftleader => build_sprocess leader_update (Term 0)
      end.

  (* authencation interfaces *)
  Instance Raft_I_Key : Key := MkKey unit unit.

  Instance Raft_I_Data : Data := MkData Raftmsg.

  Instance Raft_I_AuthTok : AuthTok := MkAuthTok unit Deq_unit.

  Instance Raft_I_AuthFun : AuthFun :=
    MkAuthFun
      (fun _ _ => [tt])
      (fun _ _ _ _ => true).

  (* authenticate data, match messages with nodes which issued them
   * ignore n since nobody sents a message to itself *)
  (* Definition Raftdata_auth : name -> Raftmsg -> option name := *)
  (*   fun n m => *)
  (*     match m with *)
  (*     | Heartbeat => Some Replica *)
  (*     | Reply _ _ => Some Replica *)
  (*     | Command _ => Some Client *)
  (*     end. *)

  (* (* link authentication function to the abstract authenticated data type *) *)
  (* Instance Raft_I_DataAuth : DataAuth := MkDataAuth Raftdata_auth. *)

  (* (* create nested authdata; tt indicates that the data is authenticated *) *)
  (* Instance Raft_I_ContainedAuthData : ContainedAuthData := *)
  (*   MkContainedAuthData (fun m => [MkAuthData m [tt]]). *)

  (* tactic hints ? *)
  (* QUESTION: Can we avoid repeating this? *)
  Hint Rewrite @map_option_option_map : option.
  Hint Rewrite @option_map_option_map : option.

  (* QUESTION: Can we export this automatically *)
  Hint Resolve if_not_first_if_first : eo.

End Raft.
