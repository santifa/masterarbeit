(*
 * This is the header file defining the basics of the raft
 * protocol with velisarios.
 *)

(* find what the quorum file defines, maybe not needed? *)
Require Export Velisarios.Quorum.
Require Export Velisarios.Process.

Section RaftHeader.

  (* needed? *)
  Local Open Scope eo.
  Local Open Scope proc.

  (* define the basic context which is included into the raft replicas *)
  Class RaftContext :=
    MkRaftContext
      {
        (* number of faults *)
        F : nat;
        (* number of replicas needed *)
        num_replicas := (3 * F) + 1;
        (* the replicas are only some type *)
        Rep : Set;
        (* replicas have decidable equality *)
        rep_deq : Deq Rep;
        (* replicas can be associated with some natural number *)
        reps2nat : Rep -> nat_n num_replicas;
        (* the projection is bijective; bijective is defined in Quorum *)
        reps_bij : bijective reps2nat;
        (* the number of clients allowed *)
        num_clients : nat;
        (* clients are just some ordenary type *)
        Client : Set;
        (* clients have decidable equality *)
        client_deq : Deq Client;
        (* clients can be associated with some number *)
        clients2nat : Client -> nat_n num_clients;
        (* the projections ist bijective *)
        clients_bij : bijective clients2nat;
        (* describe the local state machines *)
        RaftSM_state : Set;
        (* the initial state of the state machine *)
        RaftSM_initial_state : RaftSM_state;
      }.

  Context { raft_context : RaftContext }.

  (* define the node types with the arbitrary types defined in the context *)
  Inductive Raftnode :=
  | Raftreplica (n : Rep)
  | Raftclient (n : Client).

  (* extract the replica of some node *)
  Definition node2rep (n : Raftnode) : option Rep :=
    match n with
    | Raftreplica n => Some n
    | _ => None
    end.

  (* extract the client of some node *)
  Definition client2rep (n : Raftnode) : option Client :=
    match n with
    | Raftclient n => Some n
    | _ => None
    end.

  (* prove that some raft node has decidable equality *)
  Lemma RaftnodeDeq : Deq Raftnode.
  Proof.
    introv.
    destruct x as [r1|c1], y as [r2|c2].
    + destruct (rep_deq r1 r2); [left|right]; subst; auto.
      intro xx. inversion xx. subst. tcsp.
    + right; intro xx. inversion xx; subst.
    + right; intro xx. inversion xx; subst.
    + destruct (client_deq c1 c2); [left|right]; subst; auto.
      intro xx. inversion xx. subst. tcsp.
  Defined.

  Global Instance Raft_I_Node : Node := MkNode Raftnode RaftnodeDeq.

  (* ++++++++++++++ Terms ++++++++++++++
   * Terms are the progress steps of the protocol.
   * A term consists of a full round-trip through the system
   * and ends with an agreement of some new state of the system.
   * Also if some difference or failure happens within the system
   * the last terms are rolled back to get the last valid state.
   *)
  Inductive Term := term (n : nat).

  Definition term2nat (t : Term) : nat :=
    match t with
    | term n => n
    end.
  (* define that the term type and nat type are interchangable  *)
  Coercion term2nat : Term >-> nat.

  (* define the term succsessor *)
  Definition next_term (t : Term) : Term := term (S t).
  (* define the term predecessor *)
  Definition pred_term (t : Term) : Term := term (pred t).

  (* prove that terms are decidable *)
  Lemma TermDeq : Deq Term.
  Proof.
    introv. destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  (* define the initial term *)
  Definition initial_term := term 0.

  (* define lesser or equal for two terms *)
  Definition TermLe (t1 t2 : Term) : bool :=
    term2nat t1 <=? term2nat t2.

  (* define lesser for two terms *)
  Definition TermLt (t1 t2 : Term) : bool :=
    term2nat t1 <? term2nat t2.

  (* find the greater term *)
  Definition max_term (t1 t2 : Term) : Term :=
    if TermLe t1 t2 then t2 else t1.

  (* ++++++++++++++ Messsages ++++++++++++++ *)
  Inductive Raftmsg :=
  | Input (n : nat)
  | Heartbeat.

  Global Instance Raft_I_Msg : Msg := MkMsg Raftmsg.

  Definition Raftmsg2status (m : Raftmsg) : msg_status :=
    match m with
    | Input _ => MSG_STATUS_EXTERNAL
    | Heartbeat => MSG_STATUS_INTERNAL
    end.

  Global Instance Raft_I_get_msg_status : MsgStatus := MkMsgStatus Raftmsg2status.


End RaftHeader.
