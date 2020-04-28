(*! This file is part of the raft implementation with velisarios. !*)


(*! Context definitions !*)
(** This file defines the context, which means the abstract definitions replaced
 ** by the realization of some program. Also, the definition of a node and the
 ** realization of a quorum. **)
Require Export Velisarios.Quorum.
(* the process module provides the abstraction which is implemented by the protocols *)
Require Export Velisarios.Process.
Require Export String.

Section RaftContext.

  (* needed? *)
  Local Open Scope eo.
  Local Open Scope proc.

  (*! Context !*)
  (** The context provides abstract definitions which are replaced by real ones
   ** within the simulation. **)
  Class RaftContext :=
    MkRaftContext
      {
        (* number of possible faults *)
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

        (* the content type for the log *)
        Content : Set;
        (* get a textual representation from the content *)
        content2string : Content -> string;
        (* This is the state of the program to distribute. *)
        RaftSM : Set;
        (* the result type which gets issued by the state update function *)
        RaftSM_result : Set;
        (* the initial state of the state machine *)
        RaftSM_initial_state : RaftSM;
        (* the update function which produces a new state and a result. *)
        RaftSM_update_state : RaftSM -> Content -> RaftSM * RaftSM_result
      }.
  (** To get this construct clear: The proposed functions and types are used by the protocol
   ** but get instantiated in the RaftSim.v file or some other file which uses the raft protocol. **)

  (** Declares the context type class as new variable with implicit
   ** generalization of free terms. Since everything is typed no free terms are gneralized? **)
  Context { raft_context : RaftContext }.


  (*! Nodes !*)
  (** Nodes are used to distinguish between server and clients.
   ** The parameters are defined in the RaftContext, the real implementation is provided by the simulation. **)
  Inductive RaftNode :=
  (* The normal server is a replica which is denoted by the nat/name Rep provided as context information. *)
  | replica (n : Rep)
  (* The other node is the client which is in fact not modeled within COQ.
   * It is modeled in ocaml outside the protocol and only feeds the input. *)
  | client (n : Client).

  (** Get the replica name/nat of some node. **)
  Definition replica2rep (n : RaftNode) : option Rep :=
    match n with
    | replica n => Some n
    | _ => None
    end.

  (** Get the client name/nat of some node. **)
  Definition client2rep (n : RaftNode) : option Client :=
    match n with
    | client n => Some n
    | _ => None
    end.

  (** Prove that raft nodes have decidable equality like the one from Leibnitz. **)
  Lemma RaftnodeDeq : Deq RaftNode.
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

  (** Bind the real node definition as instance to the abstract definition from velisarios. **)
  Global Instance Raft_I_Node : Node := MkNode RaftNode RaftnodeDeq.

  (*! Quorum instance !*)
  (** Replicas are an injective image between names/nats and real implementations **)
  Lemma replica_inj : injective replica.
  Proof.
    introv h. ginv. auto.
  Qed.

  (** Define a quorum as a set of node names with the property of being
   ** depictable into the set of natural numbers. **)
  Global Instance Raft_I_Quorum : Quorum_context :=
    MkQuorumContext
      Rep (* the node type *)
      num_replicas (* size of the set *)
      rep_deq (* the nodes have to be decidable equality *)
      reps2nat (* fn which translates nodes to nats *)
      reps_bij (* node translation is bijective *)
      replica (* the inductive arm indicates the nodes name *)
      replica_inj. (* prove that the function is injective *)

  (* can we have something like this?
   * Since Rep is the node type it would be Rep->Rep *)
  Definition rep2node := Rep -> node_type.

  (*! More about nodes !*)
  (* 0 is less than 2*F+1 *)
  Definition nat_n_2Fp1_0 : nat_n num_replicas.
  Proof.
    exists 0.
    apply leb_correct.
    unfold num_replicas.
    omega.
  Defined.

  Definition replica0 : Rep := bij_inv reps_bij nat_n_2Fp1_0.

  Eval simpl in (name_dec (replica replica0) (replica replica0)).

  (* We'll return the node as given by our bijection if n < num_nodes,
     otherwise we return a default value (replica0) *)
  Definition nat2rep (n : nat) : Rep.
  Proof.
    destruct reps_bij as [f a b].
    destruct (lt_dec n num_replicas) as [d|d].
    - exact (f (mk_nat_n d)). (* here we now that n < num_replicas so we can use our bijection *)
    - exact replica0. (* here num_replicas <= n, so we return a default value: replica0 *)
  Defined.

  Definition reps : list Rep := (* list all nodes *)
   mapin
      (seq 0 num_replicas)
      (fun n i => bij_inv reps_bij (mk_nat_n (seq_0_lt i))).

  (* Convert node list to name list *)
  Definition nreps : list name := map replica reps.

  Lemma reps_prop : forall (x : Rep), In x reps.
  Proof.
    exact nodes_prop.
  Qed.

  Definition clients : list Client := (* list all clients *)
    mapin
      (seq 0 num_clients)
      (fun n i => bij_inv clients_bij (mk_nat_n (seq_0_lt i))).

  (* Convert client list to client name list *)
  Definition nclients : list name := map client clients.

  Lemma clients_prop : forall (x : Client), In x clients.
  Proof.
    introv.
    unfold clients.
    apply in_mapin.


    remember (clients2nat x) as nx.
    destruct nx as [nx condnx].

    pose proof (leb_complete _ _ condnx) as c.

    assert (In nx (seq O num_clients)) as i.
    { apply in_seq; omega. }

    exists nx i; simpl.

    unfold mk_nat_n.
    unfold bij_inv.
    destruct clients_bij.
    pose proof (bij_id1 x) as h.
    rewrite <- Heqnx in h; subst; simpl.

    f_equal; f_equal.
    apply UIP_dec; apply bool_dec.
  Qed.

  (*! Utilities !*)
  (** From the definition that lists all created replicas. **)
  Definition other_replicas (r : Rep) : list Rep := remove_elt rep_deq r reps.
  Definition other_names (r : Rep) : list name := map replica (other_replicas r).

End RaftContext.
