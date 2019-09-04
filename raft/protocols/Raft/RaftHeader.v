(*!
 * This is the header file defining the basics of the raft
 * protocol with velisarios.
 !*)

(* find what the quorum file defines, maybe not needed? *)
Require Export Velisarios.Quorum.
(* the process module provides the abstraction which is implemented by the protocols *)
Require Export Velisarios.Process.
Require Export String.

(*! abstract topology !*)
(** This section defines the topology of raft which is modeled as an agent
 ** based network. Here a topology describes the set of nodes within the network,
 ** the messages which can be exchanged in the network and the basics context which
 ** can be used by every node, called context. Other basic aspects of the
 ** protocol are also defined here, like progress terms. **)
Section RaftHeader.

  (* needed? *)
  Local Open Scope eo.
  Local Open Scope proc.

  (*! Context definition !*)
  (** The type class raft context provides a set of methods as dependent record.
   ** The raft context defines some basics which are used throughout all replicas.
   ** This context shall be binded by some real instance within the rest of the protocol. **)
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
        (* this should be the base timerout for the leader election
         * where no followers should start at the same moment with voting. *)
        base_timeout : nat;
        (* the content type for the log *)
        content_type : Set;
        (* get a textual representation from the content *)
        content2string : content_type -> string;
      }.

  (** Declares the context type class as new variable with implicit
   ** generalization of free terms. Since everything is typed no free terms
   ** are gneralized? **)
  Context { raft_context : RaftContext }.

  (*! Nodes !*)
  (** Define the types of nodes which are used in the system. **)
  Inductive Raftnode :=
  (* The normal replica node which is either leader or follower.
   * The parameter is defined in the context as natural number.
   * A replica has three internal states which are hidden by this definition.
   * 1. follower mode: The basic mode where the node is passive and
   *    only responds to incoming messages.
   * 2. leader mode: The replica handles all client interactions and log replication.
   *    Only one is allowed in every term.
   * 3. candidate mode: Used for the leader election and at
   *    this point all nodes are considered as possible candidates.
   * This modes or states are hidden within the replica context. *)
  | Raftreplica (n : Rep)
  (* The other node is the client which is in fact outside the agent based system
   * and only feeds the other nodes with input. The parameter is defined in the context
   * as natural number *)
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

  (** Prove that raft nodes have decidable equality like the one from Leibnitz. **)
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

  (** Bind the real node definition as instance to the abstract definition from veliarios. **)
  Global Instance Raft_I_Node : Node := MkNode Raftnode RaftnodeDeq.

  (*! TODO: Add more notes to this section!*)
  (*! Quorum instance !*)
  Lemma Raftreplica_inj : injective Raftreplica.
  Proof.
    introv h; ginv; auto.
  Qed.

  Global Instance Raft_I_Quorum : Quorum_context :=
    MkQuorumContext
      Rep
      num_replicas
      rep_deq
      reps2nat
      reps_bij
      Raftreplica
      Raftreplica_inj.

  (* can we have something like this? *)
  Definition rep2node := Rep -> node_type.

  (*! TODO: Add more notes to this section !*)
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

  (*Eval simpl in (name_dec (PBFTreplica replica0) (PBFTreplica replica0)).*)

  (* We'll return the node as given by our bijection if n < num_nodes,
     otherwise we return a default value (replica0)
   *)
  Definition nat2rep (n : nat) : Rep.
  Proof.
    destruct reps_bij as [f a b].
    destruct (lt_dec n num_replicas) as [d|d].
    - exact (f (mk_nat_n d)). (* here we now that n < num_replicas so we can use our bijection *)
    - exact replica0. (* here num_replicas <= n, so we return a default value: replica0 *)
  Defined.


  Definition reps : list Rep := (* nodes. *)
   mapin
      (seq 0 num_replicas)
      (fun n i => bij_inv reps_bij (mk_nat_n (seq_0_lt i))).

  Definition nreps : list name := map Raftreplica reps.

  Lemma reps_prop : forall (x : Rep), In x reps.
  Proof.
    exact nodes_prop.
  Qed.

  Definition clients : list Client :=
    mapin
      (seq 0 num_clients)
      (fun n i => bij_inv clients_bij (mk_nat_n (seq_0_lt i))).

  Definition nclients : list name := map Raftclient clients.

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

  (*! Here are the definitions for the types used in within the messages and states !*)

  (*! Terms and progress !*)
  (** Within this protocol the global time is divided into chunks called terms.
   ** A term starts with the leader election protocol part and
   **   ends with the supposed failure a leader.
   ** A term has at most one leader (none if election failed) and
   **   the current term is maintained by all nodes in the system.
   ** The main idea is to identify outdated data within the replicated log. **)
  Inductive Term := term (n : nat).

  (** A term is referenced by some number which is increased monotonic. **)
  Definition term2nat (t : Term) : nat :=
    match t with
    | term n => n
    end.
  (* define that the term type and nat type are interchangable *)
  Coercion term2nat : Term >-> nat.

  (** The successor of some term is the term with the next natural number. **)
  Definition next_term (t : Term) : Term := term (S t).
  (** The predecessor is the term with the preceding natural number. **)
  Definition pred_term (t : Term) : Term := term (pred t).

  (** Prove that terms have decidable equality. **)
  Lemma TermDeq : Deq Term.
  Proof.
    introv. destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  (** On boot the first term start with zero. **)
  Definition initial_term := term 0.

  (** Test wether term 1 is lesser or equal than term 2. **)
  Definition TermLe (t1 t2 : Term) : bool :=
    term2nat t1 <=? term2nat t2.

  (** Test wether term 1 is lesser than term 2. **)
  Definition TermLt (t1 t2 : Term) : bool :=
    term2nat t1 <? term2nat t2.

  (** Test which term is greater and return it. **)
  Definition max_term (t1 t2 : Term) : Term :=
    if TermLe t1 t2 then t2 else t1.

  (*! next index !*)
  (** The next index is a list of the tuple server id and the
   ** next possible index for the server.
   ** The leaders initializes this list every time to last log index + 1.
   ** The index of a node is increased monotonically if an append entries
   ** message is send to the node **)
  Inductive NextIndex :=
  | next (rep : Rep) (next_index : nat).

  (** A convient notation for a list of next indices **)
  Notation nindex := (list NextIndex).


  (** Create a new next index list out of list of nodes and an initial value **)
  Fixpoint create_next_index (reps : list Rep) (n : nat) : nindex :=
    match reps with
    | [] => []
    | r :: rs => next r n  :: create_next_index rs n
    end.

  (** Increase some index **)
  Definition increase_next_index_e (n : NextIndex) : NextIndex :=
    match n with
    | next r ni => next r (ni + 1)
    end.

  (** Increase an element in the next index list **)
  Fixpoint increase_next_index (l : nindex) (rep : Rep) : nindex :=
    match l with
    | [] => l (* return list if last element reached *)
    | (next r _) as x :: xs => if (rep_deq r rep)
                          then increase_next_index_e x :: xs
                          else x :: increase_next_index xs rep
    end.

  (** Return some index if the node is found **)
  Fixpoint get_next_index (l : nindex) (rep : Rep) : option nat :=
    match l with
    | [] => None (* the node is not found *)
    | (next r i) :: xs => if (rep_deq r rep)
                        then Some i
                        else get_next_index xs rep
    end.

  (*! match index !*)
  (** The list of match indices is basically the same as the list of next indices
   ** so the definition are just wrappers about the next index functions.
   ** The next index stores for a server the index which it knows is replicated by the
   ** node. One can see this list as mechanism to track the which server has applied
   ** an append entries message to its local log. **)
  Notation mindex := (list NextIndex).

  Definition create_match_index (reps : list Rep) : mindex := create_next_index reps 0.

  Definition increase_match_index (l : mindex) (rep : Rep) := increase_next_index l rep.

  Definition get_match_index (l : mindex) (rep : Rep) := get_next_index l rep.

  (*! Log !*)
  (** An entry in the log takes the term where it is added to the log and
   ** the content which gets added to the log.
   ** TODO: The content is a parametrized type.
   **
   ** Log matching property
   ** 1. If 2 entries in different logs have the same index and term they store the same command.
   ** 2. If 2 entries in different logs have same index and term, then the preceding
   **    entries are identical in the logs
   ** To keep the semantics clear, "log," denotes the node internal list of entries and "list Entry"
   ** denotes the new requested entries messaged through append entries calls. **)

  (** An entry is a typeclass which gets parametrized over its content. **)
  Record Entry :=
    MkEntry
      {
        entry_term : Term;
        entry : content_type;
      }.

  (** Create a new content entry from the type, entry term and content **)
  Definition new_entry (t : Term) (c : content_type) :=
    MkEntry
      t
      c.

  (** Define an abbreviation for the entry list. The comma is enforced by coq. **)
  Notation "log," := (list Entry) (at level 100).

  (** Search for the last entry and return its entry term. **)
  Fixpoint get_last_log_term (l : log,) : Term :=
    match l with
    | [] => term 0
    | {|entry_term := t|}  :: [] => t
    | _ :: xs => get_last_log_term xs
    end.

  (** Utility function which counts the elements in a log. **)
  Fixpoint get_last_log_index_util (l : log,) (n : nat) :=
    match l with
    | [] => n
    | _ :: xs => get_last_log_index_util xs (n+1)
    end.

  (** The first index is 1 **)
  Definition get_last_log_index (l : log,) : nat := get_last_log_index_util l 1.

  (** Check if at position i the entry has the entry term "t". **)
  Fixpoint check_last_log (i : nat) (t : Term) (l : log,) : bool :=
    match l with
    | [] => true (* if the log is empty any new entry is accepted *)
    | {|entry_term := t'|} :: [] => if (TermDeq t t') then true else false
    | _ :: xs => check_last_log (i - 1) t xs
    end.

  (** Take e elements from the log. Start from the end of the list. **)
  Fixpoint take_from_log_util (e : nat) (l : log,) :=
    match l with
    | [] => ([], 0)
    | x :: xs =>
      let (l, i) := take_from_log_util e xs in
      if (i <? e) then (x :: l, i+1) else (l,i)
    end.

  Definition take_from_log (e : nat) (l : log,) :=
    let (l, i) := take_from_log_util e l in l.

  (** Append new entries to a log  **)
  Fixpoint append2log (l : log,) (e : list Entry) :=
    match e with
    | [] => l
    | x :: xs => x :: append2log l xs
    end.


  (*! Request !*)
  (** A request is issued by some client and contains the client itself for the response message
   *+ and the command issued to replicate as well as the term number to participate. **)
  Inductive Request :=
  | Req (client : Client) (command : content_type) (term : Term).

  (*! Heartbeat and Log replication !*)
  (** The append entries type has two function within the protocol. First it serves as a
   ** heartbeat to prevent follower to suspect the leader is faulty and second it is used to
   ** issue a log replication by some follower.
   ** To issue a replication provide the current term, the current leader id,
   ** the last used index number and it's term number. At last the leaders last known
   ** index used and the list of entries to replicate. **)
  Inductive AppendEntries :=
  | Heartbeat
  | Replicate (term : Term) (leader : Rep) (last_log_index : nat)
              (last_log_term : Term) (commit_index : nat) (entry : list Entry).

  (*! Election !*)
  (** A vote is issued during the leader election. The candidate provides
   ** itself, the current term and the index of the last stored log and
   ** it's term number. **)
  Inductive RequestVote :=
  | Vote (term : Term) (candidate : Rep) (last_log_index : nat) (last_log_term : Term).

  (*! Results !*)
  (** The result type provides the different results used within the protocol. **)
  Inductive Result :=
  (** The leader sends the client the response if his state machine. **)
  | ClientRes (result : nat)
  (** The follower responses to the leader if the issued requests succeds and
   ** the current term to update the leader. **)
  | AppendEntriesRes (success : bool) (term : Term)
  (** A node response to a request vote wether it votes the calling candidate
   ** and it's current term to updat the requesting node. **)
  | RequestVoteRes (vote_granted : bool) (term : Term).

  (*! Messages !*)
  (** Define the messages which can be used within the system for communication
   ** between the nodes. A message takes one inductive type due to the state machine definition.
   ** Authentication is currently not provided. **)
  Inductive Raftmsg :=
  (* A client request is the command issued by the client to modify the overall state.
   * As a parameter the client sends its own id, some sequence number to eliminate duplacte
   * requests and the command to execute. *)
  | RequestMsg (request : Request)
  (* The response is sent by the leader after it applies the issued command to it's
   * own state machine and the first round of AppendEntries send through the network.
   * The result is taken from the result of the leader state machine. *)
  | ResponseMsg (result : Result)
  (* The append entries messages is invoked by the leader to replicate some client
   * request by all followers within the system.
   * If followers crash, run slowly or if network packets are dropped the leader tries
   * AppendEntries indefinitely.
   *
   * The message has a second function as heartbeat when issued without log entries
   * to be replicated by the followers. No result are expected from heartbeat messages. *)
  | AppendEntriesMsg (entries : AppendEntries)
  (* If the leader issued some log replication the follower response wether the
   * request succeds and it's current term number to inform the leader what problem
   * happens. *)
  | AppendEntriesResultMsg (result : Result)
  (* A follower issues a request vote message if it thinks the leader is faulty.
   * It transitions to candidate state and starts the leader election. *)
  | RequestVoteMsg (vote : RequestVote)
  (* The response vote messages is returned by processing some request vote message.
   * It indicates to the requesting client wether it recieves a vote from this
   * node or not. *)
  | ResponseVoteMsg (result : Result)
  (* The forwarding is used if some client send a request to a none leader replica.
   * It encapsulates the message and sends it to the current leader. *)
  | ForwardMsg (msg : Raftmsg).

  (** Bind the implemented messages to the abstract velisarios type class. **)
  Global Instance Raft_I_Msg : Msg := MkMsg Raftmsg.

  (** Forall messages some state shall be defined wether this messages comes
   ** from outside the network (client request) or is used within the network
   ** (protocol request) or within the node (internal message). **)
  Definition Raftmsg2status (m : Raftmsg) : msg_status :=
    match m with
    | RequestMsg _             => MSG_STATUS_EXTERNAL
    | ResponseMsg _            => MSG_STATUS_PROTOCOL
    | AppendEntriesMsg _       => MSG_STATUS_PROTOCOL
    | AppendEntriesResultMsg _ => MSG_STATUS_PROTOCOL
    | RequestVoteMsg _         => MSG_STATUS_PROTOCOL
    | ResponseVoteMsg _        => MSG_STATUS_PROTOCOL
    | ForwardMsg _             => MSG_STATUS_PROTOCOL
    end.

  (** Bind the real message states to the abstract definition. **)
  Global Instance Raft_I_get_msg_status : MsgStatus := MkMsgStatus Raftmsg2status.

End RaftHeader.

