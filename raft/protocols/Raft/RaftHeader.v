(*!
 * This is the header file defining the basics of the raft
 * protocol with velisarios.
 !*)

(** In general the raft protocol can be seperated into multiple parts:
 ** Client Interaction
 ** Leader Election
 ** Log Replication
 **)

Require Export Velisarios.Quorum.
(* the process module provides the abstraction which is implemented by the protocols *)
Require Export Velisarios.Process.
Require Export String.

(*! abstract topology !*)
(** This section defines the topology of raft which is modeled as an agent
 ** based network. Here a topology describes the set of nodes within the network,
 ** the messages which can be exchanged in the network and the basics abstraction context which
 ** is later filled by the application, because the types are not needed for the protocol.
 ** Other basic aspects of the protocol are also defined here, like progress terms.
 **
 ** Throughout this project types are CamelCase with some obvious exceptions and
 ** functions are snake_case with some obvious exceptions. **)
Section RaftHeader.

  (* needed? *)
  Local Open Scope eo.
  Local Open Scope proc.

  (*! Context definition !*)
  (** The context serves for abstraction of function and entities which types
   ** are provided by an implementation and can be ignored in the actual protocol. **)
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
        (* this should be the base timerout for the leader election
         * where no followers should start at the same moment with voting. *)
        base_timeout : nat;
        (* the content type for the log *)
        Content : Set;
        (* get a textual representation from the content *)
        content2string : Content -> string;
        (* the result type which gets issued by the internal state update function *)
        RaftSM_result : Set;
        (* This is the internal state machine where the
         * log entries that are committed are processed. *)
        RaftSM : Set;
        (* the initial state of the internal state machine *)
        RaftSM_initial_state : RaftSM;
        (* the update function for the internal state machine *)
        RaftSM_update_state : RaftSM -> Content -> RaftSM * RaftSM_result
      }.
  (** To get this construct clear: The here proposed functions and types are used by the protocol
   ** but get instantiated in the RaftSim.v file or some other file which uses the raft protocol. **)

  (** Declares the context type class as new variable with implicit
   ** generalization of free terms. Since everything is typed no free terms are gneralized? **)
  Context { raft_context : RaftContext }.

  (*! Nodes !*)
  (** Nodes are used to distinguish between server's.
   ** The parameters are defined in the RaftContext and are implemented by the simulation. **)
  Inductive RaftNode :=
  (* The normal replica node which is either leader or follower.
   * A replica has three internal states which are hidden by this definition.
   * 1. follower mode: The basic mode where the node is passive and
   *    only responds to incoming messages.
   * 2. leader mode: The replica handles all client interactions and log replication.
   *    Only one is allowed in every term.
   * 3. candidate mode: Used for the leader election and at
   *    this point all nodes are considered as possible candidates.
   * This modes or states are hidden within the replica context. *)
  | replica (n : Rep)
  (* The other node is the client which is in fact not modeled within COQ.
   * It is modeled in ocaml outside the protocol and only feeds the input.  *)
  | client (n : Client).

  (** Get the replica parameter of some node. **)
  Definition replica2rep (n : RaftNode) : option Rep :=
    match n with
    | replica n => Some n
    | _ => None
    end.

  (** Get the client parameter of some node. **)
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
  Lemma replica_inj : injective replica.
  Proof.
    introv h; ginv; auto.
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
     otherwise we return a default value (replica0) *)
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

  Definition nreps : list name := map replica reps.

  Lemma reps_prop : forall (x : Rep), In x reps.
  Proof.
    exact nodes_prop.
  Qed.

  Definition clients : list Client :=
    mapin
      (seq 0 num_clients)
      (fun n i => bij_inv clients_bij (mk_nat_n (seq_0_lt i))).

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

  (*! Leader election and authority !*)
  (** In raft nodes use an internal timer to recognize if the leader has failed.
   ** Since all nodes start up as followers the first round is to start the
   ** timers and recognize that nobody is a leader.
   ** The problem is that raft assumes that the timer is running internally and
   ** not as a message which is delayed so we need to model this mechanics slightly different.
   **
   ** The processing shall be the following:
   ** A node sends a TimerMsg to itself with some delay which is general node_timeout + it's
   ** own number to get different delays for different nodes, see election safety.
   ** Each TimerMsg has an natural number which serves as identification of the message.
   ** If a new message is recieved by the node it sends a new timer msg and stores internally the
   ** last timer id sends to itself.
   ** If a timer message is recieved the node checks if the timer is the last known timer.
   ** If it's the last timer id the node transitions to candidate state. Otherwise,
   ** the message is discarded. **)

  (** The timer is only a dummy type for easier modelling. **)
  Inductive Timer := timer (id : nat).

  Definition timer2nat (t : Timer) :=
    match t with
    | timer n => n
    end.
  Coercion timer2nat : Timer >-> nat.

  Definition next_timer (t : Timer) : Timer := timer (S t).

  Lemma TimerDeq : Deq Timer.
  Proof.
    introv. destruct x, y; prove_dec.
    destruct (deq_nat id id0); prove_dec.
  Defined.

  (** the initial timer **)
  Definition timer0 := timer 0.

  (*! Client Interaction !*)
  (** There are some considerations about how some client interacts with the replicated state
   ** machine.
   ** 1. How does the client find the network?
   ** For simplicity we assume the network has a fixed address and the client knows this address.
   ** The paper proposes broadcasting or dns lookup for this problem.
   ** 2. How does a request routes to the leader or the client finds the leader?
   ** The papers approach is to reject client requests if the server is not the leader and
   ** the client has to try again. This approach leads to (n+1)/2 attempts to find the current
   ** leader. The proposed optimization is that the server returns the currently known leader
   ** to the client.
   ** The second proposed mechanism is implemented here, where a server forwards the client
   ** request to the leader. **)

  (*! Linearizable semantics !*)
  (** To prevent leaders to process a request twice and change the state without
   ** knowledge for a client RAFT implements a linearizable semantics which has stronger
   ** guarantees than the at-least-once semantics.
   ** The idea is that every client registers itself by the network and gets an unique
   ** session id. Every request from a registered client has a unique serial number.
   ** If a client issues the same request twice the result is responsed from an
   ** internal map holding client requests serial numbers and the results.
   ** To maintain space by session tracking the paper proposed a LRU semantics for sessions.
   ** ! This not implemented in this prototype and a session is kept as long as
   ** the network runs and we assume the client operates without unexpected behavior. **)

  (** The session id, for some client **)
  Inductive SessionId := session_id (n : nat).

  Definition session_id2nat (si : SessionId) :=
    match si with
    | session_id n => n
    end.
  Coercion session_id2nat : SessionId >-> nat.

  Definition next_session_id (si : SessionId) : SessionId := session_id (S si).

  Lemma SessionIdDeq : Deq SessionId.
  Proof.
    introv. destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  (** the initial session id **)
  Definition session_id0 := session_id 0.

  (** A client generates monotocally the ids for its requests. **)
  Inductive RequestId := request_id (n : nat).

  Definition request_id2nat (ri : RequestId) :=
    match ri with
    | request_id n => n
    end.
  Coercion request_id2nat : RequestId >-> nat.

  Definition next_request_id (ri : RequestId) : RequestId := request_id (S ri).

  Lemma RequestIdDeq : Deq RequestId.
  Proof.
    introv. destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  (** the initial request id **)
  Definition request_id0 := request_id 0.

  (** This implementation keeps sessions until the network restarts.
   ** A session is a tuple of some proposed id, the corresponding clien (maybe useless)
   ** and the last issued request id. The request ids are incremented monotonically. **)
  Notation Sessions := (list (SessionId * Client * RequestId)).

  (** Return the las found session if some **)
  Fixpoint get_last_session (s : Sessions) :=
    match s with
    | [] => None
    | x :: [] => Some x
    | x :: xs => get_last_session xs
    end.

  Fixpoint last_session_id (s : Sessions) : SessionId :=
    let session := get_last_session s in
    match session with
    | None => session_id0
    | Some (si, _, _) => si
    end.

  (** Register some client **)
  Definition add_session (s : Sessions) (c : Client) : (Sessions * SessionId) :=
    let si := next_session_id (last_session_id s) in
    ((si, c, request_id0) :: s, si).

  Fixpoint get_session (s : Sessions) (i : SessionId) :=
    match s with
    | [] => None
    | (si, _, _) as x :: xs => if (SessionIdDeq si i) then Some x else get_session xs i
    end.

  (** Check if a session is valid. **)
  Definition valid_session (s : Sessions) (si : SessionId) : bool :=
    match get_session s si with
    | None => false
    | Some _ => true
    end.

  (** returns wether the request id was already processed or not.
   ** The implementation returns None, if no session is found,
   ** false if not processed, true if processed**)
  Definition already_processed_request (s : Sessions) (si : SessionId) (ri : RequestId) : option bool :=
    match get_session s si with
    | None => None
    | Some (_, _, ri') => if RequestIdDeq ri ri' then Some true else Some false
    end.

  (** If a new request is processed, increment the request id.
   ** We assume that request ids are incremented monotonically on booth sides. **)
  Fixpoint increase_request_id (s : Sessions) (si : SessionId) : Sessions :=
    match s with
    | [] => s (* do nothing if session not found *)
    | (si', c, ri) as x :: xs => if SessionIdDeq si si'
                              then (si', c, next_request_id ri) :: xs
                              else x :: increase_request_id xs si
    end.

  (*! Terms and progress !*)
  (** Within this protocol the global time is divided into chunks called terms.
   ** A term starts with the leader election and ends with the failure a leader.
   ** A term has at most one leader or none if the election failed.
   ** The current term is maintained by all nodes in the system.
   ** The main idea is to identify outdated data within the replicated log. **)
  Inductive Term := term (n : nat).

  (** A term is referenced by some number which is increased monotonically. **)
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
  Definition term0 := term 0.

  (** Test wether term 1 is lesser or equal than term 2. **)
  Definition TermLe (t1 t2 : Term) : bool :=
    term2nat t1 <=? term2nat t2.

  (** Test wether term 1 is lesser than term 2. **)
  Definition TermLt (t1 t2 : Term) : bool :=
    term2nat t1 <? term2nat t2.

  (** Test which term is greater and return it. **)
  Definition max_term (t1 t2 : Term) : Term :=
    if TermLe t1 t2 then t2 else t1.

  (*! Index !*)
  (** The index type is used multiple times as base element for other list types. **)
  Inductive Index := index (rep : Rep) (index : nat).

  Definition index2nat (i : Index) : nat :=
    match i with
    | index _ i => i
    end.

  Definition index2rep (i : Index) : Rep :=
    match i with
    | index r _ => r
    end.

  Definition next_index (i : Index) : Index :=
    match i with
    | index r i => index r (i + 1)
    end.

  (*! NextIndex !*)
  (** The next index list is stored on the leader node and maintains a
   ** list of followers and their next possible log index to use.
   ** The idea is if outdated log data is found on some follower the leader can decrease
   ** this index until it finds the first correct log.
   ** The index for some follower is increased for every unique append entries message. **)
  Definition NextIndex := list Index.

  (** Create a new next index list. The list is initialized by every new leader
   ** to its own last log index + 1. **)
  Fixpoint create_next_index (reps : list Rep) (n : nat) : NextIndex :=
    match reps with
    | [] => []
    | r :: rs => index r n  :: create_next_index rs n
    end.

  (** Increase an element in the next index list **)
  Fixpoint increase_next_index (l : NextIndex) (rep : Rep) : NextIndex :=
    match l with
    | [] => l (* return list if last element reached *)
    | (index r _) as x :: xs => if (rep_deq r rep)
                          then next_index x :: xs
                          else x :: increase_next_index xs rep
    end.

  (** Return some index if the node is found **)
  Fixpoint get_next_index (l : NextIndex) (rep : Rep) : option nat :=
    match l with
    | [] => None (* the node is not found *)
    | (index r i) :: xs => if (rep_deq r rep)
                        then Some i
                        else get_next_index xs rep
    end.

  (*! MatchIndex !*)
  (** The list of match indices stores for every follower node which log entries
   ** are already replicated on the follower. If an append entries messages returns
   ** successfull to the leader it notices the replication by increasing his index.
   ** TODO: It is unclear what happens if results don't appear in order. **)
  Definition MatchIndex := list Index.

  (** These calls are just wrappers around the next index functions. **)
  Definition create_match_index (reps : list Rep) : MatchIndex := create_next_index reps 0.
  Definition increase_match_index (l : MatchIndex) (rep : Rep) := increase_next_index l rep.
  Definition get_match_index (l : MatchIndex) (rep : Rep) := get_next_index l rep.

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
        entry : Content;
      }.

  (** Create a new content entry from the type, entry term and content **)
  Definition new_entry (t : Term) (c : Content) :=
    MkEntry
      t
      c.

  (** Define an abbreviation for the entry list. The comma is enforced by coq. **)
  Notation Log := (list Entry).

  (** Search for the last entry and return its entry term. **)
  Fixpoint get_last_log_term (l : Log) : Term :=
    match l with
    | [] => term 0
    | {|entry_term := t|}  :: [] => t
    | _ :: xs => get_last_log_term xs
    end.

  (** Utility function which counts the elements in a log. **)
  Fixpoint get_last_log_index_util (l : Log) (n : nat) :=
    match l with
    | [] => n
    | _ :: xs => get_last_log_index_util xs (n+1)
    end.

  (** The first index is 1 **)
  Definition get_last_log_index (l : Log) : nat := get_last_log_index_util l 1.

  (** Check if at position i the entry has the entry term "t". **)
  Fixpoint check_last_log (i : nat) (t : Term) (l : Log) : bool :=
    match l with
    | [] => true (* if the log is empty any new entry is accepted *)
    | {|entry_term := t'|} :: [] => if (TermDeq t t') then true else false
    | _ :: xs => check_last_log (i - 1) t xs
    end.

  (** Take e elements from the log. Start from the end of the list. **)
  Fixpoint take_from_log_util (e : nat) (l : Log) :=
    match l with
    | [] => ([], 0)
    | x :: xs =>
      let (l, i) := take_from_log_util e xs in
      if (i <? e) then (x :: l, i+1) else (l,i)
    end.

  Definition take_from_log (e : nat) (l : Log) :=
    let (l, i) := take_from_log_util e l in l.

  (** Append new entries to a log  **)
  Fixpoint append2log (l : Log) (e : list Entry) :=
    match e with
    | [] => l
    | x :: xs => x :: append2log l xs
    end.

  (** The client issues a new session id by the network.  **)
  Inductive RegisterClient := register_client (c : Client).

  (** To alternate the state a client sends an identifiable message to the network. **)
  Inductive ClientRequest :=
  | client_request (client : Client) (session_id : SessionId) (request_id : RequestId)
                   (command : Content).

  (*! Heartbeat and Log replication !*)
  (** The append entries type has two function within the protocol. First it serves as a
   ** heartbeat to prevent follower to suspect the leader is faulty and second it is used to
   ** issue a log replication by some follower.
   ** To issue a replication provide the current term, the current leader id,
   ** the last used index number and it's term number. At last the leaders last known
   ** index used and the list of entries to replicate. **)
  Inductive AppendEntries :=
  | heartbeat
  | replicate (term : Term) (leader : Rep) (last_log_index : nat)
              (last_log_term : Term) (commit_index : nat) (entry : list Entry).

  (*! Election !*)
  (** A vote is issued during the leader election. The candidate provides
   ** itself, the current term and the index of the last stored log and
   ** it's term number. **)
  Inductive RequestVote :=
  | request_vote (term : Term) (candidate : Rep) (last_log_index : nat) (last_log_term : Term).

  (*! Results !*)
  (** The result type provides the different results used within the protocol. **)
  Inductive Result :=
  (** The leader sends the client the response if his state machine. **)
  | client_res (result : nat)
  (** The follower responses to the leader if the issued requests succeds and
   ** the current term to update the leader. **)
  | append_entries_res (success : bool) (term : Term)
  (** A node response to a request vote wether it votes the calling candidate
   ** and it's current term to updat the requesting node. **)
  | request_vote_res (vote_granted : bool) (term : Term)
  (** Return if the client is registered and its new session id **)
  | register_client_res (status: bool) (session_id : SessionId) (leader : option Rep).

  (*! Messages !*)
  (** Define the messages which can be used within the system for communication
   ** between the nodes. A message takes one inductive type due to the state machine definition.
   ** Authentication is currently not provided. **)
  Inductive RaftMsg :=
  (* Before communicating with the network a client registers itself at the network. *)
  | register_msg (register : RegisterClient)
  (* Respond to a register message. *)
  | register_result_msg (result : Result)
  (* If the sessions changes and a new client enters the network
   * the leader broadcast the new sessions to all followers.
   * This is done to find duplicated request early and new leaders didn't forget clients. *)
  | broadcast_sessions_msg (sessions : Sessions)
  (* A client request is the command issued by the client to modify the overall state.
   * As a parameter the client sends its own id, some sequence number to eliminate duplacte
   * requests and the command to execute. *)
  | request_msg (request : ClientRequest)
  (* The response is sent by the leader after it applies the issued command to it's
   * own state machine and the first round of AppendEntries send through the network.
   * The result is taken from the result of the leader state machine. *)
  | response_msg (result : Result)
  (* The append entries messages is invoked by the leader to replicate some client
   * request by all followers within the system.
   * If followers crash, run slowly or if network packets are dropped the leader tries
   * AppendEntries indefinitely.
   *
   * The message has a second function as heartbeat when issued without log entries
   * to be replicated by the followers. No result are expected from heartbeat messages. *)
  | append_entries_msg (entries : AppendEntries)
  (* If the leader issued some log replication the follower response wether the
   * request succeds and it's current term number to inform the leader what problem
   * happens. *)
  | append_entries_result_msg (result : Result)
  (* A follower issues a request vote message if it thinks the leader is faulty.
   * It transitions to candidate state and starts the leader election. *)
  | request_vote_msg (vote : RequestVote)
  (* The response vote messages is returned by processing some request vote message.
   * It indicates to the requesting client wether it recieves a vote from this
   * node or not. *)
  | response_vote_msg (result : Result)
  (* The forwarding is used if some client send a request to a none leader replica.
   * It encapsulates the message and sends it to the current leader. *)
  | forward_msg (msg : RaftMsg)
  (* A node sends timer messages to itself to recognize if the leader failed or the
   * system works properly. *)
  | timer_msg (timer : Timer)
  (* The debug messsage ist used to collect informations from the network. *)
  | debug_msg (debug : string)
  (* The init message starts the systems first leader election after boot up.
   * At the moment this is mandatory but unpleasent. An offset is needed,
   * so that no all node start simultaniously. *)
  | init_msg (offset: nat).

  (** Bind the implemented messages to the abstract velisarios type class. **)
  Global Instance Raft_I_Msg : Msg := MkMsg RaftMsg.

  (** Forall messages some state shall be defined wether this messages comes
   ** from outside the network (client request) or is used within the network
   ** (protocol request) or within the node (internal message). **)
  Definition Raftmsg2status (m : RaftMsg) : msg_status :=
    match m with
    | register_msg _              => MSG_STATUS_EXTERNAL
    | register_result_msg _       => MSG_STATUS_PROTOCOL
    | broadcast_sessions_msg _    => MSG_STATUS_PROTOCOL
    | request_msg _               => MSG_STATUS_EXTERNAL
    | response_msg _              => MSG_STATUS_PROTOCOL
    | append_entries_msg _        => MSG_STATUS_PROTOCOL
    | append_entries_result_msg _ => MSG_STATUS_PROTOCOL
    | request_vote_msg _          => MSG_STATUS_PROTOCOL
    | response_vote_msg _         => MSG_STATUS_PROTOCOL
    | forward_msg _               => MSG_STATUS_PROTOCOL
    | timer_msg _                 => MSG_STATUS_INTERNAL
    | debug_msg _                 => MSG_STATUS_PROTOCOL
    | init_msg _                  => MSG_STATUS_EXTERNAL
    end.

  (** Bind the real message states to the abstract definition. **)
  Global Instance Raft_I_get_msg_status : MsgStatus := MkMsgStatus Raftmsg2status.

End RaftHeader.

