(*!
 * This is implementation of raft with velisarios.
 * See the raft header file for the abstract topology definition.
!*)

(* import velisarios and the abstract definitions *)
Require Export Protocols.Raft.RaftHeader.
Require Export String.
Require Export Peano.
Require Export List.

(** After the raft header defines the topological components of the network
 ** this section defines the executed parts of the protocol.
 ** Namely the state machine transitions, real message sending
 ** and how the nodes and velisarios components are parametrized. **)
Section Raft.

  Local Open Scope eo.
  Local Open Scope proc.

  (** Redeclare the general system context as new local variable. **)
  Context { raft_context : RaftContext }.

  (*! Leader state !*)
  (** The leader state indicates the node as leader and is reinitialized after every
   ** election round. **)
  Record RaftLeaderState :=
    Build_Leader_State
      {
        (* Indicates wether the node is the leader. *)
        is_leader : bool;
        (* Volatile; reset after election -
         * The list of followers and the next possible index to send to the follower.
         * Try list index as node marker -> (node_num, next_index)*)
        next_index : list nat;
        (* Volatile; reset after election -
         * The list of servers and their index of the highest log entry.
         * Try the list index as a marker for the node id. *)
        match_index : list nat;
      }.

  (** This definition is used to initialize the network, because
   ** their is no leader in the beginning. **)
  Definition initial_leader_state : RaftLeaderState :=
    Build_Leader_State false [] [].

  (** Build a list with some default number. **)
  Fixpoint build_follower_list (arg : nat) (followers : nat) : list nat :=
    match followers with
    | O => []
    | S n => [arg] ++ build_follower_list arg n
    end.

  (** This definition reinitializes the node that has won the leader election. **)
  Definition after_election_leader (next_index : nat) (followers : nat) : RaftLeaderState :=
    Build_Leader_State true
                       (build_follower_list next_index followers)
                       (build_follower_list 0 followers).

  (*! Node State !*)
  (** The state describes the parts that are persistent on all nodes. **)
  Record RaftState :=
    Build_State
      {
        (* The last term the node has seen. *)
        current_term : Term;
        (* The candidate this node voted for the current term or null if none *)
        voted_for : (option nat);
        (* The replicated log data. !Use nat at the beginning! *)
        log : list nat;
        (* Volatile - The last log index known to be committed. *)
        commit_index : nat;
        (* Volatile - The last log index applied to the state machine. *)
        last_applied : nat;
        (* the timeout in secs after which a new election is triggered.
         * To get different timouts the node_timout should be the base_timeout
         * with some offset like node * 10 + timeout *)
        node_timeout : nat;
        (* the node local state machine *)
        sm_state : RaftSM_state;
        (* The leader state if the node is the leader *)
        leader : RaftLeaderState;
      }.

  (** The initial state for all nodes. **)
  Definition initial_state (r : Rep) : RaftState :=
    Build_State
      initial_term (* zero at first boot *)
      None (* voted for no one. *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      0 (* nothing applied to state machine *)
      5 (* some way of defining an offset is needed *)
      RaftSM_initial_state (* defined within the raft context *)
      initial_leader_state.

  (*! State transitions !*)
  (** If some leader is byzantine a new election starts and the term number is increased **)
  Definition increment_term_num (s : RaftState) : RaftState :=
    Build_State
      (next_term (current_term s))
      (voted_for s)
      (log s)
      (commit_index s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (leader s).


  (*! The message handling - Update function !*)
  (** Each possible transition has it's own handle function for the input message.
   ** Since the Update definition is a triple where the second type is replaced by the
   ** actual implementation provide higher types if you need multiple arguments
   ** to handle the message. **)

  (** L - Handle client input to the system. **)
  Definition Rafthandle_request (slf : Rep) : Update RaftState Request DirectedMsgs :=
    fun state _ => (Some state, []).

    (** Cl - Handle client response - currently nothing **)
  Definition Rafthandle_response (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state _ => (Some state, []).

  (** F - Handle append entries messages which are used as heartbeat and log replication. **)
  Definition Rafthandle_append_entries (slf : Rep) : Update RaftState AppendEntries DirectedMsgs :=
    fun state _ => (Some state, []).

  (** L - Handle results messages from followers. **)
  Definition Rafthandle_append_entries_result (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state _ => (Some state, []).

    (** C - Handle incoming votes from candidates. **)
  Definition Rafthandle_request_vote (slf : Rep) : Update RaftState RequestVote DirectedMsgs :=
    fun state _ => (Some state, []).

    (** C - Handle incoming voting results from candidates. **)
  Definition Rafthandle_response_vote (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state _ => (Some state, []).

  (** The main update function which calls the appropriate handler function
   ** for the incoming message type. **)
  Definition Raftreplica_update (slf : Rep) : MUpdate RaftState :=
    fun state m =>
      match m with
      | RequestMsg d => Rafthandle_request slf state d
      | ResponseMsg d => Rafthandle_response slf state d
      | AppendEntriesMsg d => Rafthandle_append_entries slf state d
      | AppendEntriesResultMsg d => Rafthandle_append_entries_result slf state d
      | RequestVoteMsg d => Rafthandle_request_vote slf state d
      | ResponseVoteMsg d => Rafthandle_response_vote slf state d
      end.

  (*! System definitions !*)
  (** Define the actual state machine used by velisarios **)
  Definition RaftreplicaSM (slf : Rep) : MStateMachine _ (* let the compiler guess ? *) :=
    mkSM
      (Raftreplica_update slf)
      (initial_state slf).

  (* match node names with state machines *)
  Definition Raftnstate (n : name) :=
    match n with
    | Raftreplica _ => RaftState
    | _ => unit
    end.

  Definition Raftsys : MUSystem Raftnstate :=
    fun name =>
      match name return StateMachine (Raftnstate name) msg DirectedMsgs with
      | Raftreplica n => RaftreplicaSM n
      | _ => MhaltedSM tt
      end.

  (* tactic hints ? *)
  (* QUESTION: Can we avoid repeating this? *)
  Hint Rewrite @map_option_option_map : option.
  Hint Rewrite @option_map_option_map : option.

  (* QUESTION: Can we export this automatically *)
  Hint Resolve if_not_first_if_first : eo.

End Raft.
