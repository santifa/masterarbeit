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

  (** redeclare the notations **)
  Notation Nindex := (list NextIndex).
  Notation Mindex := (list NextIndex).
  Notation Log := (list Entry).
  Notation Commit_log := (list Entry).

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
        next_index : Nindex;
        (* Volatile; reset after election -
         * The list of servers and their index of the highest log entry.
         * Try the list index as a marker for the node id. *)
        match_index : Mindex;
      }.

  (** This definition is used to initialize the network, because
   ** their is no leader in the beginning. **)
  Definition no_leader_state : RaftLeaderState :=
    Build_Leader_State false [] [].

  (** This definition is used only for testing. It creates an initial leader *)
  (*  ** with a provided follower network. **)
  Definition init_leader_state (followers : list nat) : RaftLeaderState :=
    let reps := List.map nat2rep followers in
    Build_Leader_State true
                       (create_next_index reps 0)
                       (create_match_index reps).

  (** This definition reinitializes the node that has won the leader election. **)
  Definition after_election_leader (next_index : nat) (followers : list Rep) : RaftLeaderState :=
    Build_Leader_State true
                       (create_next_index followers next_index)
                       (create_match_index followers).

  (*! Node State !*)
  (** The state describes the parts that are persistent on all nodes. **)
  Record RaftState :=
    Build_State
      {
        (* The last term the node has seen, this should be persitent over crashes. *)
        current_term : Term;
        (* The candidate this node voted for the current term or null if none *)
        voted_for : (option nat);
        (* The replicated log data which should be persitent over crashes
         * !Use nat at the beginning! *)
        log : Log;
        (* Volatile - The last log index known to be committed.
         * The index provides information to which request the global state machine
         * has applied the requests. *)
        commit_index : nat;
        (* Since we don't implement a real state machine where the commited logs
         * gets applied (out of scope) a second list is used as dummy to show the mechanics.
         * If a majority agrees on a log entry the entry gets copied to the commited_log. *)
        committed : Commit_log;
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
        (* The term leader *)
        current_leader : (option Rep);
        (* the list of other servers excluding this one *)
        nodes : list nat;
      }.

  (** The initial state for all nodes. **)
  Definition initial_state : RaftState :=
    Build_State
      initial_term (* zero at first boot *)
      None (* voted for no one. *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      [] (* empty commited log *)
      0 (* nothing applied to state machine *)
      5 (* some way of defining an offset is needed *)
      RaftSM_initial_state (* defined within the raft context *)
      no_leader_state (* at default no one is leader *)
      None (* set leader to none *)
      [].

  (** An initial state for replicas with the leader set to replica 0. **)
  Definition initial_faked_leader_state : RaftState :=
    Build_State
      initial_term (* zero at first boot *)
      None (* voted for no one. *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      [] (* empty commited log *)
      0 (* nothing applied to state machine *)
      5 (* some way of defining an offset is needed *)
      RaftSM_initial_state (* defined within the raft context *)
      no_leader_state (* at default no one is leader *)
      (Some (nat2rep 0)) (* set leader to 0 *)
      [] (* empty list of nodes *).


  (** An initial leader state which should only used for testing. **)
  Definition initial_leader_state : RaftState :=
    Build_State
      initial_term (* zero at first boot *)
      None (* voted for no one. *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      [] (* empty commited log *)
      0 (* nothing applied to state machine *)
      5 (* some way of defining an offset is needed *)
      RaftSM_initial_state (* defined within the raft context *)
      (init_leader_state [1, 2, 3]) (* define as leader with 3 followers *)
      (Some (nat2rep 0)) (* set leader to 0 for testing *)
      [1, 2, 3] (* empty list of nodes *).

  (*! State transitions !*)
  (** If some leader is byzantine a new election starts and the term number is increased **)
  Definition increment_term_num (s : RaftState) : RaftState :=
    Build_State
      (next_term (current_term s))
      (voted_for s)
      (log s)
      (commit_index s)
      (committed s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (leader s)
      (current_leader s)
      (nodes s).

  (** replace the nodes log **)
  Definition update_log (s : RaftState) (l : list Entry) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      l
      (commit_index s)
      (committed s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (leader s)
      (current_leader s)
      (nodes s).

    (** replace the commit index **)
  Definition update_commit_log (s : RaftState) (ci : nat) (l : Commit_log) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (log s)
      ci
      l
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (leader s)
      (current_leader s)
      (nodes s).

  Definition update_leader (s : RaftState) (l : Rep) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (log s)
      (commit_index s)
      (committed s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (leader s)
      (Some l)
      (nodes s).


  (*! Utilities !*)

  (** TODO: This seems like vodoo, at the moment, where does reps come from. **)
  Definition other_replicas (r : Rep) : list Rep := remove_elt rep_deq r reps.
  Definition other_names (r : Rep) : list name := map Raftreplica (other_replicas r).

  Definition leading (s : RaftState) : bool := (is_leader (leader s)).

  (*! The message handling - Update function !*)
  (** Each possible transition has it's own handle function for the input message.
   ** Since the Update definition is a triple where the second type is replaced by the
   ** actual implementation provide higher types if you need multiple arguments
   ** to handle the message. **)

  (*! Internal Forwarding !*)
  (** The internal forwarding mechanism is a fairly simple one.
   ** 1. If a client request is send to the wrong node it gets forwarded to the node
   ** this node assumes to be the leader.
   ** 2. If this node has no leader (newly started network) it currently drops the request.
   ** 3. The reciever forwards the message if it is not the leader
   ** 4. Otherwise, it unpacks all messages and sends the innerst message to itself **)
  Definition create_forward_msg (s : option Rep) (o : Raftmsg) : DirectedMsgs :=
    match s with
      (* we have no new current leader, maybe the system was recently initialized and
       * no leader is elected yet. TODO: Ignore the message at the moment *)
    | None => []
    | Some l => [MkDMsg (ForwardMsg o) [Raftreplica l] 0]
    end.

  (** Unwrap all possible wrapped forwarded messages and return the original message. **)
  Fixpoint unpack_forwards (f : Raftmsg) : Raftmsg :=
    match f with
    | ForwardMsg f => unpack_forwards f
    | f => f
    end.

  (** L - Handle fowarded message - unpack and send original message to self. **)
  Definition Rafthandle_forward_msg (slf : Rep) : Update RaftState Raftmsg DirectedMsgs :=
    fun state f =>
      if leading state then
        (* maybe there is a better way of handling this. *)
        let msg := unpack_forwards f in
        (Some state, [MkDMsg msg [(Raftreplica slf)] 0])
      (* Either forward the message to the current leader or ignore it.
       * Maybe a TODO to handle the first encountered messages if there is no leader. *)
      else (Some state, (create_forward_msg (current_leader state) f)).

  (*! Log replication !*)
  (** 1. If a node gets a request and it is not the leader it forwards the request.
   ** 2. If the node is the leader
   ** 2.1 It stores the request in its internal log
   ** 2.2 It sends append entries messages to all its followers
   ** 3. A follower applies the entries to it's internal log if the index is free or a wrong entry is present.
   ** 3.1 It ignores the entries if the index is present and the terms are matching
   ** 4. The follower updates the commit_index and commits log entries to the commited_log
   ** 5. The follower repsonds to the leader with it's result and the current term
   ** 6. If the leader gets a majority of successfull repsonses from the followers
   **    it commits the log entry to the commited_log. **)

  (** Create the replication messages which are send to the followers
   ** To make this easy the request sends a nat as cmd to the leader and
   ** the leader converts this into a single entry list for the log replication. **)
  Definition create_append_msg (slf : Rep) (s : RaftState) (entries: list Entry) : DirectedMsgs :=
    let leader := leader s in
    let llt := get_last_log_term (log s) in
    let lli := get_last_log_index (log s) in
    let msg := Replicate (current_term s) slf lli llt (commit_index s) entries in
    [MkDMsg (AppendEntriesMsg msg) (other_names slf) 0].

  (** 1. If the next used log index is equal to the internal log index
   ** 1.1 check if the terms of the entries are matching and
   ** 1.1.1 if the terms are equal do nothing
   ** 1.1.2 if the terms are unequal take only the log until the last_log_index and append the new entries
   ** 2. If the next used log index is free append the entries **)
  Definition append_entries2log (entries : list Entry) (lli : nat) (t : Term) (s : RaftState) :=
    let log := log s in
    let last_index := get_last_log_index log in
    if ((lli + 1) ==  last_index) then
      (* an entry exists, now check if terms are matching *)
      let last_term := get_last_log_term log in
      if (TermDeq t last_term) then
        (* the terms are matching, we assume the entry is correct *)
        []
      else (* delete the requested index and all entries which follow this one *)
        let log' := take_from_log (lli + 1) log in
        append2log log' entries
    else append2log log entries.

  (** If the internal commit index is lower than the provided one
   ** return min (provided_commit_index, last_log_index) **)
  Definition new_commit_index (s : RaftState) (ci : nat) :=
    if ((commit_index s) <? ci) then
      let lli := get_last_log_index (log s) in
      min ci lli
    else (commit_index s). (* if the nodes index is higher the paper doesn't handle this case *)

  (** Check if there are new commits and apply them to the local committed log. **)
  Definition commit (s : RaftState) (ci : nat) :=
    let new_ci := new_commit_index s ci in
    let log := take_from_log new_ci (log s) in
    (update_commit_log s new_ci log).

  (** L - Handle client input to the system. **)
  (** Forward the message if the request reaches the wrong node.
   ** As leader generate the entries from the request and apply the entries to the
   ** internal log. Afterwards send AppendEntries messages to the followers. **)
  Definition Rafthandle_request (slf : Rep) : Update RaftState Request DirectedMsgs :=
    fun state r =>
      if leading state then
        (* We are the leader *)
        match r with
        | Req client cmd t =>
          let entry := [new_entry (term (current_term state)) cmd] in
          (* create the replication messages for all leaders *)
          let dmsgs := create_append_msg slf state entry in
          (* apply the messages to your own log
           * Paper missing description about how to add as a leader, currently use the same fn as the followers *)
          let lli := get_last_log_index (log state) in
          let new_state := (update_log state (append_entries2log entry lli (current_term state) state)) in
          (Some new_state, dmsgs)
        end
      else
      (* Some node that forwards *)
        let msg := create_forward_msg (current_leader state) (RequestMsg r) in
        (Some state, msg).

  (** F - Handle append entries messages which are used as heartbeat and log replication. **)
  (** As a leader ignore the message.
   ** As a follower
   ** 1. Check if the message is a heartbeat or replication
   ** 2. Ignore heartbeats at the moment
   ** 3. Check if the entries could be applied to the internal log
   ** 3.1 Ignore the request if the current term doesn't match or the entry is already there (index + term)
   ** 3.2 Apply the entries to the internal log by removing false entries and response with success and the current term **)
  Definition Rafthandle_append_entries (slf : Rep) : Update RaftState AppendEntries DirectedMsgs :=
    fun state msg =>
      if leading state then (Some state, []) (* this shouldn't happen *)
      else
        match msg with
        (* leader timeout reset *)
        | Heartbeat => (Some state, []) (* TODO: ignore election at the moment *)
        (* log replication *)
        | Replicate t l lli llt ci entries =>
          if (TermLt t (current_term state)) then
            (* reply false if the replication term is lower than the current term *)
            let result := AppendEntriesRes false (current_term state) in
            (Some state, [MkDMsg (AppendEntriesResultMsg result) [Raftreplica l] 10])
          else
            if (negb (check_last_log lli llt (log state))) then
              (* reply false if the last log index or term does not match *)
              let result := AppendEntriesRes false (current_term state) in
              (Some state, [MkDMsg (AppendEntriesResultMsg result) [Raftreplica l] 20])
            else
              (* handle the replication request *)
              let new_log := append_entries2log entries lli t state in
              let result := AppendEntriesRes true (current_term state) in
              let s := (update_log state new_log) in
              let s' := (commit s ci) in
              let s'' := (update_leader s' l) in
              (Some s'', [MkDMsg (AppendEntriesResultMsg result) [Raftreplica l] 0])
        end.

  (** L - Handle results messages from followers. **)
  Definition Rafthandle_append_entries_result (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state r =>
      if leading state then
        (* let c := [Raftclient client] in *)
        (* (Some state, [MkDMsg (ResponseMsg (ClientRes cmd)) c 0]) *)
        (Some state, [])
    
      else (Some state, []). (* this shoudln't happen *)

  (** C - Handle incoming votes from candidates. **)
  Definition Rafthandle_request_vote (slf : Rep) : Update RaftState RequestVote DirectedMsgs :=
    fun state _ => (Some state, []).

  (** C - Handle incoming voting results from candidates. **)
  Definition Rafthandle_response_vote (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state _ => (Some state, []).

  (** Cl - The client handles the response from a node - currently nothing **)
  Definition Rafthandle_response (slf : Rep) : Update RaftState Result DirectedMsgs :=
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
      | ForwardMsg msg => Rafthandle_forward_msg slf state msg
      end.

  (*! System definitions !*)
  (** Define the actual state machine used by velisarios **)
  Definition RaftreplicaSM (slf : Rep) : MStateMachine _ (* let the compiler guess ? *) :=
    mkSM
      (Raftreplica_update slf)
      (initial_faked_leader_state).

  (** This binding should only used for testing. **)
  Definition RaftLeaderreplicaSM (slf : Rep) : MStateMachine _ (* let the compiler guess ? *) :=
    mkSM
      (Raftreplica_update slf)
      (initial_leader_state).

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
