(*!
 * This file is part of the raft implementation in velisarios.
 *
 * See the RaftHeader.v file for the basic definitions of the
 * global context and elements used in the protocol.
 *
 * This file implements the mechanics of raft by defining the node
 * state and its transitions as well as the handling of incomming messages.
 *
 * A raft node has three possible main states:
 * follower (initial state on bootup and a passive drone),
 * leader (the one and only elected),
 * candidate (a new leader is needed)
 !*)

(* import velisarios and the basic definitions *)
Require Export Protocols.Raft.RaftHeader.
Require Export String.
Require Export Peano.
Require Export List.

Section Raft.

  Local Open Scope eo.
  Local Open Scope proc.

  (** Redeclare the general system context as new local variable. **)
  Context { raft_context : RaftContext }.

  (** redeclare the notations **)
  Notation Log := (list Entry).
  Notation Sessions := (list (SessionId * Client * RequestId)).

  (*! Utilities !*)
  (** TODO: This seems like vodoo, at the moment, where does reps come from. **)
  Definition other_replicas (r : Rep) : list Rep := remove_elt rep_deq r reps.
  Definition other_names (r : Rep) : list name := map replica (other_replicas r).

  (*! Leader state !*)
  (** The leader state is reinitialized after every election and keeps track
   ** of the current state of the log replication. **)
  Record LeaderState :=
    Build_Leader_State
      {
        (* Volatile; reset after election -
         * The list of followers and the next possible index to send to the follower.
         * Try list index as node marker -> (node_num, next_index)*)
        next_index : NextIndex;
        (* Volatile; reset after election -
         * The list of servers and their index of the highest log entry.
         * Try the list index as a marker for the node id. *)
        match_index : MatchIndex;
      }.

  (** This definition is used to initialize the network, because
   ** their is no leader in the beginning. **)
  Definition no_leader_state : LeaderState :=
    Build_Leader_State [] [].

  (** This definition is used only for testing. It creates an initial leader *)
  (*  ** with a provided follower network. **)
  (* Definition init_leader_state (followers : list nat) : LeaderState := *)
  (*   let reps := List.map nat2rep followers in *)
  (*   Build_Leader_State (create_next_index reps 0) *)
  (*                      (create_match_index reps). *)

  (** This definition reinitializes the node that has won the leader election. **)
  Definition after_election_leader (next_index : nat) (followers : list Rep) : LeaderState :=
    Build_Leader_State (create_next_index followers next_index)
                       (create_match_index followers).

 

  (*! Node State !*)
  (* Indicates which type a node currently has. *)
  Inductive NodeState :=
  | leader (l : LeaderState)
  | follower
  | candidate.

  (** The state describes the parts that are persistent on all nodes. **)
  (** Every node uses an internal state to manage the protocol details. **)
  Record RaftState :=
    Build_State
      {
        (* The last term the node has seen, this should be persitent over crashes. *)
        current_term : Term;
        (* maintain the client sessions *)
        sessions: Sessions;
        (* The candidate this node voted for the current term or null if none *)
        voted_for : (option Rep);
        (* The replicated log data which should be persitent over crashes
         * !Use nat at the beginning! *)
        log : Log;
        (* Volatile - The last log index known to be committed.
         * The index provides information to which request the global state machine
         * has applied the requests. *)
        commit_index : nat;
        (* Volatile - The last log index applied to the state machine. *)
        last_applied : nat;
        (* the timeout in secs after which a new election is triggered.
         * To get different timouts the node_timout should be the base_timeout
         * with some offset like node * 10 + timeout *)
        node_timeout : nat;
        (* This state machine is the one which is defined external by the usage.
         * The state machine processes the replicated log messages and defines the
         * distributed state of the application. *)
        sm_state : RaftSM;
        (*  Defines the state of the server. *)
        node_state : NodeState;
        (* The actual term leader the node knows. *)
        current_leader : (option Rep);
        (* The list of other servers excluding this one *)
        (* nodes : list nat; *)
        (* The id of the last send timout message. *)
        timer : Timer;
      }.

  (** The initial state for all nodes on bootup. **)
 Definition state0 : RaftState :=
    Build_State
      term0 (* zero at first boot *)
      [] (* No clients added *)
      None (* voted for no one. *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      0 (* nothing applied to state machine *)
      5 (* some way of defining an offset is needed *)
      RaftSM_initial_state (* defined within the raft context *)
      follower (* at default no one is leader *)
      None (* no leader known *)
      (* [] *)
      timer0.

  (*! State transitions !*)
  (** If some leader is byzantine a new election starts and the term number is increased **)
  Definition increment_term_num (s : RaftState) : RaftState :=
    Build_State
      (next_term (current_term s))
      (sessions s)
      (voted_for s)
      (log s)
      (commit_index s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (node_state s)
      (current_leader s)
      (* (nodes s) *)
      (timer s).

  (** Increment the timer id if a new timer message was send. **)
  Definition increment_timer_id (s : RaftState) : RaftState :=
    Build_State
      (current_term s)
      (sessions s)
      (voted_for s)
      (log s)
      (commit_index s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (node_state s)
      (current_leader s)
      (* (nodes s) *)
      (next_timer (timer s)).


  (** Replace the internal log with a new one **)
  Definition update_log (s : RaftState) (l : Log) : RaftState :=
    Build_State
      (current_term s)
      (sessions s)
      (voted_for s)
      l
      (commit_index s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (node_state s)
      (current_leader s)
      (timer s).

  (** Update the state machine and index of already commited log entries **)
  Definition update_sm (s : RaftState) (ci : nat) (sm : RaftSM) : RaftState :=
    Build_State
      (current_term s)
      (sessions s)
      (voted_for s)
      (log s)
      ci
      (last_applied s)
      (node_timeout s)
      sm
      (node_state s)
      (current_leader s)
      (timer s).

  (** Update the nodes state type **)
  Definition update_current_leader (s : RaftState) (l : Rep) : RaftState :=
    Build_State
      (current_term s)
      (sessions s)
      (voted_for s)
      (log s)
      (commit_index s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (node_state s)
      (Some l)
      (timer s).

  (** Update the sessions to accept a new client **)
  Definition update_node_state (s : RaftState) (ns : NodeState) : RaftState :=
    Build_State
      (current_term s)
      (sessions s)
      (voted_for s)
      (log s)
      (commit_index s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      ns
      (current_leader s)
      (timer s).

  (** Update the sessions to accept a new client **)
  Definition update_sessions (s : RaftState) (se : Sessions) : RaftState :=
    Build_State
      (current_term s)
      se
      (voted_for s)
      (log s)
      (commit_index s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (node_state s)
      (current_leader s)
      (timer s).

  (** Update the information what the client voted for in the currents term or none **)
  Definition update_voted_for (s : RaftState) (slf : Rep) : RaftState :=
    Build_State
      (current_term s)
      (sessions s)
      (Some slf)
      (log s)
      (commit_index s)
      (last_applied s)
      (node_timeout s)
      (sm_state s)
      (node_state s)
      (current_leader s)
      (timer s).
    
  (** Check if a node is the leader **)
  Definition is_leader (s : RaftState) : bool :=
    match (node_state s) with
    | leader _ => true
    | _ => false
    end.

  (** Get the leader internals from the node type **)
  Definition get_leader (s : RaftState) : option LeaderState :=
    match (node_state s) with
    | leader l => (Some l)
    | _ => None
    end.

  (*! The message handling - Update function !*)
  (** The semantics is that an incoming message gets handled by an appropriate
   ** function which creates a new state protocol and some output messages if any.
   ** A direct message is a triple of some message type with the destinations and
   ** some delay in milliseconds. Since a message leaves the type abstract the implementation
   ** decides the type used and returned. **)

  (*! System boot up !*)
  (** Every node needs to start its timer on boot up. **)
  Definition handle_init_msg (slf : Rep) : Update RaftState nat DirectedMsgs :=
    fun state offset =>
      let state' := increment_timer_id state in
      let delay := base_timeout + offset in
      let msg := [MkDMsg (timer_msg (timer state')) [replica slf] delay] in
      (Some state', msg).

  (*! Timer !*)
  (** The raft protocol enforces that every node has an internal timer which gets reseted
   ** if a message from the leader node arrives. To model this with velisarios a node
   ** sends messages with a fix delay to itself and keeps track of the last valid
   ** timer id. FIXME, a more performant way. **)


  (** Check if the timer is valid, if not reject the message, otherwise start election. **)
  Definition handle_timer_msg (slf : Rep) : Update RaftState Timer DirectedMsgs :=
    fun state msg =>
      (* the internal timer has ended and no new message arrived in between *)
      if TimerDeq (timer state) msg then
        (* re-elect the leader *)
        let state' := increment_term_num state in
        let state'' := update_node_state state' candidate in
        let state''' := update_voted_for state'' slf in
        (* TODO: semantic or storage of last_log_index, last_log_term, last_applied, commit_index not clear *)
        let lli := get_last_log_index (log state''') in
        let llt := get_last_log_term (log state''') in
        let vote := request_vote (current_term state''') slf lli llt  in
        (Some state''', [MkDMsg (request_vote_msg vote) (other_names slf) 0])
      else (Some state, []). (* drop the message *)


  (*! Internal Forwarding !*) 
  (** The internal forwarding is used to keep the client network handling easy from
   ** the clients perspective. A wrongly delivered message (node not leader) is forwarded
   ** to the clients last known leader.
   ** FIXME: If there is currently no leader the messages is dropped.
   ** If the assumed leader is not a leader the message gets forwarded again.
   ** The leader node unpacks all the layers and sends the request to itself. **)

  Definition create_forward_msg (s : option Rep) (o : RaftMsg) : DirectedMsgs :=
    match s with
      (* we have no new current leader, maybe the system was recently initialized and
       * no leader is elected yet. TODO: Ignore the message at the moment *)
    | None => []
    | Some l => [MkDMsg (forward_msg o) [replica l] 0]
    end.

  (** Recursivly unwrap the forward message until the original request is returned. **)
  Fixpoint unpack_forward_msg (f : RaftMsg) : RaftMsg :=
    match f with
    | forward_msg f => unpack_forward_msg f
    | f => f
    end.

  (** L - Handle fowarded message - unpack and send original message to self. **)
  Definition handle_forward_msg (slf : Rep) : Update RaftState RaftMsg DirectedMsgs :=
    fun state f =>
      if is_leader state then
        (* maybe there is a better way of handling this. *)
        let msg := unpack_forward_msg f in
        (Some state, [MkDMsg msg [(replica slf)] 0])
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
  (* TODO: resend append entry calls indefinitely if followers does not answer
   * TODO: apply log entry as committed if majority of followers succeds
   * TODO: leader send response to server
   * TODO: deal with log inconsistency -> the leader needs to detect the last valid log. *)

  (** Create the replication messages which are send to the followers
   ** To make this easy the request sends a nat as cmd to the leader and
   ** the leader converts this into a single entry list for the log replication. **)
  Definition create_append_msg (slf : Rep) (s : RaftState) (entries: list Entry) : DirectedMsgs :=
    let leader := (get_leader s) in
    let llt := get_last_log_term (log s) in
    let lli := get_last_log_index (log s) in
    let msg := replicate (current_term s) slf lli llt (commit_index s) entries in
    [MkDMsg (append_entries_msg msg) (other_names slf) 0].

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
    (update_sm s new_ci (sm_state s)).

  (** L - Handle client input to the system. **)
  (** Forward the message if the request reaches the wrong node.
   ** As leader generate the entries from the request and apply the entries to the
   ** internal log. Afterwards send AppendEntries messages to the followers. **)
  Definition handle_request (slf : Rep) : Update RaftState ClientRequest DirectedMsgs :=
    fun state r =>
      if is_leader state then
        (* We are the leader *)
        match r with
        | client_request c si ri cmd =>
          if (valid_session (sessions state) si) then
          let entry := [new_entry (term (current_term state)) cmd] in
          (* create the replication messages for all leaders *)
          let dmsgs := create_append_msg slf state entry in
          (* apply the messages to your own log
           * Paper missing description about how to add as a leader, currently use the same fn as the followers *)
          let lli := get_last_log_index (log state) in
          let new_state := (update_log state (append_entries2log entry lli (current_term state) state)) in
          (Some new_state, dmsgs)
          else
            (Some state, []) (* ignore the message if there is no session *)
        end
      else
      (* Some node that forwards *)
        let msg := create_forward_msg (current_leader state) (request_msg r) in
        (Some state, msg).

  (** F - Handle append entries messages which are used as heartbeat and log replication. **)
  (** As a leader ignore the message.
   ** As a follower
   ** 1. Check if the message is a heartbeat or replication
   ** 2. Ignore heartbeats at the moment
   ** 3. Check if the entries could be applied to the internal log
   ** 3.1 Ignore the request if the current term doesn't match or the entry is already there (index + term)
   ** 3.2 Apply the entries to the internal log by removing false entries and response with success and the current term **)
  Definition handle_append_entries (slf : Rep) : Update RaftState AppendEntries DirectedMsgs :=
    fun state msg =>
      if is_leader state then (Some state, []) (* this shouldn't happen *)
      else
        match msg with
        (* leader timeout reset *)
        | heartbeat => (Some state, []) (* TODO: ignore election at the moment *)
        (* log replication *)
        | replicate t l lli llt ci entries =>
          if (TermLt t (current_term state)) then
            (* reply false if the replication term is lower than the current term *)
            let result := append_entries_res false (current_term state) in
            (Some state, [MkDMsg (append_entries_result_msg result) [replica l] 10])
          else
            if (negb (check_last_log lli llt (log state))) then
              (* reply false if the last log index or term does not match *)
              let result := append_entries_res false (current_term state) in
              (Some state, [MkDMsg (append_entries_result_msg result) [replica l] 20])
            else
              (* handle the replication request *)
              let new_log := append_entries2log entries lli t state in
              let result := append_entries_res true (current_term state) in
              let s := (update_log state new_log) in
              let s' := (commit s ci) in
              let s'' := (update_current_leader s' l) in
              (Some s'', [MkDMsg (append_entries_result_msg result) [replica l] 0])
        end.

  (** L - Handle results messages from followers. **)
  Definition handle_append_entries_result (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state r =>
      if is_leader state then
        (* let c := [Raftclient client] in *)
        (* (Some state, [MkDMsg (ResponseMsg (ClientRes cmd)) c 0]) *)
        (Some state, [])

      else (Some state, []). (* this shoudln't happen *)

  (** C - Handle incoming votes from candidates. **)
  Definition handle_request_vote (slf : Rep) : Update RaftState RequestVote DirectedMsgs :=
    fun state _ => (Some state, []).

  (** C - Handle incoming voting results from candidates. **)
  Definition handle_response_vote (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state _ => (Some state, []).

  (*! Register some client at the network !*)
  Definition create_register_result_msg (c : Client) (r : Result) :=
    [MkDMsg (register_result_msg r) [client c] 0].

  Definition create_broadcast_msg (slf : Rep) (b : RaftMsg) :=
    [MkDMsg b (other_names slf) 0].

  (** L _ Handle incoming new clients **)
  (** Some client sends an empty register_client message and the leader creates a session
   ** for this client. This session is distributed across the network.
   **
   ** The papers approach is to handle regiter messages like normal log replication messages.
   ** No checks are done if the distribution was successfully since all client messages
   ** are forwarded to the leader. So, the disribution is implemented as a showcase. **)
  Definition handle_register (slf : Rep) : Update RaftState RegisterClient DirectedMsgs :=
    fun state msg =>
      if is_leader state then
        match msg with (* we're the leader and register the client *)
        | register_client c =>
          let (sessions, id) := add_session (sessions state) c in
          let s' := update_sessions state sessions in
          let result := register_client_res true id (Some slf) in
          let broadcast := create_broadcast_msg slf (broadcast_sessions_msg sessions) in
          (Some s', create_register_result_msg c result ++ broadcast)
        end
      else
        let forward := create_forward_msg (current_leader state) (register_msg msg) in
        (Some state, forward). (* forward messsage if we're not the leader *)

  (** F - Handle a leader brodacast with new sessions by just replacing the own sessions. **)
  Definition handle_sessions_broadcast (slf : Rep) : Update RaftState Sessions DirectedMsgs :=
    fun state sessions =>
      if is_leader state then (Some state, [])
      else (Some (update_sessions state sessions), []).

  (*! maybe useless !*)
  (** Cl - A client handles the response for the register message of the client - nothing atm **)
  Definition handle_register_result (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state _ => (Some state, []).

  (** Cl -  The client handles the response from a node - currently nothing **)
  Definition handle_response (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state _ => (Some state, []).


  Definition handle_debug_msg (slf : Rep) : Update RaftState string DirectedMsgs :=
    fun state _ => (Some state, []).

  (** The main update function which calls the appropriate handler function
   ** for the incoming message type. **)
  Definition replica_update (slf : Rep) : MUpdate RaftState :=
    fun state m =>
      match m with
      | register_msg d => handle_register slf state d
      | register_result_msg d => handle_register_result slf state d
      | broadcast_sessions_msg d => handle_sessions_broadcast slf state d
      | request_msg d => handle_request slf state d
      | response_msg d => handle_response slf state d
      | append_entries_msg d => handle_append_entries slf state d
      | append_entries_result_msg d => handle_append_entries_result slf state d
      | request_vote_msg d => handle_request_vote slf state d
      | response_vote_msg d => handle_response_vote slf state d
      | forward_msg msg => handle_forward_msg slf state msg
      | timer_msg d => handle_timer_msg slf state d
      | init_msg d => handle_init_msg slf state d
      | debug_msg d => handle_debug_msg slf state d
      end.


  (*! Define fake states for testing !*)
 Definition initial_faked_leader_state : RaftState :=
    Build_State
      term0 (* zero at first boot *)
      [] (* *)
      None (* voted for no one. *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      0 (* nothing applied to state machine *)
      5 (* some way of defining an offset is needed *)
      RaftSM_initial_state (* defined within the raft context *)
      follower (* at default no one is leader *)
      (Some (nat2rep 0)) (* set leader to 0 *)
      [] (* empty list of nodes *).


  (** An initial leader state which should only used for testing. **)
  Definition initial_leader_state : RaftState :=
    Build_State
      term0 (* zero at first boot *)
      []
      None (* voted for no one. *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      0 (* nothing applied to state machine *)
      5 (* some way of defining an offset is needed *)
      RaftSM_initial_state (* defined within the raft context *)
      (leader (init_leader_state [1, 2, 3])) (* define as leader with 3 followers *)
      (Some (nat2rep 0)) (* set leader to 0 for testing *)
      [1, 2, 3] (* set follower nodes *).


  (*! System definitions !*)
  (* match node names with state machines *)
  Definition Raftnstate (n : name) :=
    match n with
    | replica _ => RaftState
    | _ => unit
    end.

  (** Define the actual state machine used by velisarios **)
  Definition RaftReplicaSM (slf : Rep) : MStateMachine _ (* let the compiler guess ? *) :=
    mkSM
      (replica_update slf)
      (state0).

  (** This binding should only used for testing. **)
  (* Definition RaftLeaderreplicaSM (slf : Rep) : MStateMachine _ (* let the compiler guess ? *) := *)
  (*   mkSM *)
  (*     (replica_update slf) *)
  (*     (initial_leader_state). *)


  Definition Raftsys : MUSystem Raftnstate :=
    fun name =>
      match name return StateMachine (Raftnstate name) msg DirectedMsgs with
      | replica n => RaftReplicaSM n
      | _ => MhaltedSM tt
      end.

  (* tactic hints ? *)
  (* QUESTION: Can we avoid repeating this? *)
  Hint Rewrite @map_option_option_map : option.
  Hint Rewrite @option_map_option_map : option.

  (* QUESTION: Can we export this automatically *)
  Hint Resolve if_not_first_if_first : eo.

End Raft.
