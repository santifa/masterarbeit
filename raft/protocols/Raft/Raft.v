(*!
 * This file is part of the raft implementation in velisarios.
 !*)

(*! abstract !*)
(** See the RaftContext.v for the context definition which are implementation dependent.
 ** See the RaftHeader.v file for the basic datatypes and messages used by the protocol.
 **
 ** This file ties together the datatypes, context information and velisarios.
 ** The main protocol handling is implemented here by defining handler which
 ** are called by the upon message delivery. Also the state handling is implemented here.
 **
 ** A raft node has three possible main states:
 ** follower (initial state on bootup and a passive replication drone),
 ** leader (the one and only elected),
 ** candidate (a new leader is needed) **)

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
  Notation Sessions := (list (SessionId * Client)).

  (*! Utilities !*)
  (** TODO: This seems like vodoo, at the moment, where does reps come from. **)
  (* Definition other_replicas (r : Rep) : list Rep := remove_elt rep_deq r reps. *)
  (* Definition other_names (r : Rep) : list name := map replica (other_replicas r). *)

  (*! Leader state !*)
  (** The leader state is reinitialized after every election and keeps track
   ** of the current state of the log replication. **)
  (* Record LeaderState := *)
  (*   Build_Leader_State *)
  (*     { *)
  (*       (* Volatile; reset after election - *)
  (*        * The list of followers and the next possible index to send to the follower. *)
  (*        * Try list index as node marker -> (node_num, next_index)*) *)
  (*       next_index : NextIndex; *)
  (*       (* Volatile; reset after election - *)
  (*        * The list of servers and their index of the highest log entry. *)
  (*        * Try the list index as a marker for the node id. *) *)
  (*       match_index : MatchIndex; *)
  (*     }. *)

  (** This definition is used to initialize the network, because
   ** their is no leader in the beginning. **)
  (* Definition leader_state0 : LeaderState := *)
  (*   Build_Leader_State [] []. *)

  (** Create a new leader state for the node who won the election. **)
  (* Definition new_leader (next_index : nat) (followers : list Rep) : LeaderState := *)
  (*   Build_Leader_State (create_next_index followers next_index) *)
  (*                      (create_match_index followers). *)

  (* Definition update_leader_state (ni : NextIndex) (mi : MatchIndex) : LeaderState := *)
  (*   Build_Leader_State ni mi. *)

  (** A candidate needs to know the amount of recieved votes for itself. **)
  (* Record CandidateState := *)
  (*   Build_Candidate_State *)
  (*     { *)
  (*       (* recieved votes *) *)
  (*       votes : nat; *)
  (*     }. *)

  (** initial candidate has voted for itself **)
  (* Definition candidate_state0 : CandidateState := Build_Candidate_State 1. *)

  (* Definition increment_votes (s : CandidateState) : CandidateState := *)
  (*   Build_Candidate_State (S (votes s)). *)

  (*! Node State !*)
  (* Indicates which type a node currently has. *)
  (* Inductive NodeState := *)
  (* | leader (l : LeaderState) *)
  (* | follower *)
  (* | candidate (c : CandidateState). *)

  (*! State !*)
  (** The state describes the parts that are persistent or volatile on all nodes. **)
  (** Every node uses an internal state to manage the protocol details. **)
  Record RaftState :=
    Build_State
      {
        (* persistent - The last term the node has seen, this should be persitent over crashes. *)
        current_term : Term;
        (* persistent - The candidate this node voted for the current term or null if none *)
        voted_for : option name;
        (* persistent - The actual term leader the node knows. *)
        leader_id : option name;
        (* persistent - The replicated log data which should be persitent over crashes
         * !Use nat at the beginning! *)
        log : Log;
        (* Volatile - The last log index known to be committed.
         * The index provides information to which request the global state machine
         * has applied the requests. *)
        commit_index : nat;
        (* Volatile - The last log index applied to the state machine. *)
        last_applied : nat;
        (* volatile - This state machine is the one which is defined external by the usage.
         * The state machine processes the replicated log messages and defines the
         * distributed state of the application. *)
        sm : RaftSM;
        (*  volatile - Defines the state of the server. *)
        node_state : NodeState;
        (* internal volatile - maintain the client sessions *)
        sessions: Sessions;
        (* internal volatile - cache the clients requests *)
        cache : list Cache;
        (* internal persistent - the timeout in millisecs after which a new election is triggered.
         * The timeout is set with init message which provides a random value. *)
        timeout : nat;
        (* internal volatile - The id of the last send timout message. *)
        timer : Timer;
        (* internal volatile - The timer for messages which should be resend indefinitly if no response *)
        msg_timer : Timer;
       }.

  (** The initial state for all nodes on bootup. **)
  Definition state0 : RaftState :=
    Build_State
      term0 (* zero at first boot *)
      None (* voted for no one. *)
      None (* no leader known *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      0 (* nothing applied to state machine *)
      RaftSM_initial_state (* defined within the raft context *)
      follower (* at default no one is leader *)
      [] (* No clients added *)
      [] (* empty cache *)
      0 (* the timeout gets overwritten at start up *)
      timer0 (* start with the initial timer *)
      timer0.

  (*! State transitions !*)
  (** If the input term is newer, advance this node to the new term. **)
    Definition advance_term (s : RaftState) (t : Term) : RaftState :=
      if TermLt (current_term s) t then
        Build_State
          t
          None
          None
          (log s)
          (commit_index s)
          (last_applied s)
          (sm s)
          follower
          (sessions s)
          (cache s)
          (timeout s)
          (timer s)
          (msg_timer s)
        else s.

 (** If some leader is byzantine a new election starts and the term number is increased **)
  Definition increment_term (s : RaftState) : RaftState :=
    let next_term := next_term (current_term s) in
    advance_term s next_term.

  (** Increment the timer id if a new timer message was send. **)
  Definition set_timer (s : RaftState) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      (log s)
      (commit_index s)
      (last_applied s)
      (sm s)
      (node_state s)
      (sessions s)
      (cache s)
      (timeout s)
      (next_timer (timer s))
      (msg_timer s).

    (** Increment the timer id if a new timer message was send. **)
  Definition set_msg_timer (s : RaftState) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      (log s)
      (commit_index s)
      (last_applied s)
      (sm s)
      (node_state s)
      (sessions s)
      (cache s)
      (timeout s)
      (timer s)
      (next_timer (msg_timer s)).

  (** Update the timer offset on boot up. **)
  Definition update_timeout (s : RaftState) (n : nat) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      (log s)
      (commit_index s)
      (last_applied s)
      (sm s)
      (node_state s)
      (sessions s)
      (cache s)
      n
      (timer s)
      (msg_timer s).


  (** Increment the last applied log index **)
  Definition increment_last_applied (s : RaftState) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      (log s)
      (commit_index s)
      ((last_applied s) + 1)
      (sm s)
      (node_state s)
      (sessions s)
      (cache s)
      (timeout s)
      (timer s)
      (msg_timer s).

  (** Increment the commit_index  **)
  Definition increment_commit_index (s : RaftState) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      (log s)
      ((commit_index s) + 1)
      (last_applied s)
      (sm s)
      (node_state s)
      (sessions s)
      (cache s)
      (timeout s)
      (timer s)
      (msg_timer s).

  (** Replace the internal log with a new one **)
  Definition update_log (s : RaftState) (l : Log) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      l
      (commit_index s)
      (last_applied s)
      (sm s)
      (node_state s)
      (sessions s)
      (cache s)
      (timeout s)
      (timer s)
      (msg_timer s).

  (** Update the state machine and index of already commited log entries **)
  Definition update_sm (s : RaftState) (sm : RaftSM) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      (log s)
      (commit_index s)
      (last_applied s)
      sm
      (node_state s)
      (sessions s)
      (cache s)
      (timeout s)
      (timer s)
      (msg_timer s).

  (** If commit_index > last_applied -> apply log[last_applied] to sm **)
  Definition apply_to_sm (s : RaftState) : (RaftState * option RaftSM_result) :=
    if (last_applied s) <? (commit_index s) then (* check if we have something to commit *)
      let s' := increment_last_applied s in (* TODO: apply the whole log till commit_index *)
      let e := get_log_entry (log s') (last_applied s') in
      match e with
      | None => (s, None) (* the log is not long enough, do not apply anything *)
      | Some e' => (* we found the entry to apply *)
        match (entry e') with
        | content e'' => (* we have a content log to apply *)
          let (sm, result) := RaftSM_update_state (sm s) e'' in (* run the internal sm *)
          let s'' := update_sm s sm in
          (s'', Some result) (* return the new state and result *)
        | _ => (s, None) (* only content logs are applied *)
        end
      end
    else
      (s, None). (* nothing to commit *)

  (** Update the nodes known leader **)
  Definition update_current_leader (s : RaftState) (l : name) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (Some l)
      (log s)
      (commit_index s)
      (last_applied s)
      (sm s)
      (node_state s)
      (sessions s)
      (cache s)
      (timeout s)
      (timer s)
      (msg_timer s).

  (** Update the sessions to accept a new client **)
  Definition update_node_state (s : RaftState) (ns : NodeState) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      (log s)
      (commit_index s)
      (last_applied s)
      (sm s)
      ns
      (sessions s)
      (cache s)
      (timeout s)
      (timer s)
      (msg_timer s).

  (** shortcuts for node state transitions **)
  Definition to_follower (s : RaftState) :=
    update_node_state s follower.

  (** If a node turns to a candidate it advances it's current term. **)
  Definition to_candidate (s : RaftState) :=
    let s' := increment_term s in
    update_node_state s' (candidate candidate_state0).

  Definition to_leader (s : RaftState) (slf : Rep) : RaftState :=
    let lli := get_last_log_index (log s) in
    let l := new_leader (lli + 1) slf in (* init next index list to log index + 1 *)
    update_node_state s (leader l).

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

  (** Convert a node to follower state if it's term is lesser. **)
  Definition equal_term_or_follower (s : RaftState) (t : Term) : RaftState :=
     if TermDeq (current_term s ) t then s
    else if TermLt (current_term s) t then increment_term (to_follower s) else s.

  Definition incr_leaders_next_index (s : RaftState) : RaftState :=
    match (get_leader s) with
    | None => s
    | Some l =>
      let ni := increase_next_index_all (next_index l) in
      update_node_state s (leader (update_leader_state ni (match_index l)))
    end.

  (** Update the sessions to accept a new client **)
  Definition update_sessions (s : RaftState) (se : Sessions) : RaftState :=
    Build_State
      (current_term s)
      (voted_for s)
      (leader_id s)
      (log s)
      (commit_index s)
      (last_applied s)
      (sm s)
      (node_state s)
      se
      (cache s)
      (timeout s)
      (timer s)
      (msg_timer s).

  (** Create a new session and update the state **)
  Definition mk_session (s : RaftState) (c : Client) : (RaftState * SessionId) :=
      let (sessions, id) := new_session (sessions s) c in
      let s' := update_sessions s sessions in
      (s', id).


  (** Update the information what the client voted for in the currents term or none **)
  Definition update_voted_for (s : RaftState) (c : option name) : RaftState :=
    Build_State
      (current_term s)
      c
      (leader_id s)
      (log s)
      (commit_index s)
      (last_applied s)
      (sm s)
      (node_state s)
      (sessions s)
      (cache s)
      (timeout s)
      (timer s)
      (msg_timer s).

  Definition add_vote (s : RaftState) : RaftState :=
    match (node_state s) with
    | candidate s' => update_node_state s (candidate (increment_votes s'))
    | _ => s
    end.

  Definition get_votes (s : RaftState) : nat :=
    match (node_state s) with
    | candidate s' => (votes s')
    | _ => 0
    end.

  (*! create messages and states !*)
  (** Forward the messag if a leader is known **)
  Definition mk_forward_msg (s : RaftState) (o : RaftMsg) : DirectedMsgs :=
    match (leader_id s) with
      (* we have no new current leader, maybe the system was recently initialized and
       * no leader is elected yet. TODO: Ignore the message at the moment *)
    | None => []
    | Some l =>
      [MkDMsg (forward_msg o) [l] 0]
    end.

  (** Create a new timer message **)
  Definition mk_timer_msg (s : RaftState) (slf : Rep) (timeout : nat) : DirectedMsg :=
    MkDMsg (timer_msg (timer s)) [replica slf] timeout.

    (** Create a vote for yourself **)
  Definition mk_vote_request_msg (s : RaftState) (slf : Rep) : DirectedMsg :=
    let lli := get_last_log_index (log s) in
    let llt := get_last_log_term (log s) in
    let vote := request_vote (current_term s) slf lli llt in
    MkDMsg (request_vote_msg vote) (other_names slf) 0.

  (** create an answer to some request vote message **)
  Definition mk_vote_response_msg (t : Term) (g : bool) (n : Rep) : DirectedMsg :=
    let response := request_vote_res t g in
    MkDMsg (request_vote_response_msg response) [replica n] 0.

  (** create a  heartbet message **)
  Definition mk_heartbeat_msg (s : RaftState) (slf : Rep) : DirectedMsg :=
    let lli := get_last_log_index (log s) in
    let llt := get_last_log_term (log s) in
    let beat := heartbeat (current_term s) slf lli llt (commit_index s) in
    MkDMsg (append_entries_msg beat) (other_names slf) 0.

  (** Create the replication messages which are send to the followers
   ** To make this easy the request sends a nat as cmd to the leader and
   ** the leader converts this into a single entry list for the log replication. **)
  Definition mk_append_entries_msg (slf : Rep) (s : RaftState)
             (entries: list Entry) (id : SessionId * RequestId) : DirectedMsgs :=
    let leader := (get_leader s) in
    let llt := get_last_log_term (log s) in
    let lli := get_last_log_index (log s) in
    let msg := replicate (current_term s) slf lli llt (commit_index s) entries id in
    [MkDMsg (append_entries_msg msg) (other_names slf) 0].

  Definition mk_client_response_msg (c : Client) (r : Result) :=
    [MkDMsg (response_msg r) [client c] 0].

  (** Create a new registering result message **)
  Definition mk_register_response_msg (c : Client) (r : Result) :=
    [MkDMsg (register_response_msg r) [client c] 0].

  Definition mk_broadcast_session_msg (slf : Rep) (s : RaftState) : DirectedMsgs :=
    let entry := new_sessions_entry (current_term s) (sessions s) in
    mk_append_entries_msg slf s [entry] (session_id0, request_id0).

  (** Create a broadcast message to inform other nodes about new sessions **)
  (* Definition mk_broadcast_msg (slf : Rep) (s : Sessions) := *)
  (*   [MkDMsg (broadcast_sessions_msg s) (other_names slf) 0]. *)

  (*! combine state transitions and message creation !*)
  (** Create a new timer by setting the new id in the state and creating the corresponding msg. **)
  Definition mk_timer (s : RaftState) (slf : Rep) : (RaftState * DirectedMsg) :=
    let s := set_timer s in
    let msg := mk_timer_msg s slf (timeout s) in
    (s, msg).

  (** Create a new leader timer which gets issued in 50 milliseconds interval **)
  Definition mk_leader_timer (s : RaftState) (slf : Rep) : (RaftState * DirectedMsg) :=
    let s := set_timer s in
    let msg := mk_timer_msg s slf 50 in
    (s, msg).

  (*! The message handling - Update function !*)
  (** The semantics is that an incoming message gets handled by an appropriate
   ** function which creates a new state protocol and some output messages if any.
   ** A direct message is a triple of some message type with the destinations and
   ** some delay in milliseconds. Since a message leaves the type abstract the implementation
   ** decides the type used and returned. **)

  (*! System boot up !*)
  (** A - If the system boots up, the node gets an init message with the
   **     timer offset. The node start it's internal message timer. **)
  Definition handle_init_msg (slf : Rep) : Update RaftState nat DirectedMsgs :=
    fun state timeout =>
      let s := update_timeout state timeout in
      let (s', msg) := mk_timer s slf in
      (Some s', [msg]).

  (*! Register some client at the network !*)
  (** L - Handle incoming new clients **)
  (** Some client sends an empty register_client message and the leader creates a session
   ** for this client. This session is distributed across the network.
   **
   ** The papers approach is to handle register messages like normal log replication messages.
   ** No checks are done if the distribution was successfully since all client messages
   ** are forwarded to the leader. So, the disribution is implemented as a showcase. **)
  Definition handle_register (slf : Rep) : Update RaftState RegisterClient DirectedMsgs :=
    fun state msg =>
        match msg with
        | register_client c =>
          match (node_state state) with
          | leader _ =>
            (* the leader creates a new session and updates it state *)
            let (s, id) := mk_session state c in
            (* create the result message and the log replication message for sessions *)
            let result := register_client_res true id (Some slf) in
            let broadcast := mk_broadcast_session_msg slf s in
            (Some s, mk_register_response_msg c result ++ broadcast)
          | _ =>
            (* forward as everything else *)
            let forward := mk_forward_msg state (register_msg msg) in
            (Some state, forward)
         end
       end.

  (*! Internal Forwarding !*)
  (** The internal forwarding is used to keep the client network handling easy from
   ** the clients perspective. A wrongly delivered message (node not leader) is forwarded
   ** to the clients last known leader.
   ** FIXME: If there is currently no leader the messages is dropped.
   ** If the assumed leader is not a leader the message gets forwarded again.
   ** The leader node unpacks all the layers and sends the request to itself. **)

  (** Recursivly unwrap the forward message until the original request is returned. **)
  Fixpoint unpack_forward_msg (f : RaftMsg) : RaftMsg :=
    match f with
    | forward_msg f => unpack_forward_msg f
    | f => f
    end.

  (** L - Handle fowarded message - unpack and send original message to self. **)
  Definition handle_forward_msg (slf : Rep) : Update RaftState RaftMsg DirectedMsgs :=
    fun state f =>
      match (node_state state) with
      | leader _ =>
        (* maybe there is a better way of handling this. *)
        let msg := unpack_forward_msg f in
        (Some state, [MkDMsg msg [(replica slf)] 0])
      (* Either forward the message to the current leader or ignore it.
       * Maybe a TODO to handle the first encountered messages if there is no leader. *)
      | _ => (Some state, (mk_forward_msg state f))
      end.

  (*! Timer !*)
  (** The raft protocol enforces that every node has an internal timer which gets reseted
   ** if a message from the leader node arrives. To model this with velisarios a node
   ** sends messages with a fix delay to itself and keeps track of the last valid
   ** timer id. FIXME, a more performant way. **)

  (** The node converts to candidate state and starts the election protocol **)
  Definition start_election (state : RaftState) (slf : Rep) : (RaftState * DirectedMsg) :=
    let s := to_candidate state in
    let s' := update_voted_for s (Some (replica slf)) in
    let msg := mk_vote_request_msg s' slf in
    (s', msg).

  (** A - Check if the timer is valid, if not reject the message, otherwise start election.
   **     A leader uses a faster timer to maintain authority **)
  Definition handle_timer_msg (slf : Rep) : Update RaftState Timer DirectedMsgs :=
    fun state msg =>
      (* the internal timer has ended and no new message arrived in between *)
      if TimerDeq (timer state) msg then
        (* keep the internal timer running *)
          match node_state state with
          | leader l => (* as a leader ignore the timeouts, since the leader doesn't send msgs
                        * to itself. Keep the timer running for the time the node looses
                        * the leader state. *)
            let (s, timer) := mk_leader_timer state slf in
            let beat := mk_heartbeat_msg s slf in
            (Some s, [beat; timer])
          | _ => (* the leader failed to respond or the election timed out. *)
            let (s, msg) := start_election state slf in
            let (s', timer) := mk_timer s slf in
            (Some s', [msg; timer])
          end
      else (Some state, []). (* not the right timer -> drop the message *)

  (** A candidate is valid if nothing voted for until now or the candidate was already voted **)
  Definition valid_candidate (s : RaftState) (candidate : Rep) : bool :=
    match voted_for s with
    | None => true
    | Some (replica c) => if rep_deq c candidate then true else false
    | _ => false
    end.

  (** Return true if the logs are equal and (not voted yet or already voted for) **)
  Definition valid_vote state candidate lli llt : bool :=
    let valid_log := check_entry_term (log state) lli llt in
    valid_candidate state candidate && valid_log.

   (** A - all nodes in either way respond to a vote request.
    ** L - if the term is more advanced step back otherwise ignore
    ** C - Check if the vote is valid and maybe grant the vote
    ** F - Check if the vote is valid and maybe grant the vote **)
  Definition handle_request_vote (slf : Rep) : Update RaftState RequestVote DirectedMsgs :=
    fun state msg =>
      (* reissue a new timer *)
      let (s, timer) := mk_timer state slf in
      match msg with
      | request_vote t candi lli llt =>
        if TermLt t (current_term state) then (* ignore the vote is from an old term *)
          (Some state, [mk_vote_response_msg (current_term state) false candi]) (* keep the timer running *)
        else
          let s' := equal_term_or_follower s t in (* check and advance the current term *)
          (* return false if there is some current leader *)
          if andb (if leader_id s' then false else true)
                  (check_entry_term (log s') lli llt ) then
            match voted_for s' with
            | None =>
              let s'' := update_voted_for s' (Some (replica candi)) in
              (Some s'', [mk_vote_response_msg (current_term state) true candi; timer])
            | Some (replica c) =>
              let valid := if rep_deq c candi then true else false in
              (Some s', [mk_vote_response_msg (current_term state) valid candi; timer])
            (* a vote for a client?*)
            | _ => (Some s', [mk_vote_response_msg (current_term state) false candi])
            end
              (* either we have a current leader or we have unequal logs*)
          else (Some s, [mk_vote_response_msg (current_term state) false candi; timer])
      end.

  (** A candidate server checks if the amount of votes recieved from other nodes is the
   ** majority. To check devide the amount of nodes in the network by two and check if
   ** the recieved votes are greater then half the servers. **)
  Definition try_to_become_leader (s : RaftState) (slf : Rep) : (RaftState * list DirectedMsg) :=
    let votes := get_votes s in
    let limit := Nat.div2 num_replicas in (* the minimum of votes needed are >50% *)
    if (Nat.ltb limit votes) then (* we have a majority *)
      let s' := to_leader s slf in
      let msg := mk_heartbeat_msg s' slf in
      let s'' := update_current_leader s' (replica slf) in
      (s'', [msg])
    else (s, []). (* we have no majority yet *)


  (** C - Handle incoming voting results from candidates. **)
  Definition handle_response_vote (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state msg =>
      match msg with
      | request_vote_res t g =>
        if g then (* the vote was granted, check if we have the majority *)
          let s := add_vote state in
          let (s', msgs) := try_to_become_leader s slf in
          if is_leader s' then
                 let (s'', timer) := mk_leader_timer s' slf in
                 (Some s'', msgs ++ [timer])
          else
            let (s'', timer) := mk_timer s' slf in
            (Some s'', msgs ++ [timer])
        else
          let s := equal_term_or_follower state t in
          (Some s, [])
      | _ => (* ignore the message if not a voting message result *)
        (Some state, [])
      end.

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
   * TODO: leader send response to client
   * TODO: deal with log inconsistency -> the leader needs to detect the last valid log. *)

  (** Check if a client request is valid and enter it into the cache.
   ** TODO: Adding the request beforehand is maybe inappropriate **)
  (* Definition valid_request (state : RaftState) (si : SessionId) (ri : RequestId) : option RaftSM_result := *)
  (*   if valid_session (sessions state) si then *)
  (*     processed_request (cache state) si ri *)
  (*   else None. *)

  (** Check if we already have a result and answer with the result or answer with false **)
  Definition cached_request (c : Cache) (cl : Client) :=
    match (result c) with
    | None => [] (* TODO: at the moment return nothing if we have no cached result *)
    | Some res =>
      let response := client_res true res in
      [MkDMsg (response_msg response) [client cl] 0]
    end.

  (** Create a new log entry and update the state **)
  Definition add2log (s : RaftState) (cmd : Content) : (RaftState * Log):=
    let entry := [new_entry (term (current_term s)) cmd] in
    let s' := update_log s (append2log (log s) entry) in
    (s', entry).

  (** L - Handle client input to the system. **)
  (** Forward the message if the request reaches the wrong node.
   ** As leader generate the entries from the request and apply the entries to the
   ** internal log. Afterwards send AppendEntries messages to the followers.
   ** A follower gets an request if last_log_index >= next_index for a follower **)
  Definition handle_request (slf : Rep) : Update RaftState ClientRequest DirectedMsgs :=
    fun state r =>
      match node_state state with
      | candidate _ => (Some state, []) (* a candidate ignores requests from clients *)
      | follower => (* Some follower that forwards *)
        let msg := mk_forward_msg state (request_msg r) in
        (Some state, msg)
      | leader _ => (* the leader handles client requests *)
        match r with (* destructre the message *)
        | client_request c si ri cmd =>
          if valid_session (sessions state) si then
            match in_cache (cache state) si ri with
            | Some res => (* the request was already handled, return the cached result *)
              let msg := cached_request res c in
              (* let response := client_res true res in *)
              (* let msg := [MkDMsg (response_msg response) [client c] 0] in *)
              (Some state, msg)
            | None => (* we have new request *)
              (* simply append the message to the leaders log *)
              let (s, entry) := add2log state cmd in
              (* let id := (si, ri) in *)
              (* let entry := [new_entry (term (current_term state)) cmd] in *)
              (* let s := update_log state (append2log (log state) entry) in *)
              (* create the replication messages for all nodes *)
              let dmsgs := mk_append_entries_msg slf s entry (si, ri) in
              let s' := incr_leaders_next_index s in
              (Some s', dmsgs)
            end
          else (Some state, []) (* ignore messages with no valid session *)
        end
      end.

  (** 1. If the next used log index is equal to the internal log index
   ** 1.1 check if the terms of the entries are matching and
   ** 1.1.1 if the terms are equal do nothing
   ** 1.1.2 if the terms are unequal take only the last_log_index and append the new entries
   ** 2. If the next used log index is free append the entries **)
  Definition append_entries2log (entries : list Entry) (lli : nat) (t : Term) (s : RaftState) :=
    let log := log s in
    let last_index := get_last_log_index log in
    if ((lli + 1) ==  last_index) then
      (* an entry exists, now check if terms are matching *)
      let last_term := get_last_log_term log in
      if (TermDeq t last_term) then
        (* the terms are matching, we assume the entry is already there *)
        log
      else (* delete the requested index and all entries which follow this one *)
        let log' := take_from_log (lli + 1) log in
        append2log log' entries
    else append2log log entries.

    Definition update_term_and_leader (s : RaftState) (t : Term) (l : Rep) :=
      let s' := equal_term_or_follower s t in
      update_current_leader s' (replica l).

    Definition handle_log_entry (s : RaftState) (ci : nat) :=
      let (s', _) := apply_to_sm s in
      s'.

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
      match node_state state, msg with
      | leader _, _ => (Some state, []) (* a leader ignores append entries messages *)
      | _, heartbeat t l lli llt ci => (* adhere to the beat and update yourself *)
        let s := update_term_and_leader state t l in
        (* let s := equal_term_or_follower state t in *)
        (* let s' := update_current_leader s (replica l) in *)
        let (s', timer) := mk_timer s slf in
        (Some s', [timer]) (* we recieved a heartbeat and restart our internal interval *)

      | _, replicate t l lli llt ci entries id => (* replicate and update yourself *)
        (* let s := equal_term_or_follower state t in *)
        (* let s' := update_current_leader s (replica l) in *)
        let s := update_term_and_leader state t l in
        if (TermLt t (current_term state)) then
          (* reply false if the replication term is lower than the current term *)
          let result := append_entries_res (current_term state) false slf id in
          (Some state, [MkDMsg (append_entries_response_msg result) [replica l] 10])
        else
          if (negb (check_entry_term (log state) lli llt )) then
            (* reply false if the last log index or term does not match *)
            let result := append_entries_res (current_term state) false slf id in
            (Some state, [MkDMsg (append_entries_response_msg result) [replica l] 20])
          else
            (* handle the replication request *)
            let new_log := append_entries2log entries lli t state in
            let s := (update_log state new_log) in
            (* handle the replication cases *)
            let s' := handle_log_entry s ci in
            let result := append_entries_res (current_term s') true slf id in
            (* let s' := (update_log s new_log) in *)
            (* let (s'', _) := apply_to_sm s' in (* apply to internal sm if new commits happend *) *)
            (Some s', [MkDMsg (append_entries_response_msg result) [replica l] 0])
      end.


  (** Check if the majority of servers replicated the log. **)
  Definition is_replicated (s : RaftState) : bool :=
    let lli := get_last_log_index (log s) in
    match (get_leader s) with
    | None => false (* not a leader node *)
    | Some l =>
      let replicated := num_replicated (next_index l) lli 0 in
      let limit := Nat.div2 num_replicas in (* the minimum needed are >50% *)
      if (Nat.ltb limit replicated) then (* we have a majority *)
        true
      else false
    end.

  (** L - Handle results messages from followers. **)
  Definition handle_append_entries_result (slf : Rep) : Update RaftState Result DirectedMsgs :=
    fun state msg =>
      match node_state state, msg with
      | leader l, append_entries_res t true node (si, ri) =>
        (* the follower updated its log and the leader updates the next index. *)
        let ni := increase_next_index (next_index l) node in
        let l' := update_leader_state ni (match_index l) in
        let s := update_node_state state (leader l') in
        if is_replicated s then
          let s' := increment_commit_index s in
          let (s'', result) := apply_to_sm s' in
          match result with
          | None => (Some s, []) (* something failed by applying the sm *)
          | Some r =>
            let res := client_res true r in
            let client_msg := mk_client_response_msg  (* FIXME *) res  in
            (Some s'', client_msg)
          end
        else (Some s, []) (* the majority is still missing the current log entry *)
      | leader l, append_entries_res t false node id =>
        if TermLt (current_term state) t then
          (* the leader has an outdated term, so return to follower *)
          let s := equal_term_or_follower state t in
          (Some s, [])
        else
          (Some state, [])
      | _, _ => (Some state, [])
      end.
        (*          match msg with *)
      (*   | append_entries_res t true node => *)
      (*     (* the follower updated its log and the leader updates the next index. *) *)
      (*     let ni := increase_next_index (next_index l) node in *)
      (*     let l' := update_leader_state ni (match_index l) in *)
      (*     let s := update_node_state state (leader l') in *)
      (*     if is_replicated s then *)
      (*       (Some s, []) *)
      (*     else (Some s, []) (* the majority is still missing the current log entry *) *)
      (*   | append_entries_res t false node => (* the replication doesn't work *) *)
      (*     if TermLt (current_term state) t then *)
      (*     (* the leader has an outdated term, so return to follower *) *)
      (*       let s := equal_term_or_follower state t in *)
      (*       (Some s, []) *)
      (*     else *)
      (*       (Some state, []) *)
      (*   | _ => (Some state, []) (* we got the wrong result message *) *)
      (*   end *)
      (* | _ => (Some state, []) (* the results are for the leader *) *)
      (* end. *)

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
 (* Definition initial_faked_leader_state : RaftState := *)
 (*    Build_State *)
 (*      term0 (* zero at first boot *) *)
 (*      [] (* *) *)
 (*      None (* voted for no one. *) *)
 (*      [] (* no log entries stored *) *)
 (*      0 (* no commit done *) *)
 (*      0 (* nothing applied to state machine *) *)
 (*      5 (* some way of defining an offset is needed *) *)
 (*      RaftSM_initial_state (* defined within the raft context *) *)
 (*      follower (* at default no one is leader *) *)
 (*      (Some (nat2rep 0)) (* set leader to 0 *) *)
 (*      timer0. *)


  (** An initial leader state which should only used for testing. **)
 (* Definition initial_leader_state : RaftState := *)
 (*   let reps := List.map nat2rep [1, 2, 3] in *)
 (*    let leader' := after_election_leader 0 reps in *)
 (*    Build_State *)
 (*      term0 (* zero at first boot *) *)
 (*      [] *)
 (*      None (* voted for no one. *) *)
 (*      [] (* no log entries stored *) *)
 (*      0 (* no commit done *) *)
 (*      0 (* nothing applied to state machine *) *)
 (*      5 (* some way of defining an offset is needed *) *)
 (*      RaftSM_initial_state (* defined within the raft context *) *)
 (*      (leader leader') (* define as leader with 3 followers *) *)
 (*      (Some (nat2rep 0)) (* set leader to 0 for testing *) *)
 (*      (* [1, 2, 3] (* set follower nodes *). *) *)
 (*      timer0. *)


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

  (** This is a special purpose state, which initiates a leader.
   ** Providing an initial leader is not inteded by the raft protocol.
   ** This state assumes that the network has 3 followers. **)
  Definition dummy_leader_state : RaftState :=
    Build_State
      term0
      None
      (Some (replica (nat2rep 0)))
      []
      0
      0
      RaftSM_initial_state
      (leader (new_leader 0 (List.map nat2rep [1, 2, 3])))
      []
      []
      150
      timer0
      timer0.

  (** This binding should only used for testing. **)
  Definition RaftLeaderSM (slf : Rep) : MStateMachine _ (* let the compiler guess ? *) :=
    mkSM
      (replica_update slf)
      (dummy_leader_state).


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
