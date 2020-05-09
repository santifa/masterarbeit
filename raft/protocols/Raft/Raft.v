(*! This file is part of the raft implementation in velisarios. !*)

(*! abstract !*)
(** This file implements the real protocol. First the velisarios process states
 ** and transitions are defined and than the handler functions which process the
 ** incoming messages updates the state and sends outgoing messages.
 **
 ** NOTE: Not implemented is log compaction, membership changes, read only queries
 ** Leader Timer is set to 50ms **)

Require Export Protocols.Raft.RaftHeader.
Require Export String.
Require Export Peano.
Require Export List.
(* short record updates *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section Raft.

  Local Open Scope eo.
  Local Open Scope proc.

  (** Redeclare the general system context as new local variable. **)
  Context { raft_context : RaftContext }.

  (*! Process State !*)
  (** Every node or process has a state for managing the protocol internals and
   ** the log and state machine. **)
  Record RaftState :=
    MkState
      {
        (* persistent - The last term the node has seen, this should be persitent over crashes. *)
        current_term : Term;
        (* persistent - The candidate this node voted for the current term or null if none *)
        voted_for : option Rep;
        (* persistent - The actual term leader the node knows. *)
        leader_id : option Rep;
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
        (* sessions: Sessions; *)
        (* internal volatile - cache the clients requests *)
        cache : Cache;
        (* internal persistent - the timeout in millisecs after which a new election is triggered.
         * The timeout is set with init message which provides a random value. *)
        timeout : nat;
        (* internal volatile - The id of the last send timout message. *)
        timer : Timer;
        (* internal volatile -
         * The timer for messages which should be resend indefinitly if no response *)
        msg_timer : list Timer;
      }.

  (* abuse typeclasses to provide an update mechanism by record field name. *)
  Instance etaRaftState : Settable _ :=
    settable! MkState <current_term; voted_for; leader_id; log; commit_index;
      last_applied; sm; node_state; cache; timeout; timer; msg_timer>.


  (** The initial state for all nodes on bootup. **)
  Definition state0 : RaftState :=
    MkState
      term0 (* zero at first boot *)
      None (* voted for no one. *)
      None (* no leader known *)
      [] (* no log entries stored *)
      0 (* no commit done *)
      0 (* nothing applied to state machine *)
      RaftSM_initial_state (* defined within the raft context *)
      follower (* at default no one is leader *)
      [] (* No clients added *)
      (* [] (* empty cache *) *)
      0 (* the timeout gets overwritten at start up *)
      timer0 (* start with the initial timer *)
      [].

  (*! State transitions !*)
  (** Update the timer offset on boot up. **)
  Definition update_timeout (s : RaftState) (n : nat) : RaftState :=
    s <| timeout := n |>.

  (** If the input term is newer, advance this node to the new term. **)
  Definition advance_term (s : RaftState) (t : Term) :RaftState :=
    if (current_term s) <? t then
      s <| current_term := t |> <| voted_for := None|>
        <|leader_id := None |> <| node_state := follower |>
    else s.

 (** If some leader is byzantine a new election starts and the term number is increased **)
  Definition inc_term (s : RaftState) : RaftState :=

    advance_term s (next_term (current_term s)).

  (** Increment the timer id if a new timer message was send. **)
  Definition set_timer (s : RaftState) : RaftState :=
    s <| timer := (next_timer (timer s)) |>.

    (** Increment the timer id if a new timer message was send. **)
  (* Definition set_msg_timer (s : RaftState) : RaftState := *)
  (*   s <| msg_timer := (next_timer (msg_timer s)) |>. *)

  (** Replace the internal log with a new one **)
  Definition update_log (s : RaftState) (l : Log) : RaftState :=
    s <| log := l |>.

  (** Update the state machine and index of already commited log entries **)
  Definition update_sm (s : RaftState) (st : RaftSM) : RaftState :=
    s <| sm := st |>.

  (** Update the information what the client voted for in the currents term or none **)
  Definition update_voted_for (s : RaftState) (c : Rep) : RaftState :=
    s <| voted_for := (Some c) |>.

  (** Increment the last applied log index **)
  Definition inc_last_applied (s : RaftState) : RaftState :=
    s <| last_applied := (last_applied s) + 1 |>.

  (** Increment the commit_index  **)
  Definition inc_commit_index (s : RaftState) : RaftState :=
    s <| commit_index := (commit_index s) + 1 |>.

  (** update the commit index to min(ci, last_applied) if leader ci > ci **)
  Definition update_commit_index (s : RaftState) (ci : nat) : RaftState :=
    if ((commit_index s) <? ci) then
      s <| commit_index := Nat.min ci (last_applied s) |>
    else s.

  (** Update the nodes known leader **)
  Definition update_leader_id (s : RaftState) (l : Rep) : RaftState :=
    s <| leader_id := (Some l) |>.

  Definition update_cache (s : RaftState) (c : Cache) : RaftState :=
    s <| cache := c |>.

  (** Update the sessions to accept a new client **)
  Definition update_node_state (s : RaftState) (ns : NodeState) : RaftState :=
    s <| node_state := ns |>.

  (*! Transition rules !*)
  (** Utility function which accepts a partial message and isnerts the missing state parts. **)
  Definition mk_msg (f : Term -> nat -> Term -> nat -> DirectedMsg) (s : RaftState) :=
    let lli := last_log_index (log s) in
    let llt := last_log_term (log s) in
    f (current_term s) lli llt (commit_index s).

  (*! Node State & Voting !*)
  (** shortcuts for node state transitions **)
  Definition to_follower (s : RaftState) :=
    update_node_state s follower.

  (** If a node turns to a candidate it advances it's current term. **)
  Definition to_candidate (s : RaftState) :=
    let s' := inc_term s in
    update_node_state s' (candidate candidate_state0).

  Definition to_leader (s : RaftState) (slf : Rep) : RaftState :=
    let lli := last_log_index (log s) in
    let l := new_leader (lli + 1) slf in (* init next index list to log index + 1 *)
    update_leader_id (update_node_state s (leader l)) slf.

  (** Convert a node to follower state if it's term is lesser and updates
   ** to the provided term. **)
  Definition equal_term_or_follower (s : RaftState) (t : Term) : RaftState :=
    if TermDeq (current_term s ) t then s
    else if TermLt (current_term s) t then advance_term (to_follower s) t else s.

  (** increment the vote count **)
  Definition add_vote (s : RaftState) : RaftState :=
    update_node_state s (increment_votes (node_state s)).

  (** Return true if the voted_for is None or the candidate  and the
   ** log index and term matches with the vote request index and term. **)
  Definition is_valid_vote_request (s : RaftState) (lli : nat) (llt : Term) (c : Rep) : bool :=
    let equal_log := check_entry_term (log s) lli llt in
    let not_voted :=
        match voted_for s with
        | None => true
        | Some n => if rep_deq n c then true else false
        end in
    andb equal_log not_voted.

  (** Start a new election by transitioning to candidate state and vote for itself. **)
  Definition start_election (s : RaftState) (n : Rep) : RaftState :=
    update_voted_for (to_candidate s) n.

  (** Test if the candidate has the majority of votes and convert to leader if so. **)
  Definition try_leadership (s : RaftState) (slf : Rep) : (RaftState * list DirectedMsg) :=
    if majority_votes (node_state s) then
      let s' := to_leader s slf in
      let beat_pf := mk_heartbeat_msg slf in
      (s', [mk_msg beat_pf s])
    else (s, []).

  (*! State machine !*)
  (** apply an entry if it is a content entry to the sm **)
  Definition apply_entry (s : RaftState) (e : Entry) : RaftState * option RaftSM_result :=
    match (entry e) with
    | content c =>
      let (sm, result) := RaftSM_update_state (sm s) c in
      (update_sm s sm, Some result)
    | _ => (s, None)
    end.

  (** Apply a list of entries and return the last state and the sm results. **)
  Definition apply_entries (s : RaftState) (l : Log) : RaftState * list (option RaftSM_result) :=
    let r := map (fun x => apply_entry s x) l in
    let r' := map (fun x => snd x) r in
    let s' := last r (s, None) in
    ((fst s'), r').

  (** Apply rule: commit_index > last_applied -> apply log[last_applied++] to sm.
   ** NOTE: only one entry is applied at the moment **)
  Definition apply_to_sm (s : RaftState) : (RaftState * option RaftSM_result) :=
    if (last_applied s) <? (commit_index s) then (* commit_index > last_applied *)
      let s' := inc_last_applied s in
      let e := get_log_entry (log s') (last_applied s') in (* get the log entry *)
      match e with (* check if the log entry was found *)
      | None => (s, None) (* no entry found, skip *)
      | Some e' => apply_entry s' e'
      end
    else (s, None).

  (** Add new entries to the log and fix logs which have an entry at position (lli + 1)
   ** with a different term then llt by removing all entries from this one till the end. **)
  Definition fix_log (s : RaftState) (e : list Entry) (lli : nat) (llt : Term) : RaftState :=
    match get_log_entry (log s) (lli + 1) with
    (* We have no entry at position llit + 1, so we can just add the new entries. *)
    | None => update_log s (add2log (log s) e)
    | Some e' => (* test if we have an conflicting entry or maybe the same *)
      if TermDeq (entry_term e') llt then
        (* the entries are equal so do nothing *)
        s
      else (* the entries conflict so remove the log tail from this entry on *)
        let lli' := Datatypes.length (log s) - (lli + 1) in
        let l := take_from_log (log s) lli' in
        update_log s (add2log l e)
    end.

  (*! Sessions !*)
  (** Create a new session and update the log **)
  Definition mk_session (s : RaftState) (c : Client) : RaftState * SessionId :=
    let sessions := last_session (log s) in
    let (sessions', id) := new_session sessions c in
    let entry := new_sessions_entry (current_term s) sessions' in
    let log := add2log (log s) [entry] in
    (update_log s log, id).

  (** As leader increment all next index for all nodes. This typically happens
   ** if the leader sends a replication message to all nodes. **)
  Definition incr_next_index_all (s : RaftState) : RaftState :=
    let l := (node_state s) in
    match l with
    | leader l =>
      (* increment the next_index for all nodes including the leader *)
      let ni' := map succ_index (next_index l) in
      update_node_state s (leader (update_leader_state ni' (match_index l)))
    | _ => s
    end.

  (** Prepare the replication, add the entry to the log, increment the counters and
   ** create the message. **)
  Definition mk_replication (s : RaftState) (slf : Rep) (e : Entry)
    (sid : SessionId * RequestId) : RaftState * DirectedMsg :=
    (* add the entry to the log *)
    let s' := update_log s (add2log (log s) [e]) in
    (* create the replication messages *)
    let ae_pf := mk_append_entries_msg slf e sid in
    let ae_msg := mk_msg ae_pf s in
    (* bump the next index of all nodes *)
    let s'' := incr_next_index_all s in
    (s'', ae_msg).

  (** Create a new response to the leader if one exists or nothing otherwise. **)
  Definition mk_append_response (s : RaftState) (slf : Rep) (g : bool) : DirectedMsgs :=
    match leader_id s with
    | None => []
    | Some l =>
      [mk_append_entries_response_msg (current_term s) g (session_id0, request_id0) slf l]
    end.

  (*! The message handling - Update function !*)
  (** Velisarios uses update functions which changes the state and produces outgoing
   ** messages to react to incoming messages aka events. The used message type is
   ** the directed messages which is a triple of some payload, the destinations and
   ** some delay. The functions are designed to handle requests and responses of some
   ** message type, for instance the handle_vote functions is responsible for
   ** vote_requests and vote_responses. **)

  (*! System boot up !*)
  (** A - If the system boots up, the node gets an init message with the
   **     timer offset. The node start it's internal message timer. **)
  Definition handle_init_msg (slf : Rep) : Update RaftState nat DirectedMsgs :=
    fun state timeout =>
      let s := set_timer (update_timeout state timeout) in
      let msg := mk_timer_msg (timer s) slf timeout in
      (Some s, [msg]).

  (*! Register some client at the network !*)
  (** The client sends an request_reigster_client message with itself as payload.
   ** If it's not the leader the node points to the real leader.
   ** NOTE: The real leader can be None if the system has no current leader.

   ** The leader creates a new session for the client and replicates the new log entry
   ** across the network. **)
  Definition handle_register (slf : Rep) : Update RaftState RegisterClient DirectedMsgs :=
    fun state msg =>
        match msg with
        | request_register_client c =>
          match (node_state state) with
          | leader _ => (* we're the leader *)
            (* the leader creates a new session and updates it state *)
            let (s, id) := mk_session state c in
            (* create the success result message. provide no leader hint,
               the client has already choosen correct *)
            let result_msg := mk_register_response_msg c id true None in
            (* Create a new session entry out of the newly created log item. *)
            let entry := new_sessions_entry (current_term s) (last_session (log s)) in
            (* Take the entry and create the replication messages. *)
            let (s', ae_msg) := mk_replication s slf entry (session_id0, request_id0) in
            (Some s', [result_msg, ae_msg])
          | _ => (* point to the real leader *)
            (* if leader_id says none the network has no current leader *)
            let msg := mk_register_response_msg c session_id0 false (leader_id state) in
            (Some state, [msg])
          end
        | _ => (Some state, []) (* ignore responses to client register messages *)
       end.

  (*! Timers for nodes and leaders !*)
  (** The raft protocol uses timers to handle failures in the system.
   ** This is modeled as timer messages which a node sends itself with a certain delay.
   ** A normal node uses around 300ms and the leader node 50ms as a delay.
   ** The leader maintains its authority by sending heartbeat messages in idle times.
   ** A normal node detects failed leaders when no more message are arrevied by the leader. **)
  Definition handle_timer (slf : Rep) : Update RaftState Timer DirectedMsgs :=
    fun state msg =>
      (* the internal timer has ended and no new message arrived in between *)
      if TimerDeq (timer state) msg then
        (* check if leader or "normal" timer *)
          match node_state state with
          | leader l => (* 50ms are over trigger a new round of heartbeats *)
            let s := set_timer state in
            (* reset the leader timer *)
            let timer_msg := mk_leader_timer_msg (timer s) slf in
            (* Create the partial message and insert the missing parts *)
            let beat_pf :=  mk_heartbeat_msg slf in
            let beat := mk_msg beat_pf s in
            (* update and send messages *)
            (Some s, [beat; timer_msg])
          | _ => (* the leader failed to respond or the election timed out. *)
            let s := set_timer (start_election state slf) in
            (* create a new partial voting message and fill the missing parts. *)
            let vote_pf := mk_request_vote_msg slf in
            let vote_msg := mk_msg vote_pf s in
            (* create a new timer message *)
            let timer_msg := mk_timer_msg (timer s) slf (timeout s) in
            (Some s, [timer_msg])
          end
      else (Some state, []). (* not the right timer -> drop the message *)

  (*! Voting process !*)
  (** Every node handles a vote request by first checking if the request is at least
   ** the same term. Then grant the vote if the node has not already voted or it's the
   ** same candidate and the logs are equal until the candidates last index and term.

   ** A response is handled by all nodes by checking if the vote is granted.
   ** If so the node increments the votes and checks if it has a majoritiy.
   ** If yes the node maintains leadership.
   ** NOTE: Since the state is not changed if the votes are old, the node only
   ** restarts its timer. Old votes are dropped and if the node see a newer term in all
   ** cases it converts to a follower. **)
  Definition handle_vote (slf : Rep) : Update RaftState RequestVote DirectedMsgs :=
    fun state msg =>
      (* reissue a new timer *)
      let s := set_timer state in
      let timer_msg := mk_timer_msg (timer s) slf (timeout s) in
      (* Handle the vote message which can be either a request or response *)
      match msg with

      (* Vote request *)
      | request_vote t c lli llt =>
        if t <? (current_term state) then
          (* ignore the vote is from an old term *)
          let response := mk_request_vote_response_msg (current_term s) false c in
          (* respond with a deny and restart the timer. *)
          (Some state, [response; timer_msg])
        else
          (* We have a vote from the current or newer term. *)
          (* Check if the term is newer and maybe update and convert to follower *)
          let s' := equal_term_or_follower s t in
          (* the logs matched and the node hasn't voted yet or it's the same candidate. *)
          if is_valid_vote_request s lli llt c then
            (* Update voted_for and respond with success *)
            let s'' := update_voted_for s' c in
            let response := mk_request_vote_response_msg (current_term s'') true c in
            (Some s'', [response; timer_msg])
          else
            (* The log didn't match or already voted for another candidate reply failure. *)
            let response := mk_request_vote_response_msg (current_term s') false c in
            (Some s', [response; timer_msg])

      (* Vote responses - also restart the election timeout *)
      | response_vote t g =>
        match g with
        | false => (* The vote was not granted *)
          (* check if maybe a next election round was triggered *)
          let s' := equal_term_or_follower s t in
          (Some s', [])

        | true => (* The vote was granted *)
          let (s', msgs) := try_leadership (add_vote s) slf in
          if is_leader (node_state s') then
            (* Act as leader and maintain leadership *)
            let s'' := set_timer state in
            (* reset the leader timer *)
            let timer_msg := mk_leader_timer_msg (timer s'') slf in
            (* Create the partial message and insert the missing parts *)
            let beat_pf :=  mk_heartbeat_msg slf in
            let beat := mk_msg beat_pf s'' in
            (* Add a new_term to the log and replicate it. *)
            let entry := new_term_entry (term t) in
            (* Give dummy session to the leader and ignore it in he caching *)
            let (s''', ae_msg) := mk_replication s slf entry (session_id0, request_id0) in
            (Some s''', msgs ++ [timer_msg, ae_msg])
         else
           (* Not enough votes restart election timer *)
           (Some s', msgs ++ [timer_msg])
        end
      end.

  (*! Log replication !*)
  (** The log replication is the process of distributing informations across the network
   ** and update the nodes and internal state machines along. This process hast multiple
   ** parts. 1. The leader recieves a valid requests and updates its log and sends
   ** replication reqeests to all other nodes. 2. The nodes handle the replication request
   ** and update its log and the internal state machine. Afterwards, it sends
   ** informations about the replication back to the leader. 3. The leader evaluates the
   ** response informations and maybe applies log entries to its own state machine and
   ** resond to the client.

   ** NOTE: The process is quite complex since the linearizable semantics are applyed and
   ** Caches and Sessions are used to handle the requests.
   ** NOTE: The leader resend replication requests if the node doesn't respond. #TODO
   ** NOTE: The leader applies log entries replicated by the majority to the state machine.
   ** NOTE: The leader shall rebuild node logs with inconsitencies. **)

  (*! Handle incoming requests !*)
  (** The leader accepts incoming requests if the client has a valid session and
   ** checks the cache is the request is already pending. If the request is valid and
   ** not pending the leader issues replication requests across the network.
   ** NOTE: The leader should respond different indicators what went wrong. This is not done.
   ** The leader sends only true if the request is valid but he sends all informations
   ** it knows to the client. Such that, a leader replies false with a cached result.
   ** NOTE: The leader responds to the client after the majority of the network has
   ** replicated the request. This is maybe a bit defensive. **)
  Definition handle_request (slf : Rep) : Update RaftState ClientRequest DirectedMsgs :=
    fun state msg =>
       match msg with
       | client_request c sid rid cmd =>
         let failed_response := mk_client_response false None (leader_id state) (Some c) in
         (* we have a request and we're the leader *)
         if is_leader (node_state state) then
           (* check if the request is new and the session is valid *)
            if valid_request (last_session (log state)) sid rid then
              (* create the entry and add the request to the log *)
              let entry := new_content_entry (current_term state) cmd in
              let (s, ae_msg) := mk_replication state slf entry (sid, rid) in
              (* add the entry to the internal cache *)
              let s' := update_cache s (add2cache (cache s) sid rid (last_log_index (log s))) in
              (* replicate the request *)
              (Some s', [ae_msg])
            else (* The request is old so check the cache even if the session is invalid *)
              let result := get_cached_result (cache state) sid rid in
              let response := mk_client_response false result (leader_id state) (Some c) in
              (Some state, response)
        else (* we're not the leader so point the leader if one *)
          (Some state, failed_response)
      | _ => (Some state, []) (* ignore response messages *)
      end.


  (*! Handle the replication process !*)
  (** This is the whole raft core update process. The leader handles response messages
   ** from followers. Followers react to heartbeat and replicate messages from the leader.
   ** Candidates convert to followers if a heartbeat with at least the same term is recieved.
   **
   ** 1. Heartbeats are used to maintain leadership in the network. In the original paper
   ** heartbeats are empty append entry calls. A reciever checks the term and the last log index and term.
   ** If there is something to commit the node applies it to the raft state machine.
   **
   ** 2. Replication messages are triggered by the leader to update the log of its followers.
   ** A follower checks the senders term and last log index and term and maybe correct its log.
   ** It creates a cache entry for the replication request and updates its log.
   ** If there is something to apply to the raft state machine, apply and update the cache.
   **
   ** 3. Response
   **
   ** NOTE: The process enforces that a new leader first sends a heartbeat since only followers
   ** racts to replication messages.
   ** NOTE: Even if the message can contain lists of entries and most functions handles lists
   ** of new log entries some are only build to apply the new head. So only send messages with
   ** one entry at a time to ensure correctness.
   **
   ** TODO: Handle log mismatches correctly, resending of old entries
   ** TODO: Resend failed entries
   ** TODO: Apply early to the state machine as leader and late as follower
   ** TODO: Rewrite some functions to handle updates more precisly in one function instead
   ** of cluttering them. **)
  Definition handle_append_entries (slf : Rep) : Update RaftState AppendEntries DirectedMsgs :=
    fun state msg =>
      match msg, node_state state with
      | replicate t l lli llt ci e id, follower =>
        (* replication messages are only handled by followers *)
        if t <? (current_term state) then
          (* the senders term is lower deny the replication request  *)
          let response := mk_append_response state slf false in
          (Some state, response)
        else (* the senders term is equal or greater *)
          (* convert the node or update the term if neccessary *)
          let s := equal_term_or_follower state t in
          if check_entry_term (log state) lli (term llt) then
            let s' := update_leader_id state l in
            let s'' := match e with
                       | [] => s' (* we have an heartbeat *)
                       | x => (* we have an replication request *)
                         (* add the recieved entries to the log and possible fix the log. *)
                         let s' := fix_log s e lli llt in
                         (* add the new entry to the cache with the next index for recognition *)
                         let c := add2cache (cache s') (fst id) (snd id) (last_log_index (log s')) in
                         update_cache s c
                       end in
            (* check for new commits and apply them to the raft state machine *)
            let (s''', result) := apply_to_sm (update_commit_index s'' ci) in
            let st := update_cache s''' (result2cache (cache s''') (last_applied s''') result) in
            (* Respond with success to the leader *)
            let response := mk_append_response st slf true in
            (Some st, response)
          else (* the logs doesn't match, so only respond with false *)
            let response := mk_append_response state slf false in
            (Some state, response)

      | response t g n id, leader l =>
        (* Only leaders react to replication response messages *)
        if g then (* the replication was successfull on the node n *)
          (* increase the index of the highest log entry known to be replicated on that node *)
          let mi := increase_match_index (match_index l) n in
          let s := update_node_state state (leader (update_leader_state (next_index l) mi)) in
          (* check if the majority has already replicated that entry *)
          if majority_replicated mi (get_match_index mi n) then
            (* increment the commit index and apply the newly commited entry
             * to the raft state machien *)
            let (s', result) := apply_to_sm (inc_commit_index s) in
            let s'' := update_cache s' (result2cache (cache s') (last_applied s') result) in
            let c := get_session_client (last_session (log s'')) (fst id) in
            match c with
              (* no client associated, ignore result *)
            | None => (Some state, [])
            | Some c' =>
              (* Return the result to the client *)
              let response := mk_client_response true result (leader_id s'') (Some c') in
              (Some s'', response)
            end
          else (* not replicated to a majority, so do nothing *)
            (Some s, [])
        else
          (* Something failed, TODO: handle possible failure cases, such at
           * outdated term, log mismatch etc. *)
        (Some state, [])

      | _, _ => (Some state, []) (* otherwise ignore the replication request at the moment *)
      end.

  (** The main update function which calls the appropriate handler function
   ** for the incoming message type. **)
  Definition replica_update (slf : Rep) : MUpdate RaftState :=
    fun state m =>
      match m with
      (* Boot up the system *)
      | init_msg d => handle_init_msg slf state d
      (* Register a new client *)
      | register_msg d => handle_register slf state d
      (* Heartbeat or replication *)
      | append_entries_msg d => handle_append_entries slf state d
      (* Request a vote *)
      | request_vote_msg d => handle_vote slf state d
      (* Respond to a vote request *)
      | request_vote_response_msg d => handle_vote slf state d
      (* React to a timer  *)
      | timer_msg d => handle_timer slf state d
      (* Handle client requests *)
      | request_msg d => handle_request slf state d
      (* Ignore messages which are directed to the client *)
      | _ => (Some state, [])
      end.

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
