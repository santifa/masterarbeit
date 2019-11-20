(*!
 * This file is part of the raft implementation with velisarios.
!*)

(*! abstract !*)
(** This file defines the basics parts used within the protocol.
 ** In general the protocol can be devided into three main parts:
 ** - Client Interaction
 ** - Leader Election
 ** - Log Replication
 **
 ** The protocol is modeled as an agent based message passing network.
 ** Which means, that the nodes only communicate with messages over the network or
 ** node internal. Since coq uses exhausting pattern matching all cases needs to be handled
 ** even if they only exists in theory.
 **
 ** Throughout this project the follwing naming convention is used:
 ** - Definitions, fixpoints and inductive type cases are in snake_case
 ** - Types, proven definitions are in CamelCase
 ** - There are exceptions **)
Require Export RaftContext.
Require Export String.

Section RaftHeader.

  (** Redeclare the general system context. **)
  Context { raft_context : RaftContext }.


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

  (** The session id for some client.
   ** Upon registering the leader creates the session id for the client. **)
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

  (** A client generates monotocally the ids for its requests.
   ** A Client should use this methods for commincation with the network. **)
  Inductive RequestId := request_id (n : nat).

  Definition request_id2nat (id : RequestId) : nat :=
    match id with
    | request_id id' => id'
    end.
  Coercion request_id2nat : RequestId >-> nat.

  Definition next_request_id (id : RequestId) : RequestId := request_id (S id).

  Lemma RequestIdDeq : Deq RequestId.
  Proof.
    introv. destruct x, y; prove_dec.
    destruct (deq_nat n n0); prove_dec.
  Defined.

  (** the initial request id **)
  Definition request_id0 := request_id 0.

  (** This implementation keeps sessions until the network restarts.
   ** A session is a tuple of some proposed id, the corresponding client. **)
  Notation Sessions := (list (SessionId * Client)).

  (** Return the last known session id or the default **)
  Fixpoint last_session_id (s : Sessions) : SessionId :=
    match s with
    | [] => session_id0
    | [(id, c)] => id
    | _ :: xs => last_session_id xs
    end.

  (** Register some client and append the session to the end.  **)
  Definition new_session (s : Sessions) (c : Client) : (Sessions * SessionId) :=
    let id := next_session_id (last_session_id s) in
    ((List.app s [(id, c)]), id).

  (** Return true if we have a registered client session. **)
  Fixpoint valid_session (s : Sessions) (id : SessionId) : bool :=
    match s with
    | [] => false
    | (id', _) :: xs => if SessionIdDeq id id' then true else valid_session xs id
    end.

  (** Return the session client if some **)
  Fixpoint get_session_client (s : Sessions) (id : SessionId) : option Client :=
    match s with
    | [] => None
    | (id', c) :: xs => if SessionIdDeq id id' then Some c else get_session_client xs id
    end.

  (*! Cache results !*)
  (** The server uses a client caching mechanism to implement the linearizable semantics.
   ** After a request the leader stores the request in the cache and after the majority
   ** of server replicated the request, the log is applied to the sm. The result is
   ** stored in the cache and the client gets a response.
   ** As second mechanics the cache is used to find the correct client which gets the
   ** result back, since there is no other internal mechanics of recognizing which
   ** client has done which request. **)
  Record Cache :=
    Build_Cache
      {
        sid : SessionId;
        rid : RequestId;
        result : option RaftSM_result;
      }.

  (** A small helper which decides if the cache entry matches session and request id **)
  Definition correct_entry (c : Cache) (si : SessionId) (ri : RequestId) : bool :=
    if SessionIdDeq (sid c) si then if RequestIdDeq (rid c) ri then true else false else false.

  (** Returns the cache element if some is found. **)
  Fixpoint in_cache (c : list Cache) (sid : SessionId) (ri : RequestId) : option Cache :=
    match c with
    | [] => None
    | x :: xs =>
      if correct_entry x sid ri then Some x else in_cache xs sid ri
    end.

  (** Add a request to the cache. Duplicates should be checked beforehand.  **)
  Definition add2cache (c : list Cache) (sid : SessionId) (rid : RequestId) : list Cache :=
    let entry := Build_Cache sid rid None in
    entry :: c.

  (** The log entry is replicated across a majority of the network, so the sm result
   ** is remarked in the cache for later usage. **)
  Fixpoint apply2cache (c : list Cache) (si : SessionId)
             (ri : RequestId) (r : RaftSM_result) : list Cache :=
    match c with
    | [] => [] (* do nothing with an empty cache  *)
    | x :: xs =>
      if correct_entry x si ri then
        (* rebuild the cache entry and switch it with the old entry. *)
        let entry := Build_Cache si ri (Some r) in
        entry :: xs
      else x :: apply2cache xs si ri r
    end.

  (*! Leader election and authority !*)
  (** In raft nodes use an internal timer to recognize if the leader has failed.
   ** Since all nodes start up as followers the first round is to start the
   ** timers and recognize that nobody is a leader.
   ** The problem is that raft assumes that the timer is running internally and
   ** not as a message which is delayed so we need to model this mechanics slightly different
   ** as in the paper.
   **
   ** The processing shall be the following:
   ** A node sends a TimerMsg to itself with some delay which is general a random number between
   ** 150 and 300 ms to get different delays for different nodes, see election safety.
   ** Each TimerMsg has an natural number which serves as identification of the message.
   ** If a new heartbeat is recieved by the node it sends a new timer msg and stores internally the
   ** last timer id sends to itself.
   ** If a timer message is recieved the node checks if the timer is the last known timer.
   ** If it's the last timer id the node transitions to candidate state. Otherwise,
   ** the message is discarded.
   **
   ** The leader uses the timer to trigger new heartbeat messages to followers and
   ** to resend messages which it recieved no ack in a given time. **)

  (** The timer is only a dummy type for easier modelling. **)
  Inductive Timer := timer (id : nat).

  (** Say that a timer is nothing else than a number. **)
  Definition timer2nat (t : Timer) :=
    match t with
    | timer n => n
    end.
  Coercion timer2nat : Timer >-> nat.

  (** Increment the timer id. **)
  Definition next_timer (t : Timer) : Timer := timer (S t).

  (** Prove that timers have decidable equality. **)
  Lemma TimerDeq : Deq Timer.
  Proof.
    introv. destruct x, y; prove_dec.
    destruct (deq_nat id id0); prove_dec.
  Defined.

  (** the initial timer **)
  Definition timer0 := timer 0.

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
  Inductive Index := index (index : nat) (rep : Rep).

  Definition index2nat (i : Index) : nat :=
    match i with
    | index n _ => n
    end.

  Definition index2rep (i : Index) : Rep :=
    match i with
    | index _ r => r
    end.

  Definition suc_index (i : Index) : Index :=
    match i with
    | index n r => index (n + 1) r
    end.

  Definition prev_index (i : Index) : Index :=
  match i with
  | index 0 r => index 0 r
  | index n r => index (n - 1) r
  end.

  (*! NextIndex !*)
  (** The leader stores a list of nodes with a nat index which indicates
   ** the next log index which should be replicated on the server.
   ** If the followers log is lower start replicating at that log index.
   ** If the replication fails, decrement the index value and try again. **)
  Definition NextIndex := list Index.

  (** Helper for creating a new next index list. **)
  Fixpoint create_next_index (reps : list Rep) (n : nat) : NextIndex :=
    match reps with
    | [] => []
    | x :: xs => index n x  :: create_next_index xs n
    end.

  (** Creates a new next_index on leader change.
   ** The list is initialized to the leader last_log_index + 1. **)
  Definition next_index0 (slf : Rep) (n : nat) : NextIndex :=
    create_next_index (other_replicas slf) n.

  (** Increase the index of an element in the index list **)
  Fixpoint increase_next_index (l : NextIndex) (rep : Rep) : NextIndex :=
    match l with
    | [] => [] (* return list if last element reached *)
    | (index _ r) as x :: xs =>
      if (rep_deq r rep) then suc_index x :: xs else x :: increase_next_index xs rep
    end.

  Fixpoint increase_next_index_all (l : NextIndex) : NextIndex :=
    match l with
    | [] => []
    | x :: xs => suc_index x :: increase_next_index_all xs
    end.

  (** If the log of some node is not up to date decrease the next index on the leader.
   ** The leader now tries to resend that log index and hope it succeds or decreases again. **)
  Fixpoint decrease_next_index (l : NextIndex) (rep : Rep) : NextIndex :=
    match l with
    | [] => []
    | (index _ r) as x :: xs =>
      if rep_deq r rep then prev_index x :: xs else x :: decrease_next_index xs rep
    end.

  (** Return some index if the node is found **)
  Fixpoint get_next_index (l : NextIndex) (rep : Rep) : option nat :=
    match l with
    | [] => None (* the node is not found *)
    | (index i r) :: xs =>
      if (rep_deq r rep) then Some i else get_next_index xs rep
    end.

  (** Run over the next index list and find the number of matching nodes. **)
  Fixpoint num_replicated (ni : NextIndex) (i : nat) (num : nat) : nat :=
    match ni with
    | [] => num
    | (index i' _) :: xs =>
      if i =? i' then num_replicated xs i (num + 1)
      else num_replicated xs i num
    end.

  (** Check if the majority of nodes in the next index list has relpicated some log index. **)
  Definition majority_replicated (ni : NextIndex) (i : nat) : bool :=
    let limit := Nat.div2 num_replicas in (* 50% of replicas are the lower limit *)
    let replicated := num_replicated ni i 0 in
    (* true if the number of nodes which replicated the logs is above or equal to 50% of nodes *)
    if Nat.leb limit replicated then true else false.

  (*! MatchIndex !*)
  (** The match index is stored by the leader and holds for every node the
   ** log index for which the leader knows it's replicated by the follower.
   ** A successfull append entrie call to a follower increments the index in this list.
   **
   ** TODO: It is unclear what happens if results don't appear in order. **)
  Definition MatchIndex := list Index.

  (** These calls are just wrappers around the next index functions. **)
  Definition match_index0 (slf : Rep) : MatchIndex := next_index0 slf 0.
  Definition increase_match_index (l : MatchIndex) (rep : Rep) := increase_next_index l rep.
  Definition get_match_index (l : MatchIndex) (rep : Rep) := get_next_index l rep.

  (*! Node states !*)
  (** Within the raft protocol a server node can be in one of three internal state.
   ** Either it is a simple follower, or it can be a candidate running an election
   ** or it is the leader of the network.**)

  (*! Leader state !*)
  (** The leader state is reinitialized after every election and keeps track
   ** of the current state of the log replication. **)
  Record LeaderState :=
    Build_Leader_State
      {
        (* Volatile; reset after election -
         * The list of followers and the next possible index to send to the follower. *)
        next_index : NextIndex;
        (* Volatile; reset after election -
         * The list of servers and their index of the known highest log entry. *)
        match_index : MatchIndex;
      }.

  (** This definition is used to initialize the network, because
   ** their is no leader in the beginning. **)
  Definition leader_state0 : LeaderState := Build_Leader_State [] [].

  (** Create a new leader state for the node who won the election. **)
  Definition new_leader (next_index : nat) (slf : Rep) : LeaderState :=
    Build_Leader_State (next_index0 slf next_index) (match_index0 slf).

  Definition update_leader_state (ni : NextIndex) (mi : MatchIndex) : LeaderState :=
    Build_Leader_State ni mi.

  (*! Candidate State !*)
  (** A candidate runs the self-election and only needs to know
   ** the amount of nodes it recieved.. **)
  Record CandidateState :=
    Build_Candidate_State
      {
        votes : nat;
      }.

  (** initial a candidate has voted for itself **)
  Definition candidate_state0 : CandidateState := Build_Candidate_State 1.

  (** A new vote recieved **)
  Definition increment_votes (s : CandidateState) : CandidateState :=
    Build_Candidate_State (S (votes s)).

  (*! Node State !*)
  (** The node state indicates which role the server has. **)
  Inductive NodeState :=
  | leader (l : LeaderState)
  | follower
  | candidate (c : CandidateState).

  (*! Log !*)
  (** An entry in the log takes the term where it is added to the log and
   ** the content which gets added to the log.
   **
   ** Log matching property
   ** 1. If 2 entries in different logs have the same index and term they store the same command.
   ** 2. If 2 entries in different logs have same index and term, then the preceding
   **    entries are identical in the logs
   ** To keep the semantics clear, "log," denotes the node internal list of entries and "list Entry"
   ** denotes the new requested entries messaged through append entries calls. **)

  (** The entry type enables to store internal messages such as registering and other things
   ** into the log. **)
  Inductive EntryType :=
  (* The normal log content from a client request *)
  | content (c : Content)
  (* The current valid sessions are also replicated as log entry to save messages. *)
  | session (s : Sessions).


  (** An entry is a typeclass which gets parametrized over its content. **)
  Record Entry :=
    MkEntry
      {
        entry_term : Term;
        entry : EntryType;
      }.

  (** Create a new content entry from the type, entry term and content **)
  Definition new_entry (t : Term) (c : Content) :=
    MkEntry t (content c).

  Definition new_sessions_entry (t : Term) (s : Sessions) :=
    MkEntry t (session s).

  (** Define an abbreviation for the entry list. **)
  Notation Log := (list Entry).

  (** Search for the last entry and return its term. **)
  Fixpoint get_last_log_term (l : Log) : Term :=
    match l with
    | [] => term0
    | [{|entry_term := t|}] => t
    | _ :: xs => get_last_log_term xs
    end.

  (** Utility function which counts the elements in a log. **)
  Fixpoint get_last_log_index_util (l : Log) (n : nat) :=
    match l with
    | [] => n
    | _ :: xs => get_last_log_index_util xs (n + 1)
    end.

  (** The first index is 1 **)
  Definition get_last_log_index (l : Log) : nat := Datatypes.length l.
    (* get_last_log_index_util l 0. *)

  (** Return the nth entry iff found. **)
  Definition get_log_entry (l : Log) (i : nat) : option Entry := List.nth_error l i.
    (* match l with *)
    (* | [] => None *)
    (* | x :: xs => if i == 1 then Some x else get_log_entry xs (i - 1) *)
    (* end. *)

  (** Check if the log entry a position i has term t **)
  Fixpoint check_entry_term (l : Log) (i : nat) (t : Term) : bool :=
    match i, l with
    | _, [] => true (* the empty log accepts every entry *)
    | O, {|entry_term := t'|} :: xs => if TermDeq t t' then true else false
    | S n, _ :: xs => check_entry_term xs n t
    end.

  (** Check if at position i the entry has the entry term "t". **)
  (* Fixpoint check_last_log (l : Log) (i : nat) (t : Term) : bool := *)
  (*   match l, i with *)
  (*   | [], _ => true (* if the log is empty a new entry is accepted *) *)
  (*   | {|entry_term := t'|} :: xs, 0 => if (TermDeq t t') then true else false *)
  (*   | _ :: xs, _ => check_last_log xs (i - 1) t *)
  (*   end. *)

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
  Fixpoint append2log (l : Log) (e : list Entry) := Datatypes.app e l.
    (* match e with *)
    (* | [] => l *)
    (* | x :: xs => x :: append2log l xs *)
    (* end. *)

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
  | heartbeat (term : Term) (leader : Rep) (last_log_index : nat)
              (last_log_term : nat) (commit_index : nat)
  | replicate (term : Term) (leader : Rep) (last_log_index : nat) (last_log_term : Term)
              (commit_index : nat) (entry : list Entry) (id : SessionId * RequestId).

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
  | client_res (status : bool) (result : RaftSM_result)
  (** The follower responses to the leader if the issued requests succeds and
   ** the current term to update the leader. **)
  | append_entries_res (term : Term) (success : bool) (node : Rep) (id : SessionId * RequestId)
  (** A node response to a request vote wether it votes the calling candidate
   ** and it's current term to updat the requesting node. **)
  | request_vote_res (term : Term) (vote_granted : bool)
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
  | register_response_msg (result : Result)
  (* If the sessions changes and a new client enters the network
   * the leader broadcast the new sessions to all followers.
   * This is done to find duplicated request early and new leaders didn't forget clients. *)
  (* | broadcast_sessions_msg (sessions : Sessions) *)
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
  | append_entries_response_msg (result : Result)
  (* A follower issues a request vote message if it thinks the leader is faulty.
   * It transitions to candidate state and starts the leader election. *)
  | request_vote_msg (vote : RequestVote)
  (* The response vote messages is returned by processing some request vote message.
   * It indicates to the requesting client wether it recieves a vote from this
   * node or not. *)
  | request_vote_response_msg (result : Result)
  (* The forwarding is used if some client send a request to a none leader replica.
   * It encapsulates the message and sends it to the current leader. *)
  | forward_msg (msg : RaftMsg)
  (* A node sends timer messages to itself to recognize if the leader failed or the
   * system works properly. *)
  | timer_msg (timer : Timer)
  (* The debug messsage ist used to collect informations from the network. *)
  (* | debug_msg (debug : string) *)
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
    | register_msg _                => MSG_STATUS_EXTERNAL
    | register_response_msg _       => MSG_STATUS_PROTOCOL
    (* | broadcast_sessions_msg _    => MSG_STATUS_PROTOCOL *)
    | request_msg _                 => MSG_STATUS_EXTERNAL
    | response_msg _                => MSG_STATUS_PROTOCOL
    | append_entries_msg _          => MSG_STATUS_PROTOCOL
    | append_entries_response_msg _ => MSG_STATUS_PROTOCOL
    | request_vote_msg _            => MSG_STATUS_PROTOCOL
    | request_vote_response_msg _   => MSG_STATUS_PROTOCOL
    | forward_msg _                 => MSG_STATUS_PROTOCOL
    | timer_msg _                   => MSG_STATUS_INTERNAL
    (* | debug_msg _                 => MSG_STATUS_PROTOCOL *)
    | init_msg _                    => MSG_STATUS_EXTERNAL
    end.

  (** Bind the real message states to the abstract definition. **)
  Global Instance Raft_I_get_msg_status : MsgStatus := MkMsgStatus Raftmsg2status.

End RaftHeader.
