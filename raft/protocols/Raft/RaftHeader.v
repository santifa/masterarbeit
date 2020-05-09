(*! This file is part of the raft implementation with velisarios. !*)

(*! Abstract !*)
(** The header file contains the basic definitions and terms
 ** to speak about raft and its mechanics. The main parts are:
 ** - Progress
 ** - Leader and Candidate states
 ** - All about logs
 ** - Sessions and Caching (linearizable semantics)
 ** - Messages
 **
 ** Velisarios models protocols as agent (node) based message passing
 ** system where the nodes communicate via exchanging messages over some
 ** channel. Raft is designed with remote procedure calls in mind and for
 ** flexible and hackable languages. So, some parts may differ from the
 ** original postulation.
 **
 ** Conventions:
 ** - Definitions, fixpoints and inductive types are snacke_case
 ** - Types, proofs are CamelCase
 ** - No rule without some exceptions **)
Require Export RaftContext.
Require Export String.

Section RaftHeader.

  Definition option2bool {A : Type} (a : option A) : bool :=
    match a with
    | None => false
    | Some _ => true
    end.

  Definition flat_option {A : Type} (a : option (option A)) : option A :=
    match a with
    | None => None
    | Some a => a
    end.

  (** Redeclare the abstract definitions. **)
  Context { raft_context : RaftContext }.

  (*! Progress !*)
  (** Raft divides the time into chunks called terms. Terms are monotonically
   ** increasing natural numbers. The term increases with the start of a leader
   ** election and is propagated to all nodes in the systems. The idea is to
   ** find and update outdated nodes and data on the nodes. **)
  Inductive Term := term (n : nat).

  (** A term is referenced by some number which is increased monotonically. **)
  Definition term2nat (t : Term) : nat :=
    match t with
    | term n => n
    end.
  (* define that the term type and nat type are interchangable *)
  Coercion term2nat : Term >-> nat.

  (** The successor of some term is the term with the next natural number. **)
  Definition next_term (t : Term) : Term :=  term (S t).

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
    if t1 <? t2 then t2 else t1.

  (** The timer is used for measuring leader fails and heartbeats.
   ** The process is as follows:
   ** A node sends a timer message every time it recieves a messages from
   ** the leader and stores the id in its process state.
   ** It assumes the leader has failed if it gets a timer message with the stored id.
   ** The leader sends heartbeats if it gets a valid timer message. **)

  (** The second mechanic to make progress is to detect failed leaders and
   ** resend messages which are failed to deliver. Raft uses internal
   ** timers with an individual timeout to do so. This is modeled as
   ** a separat timer message. The timer has some id and the message some delay
   ** and if a node recieves a timer message with the correct id it assumes
   ** the leader has failed or the message wasn't recieved. **)
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

  (*! State !*)
  (** The index is a basic type for the leader state. It recognizes some index id
   ** along with some node. This is used by the leader to recognize the replication state
   ** of the other nodes. **)
  Inductive Index := index (index : nat) (rep : Rep).

  Definition index2nat (i : Index) : nat :=
    match i with
    | index n _ => n
    end.
  Coercion index2nat : Index >-> nat.

  Definition index2rep (i : Index) : Rep :=
    match i with
    | index _ r => r
    end.
  Coercion index2rep : Index >-> Rep.

  Definition succ_index (i : Index) : Index :=
    match i with
    | index n r => index (n + 1) r
    end.

  Definition prev_index (i : Index) : Index :=
  match i with
  | index 0 r => index 0 r
  | index n r => index (n - 1) r
  end.

  (*! NextIndex !*)
  (** The next index list is managed by the leader and stores the
   ** next log index which the leader can send to some node.
   ** It is decremented if the node is behind the leaders log and
   ** incremented if the node refills its log. **)
  Definition NextIndex := list Index.

  (**  Create a new next index list for a leader. **)
  Fixpoint next_index0 (slf : Rep) (n : nat) : NextIndex :=
    map (fun x => index n x) (other_replicas slf).

  (** Increase the index of an element in the index list **)
  Fixpoint increase_next_index (l : NextIndex) (rep : Rep) : NextIndex :=
    map (fun x => if rep_deq (index2rep x) rep then succ_index x else x) l.

  (** If the log of some node is not up to date decrease the next index on the leader.
   ** The leader now tries to resend that log index and hope it succeds or decreases again. **)
  Fixpoint decrease_next_index (l : NextIndex) (rep : Rep) : NextIndex :=
    map (fun x => if rep_deq (index2rep x) rep then prev_index x else x) l.

  (** Return some index if the node is found **)
  Fixpoint get_next_index (l : NextIndex) (rep : Rep) : option nat :=
    option_map index2nat (find (fun x => if rep_deq (index2rep x) rep then true else false) l).

  (*! MatchIndex !*)
  (** The match index list stores for every node the last log index which is known
   ** to be replicated on the node. A successfull append entry message increases this
   ** index and if the majority has replicated the entry the leader can commit the entry. **)
  Definition MatchIndex := list Index.

  (** These calls are just wrappers around the next index functions. **)
  Definition match_index0 (slf : Rep) : MatchIndex := next_index0 slf 0.
  Definition increase_match_index (l : MatchIndex) (rep : Rep) := increase_next_index l rep.
  Definition get_match_index (l : MatchIndex) (rep : Rep) :=
    match get_next_index l rep with
    | None => 0 (* return zero if no matching node is found *)
    | Some i => i (* return the match index found *)
    end.

  (** Run over the next index list and find the number of matching nodes. **)
  Fixpoint num_replicated (mi : MatchIndex) (i : nat) (num : nat) : nat :=
    match mi with
    | [] => num
    | (index i' _) :: xs =>
      if i =? i' then num_replicated xs i (num + 1)
      else num_replicated xs i num
    end.

  (** Check if the majority of nodes in the match index list has relpicated some log index. **)
  Definition majority_replicated (mi : MatchIndex) (i : nat) : bool :=
    let limit := Nat.div2 num_replicas in (* 50% of replicas are the lower limit *)
    let replicated := num_replicated mi i 0 in
    (* true if the number of nodes which replicated the logs is above or equal to 50% of nodes *)
    if Nat.leb limit replicated then true else false.


  (*! Node states !*)
  (** Within the raft protocol a server node can be in one of three internal state.
   ** Either it is a simple follower, or it can be a candidate running an election
   ** or it is the leader of the network.**)

  (*! Leader state !*)
  (** The leader state is reinitialized after every election and keeps track
   ** of the current state of the log replication. **)
  Record LeaderState :=
    MkLeaderState
      {
        (* Volatile; reset after election -
         * The list of followers and the next possible index to send to the follower. *)
        next_index : NextIndex;
        (* Volatile; reset after election -
         * The list of servers and their index of the highest replicated log entry. *)
        match_index : MatchIndex;
      }.

  (** Create a new leader state for the node who won the election.
   ** Initialize match_index to zero and next_index to the leaders last
   ** log entry. **)
  Definition new_leader (next_index : nat) (slf : Rep) : LeaderState :=
    MkLeaderState (next_index0 slf next_index) (match_index0 slf).

  Definition update_leader_state (ni : NextIndex) (mi : MatchIndex) : LeaderState :=
    MkLeaderState ni mi.

  (*! Candidate State !*)
  (** The candidate for the leader election. It only needs to know
   ** the amount of votes recieved by all nodes. **)
  Record CandidateState :=
    MkCandidateState
      {
        votes : nat;
      }.

  (** initial a candidate has voted for itself **)
  Definition candidate_state0 : CandidateState := MkCandidateState 1.

  (** A new vote recieved **)
  (* Definition increment_votes (s : CandidateState) : CandidateState := *)
  (*   MkCandidateState (S (votes s)). *)

  (*! Node State !*)
  (** The node state indicates which role the server has. **)
  Inductive NodeState :=
  | follower
  | candidate (c : CandidateState)
  | leader (l : LeaderState).

  (** Add a new vote **)
  Definition increment_votes (s : NodeState) : NodeState :=
    match s with
    | candidate c => candidate (MkCandidateState (S (votes c)))
    | _ => s
    end.

  (** Get the amount of recieved votes **)
  Definition get_votes (s : NodeState) : nat :=
    match s with
    | candidate c => (votes c)
    | _ => 0
    end.

  (** Determine if some node has the majority of votes already. **)
  Definition majority_votes (s : NodeState) : bool :=
    let votes := get_votes s in (* get all recieved votes *)
    let half := Nat.div2 num_replicas in (* minimum of >50% needed *)
    if (Nat.ltb half votes) then true else false.

  (** check if the node is leader **)
  Definition is_leader (s : NodeState) : bool :=
    match s with
    | leader _ => true
    | _ => false
    end.

  Definition gni (s : NodeState) : NextIndex :=
    match s with
    | leader l => (next_index l)
    | _ => []
    end.

  Definition gmi (s : NodeState) : MatchIndex :=
    match s with
    | leader l => (match_index l)
    | _ => []
    end.

  (*! Client and linearizable semantics !*)
  (** The client needs to register at the network which creates a session id for
   ** the client and expects request ids for every client request along with the
   ** session id. Both are used to cache client requests and detect double requests.
   ** This is the at-least-once semantics proposed by the raft protocol. Sessions
   ** Cached request are stored in the log along with the regular content.
   ** NOTE: Sessions and Caches are kept until the whole network restarts. **)

  (** Upon registering the leader creates the session id for the client. **)
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

  (** the initial session id is used by the leaders, so start with the next one for clients. **)
  Definition session_id0 := session_id 0.

  (** A client send requests with some request id which increases monotonically. **)
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

  (** A session is a tuple of some proposed id, the corresponding client. **)
  Definition Sessions := list (SessionId * Client * RequestId).

  (** Two sessions are equal if the have the same session id. **)
  Definition ses_deq (s : (SessionId * Client * RequestId)) (id : SessionId) : bool :=
    let (s', _) := fst s in if SessionIdDeq s' id then true else false.

  (** Return the last known session id or the first usable for a client. **)
  Fixpoint last_session_id (s : Sessions) : SessionId :=
    last (map (fun x => fst (fst x)) s) (next_session_id (session_id0)).

  (** Register some client and append the session to the end.  **)
  Definition new_session (s : Sessions) (c : Client) : (Sessions * SessionId) :=
    let id := next_session_id (last_session_id s) in
    ((List.app s [(id, c, request_id0)]), id).

  (** Return true if we have a registered client session. **)
  Definition valid_session (s : Sessions) (id : SessionId) : bool :=
    existsb (fun x => ses_deq x id) s.

  (** Return the session client if some **)
  Definition get_session_client (s : Sessions) (id : SessionId) : option Client :=
    option_map (compose snd fst) (find (fun x => if ses_deq x id then true else false) s).

  (** Update the sessions request id by replacing the matching session **)
  Fixpoint update_request_id (s : Sessions) (id : SessionId) (ri : RequestId) : Sessions :=
    match s with
    | [] => []
    | x :: ss => if ses_deq x id then
                 (fst (fst x), (snd (fst x)), ri) :: ss
               else update_request_id ss id ri
    end.

  (** Check if the request id is greater than the last request id and the session id is valid **)
  Definition valid_request (s : Sessions) (id : SessionId) (ri : RequestId) : bool :=
    existsb (fun x => andb (ses_deq x id) ((snd x) <? ri)) s.

  (*! Cache !*)
  (** Raft uses caching to prevent clients and the network from executing the
   ** same request twice and enter an illegal state. The leader creates a cache
   ** entry without result for every request. If the request is executed by the
   ** network the cache is updated. Every node has its own caching within the log.
   ** It uses the replication requests and adds new replications requests to its
   ** cache and the result if the entry is flagged as commited. To enable nodes
   ** to add results to the cache if they applied some log entry the index of
   ** the entry is added to the cache entry. The index shall be unique as in the log. **)
  Record CacheEntry :=
    MkCacheEntry
      {
        sid : SessionId;
        rid : RequestId;
        ind : nat;
        result : option RaftSM_result;
      }.

  Definition Cache := list CacheEntry.

  (** Add a request to the cache. Duplicates should be checked beforehand.  **)
  Definition add2cache (c : Cache) (sid : SessionId) (rid : RequestId) (i : nat) : Cache :=
    (MkCacheEntry sid rid i None) :: c.

  (** A small helper which decides if the cache entry matches session and request id **)
  Definition correct_entry (c : CacheEntry) (si : SessionId) (ri : RequestId) : bool :=
    if SessionIdDeq (sid c) si then if RequestIdDeq (rid c) ri then true else false else false.

  (** Returns the cache element if some is found. **)
  Definition get_cached (c : Cache) (sid : SessionId) (ri : RequestId) : option CacheEntry :=
    find (fun x => correct_entry x sid ri) c.

  Definition add_result2cache_entry (c : CacheEntry) (r : RaftSM_result) : CacheEntry :=
    MkCacheEntry (sid c) (rid c) (ind c) (Some r).

  (** Add a result to a cache entry if the result finally processed by the sm.
   ** The matching is done by using the log index as reminder. **)
  Definition add_result2cache (c : Cache) (i : nat) (r: RaftSM_result) : Cache :=
    map (fun x => if Nat.eqb (ind x) i then add_result2cache_entry x r else x) c.

  (** Add a result to the cache if there is some result. **)
  Definition result2cache (c : Cache) (i : nat) (r : option RaftSM_result) : Cache :=
    match r with
    | None => c
    | Some r' => add_result2cache c i r'
    end.

  (** Get the cached result if some. **)
  Definition get_cached_result (c : Cache) (sid : SessionId) (ri : RequestId) :
    option RaftSM_result :=
    flat_option (option_map (fun x => (result x)) (get_cached c sid ri)).

  (*! Log !*)
  (** The log is the most important part because it stores all contents which
   ** are executed on the state machine and the sessions and cache.
   ** Raft uses the log matching proptery to reason about logs.
   ** - If 2 entries in different logs have the same index and term they're equal
   ** - If 2 entries in different logs habe the same index and term, then the preceding
   **   entries are also identical
   ** NOTE: "log" is used for the nodes, "Entry" for messages. For simplicity a message
   ** can only send one entry. **)

  (** The types of entries for the log. **)
  Inductive EntryType :=
  (* The normal log content from a client request *)
  | content (c : Content)
  (* The current valid sessions are also replicated as log entry to save messages. *)
  | session (s : Sessions)
  (* mark the start of a new term. *)
  | new_term.

  (** An entry is a typeclass which gets parametrized over its content. **)
  Record Entry :=
    MkEntry
      {
        entry_term : Term;
        entry : EntryType;
      }.

  (** Create a new content entry from the type, entry term and content **)
  Definition new_content_entry (t : Term) (c : Content) :=
    MkEntry t (content c).

  Definition new_sessions_entry (t : Term) (s : Sessions) :=
    MkEntry t (session s).

  Definition new_term_entry (t : Term) :=
    MkEntry t new_term.

  (** Define an abbreviation for the entry list.  **)
  Definition Log := list Entry.

  (** Search for the last entry and return its term
   ** or if the log is empty the first term. **)
  Definition last_log_term (l : Log) : Term :=
    entry_term (last l (new_term_entry term0)).

  (** Start the log index at one. **)
  Definition last_log_index (l : Log) : nat := Datatypes.length l.

  (** Return the nth entry iff found. **)
  Definition get_log_entry (l : Log) (i : nat) : option Entry := List.nth_error l i.

  Definition get_last_entry (l : Log) (t : Term) : Entry :=
    last l (new_term_entry t).

  (** Check if the log entry a position i has term t **)
  Fixpoint check_entry_term (l : Log) (i : nat) (t : Term) : bool :=
    match i, l with
    | _, [] => true (* the empty log accepts every entry *)
    | O, {|entry_term := t'|} :: xs => if TermDeq t t' then true else false
    | S n, _ :: xs => check_entry_term xs n t
    end.

  (** Remove the last elements from a log starting at e. **)
  Definition take_from_log (l : Log) (e : nat) :=
    rev (List.skipn e (rev l)).

  (** Append new entries to a log  **)
  Fixpoint add2log (l : Log) (e : list Entry) := Datatypes.app l e.

  Definition is_session_entry (e : Entry) : bool :=
    match (entry e) with
    | session _ => true
    | _ => false
    end.

  Definition is_content_entry (e : Entry) : bool :=
    match (entry e) with
    | content _ => true
    | _ => false
    end.

  (** Find and return the last session entry or the empty list. **)
  Definition last_session (l : Log) : Sessions :=
    let entry := option_map entry (List.find is_session_entry (rev l)) in
    match entry with
    | Some (session s) => s
    | _ => []
    end.

  (*! Messages !*)
  (** Velisarios uses messages to handle communication between nodes.
   ** For every message type there is a request and a response part
   ** such that the handler function handles both cases. **)

  (** The client issues a new session id by the network. **)
  Inductive RegisterClient :=
  | request_register_client (c : Client)
  (** Return if the client is registered and its new session id and the leader hint. **)
  | response_register_client (status: bool) (session_id : SessionId) (leader : option Rep).

  (** To alternate the state a client sends an sessioned message to the network. **)
  Inductive ClientRequest :=
  | client_request (client : Client) (session_id : SessionId)
                   (request_id : RequestId) (command : Content)
   (** The leader sends the client the response if the request was executed. **)
  | client_response (status : bool) (result : option RaftSM_result) (leader : option Rep).

  (** The append entries messages are the core of raft. It is used as heartbeat maintaining
   ** leadership in idle times and for the replication itself. The heartbeat is a replication
   ** message with an empty entry list. To get the caching and
   ** recognition right the session and request ids are send along,
   ** despite the raft suggestions. **)
  Inductive AppendEntries :=
  | replicate (term : Term) (leader : Rep) (last_log_index : nat) (last_log_term : Term)
              (commit_index : nat) (entry : list Entry) (id : SessionId * RequestId)
  (** The follower responses to the leader if the issued requests succeds **)
  | response (term : Term) (success : bool) (node : Rep) (id : SessionId * RequestId).

  (** A vote is issued during the leader election. The candidate provides
   ** itself, the current term and the index of the last stored log and
   ** it's term number. **)
  Inductive RequestVote :=
  | request_vote (term : Term) (candidate : Rep) (last_log_index : nat) (last_log_term : Term)
  (** A node response to a request vote wether it votes the calling candidate
   ** and it's current term to update the requesting node. **)
  | response_vote (term : Term) (vote_granted : bool).

  (** The message types gets enclosed in the individual messages which are used
   ** by velisarios to deliver messages in the network.
   ** NOTE: authentication of messages is not done. **)
  Inductive RaftMsg :=
  (* Before communicating with the network a client registers itself at the network. *)
  | register_msg (register : RegisterClient)
  (* Respond to a register message. *)
  | register_response_msg (result : RegisterClient)
  (* A client request is the command issued by the client to modify the overall state.
   * As a parameter the client sends its own id, some sequence number to eliminate duplacte
   * requests and the command to execute. *)
  | request_msg (request : ClientRequest)
  (* The response is sent by the leader after it applies the issued command to it's
   * own state machine and the first round of AppendEntries send through the network.
   * The result is taken from the result of the leader state machine. *)
  | response_msg (result : ClientRequest)
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
  | append_entries_response_msg (result : AppendEntries)
  (* A follower issues a request vote message if it thinks the leader is faulty.
   * It transitions to candidate state and starts the leader election. *)
  | request_vote_msg (vote : RequestVote)
  (* The response vote messages is returned by processing some request vote message.
   * It indicates to the requesting client wether it recieves a vote from this
   * node or not. *)
  | request_vote_response_msg (result : RequestVote)
  (* A node sends timer messages to itself to recognize if the leader failed or the
   * system works properly. *)
  | timer_msg (timer : Timer)
  (* This special messages is used by the leader to detect failed messages and resend
   * them to the node indefinitely. *)
  | msg_timer_msg (timer : (Timer * Rep))
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
    | request_msg _                 => MSG_STATUS_EXTERNAL
    | response_msg _                => MSG_STATUS_PROTOCOL
    | append_entries_msg _          => MSG_STATUS_PROTOCOL
    | append_entries_response_msg _ => MSG_STATUS_PROTOCOL
    | request_vote_msg _            => MSG_STATUS_PROTOCOL
    | request_vote_response_msg _   => MSG_STATUS_PROTOCOL
    | timer_msg _                   => MSG_STATUS_INTERNAL
    | msg_timer_msg _               => MSG_STATUS_INTERNAL
    | init_msg _                    => MSG_STATUS_EXTERNAL
    end.

  (** Bind the real message states to the abstract definition. **)
  Global Instance Raft_I_get_msg_status : MsgStatus := MkMsgStatus Raftmsg2status.

  (*! Message creation !*)
  (** Create a new timer message **)
  Definition mk_timer_msg (t : Timer) (n : Rep) (timeout : nat) : DirectedMsg :=
    MkDMsg (timer_msg t) [replica n] timeout.

  (** The leader has a fixed timeot of 50ms to trigger the next heartbeat.
   ** This is done to maintain leadership since the heartbeat also need a timer. **)
  Definition mk_leader_timer_msg (t : Timer) (n : Rep) : DirectedMsg :=
    mk_timer_msg t n 50.

  (** NOTE: Use a timer msg to track which msg should be resend. **)
  Definition mk_msg_timer_msg (t : Timer) (n : Rep) : DirectedMsg :=
    mk_timer_msg t n 100.

  (** Create a new registration regquest message -- Client **)
  Definition mk_register_msg (c : Client) (n : Rep) : DirectedMsg :=
    MkDMsg (register_msg (request_register_client c)) [replica n] 0.

  (** Create a new registration reponse to some client **)
  Definition mk_register_response_msg (c : Client) (s : SessionId)
             (g : bool) (l : option Rep) : DirectedMsg :=
    MkDMsg (register_response_msg (response_register_client g s l)) [client c] 0.

  (** Create the initial message to bootstrap the system. -- Bootstrap **)
  Definition mk_init_msg (timeout : nat) : DirectedMsg :=
    MkDMsg (init_msg timeout) (map replica reps) 0.

  (** Create a new vote request. **)
  Definition mk_request_vote_msg (n : Rep) : (Term -> nat -> Term -> nat -> DirectedMsg) :=
    fun t lli llt ci =>
      let vote := request_vote t n lli llt in
      MkDMsg (request_vote_msg vote) (other_names n) 0.

  (** Create a new reponse to a vote request. **)
  Definition mk_request_vote_response_msg (t : Term) (g : bool) (n : Rep) : DirectedMsg :=
    MkDMsg (request_vote_response_msg (response_vote t g)) [replica n] 0.

    (** Create a new heartbeat message. **)
  Definition mk_heartbeat_msg (n : Rep) : (Term -> nat -> Term -> nat -> DirectedMsg) :=
    fun t lli llt ci =>
      let beat := replicate t n lli llt ci [] (session_id0, request_id0) in
      MkDMsg (append_entries_msg beat) (other_names n) 0.

  (** Create a replication message to all other nodes. **)
  Definition mk_append_entries_msg (n : Rep) (e : Entry) (id : SessionId * RequestId) :
    (Term -> nat -> Term -> nat -> DirectedMsg) :=
    fun t lli llt ci =>
      let msg := replicate t n lli llt ci [e] id in
      MkDMsg (append_entries_msg msg) (other_names n) 0.

  (** Create a reponse message to an append entries message. **)
  Definition mk_append_entries_response_msg (t : Term) (g : bool) (id : SessionId * RequestId)
             (n : Rep) (l : Rep) : DirectedMsg :=
    let r := response t g n id in
    MkDMsg (append_entries_response_msg r) [replica l] 0.

  (** Create a request message for a client. -- Client **)
  Definition mk_client_request (c : Client) (si : SessionId) (ri : RequestId)
             (e : Content) (n : Rep) : DirectedMsg :=
    let r := client_request c si ri e in
    MkDMsg (request_msg r) [replica n] 0.

  (** Create a reponse for some client request. **)
  Definition mk_client_response (g : bool) (r : option RaftSM_result)
             (l : option Rep) (c : option Client) : DirectedMsgs :=
    match c with
    | None => []
    | Some c => [MkDMsg (response_msg (client_response g r l)) [client c] 0]
    end.

End RaftHeader.
