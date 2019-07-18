(*
 * This is the master file for the raft implementation only.
 *)

(* import velisarios *)
Require Export Protocols.Raft.RaftHeader.
Require Export String.
Require Export Peano.
Require Export List.


Section Raft.

  Local Open Scope eo.
  Local Open Scope proc.

  Context { raft_context : RaftContext }.

  (* ++++++++++++++ Primary state ++++++++++++++ *)
  Record RaftPrimaryState :=
    Build_Primary_State
      {
        (* store the current node term number *)
        term_number_prim : Term;
      }.

  (* define the initial state for the primary *)
  Definition initial_primary_state : RaftPrimaryState :=
    Build_Primary_State
      initial_term.

  (* ++++++++++++++ State ++++++++++++++
   * This record describe the general state of all nodes
   * in the system. *)
  Record RaftState :=
    Build_State
      {
        (* store the current node term number *)
        term_number : Term;
        (* the local state machine *)
        sm_state : RaftSM_state;
        (* the timeout in secs after which a new election is triggered *)
        timeout : nat;
        (* indicate if this node is the leader *)
        leader : bool;
      }.

  (* define the first state of some node *)
  Definition initial_state (r : Rep) : RaftState :=
    Build_State
      initial_term
      RaftSM_initial_state
      5
      false.

  (* increment the term number *)
  Definition increment_term_num (s : RaftState) : RaftState :=
    Build_State
      (next_term (term_number s))
      (sm_state s)
      (timeout s)
      (leader s).

  (* ++++++++++++++ Update functions ++++++++++++++ *)
  (* handle input - currently by doing nothing *)
  Definition Rafthandle_input (slf : Rep) : Update RaftState nat DirectedMsgs :=
    fun state i => (Some state, []).

  (* handle heartbeat by reseting the timer *)
  Definition Rafthandle_heartbeat (slf : Rep) : Update RaftState unit DirectedMsgs :=
    fun state _ => (Some state, []).

  (* Define the update function which is executed within the state machines *)
  Definition Raftreplica_update (slf : Rep) : MUpdate RaftState :=
    fun state m =>
      match m with
      | Input n => Rafthandle_input slf state n
      | Heartbeat => Rafthandle_heartbeat slf state tt
      end.


  (* ++++++++++++++ System ++++++++++++++
   * Define the actual state machines and hook them into velisarios. *)
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
