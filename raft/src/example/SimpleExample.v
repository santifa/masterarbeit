(*
  This file provides a simple Ping - Pong example for Velisarios.
  It aims to demonstrate the basic concepts on how to implement
  a distributed system.

  The system is fairly simple:
  Node 1 starts with some message and node 2 replies with
  a message containing the same content.
 *)

Require Export Process.

Section PingPong.

  (*+ declare the basics +*)
  (*! node definition !*)
  (* Define the type of nodes that are used within the protocol *)
  Inductive PPnode :=
  | PPn. (* don't distinguish between nodes or is some client (initially node) needed? *)


  (* Show that the node definition holds for the decidable equality (Deq) *)
  Lemma Deq_PPnode : Deq PPnode.
  Proof.
    introv. destruct x, y. prove_dec.
  Qed.

  (* Instantiate the abstract type node with the protocol node definition *)
  Instance PP_I_Node: Node := MkNode PPnode Deq_PPnode.

  (*! message definition !*)
  (* Define the type of messages which can be send between nodes and internally  *)
  Inductive PPmsg :=
  | PPping (* Either send a Ping if this is the first round or reply to a pong *)
  | PPong. (* Reply to some incoming ping message *)

  (* Instantiate the abstract message type with the protocol message definition *)
  Instance PP_I_Msg : Msg := MkMsg PPmsg.

  (* Declare which messages are internal, external or protocol specific *)
  Definition PP_msg_status (m : PPmsg) : msg_status :=
  match m with
  | PPping => MSG_STATUS_EXTERNAL (* a ping message comes from another node *)
  | PPpong => MSG_STATUS_INTERNAL (* a pong message is a reply to some other node *)
  end.

  (* Instantiate the abstract message status with the function describing it *)
  Instance PP_I_MsgStatus : MsgStatus := MkMsgStatus PP_msg_status.

  (*! state definition !*)
  (* Declare the states for the nodes.
   * Different node types may have different states. *)
  Inductive PPstate := PPst.

  (* Define the state update function as simple echo. *)
  Definition echo : MSUpdate PPstate :=
    (* Given some msg and the current state, the next state is the same but
     * the input message is directed back to all other nodes in the network
     * via directed messages. *)
    fun state input => (state, [MkDMsg input [PPn] 0]).

  (* declare the internal state machine ?? *)
  Arguments MkSM      [S] [I] [O] _ _ _.
  Arguments sm_halted [S] [I] [O] _.
  Arguments sm_state  [S] [I] [O] _.
  Arguments sm_update [S] [I] [O] _ _ _.

  (* define the internal state machine for a ping pong node *)
  Definition PPnodeSM : MStateMachine PPstate :=
    mkSSM echo PPst.

  (* match node types with their states *)
  Definition PPState (n : name) :=
    match n with
    | PPn => PPstate
    end.

  (* match the state machine for the node type and return the next state *)
  Definition PPusys : MUSystem PPState :=
    fun name =>
      match name return StateMachine (PPState name) msg DirectedMsgs with
      | PPn => PPnodeSM
      end.

  (* build the real process with some initial state machine *)
  Definition PPsys  : System :=
    fun name =>
      match name with
      | PPn => build_sprocess echo PPst
      end.

  (*+ declare the authentication +*)
  (* create new key *)
  Instance PP_I_Key : Key := MkKey unit unit.

  (* define what type is data *)
  Instance PP_I_Data : Data := MkData PPmsg.

  (* create a new authentication token *)
  Instance PP_I_AuthTok : AuthTok := MkAuthTok unit Deq_unit.

  Instance PP_I_AuthFun : AuthFun :=
    MkAuthFun
      (fun _ _ => [tt])
      (fun _ _ _ _ => true).

  Definition PPdata_auth : name -> PPmsg -> option name :=
    fun n m =>
      match m with
      | PPping => Some PPn
      | PPong  => Some PPn
      end.

  (* Instantiate the abstract DataAuth type with the protocol implementation *)
  Instance PP_I_DataAuth : DataAuth := MkDataAuth PPdata_auth.

  (* Instantiate the ContainedAuthData which creates mesages with
   * multiple authenticated data? *)
  Instance PP_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData
      (fun m => [MkAuthData m [tt]]).

  (* add some hints to the proofer *)
  Hint Rewrite @map_option_option_map : option.
  Hint Rewrite @option_map_option_map : option.
  Hint Resolve if_not_first_if_first : eo.

  (*+ proofs about the event ordering +*)
  (* currently left out*)

End PingPong.
