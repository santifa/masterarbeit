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

  (* Define the type of nodes that are used within the protocol *)
  Inductive PPnode :=
  | PPn. (* don't distinguish between nodes or is some client (initially node) needed? *)

  (* Define the type of messages which can be send between nodes and internally  *)
  Inductive PPmsg :=
  | PPping (* Either send a Ping if this is the first round or reply to a pong *)
  | PPong. (* Reply to some incoming ping message *)

  (* Show that the node definition holds for the decidable equality (Deq) *)
  Lemma Deq_PPnode : Deq PPnode.
  Proof.
    introv. destruct x, y. prove_dec.
    Qed.

  (* Instantiate the abstract type node with the protocol node definition *)
  Instance PP_I_Node: Node := MkNode PPnode Deq_PPnode.

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

  (* Declare the internal states for the nodes.
   * Different node types may have different states. *)
  Inductive PPstate := PPst.

  (* Define the state update function as simple echo. *)
  Definition echo : MSUpdate PPstate :=
    (* Given some msg and the current state, the next state is the same but
     * the input message is directed back to all other nodes in the network. *)
    fun state input => (state, [MkDMsg input [PPn] 0]).

End PingPong.
