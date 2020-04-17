(*! This file is part of the raft implementation in velisarios !*)

(*! Abstract !*)
(** This file implements some tests and utlities used for checking
 ** the logic of the implementation. Defintions with an export flag
 ** in the comments are used in the OCaml code to test the protocol.
 ** This utilizes a dummy implementation of a possible raft state machine
 ** which only uses natural numbers and addition. **)

Require Export Simulator.
Require Export Protocols.Raft.Raft.
Require Export Ascii String.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section RaftTestInstance.



End RaftTestInstance.
