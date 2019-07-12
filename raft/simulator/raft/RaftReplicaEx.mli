
type __ = Obj.t

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val append : char list -> char list -> char list

type 't deceq = bool

type 't deq = 't -> 't -> 't deceq

type name = __

type msg = __

type directedMsg = { dmMsg : msg; dmDst : name list; dmDelay : int }

type directedMsgs = directedMsg list

type nat_n = int

type ('a, 'b) bijective =
  'b -> 'a
  (* singleton inductive, whose constructor was Build_bijective *)

type ('s, 'i, 'o) update = 's -> 'i -> 's option * 'o

type ('s, 'i, 'o) stateMachine = { sm_halted : bool;
                                   sm_update : ('s, 'i, 'o) update;
                                   sm_state : 's }

val sm_halted : ('a1, 'a2, 'a3) stateMachine -> bool

val sm_update : ('a1, 'a2, 'a3) stateMachine -> ('a1, 'a2, 'a3) update

val sm_state : ('a1, 'a2, 'a3) stateMachine -> 'a1

val mkSM : ('a3, 'a1, 'a2) update -> 'a3 -> ('a3, 'a1, 'a2) stateMachine

type ('s, 'i, 'o) sUpdate = 's -> 'i -> 's * 'o

type 's mSUpdate = ('s, msg, directedMsgs) sUpdate

val s2Update : ('a1, 'a2, 'a3) sUpdate -> ('a1, 'a2, 'a3) update

val mkSSM : ('a3, 'a1, 'a2) sUpdate -> 'a3 -> ('a3, 'a1, 'a2) stateMachine

type 's mStateMachine = ('s, msg, directedMsgs) stateMachine

val updState :
  ('a1, 'a2, 'a3) stateMachine -> 'a1 -> ('a1, 'a2, 'a3) stateMachine

val halts : ('a1, 'a2, 'a3) stateMachine -> ('a1, 'a2, 'a3) stateMachine

val force_sm :
  ('a1, 'a2, 'a3) stateMachine -> (('a1, 'a2, 'a3) stateMachine -> 'a4) -> 'a4

val lrun_sm :
  ('a1, 'a2, 'a3 list) stateMachine -> 'a2 -> ('a1, 'a2, 'a3 list)
  stateMachine * 'a3 list

type raftcontext = { clients : int; client_deq : __ deq;
                     clients2nat : (__ -> nat_n);
                     clients_bji : (__, nat_n) bijective; f : int;
                     rep_deq : __ deq; reps2nat : (__ -> nat_n);
                     reps_bij : (__, nat_n) bijective }

type c = __

type raftmsg =
| Heartbeat
| Reply of int * c
| Command of int

type raftleader_state =
  int
  (* singleton inductive, whose constructor was Term *)

val leader_update : raftcontext -> raftleader_state mSUpdate

val raftleaderSM : raftcontext -> raftleader_state mStateMachine

val str_concat : char list list -> char list

val raft_state2string : raftleader_state -> char list

val local_replica : raftcontext -> raftleader_state mStateMachine
