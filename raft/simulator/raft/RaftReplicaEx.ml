
type __ = Obj.t

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c0::s1' -> c0::(append s1' s2)

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

(** val sm_halted : ('a1, 'a2, 'a3) stateMachine -> bool **)

let sm_halted x = x.sm_halted

(** val sm_update : ('a1, 'a2, 'a3) stateMachine -> ('a1, 'a2, 'a3) update **)

let sm_update x = x.sm_update

(** val sm_state : ('a1, 'a2, 'a3) stateMachine -> 'a1 **)

let sm_state x = x.sm_state

(** val mkSM :
    ('a3, 'a1, 'a2) update -> 'a3 -> ('a3, 'a1, 'a2) stateMachine **)

let mkSM upd s =
  { sm_halted = false; sm_update = upd; sm_state = s }

type ('s, 'i, 'o) sUpdate = 's -> 'i -> 's * 'o

type 's mSUpdate = ('s, msg, directedMsgs) sUpdate

(** val s2Update : ('a1, 'a2, 'a3) sUpdate -> ('a1, 'a2, 'a3) update **)

let s2Update upd s i =
  let (s', o) = upd s i in ((Some s'), o)

(** val mkSSM :
    ('a3, 'a1, 'a2) sUpdate -> 'a3 -> ('a3, 'a1, 'a2) stateMachine **)

let mkSSM upd s =
  mkSM (s2Update upd) s

type 's mStateMachine = ('s, msg, directedMsgs) stateMachine

(** val updState :
    ('a1, 'a2, 'a3) stateMachine -> 'a1 -> ('a1, 'a2, 'a3) stateMachine **)

let updState c0 s =
  { sm_halted = c0.sm_halted; sm_update = c0.sm_update; sm_state = s }

(** val halts :
    ('a1, 'a2, 'a3) stateMachine -> ('a1, 'a2, 'a3) stateMachine **)

let halts c0 =
  { sm_halted = true; sm_update = c0.sm_update; sm_state = c0.sm_state }

(** val force_sm :
    ('a1, 'a2, 'a3) stateMachine -> (('a1, 'a2, 'a3) stateMachine -> 'a4) ->
    'a4 **)

let force_sm sm f0 =
  f0 sm

(** val lrun_sm :
    ('a1, 'a2, 'a3 list) stateMachine -> 'a2 -> ('a1, 'a2, 'a3 list)
    stateMachine * 'a3 list **)

let lrun_sm c0 i =
  if c0.sm_halted
  then (c0, [])
  else let (o0, o) = c0.sm_update c0.sm_state i in
       (match o0 with
        | Some s -> force_sm (updState c0 s) (fun sm -> (sm, o))
        | None -> force_sm (halts c0) (fun sm -> (sm, o)))

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

(** val leader_update : raftcontext -> raftleader_state mSUpdate **)

let leader_update _ state input =
  match Obj.magic input with
  | Command m -> (m, [])
  | _ -> (state, [])

(** val raftleaderSM : raftcontext -> raftleader_state mStateMachine **)

let raftleaderSM raft_context =
  mkSSM (leader_update raft_context) 0

(** val str_concat : char list list -> char list **)

let rec str_concat = function
| [] -> []
| s :: ss -> append s (str_concat ss)

(** val raft_state2string : raftleader_state -> char list **)

let raft_state2string _ =
  str_concat
    (('('::('L'::('e'::('a'::('d'::('e'::('r'::(' '::('s'::('t'::('a'::('t'::('e'::(':'::[])))))))))))))) :: ((')'::[]) :: []))

(** val local_replica : raftcontext -> raftleader_state mStateMachine **)

let local_replica =
  raftleaderSM
