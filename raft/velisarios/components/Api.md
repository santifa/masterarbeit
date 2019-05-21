# API Documentation file

It gives a rough overview about the provided types, lemmas and definitions.

## Pair.v
### Definition


    Definition pairSM_upd {SX SY I T U : Type}
    (X : Update SX I T)
    (Y : Update SY I U) : Update (pstate SX SY) I (pstate T U) :=
    fun state i =>
    match state with
    | pstate_two sx sy =>
    let (sx', t) := X sx i in
    let (sy', u) := Y sy i in
    (opt_states2pstate sx' sy', pstate_two t u)
    | pstate_left sx =>
    let (sx', t) := X sx i in
    (option_map (fun x => pstate_left x) sx', pstate_left t)
    | pstate_right sy =>
    let (sy', u) := Y sy i in
    (option_map (fun x => pstate_right x) sy', pstate_right u)
    end.

    Definition pairSM {SX SY I T U : Type}
    (X : StateMachine SX I T)
    (Y : StateMachine SY I U)
    : StateMachine (pstate SX SY) I (pstate T U) :=
    mkSM (pairSM_upd (sm_update X) (sm_update Y)) (pstate_two (sm_state X) (sm_state Y)).

    Definition npairSM {SX SY I T U : Type}
    (X : NStateMachine SX I T)
    (Y : NStateMachine SY I U)
    : NStateMachine (pstate SX SY) I (pstate T U) :=
    fun n => pairSM (X n) (Y n).

## Compose.v
### Definition


    Definition composeSM_upd {SX SY I T U W : Type}
    (f : U -> T -> W)
    (X : Update SX U T)
    (Y : Update SY I (option U)) : Update (pstate SX SY) I (option W) :=
    fun state i =>
    match state with
    | pstate_two sx sy =>
    let (syop, uop) := Y sy i in
    match uop with
    | Some u =>
    let (sxop, t) := X sx u in
    (opt_states2pstate sxop syop, Some (f u t))
    | None => (opt_states2pstate (Some sx) syop, None)
    end
    | pstate_left _ => (Some state, None)
    | pstate_right _ => (None, None)
    end.

    Definition composeSM {SX SY I T U W : Type}
    (f : U -> T -> W)
    (X : StateMachine SX U T)
    (Y : StateMachine SY I (option U))
    : StateMachine (pstate SX SY) I (option W) :=
    mkSM (composeSM_upd f (sm_update X) (sm_update Y))
    (pstate_two (sm_state X) (sm_state Y)).

    Definition ncomposeSM {SX SY I T U W : Type}
    (f : U -> T -> W)
    (X : NStateMachine SX U T)
    (Y : NStateMachine SY I (option U))
    : NStateMachine (pstate SX SY) I (option W) :=
    fun n => composeSM f (X n) (Y n).

## Map.v
### Definition


    Definition mapSM_upd {SX I T U : Type}
    (f : T -> U)
    (X : Update SX I T) : Update SX I U :=
    fun state i =>
    match X state i with
    | (Some s, t) => (Some s, f t)
    | (None, t) => (None, f t)
    end.

    Definition mapSM {SX I T U : Type}
    (f : T -> U)
    (X : StateMachine SX I T)
    : StateMachine SX I U :=
    mkSM (mapSM_upd f (sm_update X)) (sm_state X).

    Definition nmapSM {SX I T U : Type}
    (f : name -> T -> U)
    (X : NStateMachine SX I T)
    : NStateMachine SX I U := fun n => mapSM (f n) (X n).

### Lemma


    Lemma mapSM_state_iff :
    forall {SX T U}
    (f  : T -> U)
    (X  : StateMachine SX msg T)
    (eo : EventOrdering)
    (e  : Event),
    state_sm_on_event (mapSM f X) e
    = state_sm_on_event X e.

    Lemma mapSM_output_iff :
    forall {SX T U}
    (f  : T -> U)
    (X  : StateMachine SX msg T)
    (eo : EventOrdering)
    (e  : Event),
    output_sm_on_event (mapSM f X) e
    = option_map f (output_sm_on_event X e).

    Lemma mapSM_list_output_iff :
    forall {SX T U}
    (f  : T -> list U)
    (X  : StateMachine SX msg T)
    (eo : EventOrdering)
    (e  : Event)
    (u  : U),
    In u (loutput_sm_on_event (mapSM f X) e)
    <->
    In u (olist2list (option_map f (output_sm_on_event X e))).

## Parallel.v
### Definition


    Definition parallel_upd {SX SY I O : Type}
    (X : Update SX I (list O))
    (Y : Update SY I (list O)) : Update (pstate SX SY) I (list O) :=
    fun state i =>
    match state with
    | pstate_two sx sy =>
    let (sx', outx) := X sx i in
    let (sy', outy) := Y sy i in
    (opt_states2pstate sx' sy', outx ++ outy)
    | pstate_left sx =>
    let (sx', outx) := X sx i in
    (option_map (fun x => pstate_left x) sx', outx)
    | pstate_right sy =>
    let (sy', outy) := Y sy i in
    (option_map (fun x => pstate_right x) sy', outy)
    end.

    Definition parallel {SX SY I O : Type}
    (X : StateMachine SX I (list O))
    (Y : StateMachine SY I (list O))
    : StateMachine (pstate SX SY) I (list O) :=
    mkSM (parallel_upd (sm_update X) (sm_update Y))
    (pstate_two (sm_state X) (sm_state Y)).

    Definition nparallel {SX SY I O : Type}
    (X : NStateMachine SX I (list O))
    (Y : NStateMachine SY I (list O))
    : NStateMachine (pstate SX SY) I (list O) :=
    fun slf => parallel (X slf) (Y slf).

### Lemma


    Lemma state_sm_on_event_parallel_some_pstate_two_implies :
    forall {SX SY O}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (l  : SX)
    (r  : SY),
    state_sm_on_event (parallel X Y) e = Some (pstate_two l r)
    -> state_sm_on_event X e = Some l
    /\ state_sm_on_event Y e = Some r.

    Lemma state_sm_on_event_parallel_some_pstate_left_implies :
    forall {SX SY O}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (l  : SX),
    state_sm_on_event (parallel X Y) e = Some (pstate_left l)
    -> state_sm_on_event X e = Some l
    /\ state_sm_on_event Y e = None.

    Lemma state_sm_on_event_parallel_some_pstate_right_implies :
    forall {SX SY O}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (r  : SY),
    state_sm_on_event (parallel X Y) e = Some (pstate_right r)
    -> state_sm_on_event X e = None
    /\ state_sm_on_event Y e = Some r.

    Lemma state_sm_on_event_parallel_none_implies :
    forall {SX SY O}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event),
    state_sm_on_event (parallel X Y) e = None
    -> state_sm_on_event X e = None
    /\ state_sm_on_event Y e = None.

    Lemma parallel_output_iff :
    forall {SX SY O}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (x  : O),
    In x (loutput_sm_on_event (parallel X Y) e)
    <->
    (
    In x (loutput_sm_on_event X e)
    \/
    In x (loutput_sm_on_event Y e)
    ).

## Once.v
### Definition


    Definition Once {S I O : Type} (sm : StateMachine S I (list O)) : StateMachine S I (list O) :=
    MkSM
    (sm_halted sm)
    (fun s i =>
    match sm_update sm s i with
    | (Some s', l) =>
    if nullb l
    then (Some s', l)
    else (None, l) (* We halt as soon as we produce something *)
    | (None, l) => (None, l)
    end)
    (sm_state sm).

    Definition nOnce {S I O : Type} (sm : NStateMachine S I (list O)) : NStateMachine S I (list O) :=
    fun slf => Once (sm slf).

## Components.v
### Definition


    Definition Components {S I O} : Type := list (StateMachine S I O).

    
    End Components.
### Lemma


    Require Import EventOrderingLemmas.

    Require Import Process.

## PairState.v
### Definition


    Definition opt_states2pstate
    {SX SY}
    (sx : option SX)
    (sy : option SY) : option (pstate SX SY) :=
    match sx, sy with
    | Some x, Some y => Some (pstate_two x y)
    | Some x, None => Some (pstate_left x)
    | None, Some y => Some (pstate_right y)
    | None, None => None
    end.

### Inductive


    Inductive pstate SX SY :=
    | pstate_two (l : SX) (r : SY)
    | pstate_left (l : SX)
    | pstate_right (r : SY).

## Bind.v
### Definition


    Definition updStateOp {S I O}
    (sm  : StateMachine S I O)
    (sop : option S) : StateMachine S I O :=
    match sop with
    | Some s => updState sm s
    | None => MkSM true (sm_update sm) (sm_state sm)
    end.

    Definition run_main_process {SX I T}
    (X : StateMachine SX I (list T))
    (sxop : option SX)
    (i : I) : option SX * list T :=
    match sxop with
    | Some sx => sm_update X sx i
    | None => (None, [])
    end.

    Definition run_sub_process {SY I T U}
    (gY : T -> StateMachine SY I (list U))
    (p : T * SY)
    (i : I) : option (T * SY) * list U :=
    let (t,sy) := p in
    match sm_update (gY t) sy i with
    | (Some sy', outs) => (Some (t, sy'), outs)
    | (None, outs) => (None, outs)
    end.

    Definition bind_upd {SX SY I T U}
    (X : StateMachine SX I (list T))
    (gY : T -> StateMachine SY I (list U))
    : Update (bindState SX T SY) I (list U) :=
    fun state (i : I) =>
    match state with
    | bind_state sxop sys => (* The state is a pair of X and a bunch of Ys *)
    (* we run X on the input i and get some outputs outs *)
    let (sx',ts) := run_main_process X sxop i in
    (* we run the process generator gY on these outputs *)
    let sys' := map (fun t => (t, sm_state (gY t))) ts in (* NOTE: what if the state machine is supposed to be halted right from the beginning? *)
    (* now we run these Ys++Ys' on the input as well,
    and here outs is a list of pairs (option (t,state), outputs) *)
    let pairs := map (fun p => run_sub_process gY p i) (sys ++ sys') in
    (* We get the state machines and clear the ones that have halted *)
    let new_sys := mapOption fst pairs in
    (* new state *)
    let new_state :=
    if is_none sx' && nullb new_sys
    then None
    else Some (bind_state sx' new_sys) in
    (new_state, flat_map snd pairs)
    end.

    Definition bind_init {I SX T SY}
    (X : StateMachine SX I (list T)) : bindState SX T SY :=
    bind_state (Some (sm_state X)) [].

    Definition bind {SX SY I T U : Type}
    (X : StateMachine SX I (list T))
    (gY : T -> StateMachine SY I (list U))
    : StateMachine (bindState SX T SY) I (list U) :=
    mkSM (bind_upd X gY) (bind_init X).

    Definition nbind {SX SY I T U : Type}
    (X : NStateMachine SX I (list T))
    (gY : T -> NStateMachine SY I (list U))
    : NStateMachine (bindState SX T SY) I (list U) :=
    fun slf => bind (X slf) (fun t => gY t slf).

### Inductive


    Inductive bindState (SX T SY : Type) :=
    | bind_state (sx : option SX) (sys : list (T * SY)).

### Lemma


    Require Import EventOrderingLemmas.

    Require Import Process.

    Lemma state_sm_on_event_bind_some_state_X :
    forall {SX SY T U}
    (X    : StateMachine SX msg (list T))
    (gY   : T -> StateMachine SY msg (list U))
    (eo   : EventOrdering)
    (e    : Event)
    (sop  : option SX)
    (sys  : list (T * SY)),
    state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) e
    = Some (bind_state sop sys)
    -> state_sm_on_event X e = sop.

    Lemma state_sm_on_event_bind_none_state_X :
    forall {SX SY T U}
    (X    : StateMachine SX msg (list T))
    (gY   : T -> StateMachine SY msg (list U))
    (eo   : EventOrdering)
    (e    : Event),
    state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) e = None
    -> state_sm_on_event X e = None.

    Lemma bind_state_implies :
    forall {SX SY T U}
    (X    : StateMachine SX msg (list T))
    (gY   : T -> StateMachine SY msg (list U))
    (eo   : EventOrdering)
    (e    : Event)
    (sxop : option SX)
    (sys  : list (T * SY))
    (t    : T)
    (sy   : SY),
    state_sm_on_event (mkSM (bind_upd X gY) (bind_init X)) e
    = Some (bind_state sxop sys)
    -> In (t,sy) sys
    ->
    exists (e'    : Event)
    (outxs : list T)
    (p     : e' ⊑ e),
    output_sm_on_event X e' = Some outxs
    /\ In t outxs
    /\ @state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe p) = Some sy.

    Lemma implies_in_sub_component :
    forall {SX SY T U}
    (X  : StateMachine SX msg (list T))
    (gY : T -> StateMachine SY msg (list U))
    (eo : EventOrdering)
    (e' e : Event)
    (p : e' ⊑ e)
    t sy sop sys,
    In t (loutput_sm_on_event X e')
    -> @state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe p) = Some sy
    -> state_sm_on_event (bind X gY) e = Some (bind_state sop sys)
    -> In (t,sy) sys.

    Lemma implies_in_sub_component2 :
    forall {SX SY T U}
    (X  : StateMachine SX msg (list T))
    (gY : T -> StateMachine SY msg (list U))
    (eo : EventOrdering)
    (e' e : Event)
    (p : e' ⊑ e)
    t sy,
    In t (loutput_sm_on_event X e')
    -> @state_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe p) = Some sy
    -> state_sm_on_event (bind X gY) e = None
    -> False.

    Lemma output_bind_iff :
    forall {SX SY T U}
    (X  : StateMachine SX msg (list T))
    (gY : T -> StateMachine SY msg (list U))
    (eo : EventOrdering)
    (e  : Event)
    (u  : U),
    In u (loutput_sm_on_event (bind X gY) e)
    <->
    exists (e' : Event)
    (p  : e' ⊑ e)
    (t  : T),
    In t (loutput_sm_on_event X e')
    /\ In u (@loutput_sm_on_event _ _ _ _ _ (gY t) (subEventOrdering e') (mkSubOrderingLe p)).

## Loop.v
### Definition


    Definition simple_state_machine_upd {SX S I T U : Type}
    (upd : SUpdate S T U)
    (X   : Update SX I T) : Update (S * SX) I U :=
    fun state i =>
    let (s,sx) := state in
    let (sxop, t) := X sx i in
    let (s', o) := upd s t in
    (option_map (fun sx' => (s', sx')) sxop, o).

    Definition simple_state_machineSM {SX S I T U : Type}
    (upd  : SUpdate S T U)
    (init : S)
    (X    : StateMachine SX I T)
    : StateMachine (S * SX) I U :=
    mkSM (simple_state_machine_upd upd (sm_update X))
    (init, sm_state X).

    Definition n_simple_state_machineSM {SX S I T U : Type}
    (upd  : SUpdate S T U)
    (init : S)
    (X    : NStateMachine SX I T)
    : NStateMachine (S * SX) I U :=
    fun n => simple_state_machineSM upd init (X n).

    Definition state_machine_upd {SX S I T U : Type}
    (upd : Update S T U)
    (X   : Update SX I T) : Update (S * SX) I U :=
    fun state i =>
    let (s,sx) := state in
    let (sxop, t) := X sx i in
    let (sop, o) := upd s t in
    match sop, sxop with
    | Some s', Some sx' => (Some (s', sx'), o)
    | _, _ => (None, o)
    end.

    Definition state_machineSM {SX S I T U : Type}
    (upd  : Update S T U)
    (init : S)
    (X    : StateMachine SX I T)
    : StateMachine (S * SX) I U :=
    mkSM (state_machine_upd upd (sm_update X))
    (init, sm_state X).

    Definition n_state_machineSM {SX S I T U : Type}
    (upd  : Update S T U)
    (init : S)
    (X    : NStateMachine SX I T)
    : NStateMachine (S * SX) I U :=
    fun n => state_machineSM upd init (X n).

### Lemma


    Lemma simple_state_machineSM_state_iff :
    forall {S SX T U}
    (upd  : SUpdate S T U)
    (init : S)
    (X    : StateMachine SX msg T)
    (eo   : EventOrdering)
    (e    : Event)
    (s    : S)
    (sx   : SX),
    state_sm_on_event (simple_state_machineSM upd init X) e = Some (s, sx)
    <->
    exists t s' sx',
    state_sm_on_event X e = Some sx
    /\ output_sm_on_event X e = Some t
    /\ state_sm_before_event (simple_state_machineSM upd init X) e = Some (s', sx')
    /\ state_sm_before_event X e = Some sx'
    /\ op_update X sx' (trigger e) = Some (Some sx, t)
    /\ s = fst (upd s' t).

    Lemma simple_state_machineSM_output_iff0 :
    forall {S SX T U}
    (upd  : SUpdate S T U)
    (init : S)
    (X    : StateMachine SX msg T)
    (eo   : EventOrdering)
    (e    : Event)
    (u    : U),
    output_sm_on_event (simple_state_machineSM upd init X) e = Some u
    <->
    exists t s sx,
    output_sm_on_event X e = Some t
    /\ state_sm_before_event (simple_state_machineSM upd init X) e = Some (s,sx)
    /\ u = snd (upd s t).

    Lemma simple_state_machineSM_output_iff :
    forall {S SX T U}
    (upd  : SUpdate S T U)
    (init : S)
    (X    : StateMachine SX msg T)
    (eo   : EventOrdering)
    (e    : Event)
    (u    : U),
    output_sm_on_event (simple_state_machineSM upd init X) e = Some u
    <->
    exists t s,
    output_sm_on_event X e = Some t
    /\ SM_state_before_event (simple_state_machineSM upd init X) e s
    /\ u = snd (upd s t).

    Lemma simple_state_machineSM_list_output_iff :
    forall {S SX T U}
    (upd  : SUpdate S T (list U))
    (init : S)
    (X    : StateMachine SX msg T)
    (eo   : EventOrdering)
    (e    : Event)
    (u    : U),
    In u (loutput_sm_on_event (simple_state_machineSM upd init X) e)
    <->
    exists t s,
    output_sm_on_event X e = Some t
    /\ SM_state_before_event (simple_state_machineSM upd init X) e s
    /\ In u (snd (upd s t)).

    Lemma state_machineSM_state_iff :
    forall {S SX T U}
    (upd  : Update S T U)
    (init : S)
    (X    : StateMachine SX msg T)
    (eo   : EventOrdering)
    (e    : Event)
    (s    : S)
    (sx   : SX),
    state_sm_on_event (state_machineSM upd init X) e = Some (s, sx)
    <->
    exists t s' sx',
    state_sm_on_event X e = Some sx
    /\ output_sm_on_event X e = Some t
    /\ state_sm_before_event (state_machineSM upd init X) e = Some (s', sx')
    /\ state_sm_before_event X e = Some sx'
    /\ sm_update X sx' (trigger e) = (Some sx, t)
    /\ Some s = fst (upd s' t).

    Lemma state_machineSM_output_iff0 :
    forall {S SX T U}
    (upd  : Update S T U)
    (init : S)
    (X    : StateMachine SX msg T)
    (eo   : EventOrdering)
    (e    : Event)
    (u    : U),
    output_sm_on_event (state_machineSM upd init X) e = Some u
    <->
    exists t s sx,
    output_sm_on_event X e = Some t
    /\ state_sm_before_event (state_machineSM upd init X) e = Some (s,sx)
    /\ u = snd (upd s t).

    Lemma state_machineSM_output_iff :
    forall {S SX T U}
    (upd  : Update S T U)
    (init : S)
    (X    : StateMachine SX msg T)
    (eo   : EventOrdering)
    (e    : Event)
    (u    : U),
    output_sm_on_event (state_machineSM upd init X) e = Some u
    <->
    exists t s,
    output_sm_on_event X e = Some t
    /\ SM_state_before_event (state_machineSM upd init X) e s
    /\ u = snd (upd s t).

    Lemma state_machineSM_list_output_iff :
    forall {S SX T U}
    (upd  : Update S T (list U))
    (init : S)
    (X    : StateMachine SX msg T)
    (eo   : EventOrdering)
    (e    : Event)
    (u    : U),
    In u (loutput_sm_on_event (state_machineSM upd init X) e)
    <->
    exists t s,
    output_sm_on_event X e = Some t
    /\ SM_state_before_event (state_machineSM upd init X) e s
    /\ In u (snd (upd s t)).

## SendId.v
### Definition


    Definition SendId {I O : Type} (F : name -> O) : NStateMachine _ I O :=
    fun slf => mkSM (fun _ _ => (None, F slf)) tt.

### Lemma


    Lemma state_sm_on_event_SendId_none :
    forall {O} (F : name -> list O) (n : name) (eo : EventOrdering) (e : Event),
    state_sm_on_event (SendId F n) e = None.

    Lemma SendId_list_output_iff :
    forall {O} (F : name -> list O) (o : O) (n : name) (eo : EventOrdering) (e : Event),
    In o (loutput_sm_on_event (SendId F n) e)
    <-> (In o (F n) /\ isFirst e).

## Until.v
### Definition


    Definition Until_upd {SX SY I OX OY : Type}
    (X : Update SX I (list OX))
    (Y : Update SY I (list OY)) : Update (pstate SX SY) I (list OX) :=
    fun state i =>
    match state with
    | pstate_two sx sy =>
    let (sx', outx) := X sx i in
    let (sy', outy) := Y sy i in
    if nullb outy (* if outy is not null, we halt X *)
    then
    match opt_states2pstate sx' sy' with
    (* both X and Y are still running *)
    | Some (pstate_two x y) as st => (st, outx)
    (* X is still running *)
    | Some (pstate_left x) as st => (st, outx)
    (* X is not running anymore *)
    | _ => (None, outx)
    end
    else (None, outx)
    | pstate_left sx =>
    let (sx', outx) := X sx i in
    match sx' with
    | Some x => (Some (pstate_left x), outx)
    | None => (None, outx)
    end
    | _ => (None, [])
    end.

    Definition Until {SX SY I OX OY : Type}
    (X : StateMachine SX I (list OX))
    (Y : StateMachine SY I (list OY))
    : StateMachine (pstate SX SY) I (list OX) :=
    mkSM (Until_upd (sm_update X) (sm_update Y))
    (pstate_two (sm_state X) (sm_state Y)).

    Definition nUntil {SX SY I OX OY : Type}
    (X : NStateMachine SX I (list OX))
    (Y : NStateMachine SY I (list OY))
    : NStateMachine (pstate SX SY) I (list OX) :=
    fun slf => Until (X slf) (Y slf).

    Definition UntilSend_upd {SX SY I O : Type}
    (X : Update SX I (list O))
    (Y : Update SY I (list O)) : Update (pstate SX SY) I (list O) :=
    fun state i =>
    match state with
    | pstate_two sx sy =>
    let (sx', outx) := X sx i in
    let (sy', outy) := Y sy i in
    (* This is similar to Until.

    Definition UntilSend {SX SY I O : Type}
    (X : StateMachine SX I (list O))
    (Y : StateMachine SY I (list O))
    : StateMachine (pstate SX SY) I (list O) :=
    mkSM (UntilSend_upd (sm_update X) (sm_update Y))
    (pstate_two (sm_state X) (sm_state Y)).

    Definition nUntilSend {SX SY I O : Type}
    (X : NStateMachine SX I (list O))
    (Y : NStateMachine SY I (list O))
    : NStateMachine (pstate SX SY) I (list O) :=
    fun slf => UntilSend (X slf) (Y slf).

### Lemma


    Require Import EventOrderingLemmas.

    Require Import Process.

    Lemma state_sm_on_event_UntilSend_some_pstate_two_implies :
    forall {SX SY O : Type}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (l  : SX)
    (r  : SY),
    state_sm_on_event (UntilSend X Y) e = Some (pstate_two l r)
    -> state_sm_on_event X e = Some l
    /\ state_sm_on_event Y e = Some r
    /\ (forall e' x, e' ⊑ e -> ~ In x (loutput_sm_on_event Y e')).

    Lemma state_sm_on_event_UntilSend_some_pstate_left_implies :
    forall {SX SY O : Type}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (l  : SX),
    state_sm_on_event (UntilSend X Y) e = Some (pstate_left l)
    -> state_sm_on_event X e = Some l
    /\ state_sm_on_event Y e = None
    /\ (forall e' x, e' ⊑ e -> ~ In x (loutput_sm_on_event Y e')).

    Lemma state_sm_on_event_UntilSend_some_pstate_right_implies :
    forall {SX SY O : Type}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (r  : SY),
    state_sm_on_event (UntilSend X Y) e = Some (pstate_right r)
    -> False.

    Lemma state_sm_on_event_UntilSend_none_implies :
    forall {SX SY O : Type}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event),
    state_sm_on_event (UntilSend X Y) e = None
    ->
    exists e',
    e' ⊑ e
    /\
    (
    state_sm_on_event X e' = None
    \/
    exists x, In x (loutput_sm_on_event Y e')
    ).

    Lemma UntilSend_output_iff0 :
    forall {SX SY O : Type}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (o  : O),
    In o (loutput_sm_on_event (UntilSend X Y) e)
    <->
    (
    (forall e' x, e' ⊏ e -> ~ In x (loutput_sm_on_event Y e'))
    /\
    (
    In o (loutput_sm_on_event X e)
    \/
    (
    In o (loutput_sm_on_event Y e)
    /\
    exists s, state_sm_before_event X e = Some s
    )
    )
    ).

    Lemma UntilSend_output_iff :
    forall {SX SY O : Type}
    (X  : StateMachine SX msg (list O))
    (Y  : StateMachine SY msg (list O))
    (eo : EventOrdering)
    (e  : Event)
    (o  : O),
    In o (loutput_sm_on_event (UntilSend X Y) e)
    <->
    (
    no_loutput_sm_on_event_prior_to Y e
    /\
    (
    In o (loutput_sm_on_event X e)
    \/
    (
    In o (loutput_sm_on_event Y e)
    /\
    state_sm_before_event_exists X e
    )
    )
    ).

