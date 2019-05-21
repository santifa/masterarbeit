# API Documentation file

It gives a rough overview about the provided types, lemmas and definitions.

## ComponentSMExample1.v
### Definition


    Definition def_nat : nat := 0.

    
    Definition CIOnat : ComponentIO :=
    MkComponentIO nat nat def_nat.

    Definition m_counter_update : M_Update 0 "A" nat :=
    fun (s : nat) i =>
    ret _ (Some (s + i), s + i).

    Definition A : M_StateMachine 1 "A" :=
    build_m_sm m_counter_update 0.

    Definition B_update : M_Update 1 "B" nat :=
    fun s i =>
    (call_proc "A" i)
    >>= fun out =>
    ret _ (Some (s + out + 1), s + out + 1).

    Definition B : M_StateMachine 2 "B" :=
    build_m_sm B_update 0.

    Definition C_update : M_Update 2 "C" nat :=
    fun s i =>
    (call_proc "B" i)
    >>= fun out1 =>
    (call_proc "B" i)
    >>= fun out2 =>
    ret _ (Some (s + out1 + out2 + 2), s + out1 + out2 + 2).

    Definition C : M_StateMachine 3 "C" :=
    build_m_sm C_update 0.

    Definition M_update : M_Update 3 "M" unit :=
    fun s i =>
    (call_proc "C" i)
    >>= (fun out => ret _ (Some s, out)).

    Definition M : M_StateMachine 4 "M" :=
    build_m_sm M_update tt.

    Definition progs : n_procs 3 :=
    [existT _ "A" (incr_n_proc (incr_n_proc A)),
    existT _ "B" (incr_n_proc B),
    existT _ "C" C].

    Definition ls :=
    MkLocalSystem
    3
    (existT _ "M" M)
    [existT _ "A" (incr_n_proc (incr_n_proc A)),
    existT _ "B" (incr_n_proc B),
    existT _ "C" C].

### Instance


    Instance funIOnat : funIO := MkFunIO (fun _ => CIOnat).

    
    Definition m_counter_update : M_Update 0 "A" nat :=
    fun (s : nat) i =>
    ret _ (Some (s + i), s + i).

## correct.v
### Definition


    Definition correct (eo : EventOrdering) (n : name) (L : list Event) :=
    forall e e1 e2,
    In e L
    -> e1 ≼ e
    -> e2 ≼ e
    -> loc e1 = n
    -> loc e2 <> n
    -> disjoint (lkm_sending_keys (keys e1)) (lkm_sending_keys (keys e2)).

    Definition correct_e {eo : EventOrdering} (e : Event) :=
    correct eo (loc e) [e].

## Component2.v
### Definition


    Definition I := nat.

    Definition O := nat.

    Definition S := nat.

    
    Definition name := String.
string.

    Definition proc  := Process I O.

    Definition nproc := (name * proc)%type.

    Definition procs := list nproc.

    
    Definition M (A : Type) := procs -> (procs * A)%type.

    Definition M_Update (S I O : Type) := S -> I -> M (option S * O).

    
    Definition ret {A} (a : A) : M(A) := fun s => (s, a).

    Definition bind {A B} (m : M(A)) (f : A -> M(B)) : M(B) :=
    fun s =>
    let (s1,a) := m s in
    let (s2,b) := f a s1 in
    (s2,b).

    Definition call_proc (n : name) (i : I) : M O :=
    fun l =>
    match find_name n l with
    | Some pr =>
    match app_proc pr i with
    | Some (q,o) => (replace_name n q l,o)
    | None => (l,0)
    end
    | None => (l,0)
    end.

    (*Definition B_update (i : nat) : M_Update unit nat nat :=
    fun s n =>
    fun procs =>
    let (ps,out) :=
    match find_name "A" procs with
    | Some p =>
    match app_proc p n with
    | Some (q,out) => ([("A",q)],out)
    | None => ([],0)
    end
    | None => ([],0)
    end in
    (ps, (Some s, out)).
*)
    Definition M_haltedProc {I O} : M_Process I O := m_proc None.

    
    (*CoFixpoint build_m_process {S I O}
    (upd : M_Update S I O)
    (s   : S) : M_Process I O :=
    m_proc (Some
    (fun a =>
    (upd s a)
    >>= (fun x =>
    match x with
    | (Some s', out) => ret (build_m_process upd s', out)
    | (None, out) => ret (M_haltedProc, out)
    end))).
*)
    Definition m_counter_update : M_Update S I O :=
    fun s i => ret (Some (s + i), s + i).

    Definition A : M_Process I O :=
    build_m_process m_counter_update 0.

    Definition B_update : M_Update unit nat nat :=
    fun s n =>
    (call_proc "A" n)
    >>= (fun out => ret (Some s, out)).

    Definition B : M_Process I O :=
    build_m_process B_update tt.

    (*Definition prog : procs := [("A",A),("B",B)].
*)
### Inductive


    CoInductive M_Process (I O : Type) : Type :=
    | m_proc (f : option (I -> M (M_Process I O * O))).

## generic_tactics.v
## Received_or_generated.v
### Definition


    Definition received_or_generated {S}
    (eo   : EventOrdering)
    (sm   : MStateMachine S)
    (Cond : Event -> S -> Prop)
    (Rec  : Event -> S -> S -> Event -> S -> Prop)
    (Gen  : Event -> S -> S -> Event -> S  -> Prop) :=
    forall (e : Event) (st : S ),
    state_sm_on_event sm e = Some st
    -> Cond e st
    ->
    exists e' st1 st2,
    e' ⊑ e
    /\ state_sm_before_event sm e' = Some st1
    /\ state_sm_on_event sm e' = Some st2
    /\ (Rec e' st1 st2 e st \/ Gen e' st1 st2 e st).

    Definition received_or_generated_loc {S}
    (eo   : EventOrdering)
    (i    : node_type)
    (sm   : MStateMachine S)
    (Cond : Event -> node_type -> S -> Prop)
    (Rec  : Event -> S -> S -> Event -> node_type -> S -> Prop)
    (Gen  : Event -> S -> S -> Event -> node_type -> S  -> Prop) :=
    forall (e : Event) (st : S ),
    loc e = node2name i
    -> state_sm_on_event sm e = Some st
    -> Cond e i st
    ->
    exists e' st1 st2,
    e' ⊑ e
    /\ state_sm_before_event sm e' = Some st1
    /\ state_sm_on_event sm e' = Some st2
    /\ (Rec e' st1 st2 e i st \/ Gen e' st1 st2 e i st).

    Definition received_or_generated
    (eo : EventOrdering)
    (Cond : Event -> Rep -> PBFTstate -> Prop)
    (Rec  : Event -> PBFTstate -> PBFTstate -> Event -> Rep -> PBFTstate -> Prop)
    (Gen  : Event -> PBFTstate -> PBFTstate -> Event -> Rep -> PBFTstate -> Prop) :=
    forall (e : Event) (i : Rep) (st : PBFTstate),
    loc e = PBFTreplica i
    -> state_sm_on_event (PBFTreplicaSM i) eo e = Some st
    -> Cond e i st
    ->
    exists e' st1 st2,
    e' ⊑ e
    /\ state_sm_before_event (PBFTreplicaSM i) eo e' = Some st1
    /\ state_sm_on_event (PBFTreplicaSM i) eo e' = Some st2
    /\ (Rec e' st1 st2 e i st \/ Gen e' st1 st2 e i st).

## Node.v
### Instance


    Instance nat_node : Node := MkNode nat eq_nat_dec.

    
    End Node.

## LearnAndKnows.v
### Definition


    Definition lak_data2node (d : lak_data) : name :=
    node2name (lak_data2owner d).

    Definition knows
    {eo : EventOrdering}
    (e  : Event)
    (d  : lak_data) :=
    exists mem n,
    loc e = node2name n
    /\ lak_knows d mem
    /\ state_sm_on_event (lak_system n) e = Some mem.

    Definition knew
    {eo : EventOrdering}
    (e  : Event)
    (d  : lak_data) :=
    exists mem n,
    loc e = node2name n
    /\ lak_knows d mem
    /\ state_sm_before_event (lak_system n) e = Some mem.

    Definition knows_certificate
    {eo : EventOrdering}
    (e : Event)
    (n : nat)
    (i : lak_info)
    (P : list lak_data -> Prop) :=
    exists (l : list lak_data),
    n <= length l
    /\ no_repeats (map lak_data2owner l)
    /\ P l
    /\ forall d, In d l -> (knows e d /\ i = lak_data2info d).

    Definition learns {eo : EventOrdering} (e : Event) (d : lak_data) :=
    exists n,
    loc e = node2name n
    /\ In (lak_data2auth d) (bind_op_list get_contained_authenticated_data (trigger e))
    (*/\ verify_authenticated_data (loc e) (lak_data2auth d) (keys e) = true.
*)
    Definition learned {eo : EventOrdering} (e : Event) (d : lak_data) :=
    exists e', e' ⊑ e /\ learns e' d.

    Definition learns_or_knows (eo : EventOrdering) : Prop :=
    forall (d  : lak_data) (e : Event),
    knows e d
    -> learned e d \/ lak_data2node d = loc e.

    Definition learns_if_knows (eo : EventOrdering) :=
    forall (d  : lak_data) (e : Event),
    learns e d
    -> has_correct_trace_before e (lak_data2node d)
    ->
    exists e',
    e' ≺ e
    /\ loc e' = lak_data2node d
    /\ knows e' d.

    Definition learns_or_knows_if_knew (eo : EventOrdering) : Prop :=
    forall (d  : lak_data) (e : Event),
    knew e d
    -> learned e d \/ lak_data2node d = loc e.

    Definition learned_if_knows (eo : EventOrdering) :=
    forall (d  : lak_data) (e : Event),
    learned e d
    -> has_correct_trace_before e (lak_data2node d)
    ->
    exists e',
    e' ≺ e
    /\ loc e' = lak_data2node d
    /\ knows e' d.

### Lemma


    Lemma knows_implies_correct :
    forall {eo : EventOrdering} (e : Event) (d : lak_data),
    knows e d
    -> has_correct_trace_before e (loc e).

    Lemma knows_propagates :
    forall {eo : EventOrdering} (e : Event) (d : lak_data),
    learns_or_knows eo
    -> learns_if_knows eo
    -> knows e d
    -> has_correct_trace_before e (lak_data2node d)
    ->
    exists e',
    e' ≼ e
    /\ loc e' = lak_data2node d
    /\ knows e' d.

    Lemma knows_in_intersection :
    forall {eo : EventOrdering}
    (e1 e2 : Event)
    (n : nat)
    (i1 i2 : lak_info)
    (P : list lak_data -> Prop)
    (E : list Event)
    (F : nat),
    learns_or_knows eo
    -> learns_if_knows eo
    -> n <= num_nodes
    -> num_nodes + F < 2 * n
    -> knows_certificate e1 n i1 P
    -> knows_certificate e2 n i2 P
    -> exists_at_most_f_faulty E F
    -> In e1 E
    -> In e2 E
    ->
    exists e1' e2' d1 d2,
    loc e1' = loc e2'
    /\ e1' ≼ e1
    /\ e2' ≼ e2
    /\ loc e1' = lak_data2node d1
    /\ loc e2' = lak_data2node d2
    /\ knows e1' d1
    /\ knows e2' d2
    /\ i1 = lak_data2info d1
    /\ i2 = lak_data2info d2.

    Lemma local_knows_in_intersection :
    forall {eo : EventOrdering}
    (e : Event)
    (n : nat)
    (i1 i2 : lak_info)
    (P : list lak_data -> Prop)
    (E : list Event)
    (F : nat),
    n <= num_nodes
    -> num_nodes + F < 2 * n
    -> knows_certificate e n i1 P
    -> knows_certificate e n i2 P
    -> exists_at_most_f_faulty E F
    -> In e E
    ->
    exists correct d1 d2,
    has_correct_trace_before e (node2name correct)
    /\ lak_data2node d1 = lak_data2node d2
    /\ knows e d1
    /\ knows e d2
    /\ i1 = lak_data2info d1
    /\ i2 = lak_data2info d2
    /\ lak_data2owner d1 = correct
    /\ lak_data2owner d2 = correct.

    Lemma knew_implies_knows :
    forall (eo : EventOrdering) (e : Event) (d : lak_data),
    knew e d
    -> knows (local_pred e) d.

    Lemma learns_or_knows_implies_learns_or_knows_if_new :
    forall (eo : EventOrdering),
    learns_or_knows eo
    -> learns_or_knows_if_knew eo.

    Lemma knows_implies :
    forall {eo : EventOrdering} (e : Event) d,
    knows e d
    ->
    exists mem mem' n,
    loc e = node2name n
    /\ op_state (lak_system n) mem (trigger e) = Some mem'
    /\ lak_knows d mem'
    /\ state_sm_before_event (lak_system n) e = Some mem.

    Lemma knows_implies_before_after :
    forall {eo : EventOrdering} (e : Event) d,
    knows e d
    ->
    exists mem mem' n,
    loc e = node2name n
    /\ op_state (lak_system n) mem (trigger e) = Some mem'
    /\ lak_knows d mem'
    /\ state_sm_before_event (lak_system n) e = Some mem
    /\ state_sm_on_event (lak_system n) e = Some mem'.

    Lemma implies_knows :
    forall {eo : EventOrdering} (e : Event) d n mem,
    loc e = node2name n
    -> lak_knows d mem
    -> state_sm_on_event (lak_system n) e = Some mem
    -> knows e d.

    Lemma learned_local_pred_implies :
    forall (eo : EventOrdering) (e : Event) d,
    learned (local_pred e) d
    -> learned e d.

    Lemma learned_local_le_implies :
    forall (eo : EventOrdering) (e1 e2 : Event) d,
    e1 ⊑ e2
    -> learned e1 d
    -> learned e2 d.

    Lemma learns_if_knows_implies_learned_if_knows :
    forall (eo : EventOrdering),
    learns_if_knows eo
    -> learned_if_knows eo.

    Lemma knows_weak_certificate :
    forall {eo : EventOrdering}
    (e : Event)
    (n : nat)
    (i : lak_info)
    (P : list lak_data -> Prop)
    (E : list Event)
    (F : nat),
    F < n
    -> knows_certificate e n i P
    -> exists_at_most_f_faulty E F
    -> In e E
    ->
    exists d,
    has_correct_trace_before e (lak_data2node d)
    /\ knows e d
    /\ i = lak_data2info d.

    Lemma knows_weak_certificate_propagates :
    forall {eo : EventOrdering}
    (e : Event)
    (n : nat)
    (i : lak_info)
    (P : list lak_data -> Prop)
    (E : list Event)
    (F : nat),
    learns_or_knows eo
    -> learns_if_knows eo
    -> F < n
    -> knows_certificate e n i P
    -> exists_at_most_f_faulty E F
    -> In e E
    ->
    exists e' d,
    e' ≼ e
    /\ loc e' = lak_data2node d
    /\ knows e' d
    /\ i = lak_data2info d.

## ComponentSM.v
### Definition


    Definition CompName := String.
string.

    
    (* component *)
    Definition p_nproc (p : CompName -> Type) := { cn : CompName & p cn }%type.

    Definition p_procs (p : CompName -> Type) := list (p_nproc p).

    
    (* monad of the component *)
    Definition M_p (p : CompName -> Type) (PO : Type) :=
    p_procs p -> (p_procs p * PO)%type.

    Definition MP_Update (p : CompName -> Type) (I O S : Type) :=
    S -> I -> M_p p (option S * O).

    Definition CIOmsg : ComponentIO :=
    MkComponentIO msg DirectedMsgs [].

    Definition CIOdef : ComponentIO :=
    MkComponentIO unit unit tt.

    Definition msg_comp_name : CompName := "MSG".

    
    (* We constrain here that components with named [msg_comp_name] have to be
    message components, i.
e.
, taking in messages and returning directed messages *)
    Definition NFalse (cn : CompName) : Type := False.

    
    (* state machine that can have several levels as monad *)
    Fixpoint M_StateMachine (n : nat) (cn : CompName) : Type :=
    match n with
    | 0 => False (*MP_StateMachine NFalse cn*)
    | S n => MP_StateMachine (M_StateMachine n) cn [+] M_StateMachine n cn
    end.

    Definition n_proc := M_StateMachine.

    Definition n_nproc (n : nat) := {cn : CompName & n_proc n cn }.

    Definition n_procs (n : nat) := list (n_nproc n).

    
    (* monad of the list of state machines; each state machine can have several levels *)
    Definition M_n (n : nat) (PO : Type) := n_procs n -> (n_procs n * PO)%type.

    Definition M_Update (n : nat) (nm : CompName) (S : Type) :=
    S -> cio_I (fio nm) -> M_n n (option S * cio_O (fio nm)).

    Definition ret {A} (n : nat) (a : A) : M_n n A := fun s => (s, a).

    
    (* enables combining multiple state machine monads *)
    Definition bind {A B} {n:nat} (m : M_n n A) (f : A -> M_n n B) : M_n n B :=
    fun s =>
    let (s1,a) := m s in
    let (s2,b) := f a s1 in
    (s2,b).

    Definition MP_haltedSM {S}
    (n  : nat)
    (nm : CompName)
    (d  : S) : MP_StateMachine (n_proc n) nm :=
    MkMPSM
    S
    true
    (fun s i p => (p, (None, cio_default_O (fio nm))))
    d.

    Definition M_haltedSM {S}
    (nm : CompName)
    (n : nat)
    (d  : S) : M_StateMachine 1 nm :=
    inl (MkMPSM
    S
    true
    (fun s i p => (p, (None, cio_default_O (fio nm))))
    d).

    Definition incr_n_proc {n} {nm} (p : n_proc n nm) : n_proc (S n) nm := inr p.

    
    (* incr of state machine monad -each state machine can have multiple levels *)
    Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    match p with
    | existT _ m q =>
    existT _ m (incr_n_proc q)
    end.

    Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

    Definition decr_n_proc {n} {nm} : n_proc n nm -> option (n_proc (Init.
Nat.
pred n) nm) :=
    match n with
    | 0 => fun p => Some p
    | S m => fun p =>
    match p with
    | inl _ => None
    | inr q => Some q
    end
    end.

    Definition decr_n_nproc {n} (np : n_nproc n) : option (n_nproc (Init.
Nat.
pred n)) :=
    match np with
    | existT _ m p =>
    match decr_n_proc p with
    | Some q => Some (existT _ m q)
    | None => None
    end
    end.

    Definition decr_n_procs {n} (ps : n_procs n) : n_procs (Init.
Nat.
pred n) :=
    mapOption decr_n_nproc ps.

    Definition incr_pred_n_proc {n} {nm} : n_proc (pred n) nm -> n_proc n nm :=
    match n with
    | 0 => fun p => p
    | S m => inr
    end.

    Definition incr_pred_n_nproc {n} (p : n_nproc (pred n)) : n_nproc n :=
    match p with
    | existT _ m q =>
    existT _ m (incr_pred_n_proc q)
    end.

    Definition incr_pred_n_procs {n} (ps : n_procs (pred n)) : n_procs n :=
    map incr_pred_n_nproc ps.

    Definition lift_M {m} {nm} {O}
    (x : M_p (n_proc m) (MP_StateMachine (n_proc m) nm * O))
    : M_n m (M_StateMachine (S m) nm * O) :=
    fun ps =>
    let (k, qo) := x ps in
    let (q, o) := qo in
    (k, (injL(q), o)).

    Definition lift_M2 {n} {nm} {O} (m : M_n (pred n) (M_StateMachine n nm * O))
    : M_n (pred (S n)) (M_StateMachine (S n) nm * O) :=
    fun (ps : n_procs n) =>
    match m (decr_n_procs ps) with
    | (ps',(p',o)) => (incr_pred_n_procs ps', (incr_n_proc p',o))
    end.

    Definition update_state {p} {cn} (sm : MP_StateMachine p cn) (s : sm_S sm) : MP_StateMachine p cn :=
    MkMPSM
    (sm_S      sm)
    (sm_halted sm)
    (sm_update sm)
    s.

    Definition halt_machine {p} {cn} (sm : MP_StateMachine p cn) : MP_StateMachine p cn :=
    MkMPSM
    (sm_S      sm)
    true
    (sm_update sm)
    (sm_state  sm).

    Definition sm_s_to_sm {n} {nm}
    (sm : MP_StateMachine (n_proc n) nm)
    (x : M_n n (option (sm_S sm) * cio_O (fio nm)))
    : M_n n (MP_StateMachine (n_proc n) nm * cio_O (fio nm)) :=
    x >>= fun so =>
    let (ops,o) := so in
    match ops with
    | Some s => ret _ (update_state sm s,o)
    | None => ret _ (halt_machine sm, o)
    end.

    Definition call_proc {n:nat} (nm : CompName) (i : cio_I (fio nm)) : M_n n (cio_O (fio nm)) :=
    fun (l : n_procs n) =>
    match find_name nm l with
    | Some pr =>
    match app_m_proc pr i with
    | Some f =>
    match f (decr_n_procs l) with
    | (l',(pr',o)) => (replace_subs (replace_name pr' l) l',o)
    end
    | None => (l,cio_default_O (fio nm))
    end
    | None => (l,cio_default_O (fio nm))
    end.

    Definition build_mp_sm {n}
    {S}
    {nm  : CompName}
    (upd : M_Update n nm S)
    (s   : S) : MP_StateMachine (n_proc n) nm :=
    MkMPSM S false upd s.

    Definition build_m_sm {n}
    {St}
    {nm  : CompName}
    (upd : M_Update n nm St)
    (s   : St) : M_StateMachine (S n) nm :=
    inl (build_mp_sm upd s).

    Definition run_local_system (s : LocalSystem) (l : list (cio_I (fio (projT1 (ls_main s))))) :=
    run_n_proc (projT2 (ls_main s)) l (ls_subs s).

    (*Definition M_NStateMachine (nm : CompName) (n : nat) := name -> M_StateMachine n nm.
*)
    
    Definition M_USystem := name -> LocalSystem.

    Definition message_system_constraint (s : M_USystem) :=
    forall n, message_local_system_constraint (s n).

    Definition M_op_update {S} {n} {nm}
    (upd : M_Update n nm S)
    (s   : S)
    (o   : option (cio_I (fio nm)))
    : M_n n (option (option S * cio_O (fio nm))) :=
    match o with
    | Some i => (upd s i) >>= fun so => ret _ (Some so)
    | None => ret _ None
    end.

    Definition M_op_op_update {S} {n} {nm}
    (upd : M_Update n nm S)
    (s   : S)
    (o   : option (cio_I (fio nm)))
    : option (M_n n (option S * cio_O (fio nm))) :=
    match o with
    | Some i => Some (upd s i)
    | None => None
    end.

    Definition M_op_sm_update {n} {nm}
    (sm  : M_StateMachine n nm)
    (iop : option (cio_I (fio nm)))
    : M_n (pred n) (option (M_StateMachine n nm * cio_O (fio nm))) :=
    match iop with
    | Some i => match app_m_proc sm i with
    | Some x => x >>= fun x => ret _ (Some x)
    | None => ret _ None
    end
    | None => ret _ None
    end.

    (*  Definition sm2update {n} {cn} : forall (sm : n_proc n cn), MP_Update (n_proc (sm2level sm)) (cio_I (fio cn)) (cio_O (fio cn)) (sm2S sm).

    Proof.

    Definition lift_M3 {n} {O} (m : M_n (pred n) O)
    : M_n (pred (S n)) O :=
    fun (ps : n_procs n) =>
    match m (decr_n_procs ps) with
    | (ps',o) => (incr_pred_n_procs ps', o)
    end.

    Definition M_run_update_on_event {S} {n}
    (s    : S)
    (upd  : M_Update n msg_comp_name S)
    {eo   : EventOrdering}
    (e    : Event) : M_n n (option (option S * DirectedMsgs)) :=
    (M_run_update_on_list s upd (map trigger (@localPreds pn pk pm eo e)))
    >>= fun sop =>
    match sop with
    | Some s => M_op_update upd s (trigger e)
    | None => ret _ None
    end.

    Definition M_run_sm_on_event {n}
    (sm : M_StateMachine n msg_comp_name)
    {eo : EventOrdering}
    (e  : Event) : M_n (sm2level sm) (option (option (sm2S sm) * DirectedMsgs)) :=
    M_run_update_on_event (sm2state sm) (sm2update sm) e.

    Definition M_state_sm_on_event {n}
    (sm : M_StateMachine n msg_comp_name)
    {eo : EventOrdering}
    (e  : Event) : M_n (sm2level sm) (option (sm2S sm)) :=
    (M_run_sm_on_event sm e)
    >>= fun x =>
    match x with
    | Some (sm',msgs) => ret _ (Some (sm2state sm))
    | None => ret _ None
    end.

    Definition M_state_sm_before_event {n}
    (sm : M_StateMachine n msg_comp_name)
    {eo : EventOrdering}
    (e  : Event) : M_n (sm2level sm) (option (sm2S sm)) :=
    M_run_sm_on_list sm (map trigger (@localPreds pn pk pm eo e)).

### Instance


    Global Instance funIOd_msg : funIO :=
    MkFunIO (fun nm =>
    if String.
string_dec nm msg_comp_name then CIOmsg
## EventOrdering_backup.v
### Definition


    Definition Qpos := {q : Q | Qle 0 q}.

    
    Definition Qpos_lt (q1 q2 : Qpos) := Qlt (proj1_sig q1) (proj1_sig q2).

    Definition isCorrect (e : Event) : Prop :=
    mode e = correct.

    (*  Definition isCrashed (e : Event) : Prop :=
    mode e = faulty crashed.
*)
    Definition isByz (e : Event) : Prop :=
    mode e = faulty byzantine.

    Definition local_pred (e : Event) : Event :=
    match direct_pred e with
    | Some e' => e'
    | None => e
    end.

    Definition causalOrderLe (a b : Event) : Prop :=
    (a ≺ b) \/ a = b.

    Definition localCausalOrder (a b : Event) : Prop :=
    (a ≺ b) /\ loc a = loc b.

    Definition localCausalOrderLe (a b : Event) : Prop :=
    (a ≼ b) /\ loc a = loc b.

    Definition isFirst (e : Event) : Prop :=
    direct_pred e = None.

    Definition localPreds (e : Event) : list Event :=
    projT1 (localPreds_lem e).

    Definition get_first (e : Event) : Event :=
    match localPreds e with
    | [] => e
    | e' :: _ => e'
    end.

    Definition is_first (e : Event) : bool :=
    match direct_pred e with
    | Some _ => false
    | None => true
    end.

    Definition if_not_first (e : Event) (P : Prop) : Prop:=
    ~ isFirst e -> P.

    Definition subEventOrdering_cond (e e' : Event) : Prop :=
    loc e' = loc e -> e ≼ e'.

    Definition subEventOrdering_cond_bool (e e' : Event) : Prop :=
    (if subEventOrdering_cond_dec e e' then true else false) = true.

    Definition mkSubOrderingLe {e e' : Event} (p : e ⊑ e') : subEventOrdering_type e.

    Proof.

    Definition subEventOrdering_causalOrder (e : Event) :
    subEventOrdering_type e
    -> subEventOrdering_type e
    -> Prop.

    Definition subEventOrdering_loc (e : Event) :
    subEventOrdering_type e -> name.

    Definition subEventOrdering_direct_pred (e : Event) :
    subEventOrdering_type e -> option (subEventOrdering_type e).

    Definition subEventOrdering_direct_pred (e : Event) :
    subEventOrdering_type e -> option (subEventOrdering_type e).

    Definition subEventOrdering_trigger (e : Event) :
    subEventOrdering_type e -> msg.

    Definition subEventOrdering_time (e : Event) :
    subEventOrdering_type e -> Qpos.

    Definition subEventOrdering_mode (e : Event) :
    subEventOrdering_type e -> EventStatus.

    Definition subEventOrdering_keys (e : Event) :
    subEventOrdering_type e -> local_key_map.

    Definition subEventOrdering (e : Event) : EventOrdering.

    Proof.

    Definition localPredsLe (e : Event) : list Event := snoc (localPreds e) e.

    
    (*
    Record DirectedData :=
    MkDData
    {
    ddDst  : name;
    ddData : Data
    }.

    Definition LDirectedData := list DirectedData.
*)
    
    Definition Observer := forall eo : EventOrdering, @Event eo -> DirectedMsgs.

    Definition check_auth_data
    (src dst : Event) (* Byzantine source [src] *) : Prop :=
    forall m : AuthMsg,
    In m (get_contained_auth_data (data dst))
    -> verify_auth_msg m (keys src)
    ->
    (* then we have to make sure that s had enough information to generate the
    authenticated message *)
    (
    (* either [src] got the authenticated message from someone else *)
    in_trace m src
    
    \/
    
    (* or it is able to authenticate the message with one of its keys *)
    verify_keys m (keys src)
    ).
*)
    Definition is_system_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_SYSTEM   => true
    | MSG_STATUS_INTERNAL => true
    | MSG_STATUS_EXTERNAL => false
    end.

    Definition is_internal_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_SYSTEM   => false
    | MSG_STATUS_INTERNAL => true
    | MSG_STATUS_EXTERNAL => false
    end.

    Definition is_external_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_SYSTEM   => false
    | MSG_STATUS_INTERNAL => false
    | MSG_STATUS_EXTERNAL => true
    end.

    Definition authenticated_messages_were_sent_or_byz
    (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e (a : AuthenticatedData),
    In a (get_contained_authenticated_data (trigger e))
    -> exists e',
    e' ≺ e (* event e was triggered by an earlier send event e' *)
    /\
    (
    (* if we didn't verify the message then it could come from a Byzantine
    node that is impersonating someone else, without the logic knowing it
    *)
    verify_authenticated_data (loc e) a (keys e) = true
    
    ->
    
    (* e' generated the authentication code *)
    (* QUESTION: Should we say instead that the message was authenticated
    using a subset of the keys? *)
    am_auth a = authenticate (am_data a) (keys e')
    
    /\
    (
    (
    exists dst m,
    
    In a (get_contained_authenticated_data m)
    
    /\
    (* e' sent the message to some node "dst"
    following the protocol as described by F
    (only if the message is the message is internal though),
    which eventually got to e *)
    (is_system_message m = true -> In (MkDMsg dst m) (F eo e'))
    
    /\
    (* e' is the node mentioned in the authenticated message *)
    am_sender (loc e) a = Some (loc e')
    )
    
    \/
    
    (* e' is not the node mentioned in the authenticated message
    because he got the keys of some other e''
    *)
    (
    exists e'',
    e'' ≼ e'
    /\
    (* e' is byzantine because it's using the keys of e'' *)
    isByz e'
    /\
    (* e'' is byzantine because it lost it keys *)
    isByz e''
    /\
    (* the sender mentioned in m is actually e'' and not e' but e' sent the message impersonating e''.
.
.
what a nerve! *)
    Definition has_correct_trace (i : name) :=
    forall e, loc e = i -> isCorrect e.

    Definition have_correct_traces (G : list name) :=
    forall good, In good G -> has_correct_trace good.

    Definition has_correct_trace_bounded (e : Event) :=
    forall e', e' ⊑ e -> isCorrect e'.

    Definition has_correct_trace_before (e : Event) (good : name) :=
    forall e', e' ≼ e -> loc e' = good -> has_correct_trace_bounded e'.

    Definition authenticated_messages_were_sent_non_byz
    (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs):=
    forall (e : Event) (a : AuthenticatedData) (good : name),
    In a (get_contained_authenticated_data (trigger e))
    -> has_correct_trace_before e good
    -> verify_authenticated_data (loc e) a (keys e) = true
    -> am_sender (loc e) a = Some good
    ->
    exists e' dst m,
    e' ≺ e
    /\ am_auth a = authenticate (am_data a) (keys e')
    /\ In a (get_contained_authenticated_data m)
    /\ (is_system_message m = true -> In (MkDMsg dst m) (F eo e'))
    /\ loc e' = good.

    Definition internal_messages_were_sent
    (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e,
    is_internal_message (trigger e) = true
    -> isCorrect e
    ->
    exists e',
    e' ⊏ e (* event e was triggered by an earlier send event e' *)
    /\
    In (MkDMsg (loc e) (trigger e)) (F eo e').

    Definition simple_sent_byz
    (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e (a : AuthenticatedData),
    In a (get_contained_authenticated_data (trigger e))
    ->
    exists e' m,
    e' ≺ e (* event e was triggered by an earlier send event e' *)
    
    /\
    In a (get_contained_authenticated_data m)
    
    /\
    (
    (exists dst, In (MkDMsg dst m) (F eo e'))
    
    \/
    
    isByz e'
    ).

    Definition authenticated_messages_were_sent_or_byz_observer
    (s : Observer)
    := authenticated_messages_were_sent_or_byz s.

    Definition failures_dont_change :=
    forall e1 e2,
    e1 ⊏ e2
    ->
    (
    (*        (isCrashed e1 -> isCrashed e2)
    /\*)
    (isByz e1 -> isByz e2)
    ).

### Inductive


    Inductive Faulty :=
    (*  | crashed   : Faulty*)
    | byzantine : Faulty.

    Inductive EventStatus :=
    | correct
    | faulty (f : Faulty).

    Inductive msg_status :=
    (* messages sent by the system from one replica to another (possibly the same replica) *)
    | MSG_STATUS_SYSTEM
    (* internal message sent the system sent by one replica to itself *)
    | MSG_STATUS_INTERNAL
    (* external messages are sent by processes not specified by the protocol *)
    | MSG_STATUS_EXTERNAL.

### Lemma


    Lemma correct_is_not_byzantine :
    forall (e : Event), isCorrect e -> ~ isByz e.

    Lemma causalOrderLe_refl :
    forall e, e ≼ e.

    Lemma localCausalOrderLe_refl :
    forall (e : Event), e ⊑ e.

    Lemma eo_causal : well_founded causalOrder.

    Proof.

    Lemma local_implies_loc :
    forall (e1 e2 : Event), e1 ⊏ e2 -> loc e1 = loc e2.

    Lemma localLe_implies_loc :
    forall (e1 e2 : Event), e1 ⊑ e2 -> loc e1 = loc e2.

    Lemma localLe_implies_causalLe :
    forall (e1 e2 : Event), e1 ⊑ e2 -> e1 ≼ e2.

    Lemma pred_implies_causal :
    forall (e1 e2 : Event), e1 ⊂ e2 -> e1 ≺ e2.

    Lemma pred_implies_loc :
    forall (e1 e2 : Event), e1 ⊂ e2 -> loc e1 = loc e2.

    Lemma pred_implies_local :
    forall (e1 e2 : Event), e1 ⊂ e2 -> e1 ⊏ e2.

    Lemma local_implies_causal :
    forall (e1 e2 : Event), e1 ⊏ e2 -> e1 ≺ e2.

    Lemma CausalOrderInd :
    forall P : Event -> Prop,
    (forall e, (forall e', e' ≺ e -> P e') -> P e)
    -> forall e, P e.

    Lemma CausalOrderInd_type :
    forall P : Event -> Type,
    (forall e, (forall e', e' ≺ e -> P e') -> P e)
    -> forall e, P e.

    Lemma causal_trans :
    forall (e1 e2 e3 : Event),
    e1 ≺ e2 -> e2 ≺ e3 -> e1 ≺ e3.

    Lemma causal_le_r_trans :
    forall (e1 e2 e3 : Event),
    e1 ≺ e2 -> e2 ≼ e3 -> e1 ≺ e3.

    Lemma causal_le_l_trans :
    forall (e1 e2 e3 : Event),
    e1 ≼ e2 -> e2 ≺ e3 -> e1 ≺ e3.

    Lemma local_trans :
    forall (e1 e2 e3 : Event),
    e1 ⊏ e2 -> e2 ⊏ e3 -> e1 ⊏ e3.

    Lemma local_trans_le_r :
    forall (e1 e2 e3 : Event),
    e1 ⊏ e2 -> e2 ⊑ e3 -> e1 ⊏ e3.

    Lemma local_trans_le_l :
    forall (e1 e2 e3 : Event),
    e1 ⊑ e2 -> e2 ⊏ e3 -> e1 ⊏ e3.

    Lemma local_implies_le :
    forall (e1 e2 : Event), e1 ⊏ e2 -> e1 ⊑ e2.

    Lemma local_pred_le :
    forall (e : Event), (local_pred e) ⊑ e.

    Lemma localCausalOrderInd :
    forall P : Event -> Prop,
    (forall e, (forall e', e' ⊏ e -> P e') -> P e)
    -> forall e, P e.

    Lemma localCausalOrderInd_type :
    forall P : Event -> Type,
    (forall e, (forall e', e' ⊏ e -> P e') -> P e)
    -> forall e, P e.

    Lemma dec_isFirst :
    forall e, decidable (isFirst e).

    Lemma local_pred_is_direct_pred :
    forall e,
    ~ isFirst e
    -> (local_pred e) ⊂ e .

    Lemma local_pred_is_localCausal :
    forall e,
    ~ isFirst e
    -> (local_pred e) ⊏ (e).

    Lemma local_pred_is_causal :
    forall e,
    ~ isFirst e
    -> (local_pred e) ≺ (e).

    Lemma predCausalOrderInd :
    forall P : Event -> Prop,
    (forall e, (forall e', e' ⊂ e -> P e') -> P e)
    -> forall e, P e.

    Lemma predCausalOrderInd_local_pred :
    forall P : Event -> Prop,
    (forall e, (~ isFirst e -> P (local_pred e)) -> P e)
    -> forall e, P e.

    Lemma predCausalOrderInd_type :
    forall P : Event -> Type,
    (forall e, (forall e', e' ⊂ e -> P e') -> P e)
    -> forall e, P e.

    Lemma predCausalOrderInd_local_pred_type :
    forall P : Event -> Type,
    (forall e, (~ isFirst e -> P (local_pred e)) -> P e)
    -> forall e, P e.

    Lemma not_direct_pred :
    forall (e e1 e2 : Event),
    e1 ⊂ e
    -> e2 ⊏ e
    -> e1 <> e2
    -> e2 ⊏ e1.

    Lemma causal_anti_reflexive :
    forall (e : Event), ~ e ≺ e.

    Lemma localCausal_anti_reflexive :
    forall (e : Event), ~ e ⊏ e.

    Lemma pred_anti_reflexive :
    forall (e : Event), ~ e ⊂ e.

    Lemma local_implies_pred_or_local :
    forall (e1 e2 : Event),
    e1 ⊏ e2
    -> (e1 ⊂ e2 [+] {e : Event & e ⊂ e2 /\ e1 ⊏ e}).

    Lemma local_implies_local_or_pred :
    forall (e1 e2 : Event),
    e1 ⊏ e2
    -> (e1 ⊂ e2 [+] {e : Event & e1 ⊂ e /\ e ⊏ e2}).

    Lemma snoc_inj :
    forall {A} (l k : list A) a b,
    snoc l a = snoc k b
    -> l = k /\ a = b.

    Lemma localPreds_lem :
    forall (e : Event),
    {l : list Event
    & forall a b, adjacent a b (snoc l e) <-> (a ⊂ b /\ a ⊏ e) }.

    Lemma snoc_as_app {T} :
    forall (a : T) (l : list T),
    snoc l a = l ++ [a].

    Lemma localPreds_prop1 :
    forall (e e' : Event),
    In e' (localPreds e) <-> e' ⊏ e.

    Lemma if_not_first_if_first :
    forall e P,
    isFirst e
    -> if_not_first e P.

    Lemma if_not_first_implies_or :
    forall e P,
    if_not_first e P
    -> (isFirst e \/ (~ isFirst e /\ P)).

    Lemma localPreds_cond_implies_in :
    forall a b e l,
    adjacent a b l
    -> (forall a b : Event, adjacent a b (snoc l e) -> (a) ⊂ (b) /\ (a) ⊏ (e))
    -> (b) ⊏ (e).

    Lemma localPreds_cond_implies_in2 :
    forall b l x,
    In b l
    -> (forall a b : Event, adjacent a b (snoc l x) -> (a) ⊂ (b))
    -> (b) ⊏ (x).

    Lemma localPreds_cond_implies_in3 :
    forall l2 l1 b,
    In b l1
    -> (forall a b : Event, adjacent a b (l1 ++ l2) -> (a) ⊂ (b))
    -> forall x, In x l2 -> (b) ⊏ (x).

    Lemma localPreds_cond_implies_in4 :
    forall b l x,
    In b l
    -> (forall a b : Event, adjacent a b (x :: l) -> (a) ⊂ (b))
    -> (x) ⊏ (b).

    Lemma adjacent_single :
    forall {T} (a b c : T), ~ adjacent a b [c].

    Lemma pred_implies_local_pred :
    forall a b, (a) ⊂ (b) -> a = local_pred b.

    Lemma pred_implies_not_first :
    forall a b,
    a ⊂ b ->  ~ isFirst b.

    Lemma local_causal_implies_not_first :
    forall a b,
    a ⊏ b ->  ~ isFirst b.

    Lemma isFirst_implies_local_pred_eq :
    forall e, isFirst e -> local_pred e = e.

    Lemma isFirst_implies_localPreds_eq :
    forall e, isFirst e -> localPreds e = [].

    Lemma loc_local_pred :
    forall (e : Event), loc (local_pred e) = loc e.

    Lemma localCausalOrder_if_isFirst :
    forall e1 e2,
    loc e1 = loc e2
    -> isFirst e1
    -> e1 <> e2
    -> e1 ⊏ e2.

    Lemma causalLe_trans :
    forall (e1 e2 e3 : Event),
    e1 ≼ e2 -> e2 ≼ e3 -> e1 ≼ e3.

    Lemma isFirst_loc_implies_causal :
    forall (e e' : Event),
    isFirst e
    -> loc e = loc e'
    -> e ≼ e'.

    Lemma no_local_predecessor_if_first :
    forall (e e' : Event),
    isFirst e
    -> ~ (e' ⊏ e).

    Lemma tri_if_same_loc :
    forall e1 e2,
    loc e1 = loc e2
    -> (e1 ⊏ e2 \/ e1 = e2 \/ e2 ⊏ e1).

    Lemma causal_implies_causalLe :
    forall (e1 e2 : Event), e1 ≺ e2 -> e1 ≼ e2.

    Lemma localLe_trans :
    forall (e1 e2 e3 : Event),
    e1 ⊑ e2 -> e2 ⊑ e3 -> e1 ⊑ e3.

    Lemma subEventOrdering_causalLe_loc_dec :
    forall e e', loc e = loc e' -> decidable (e ≼ e').

    Lemma subEventOrdering_cond_dec :
    forall e e', decidable (subEventOrdering_cond e e').

    Lemma subEventOrdering_cond_bool_iff :
    forall e e',
    subEventOrdering_cond_bool e e'
    <-> subEventOrdering_cond e e'.

    Lemma subEventOrdering_cond_bool_local_pred :
    forall (e e' : Event),
    subEventOrdering_cond_bool e e'
    -> loc e' = loc e
    ->  e <> e'
    -> subEventOrdering_cond_bool e (local_pred e').

    Lemma diff_first_iff_not_first :
    forall (e : Event), e <> get_first e <-> ~ isFirst e.

    Lemma eq_first_iff_first :
    forall (e : Event), e = get_first e <-> isFirst e.

    Lemma subEventOrdering_Deq : forall (e : Event), Deq (subEventOrdering_type e).

    Proof.

    Lemma subEventOrdering_wf : forall (e : Event), well_founded (subEventOrdering_causalOrder e).

    Proof.

    Lemma subEventOrdering_trans :
    forall (e : Event),
    transitive (subEventOrdering_type e) (subEventOrdering_causalOrder e).

    Lemma subEventOrdering_direct_pred_some_implies :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e1 = Some e2
    -> direct_pred e1 = Some (sub_eo_event e e2).

    Lemma subEventOrdering_direct_pred_some_iff :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e1 = Some e2
    <-> direct_pred e1 = Some (sub_eo_event e e2).

    Lemma subEventOrdering_axiom_direct_pred_local :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e1 = Some e2
    -> subEventOrdering_loc e e1 = subEventOrdering_loc e e2.

    Lemma subEventOrdering_axiom_direct_pred_ord :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e1 = Some e2
    -> subEventOrdering_causalOrder e e2 e1.

    Lemma loc_get_first :
    forall (e : Event), loc (get_first e) = loc e.

    Lemma get_first_le :
    forall (e e' : Event), loc e = loc e'-> (get_first e) ≼ e'.

    Lemma get_first_get_first_eq :
    forall (e e' : Event), loc e = loc e'-> get_first e = get_first e'.

    Lemma adjacent_one_element:
    forall a b e, adjacent a b [e] -> a = Nome /\ b = None.

    Lemma subEventOrdering_axiom_direct_pred_first :
    forall (e : Event),
    forall e0 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e0 = None
    ->
    (forall e' : subEventOrdering_type e,
    subEventOrdering_loc e e' = subEventOrdering_loc e e0
    -> e0 <> e'
    -> subEventOrdering_causalOrder e e0 e').

    Lemma causalOrderLe_implies_eq :
    forall e1 e2, (e1) ≼ (e2) -> (e2) ≼ (e1) -> e1 = e2.

    Lemma subEventOrdering_axiom_direct_pred_inj :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_loc e e1 = subEventOrdering_loc e e2
    -> subEventOrdering_direct_pred e e1 = subEventOrdering_direct_pred e e2
    -> e1 = e2.

    Lemma subEventOrdering_axiom_local_order :
    forall (e : Event),
    forall e1 e2 e0 : subEventOrdering_type e,
    subEventOrdering_loc e e1 = subEventOrdering_loc e e2
    -> subEventOrdering_causalOrder e e1 e2
    -> subEventOrdering_direct_pred e e2 = Some e0
    -> e0 = e1 [+] subEventOrdering_causalOrder e e1 e0.

    Lemma subEventOrdering_axiom_causal_time :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_causalOrder e e1 e2
    -> Qpos_lt (subEventOrdering_time e e1) (subEventOrdering_time e e2).

    Lemma trigger_mkSubOrderingLe :
    forall (e e' : Event) (p : e ⊑ e'),
    @trigger (subEventOrdering e) (mkSubOrderingLe p) = trigger e'.

    Lemma trigger_in_subEventOrdering :
    forall (e : Event) (e' : subEventOrdering_type e),
    @trigger (subEventOrdering e) e' = trigger e'.

    Lemma subEventOrdering_loc_as_loc :
    forall (e : Event) (e' : subEventOrdering_type e),
    subEventOrdering_loc e e' = loc e'.

    Lemma localPreds_cond_pred :
    forall l e,
    (forall a b : Event,
    adjacent a b (snoc (snoc l (local_pred e)) e) <-> (a) ⊂ (b) /\ (a) ⊏ (e))
    -> forall a b : Event,
    adjacent a b (snoc l (local_pred e)) <-> (a) ⊂ (b) /\ (a) ⊏ (local_pred e).

    Lemma localPreds_unroll :
    forall e,
    ~ isFirst e
    -> localPreds e
    = snoc (localPreds (local_pred e)) (local_pred e).

    Lemma implies_authenticated_messages_were_sent_non_byz :
    forall F,
    authenticated_messages_were_sent_or_byz F
    -> authenticated_messages_were_sent_non_byz F.

## Component.v
### Definition


    Definition CompName := String.
string.

    
    Definition p_nproc (p : Type) := (CompName * p)%type.

    Definition p_procs (p : Type) := list (p_nproc p).

    
    Definition M_p (p : Type) (A : Type) := p_procs p -> (p_procs p * A)%type.

    Definition n_proc  (n : nat) := M_Process n.

    Definition n_nproc (n : nat) := (CompName * n_proc n)%type.

    Definition n_procs (n : nat) := list (n_nproc n).

    
    Definition M_n (n : nat) (A : Type) := n_procs n -> (n_procs n * A)%type.

    Definition M_Update (n : nat) (S : Type) := S -> cio_I -> M_n n (option S * cio_O).

    
    Definition ret {A} (n : nat) (a : A) : M_n n (A) := fun s => (s, a).

    Definition bind {A B} {n:nat} (m : M_n n A) (f : A -> M_n n B) : M_n n B :=
    fun s =>
    let (s1,a) := m s in
    let (s2,b) := f a s1 in
    (s2,b).

    Definition lift_M {m}
    (x : M_p (M_Process m) (MP_Process (M_Process m) * cio_O))
    : M_n m (M_Process (S m) * cio_O) :=
    fun ps =>
    let (k, qo) := x ps in
    let (q, o) := qo in
    (k, (injL(q), o)).

    Definition MP_haltedProc (n : nat) : MP_Process (M_Process n) := m_proc None.

    
    Definition M_haltedProc : M_Process 0 := m_proc None.

    Definition incr_n_proc {n} (p : n_proc n) : n_proc (S n) := inr p.

    
    Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    let (m,q) := p in
    (m, incr_n_proc q).

    Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

    Definition decr_n_proc {n} : n_proc n -> option (n_proc (Init.
Nat.
pred n)) :=
    match n with
    | 0 => fun p => Some p
    | S m => fun p =>
    match p with
    | inl _ => None
    | inr q => Some q
    end
    end.

    Definition decr_n_nproc {n} (np : n_nproc n) : option (n_nproc (Init.
Nat.
pred n)) :=
    let (m,p) := np in
    match decr_n_proc p with
    | Some q => Some (m,q)
    | None => None
    end.

    Definition decr_n_procs {n} (ps : n_procs n) : n_procs (Init.
Nat.
pred n) :=
    mapOption decr_n_nproc ps.

    Definition incr_pred_n_proc {n} : n_proc (pred n) -> n_proc n :=
    match n with
    | 0 => fun p => p
    | S m => inr
    end.

    Definition incr_pred_n_nproc {n} (p : n_nproc (pred n)) : n_nproc n :=
    let (m,q) := p in
    (m, incr_pred_n_proc q).

    Definition incr_pred_n_procs {n} (ps : n_procs (pred n)) : n_procs n :=
    map incr_pred_n_nproc ps.

    Definition lift_M2 {n} (m : M_n (pred n) (M_Process n * cio_O))
    : M_n (pred (S n)) (M_Process (S n) * cio_O) :=
    fun (ps : n_procs n) =>
    match m (decr_n_procs ps) with
    | (ps',(p',o)) => (incr_pred_n_procs ps', (incr_n_proc p',o))
    end.

    Definition call_proc {n:nat} (nm : CompName) (i : cio_I) : M_n n cio_O :=
    fun (l : n_procs n) =>
    match find_name nm l with
    | Some pr =>
    match app_m_proc pr i with
    | Some f =>
    match f (decr_n_procs l) with
    | (l',(pr',o)) => (replace_subs (replace_name nm pr' l) l',o)
    end
    | None => (l,cio_default_O)
    end
    | None => (l,cio_default_O)
    end.

    (*Definition B_update (i : nat) : M_Update unit nat nat :=
    fun s n =>
    fun procs =>
    let (ps,out) :=
    match find_name "A" procs with
    | Some p =>
    match app_proc p n with
    | Some (q,out) => ([("A",q)],out)
    | None => ([],0)
    end
    | None => ([],0)
    end in
    (ps, (Some s, out)).
*)
    Definition build_m_process {n} {ST}
    (upd : M_Update n ST)
    (s   : ST) : M_Process (S n) :=
    inl (build_mp_process upd s).

### Inductive


    CoInductive MP_Process (p : Type) : Type :=
    | m_proc (f : option (cio_I -> M_p p (MP_Process p * cio_O))).

## CorrectTrace.v
### Definition


    Definition has_correct_trace (eo : EventOrdering) (i : name) :=
    forall e, loc e = i -> isCorrect e.

    Definition node_has_correct_trace (eo : EventOrdering) (i : node_type) :=
    has_correct_trace eo (node2name i).

    Definition have_correct_traces (eo : EventOrdering) (G : list name) :=
    forall good, In good G -> has_correct_trace eo good.

    Definition nodes_have_correct_traces (eo : EventOrdering) (G : list node_type) :=
    have_correct_traces eo (map node2name G).

    Definition has_correct_trace_bounded {eo : EventOrdering} (e : Event) :=
    forall e', e' ⊑ e -> isCorrect e'.

    Definition have_correct_traces_before
    {eo : EventOrdering}
    (G  : list name)
    (L  : list Event) :=
    forall good e1 e2,
    In good G
    -> In e2 L
    -> e1 ≼ e2
    -> loc e1 = good
    -> has_correct_trace_bounded e1.

    Definition nodes_have_correct_traces_before
    {eo : EventOrdering}
    (G  : list node_type)
    (L  : list Event) :=
    have_correct_traces_before (map node2name G) L.

    Definition has_correct_trace_before {eo : EventOrdering} (e : Event) (good : name) :=
    forall e', e' ≼ e -> loc e' = good -> has_correct_trace_bounded e'.

    Definition node_has_correct_trace_before {eo : EventOrdering} (e : Event) (good : node_type) :=
    has_correct_trace_before e (node2name good).

    Definition authenticated_messages_were_sent_non_byz
    (eo : EventOrdering)
    (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs):=
    forall (e : Event) (a : AuthenticatedData) (good : name),
    auth_data_in_trigger a e
    -> has_correct_trace_before e good
    -> verify_authenticated_data (loc e) a (keys e) = true
    -> data_auth (loc e) (am_data a) = Some good
    ->
    exists e' m dst delay,
    e' ≺ e
    /\ am_auth a = authenticate (am_data a) (keys e')
    /\ In a (get_contained_authenticated_data m)
    /\ (is_protocol_message m = true -> In (MkDMsg m dst delay) (F eo e'))
    /\ loc e' = good.

    Definition exists_at_most_f_faulty {eo : EventOrdering} (L : list Event) (F : nat) :=
    exists (faulty : list node_type),
    length faulty <= F
    /\
    forall e1 e2,
    In e2 L
    -> e1 ≼ e2
    -> ~ In (loc e1) (map node2name faulty)
    -> has_correct_trace_bounded e1.

### Lemma


    Require Export EventOrderingLemmas.

    
    
    Section CorrectTrace.

    Lemma nodes_have_correct_traces_before_causal_le :
    forall (eo : EventOrdering) R (e e' : Event),
    e' ≼ e
    -> nodes_have_correct_traces_before R [e]
    -> nodes_have_correct_traces_before R [e'].

    Lemma nodes_have_correct_traces_before_two_left :
    forall (eo : EventOrdering) R (e1 e2 : Event),
    nodes_have_correct_traces_before R [e1, e2]
    -> nodes_have_correct_traces_before R [e1].

    Lemma nodes_have_correct_traces_before_two_right :
    forall (eo : EventOrdering) R (e1 e2 : Event),
    nodes_have_correct_traces_before R [e1, e2]
    -> nodes_have_correct_traces_before R [e2].

    Lemma nodes_have_correct_traces_before_causal :
    forall (eo : EventOrdering) R (e e' : Event),
    e' ≺ e
    -> nodes_have_correct_traces_before R [e]
    -> nodes_have_correct_traces_before R [e'].

    Lemma has_correct_trace_bounded_preserves_local_le :
    forall (eo : EventOrdering) e e',
    e' ⊑ e
    -> has_correct_trace_bounded e
    -> has_correct_trace_bounded e'.

    Lemma has_correct_trace_bounded_implies_message :
    forall {eo : EventOrdering} (e e' : Event),
    has_correct_trace_bounded e
    -> e' ⊑ e
    -> exists m, trigger e' = Some m.

    Lemma implies_authenticated_messages_were_sent_non_byz :
    forall (eo : EventOrdering) F,
    authenticated_messages_were_sent_or_byz F
    -> authenticated_messages_were_sent_non_byz eo F.

    Lemma exists_at_most_f_faulty_two_left :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
    exists_at_most_f_faulty [e1, e2] F
    -> exists_at_most_f_faulty [e1] F.

    Lemma exists_at_most_f_faulty_two_right :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
    exists_at_most_f_faulty [e1, e2] F
    -> exists_at_most_f_faulty [e2] F.

    Lemma implies_atmost_f_faulty_two_causal_le :
    forall (eo : EventOrdering) (e1 e2 e1' e2' : Event) F,
    e1' ≼ e1
    -> e2' ≼ e2
    -> exists_at_most_f_faulty [e1,e2] F
    -> exists_at_most_f_faulty [e1',e2'] F.

    Lemma implies_atmost_f_faulty_two_sym :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
    exists_at_most_f_faulty [e1,e2] F
    -> exists_at_most_f_faulty [e2,e1] F.

    Lemma exists_at_most_f_faulty_preserves_causal :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
    e1 ≺ e2
    -> exists_at_most_f_faulty [e2] F
    -> exists_at_most_f_faulty [e1] F.

    Lemma exists_at_most_f_faulty_preserves_causal_le :
    forall (eo : EventOrdering) (e1 e2 : Event) F,
    e1 ≼ e2
    -> exists_at_most_f_faulty [e2] F
    -> exists_at_most_f_faulty [e1] F.

    Lemma exists_at_most_f_faulty_twice :
    forall (eo : EventOrdering) (e : Event) F,
    exists_at_most_f_faulty [e] F
    -> exists_at_most_f_faulty [e, e] F.

    Lemma implies_atmost_f_faulty_local_pred :
    forall (eo : EventOrdering) (e : Event) F,
    exists_at_most_f_faulty [e] F
    -> exists_at_most_f_faulty [local_pred e] F.

    Lemma implies_atmost_f_faulty_causal :
    forall (eo : EventOrdering) (e e' : Event) F,
    e' ≺ e
    -> exists_at_most_f_faulty [e] F
    -> exists_at_most_f_faulty [e'] F.

    Lemma implies_atmost_f_faulty_causal_le :
    forall (eo : EventOrdering) (e e' : Event) F,
    e' ≼ e
    -> exists_at_most_f_faulty [e] F
    -> exists_at_most_f_faulty [e'] F.

    Lemma there_is_one_correct_before :
    forall (eo : EventOrdering) (L : list node_type) (E : list Event) (F : nat),
    no_repeats L
    -> F + 1 <= length L
    -> exists_at_most_f_faulty E F
    -> exists (correct : node_type),
    In correct L
    /\ forall e, In e E -> has_correct_trace_before e (node2name correct).

    Lemma has_correct_trace_before_preserves_local_le :
    forall (eo : EventOrdering) e e' k,
    e' ⊑ e
    -> has_correct_trace_before e k
    -> has_correct_trace_before e' k.

    Lemma has_correct_trace_before_preserves_causal_le :
    forall (eo : EventOrdering) e e' k,
    e' ≼ e
    -> has_correct_trace_before e k
    -> has_correct_trace_before e' k.

    Lemma some_trigger_implies_isCorrect :
    forall (eo : EventOrdering) (e : Event) x,
    trigger e = Some x
    -> isCorrect e.

    Lemma has_correct_trace_before_local_pred_implies :
    forall (eo : EventOrdering) (e : Event) i,
    loc e = i
    -> isCorrect e
    -> has_correct_trace_before (local_pred e) i
    -> has_correct_trace_before e i.

    Lemma node_has_correct_trace_before_preserves_local_le :
    forall (eo : EventOrdering) e e' k,
    e' ⊑ e
    -> node_has_correct_trace_before e k
    -> node_has_correct_trace_before e' k.

    Lemma node_has_correct_trace_before_preserves_causal_le :
    forall (eo : EventOrdering) e e' k,
    e' ≼ e
    -> node_has_correct_trace_before e k
    -> node_has_correct_trace_before e' k.

    Lemma node_has_correct_trace_before_preserves_causal :
    forall {eo : EventOrdering} (e1 e2 : Event) i,
    e1 ≺ e2
    -> node_has_correct_trace_before e2 i
    -> node_has_correct_trace_before e1 i.

    Lemma select_good_guys_before :
    forall (eo : EventOrdering) (L : list node_type) (E : list Event) F,
    no_repeats L
    -> exists_at_most_f_faulty E F
    -> exists (G : list node_type),
    subset G L
    /\ length L - F <= length G
    /\ no_repeats G
    /\ forall e good,
    In e E
    -> In good G
    -> node_has_correct_trace_before e good.

## AuthMsg.v
### Definition


    Definition verify_op (d : Data) (mac : Token) (kop : option key) : bool :=
    match kop with
    | Some k => verify d k mac
    | None => false
    end.

    Definition verify_auth_data (d : auth_data) (k : key) : bool :=
    verify (adData d) k (adToken d).

    Definition verify_auth_data_op (d : auth_data) (kop : option key) : bool :=
    match kop with
    | Some k => verify_auth_data d k
    | None => false
    end.

    Definition verify_authenticated_data_key (n : name) (m : AuthenticatedData) (k : receiving_key) : bool :=
    existsb (fun token => verify (am_data m) n k token) (am_auth m).

    Definition verify_authenticated_data_keys (n : name) (m : AuthenticatedData) (ks : receiving_keys) : bool :=
    existsb (verify_authenticated_data_key n m) ks.

    Definition verify_auth_msg_op (d : AuthMsg) (kop : option key) : bool :=
    match kop with
    | Some k => verify_auth_msg_key d k
    | None => false
    end.

    Definition am_sender (slf : name) (m : AuthenticatedData) : option name :=
    data_auth slf (am_data m).

    Definition verify_authenticated_data
    (slf  : name)
    (m    : AuthenticatedData)
    (keys : local_key_map) : bool :=
    match data_auth slf (am_data m) with
    | Some name => verify_authenticated_data_keys name m (lookup_receiving_keys keys name)
    | None => false
    end.

    Definition verify_one_auth_data
    (slf : name)
    (km  : local_key_map)
    (a   : AuthenticatedData) : bool :=
    verify_authenticated_data slf a km.

    Definition verify_keys_b (d : auth_data) (keys : local_key_map) : bool :=
    existsb (fun dk => verify_auth_data d (dk_key dk)) keys.

    Definition verify_keys (d : auth_data) (keys : local_key_map) : Prop :=
    verify_keys_b d keys = true.

    Definition verify_mac_b (d : Data) (mac : Token) (keys : local_key_map) : bool :=
    verify_keys_b (MkAuthData d mac) keys.

    Definition verify_macs_b (d : Data) (macs : Tokens) (keys : local_key_map) : bool :=
    existsb (fun mac => verify_mac_b d mac keys) macs.

    Definition verify_macs (d : Data) (macs : Tokens) (keys : local_key_map) : Prop :=
    verify_macs_b d macs keys = true.

    Definition verify_macs_with_name_b
    (d    : Data)
    (macs : Tokens)
    (keys : local_key_map)
    (n    : name) : bool :=
    match lookup_key keys n with
    | Some key =>
    existsb
    (fun mac => verify_auth_data (MkAuthData d mac) key)
    macs
    | None => false
    end.

## Msg.v
### Definition


    Definition DirectedMsgs := list DirectedMsg.

    
    End Node.

## ComponentSM_non_dep_IO.v
### Definition


    Definition CompName := String.
string.

    
    Definition p_nproc (p : Type) := (CompName * p)%type.

    Definition p_procs (p : Type) := list (p_nproc p).

    
    Definition M_p (p : Type) (PO : Type) := p_procs p -> (p_procs p * PO)%type.

    Definition MP_Update (p : Type) (S : Type) := S -> cio_I -> M_p p (option S * cio_O).

    
    Record MP_StateMachine (p : Type) : Type :=
    MkMPSM
    {
    sm_type   : Type;
    sm_halted : bool;
    sm_update :> MP_Update p sm_type;
    sm_state  : sm_type;
    }.

    Definition n_proc  (n : nat) := M_StateMachine n.

    Definition n_nproc (n : nat) := (CompName * n_proc n)%type.

    Definition n_procs (n : nat) := list (n_nproc n).

    
    Definition M_n (n : nat) (PO : Type) := n_procs n -> (n_procs n * PO)%type.

    Definition M_Update (n : nat) (S : Type) := S -> cio_I -> M_n n (option S * cio_O).

    
    Definition ret {A} (n : nat) (a : A) : M_n n (A) := fun s => (s, a).

    Definition bind {A B} {n:nat} (m : M_n n A) (f : A -> M_n n B) : M_n n B :=
    fun s =>
    let (s1,a) := m s in
    let (s2,b) := f a s1 in
    (s2,b).

    Definition MP_haltedSM {S} (n : nat) (d : S) : MP_StateMachine (M_StateMachine n) :=
    MkMPSM
    S
    true
    (fun s i => ret _ (None, cio_default_O))
    d.

    Definition M_haltedSM {S} (d : S) : M_StateMachine 0 :=
    MkMPSM
    S
    true
    (fun s i p => (p, (None, cio_default_O)))
    d.

    Definition incr_n_proc {n} (p : n_proc n) : n_proc (S n) := inr p.

    
    Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    let (m,q) := p in
    (m, incr_n_proc q).

    Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

    Definition decr_n_proc {n} : n_proc n -> option (n_proc (Init.
Nat.
pred n)) :=
    match n with
    | 0 => fun p => Some p
    | S m => fun p =>
    match p with
    | inl _ => None
    | inr q => Some q
    end
    end.

    Definition decr_n_nproc {n} (np : n_nproc n) : option (n_nproc (Init.
Nat.
pred n)) :=
    let (m,p) := np in
    match decr_n_proc p with
    | Some q => Some (m,q)
    | None => None
    end.

    Definition decr_n_procs {n} (ps : n_procs n) : n_procs (Init.
Nat.
pred n) :=
    mapOption decr_n_nproc ps.

    Definition incr_pred_n_proc {n} : n_proc (pred n) -> n_proc n :=
    match n with
    | 0 => fun p => p
    | S m => inr
    end.

    Definition incr_pred_n_nproc {n} (p : n_nproc (pred n)) : n_nproc n :=
    let (m,q) := p in
    (m, incr_pred_n_proc q).

    Definition incr_pred_n_procs {n} (ps : n_procs (pred n)) : n_procs n :=
    map incr_pred_n_nproc ps.

    Definition lift_M {m}
    (x : M_p (M_StateMachine m) (MP_StateMachine (M_StateMachine m) * cio_O))
    : M_n m (M_StateMachine (S m) * cio_O) :=
    fun ps =>
    let (k, qo) := x ps in
    let (q, o) := qo in
    (k, (injL(q), o)).

    Definition lift_M2 {n} (m : M_n (pred n) (M_StateMachine n * cio_O))
    : M_n (pred (S n)) (M_StateMachine (S n) * cio_O) :=
    fun (ps : n_procs n) =>
    match m (decr_n_procs ps) with
    | (ps',(p',o)) => (incr_pred_n_procs ps', (incr_n_proc p',o))
    end.

    Definition sm_s_to_sm {m}
    (sm : MP_StateMachine (M_StateMachine m))
    (x : M_p (M_StateMachine m) (option (sm_type sm) * cio_O))
    : M_p (M_StateMachine m) (MP_StateMachine (M_StateMachine m) * cio_O) :=
    fun ps =>
    let (ps', so) := x ps in
    let (ops,o) := so in
    match ops with
    | Some s =>
    (ps',
    (MkMPSM
    (sm_type   sm)
    (sm_halted sm)
    (sm_update sm)
    s,o))
    | None =>
    (ps',
    (MkMPSM
    (sm_type   sm)
    true
    (sm_update sm)
    (sm_state  sm),
    o))
    end.

    Definition call_proc {n:nat} (nm : CompName) (i : cio_I) : M_n n cio_O :=
    fun (l : n_procs n) =>
    match find_name nm l with
    | Some pr =>
    match app_m_proc pr i with
    | Some f =>
    match f (decr_n_procs l) with
    | (l',(pr',o)) => (replace_subs (replace_name nm pr' l) l',o)
    end
    | None => (l,cio_default_O)
    end
    | None => (l,cio_default_O)
    end.

    Definition build_mp_sm {n}
    {S}
    (upd : M_Update n S)
    (s   : S) : MP_StateMachine (M_StateMachine n) :=
    MkMPSM S false upd s.

    Definition build_m_sm {n}
    {St}
    (upd : M_Update n St)
    (s   : St) : M_StateMachine (S n) :=
    inl (build_mp_sm upd s).

## CorrectKeys.v
### Definition


    Definition correct_keys {F}
    (sm : MUSystem F)
    (K  : forall (i : name), F i -> local_key_map)
    (eo : EventOrdering) : Prop :=
    forall (e : Event) (i : name) (s : F i),
    has_correct_trace_before e i
    -> state_sm_before_event (sm i) e = Some s
    -> keys e = K i s.

## Process.v
### Definition


    Definition MProcess := Process msg (@DirectedMsgs pn pm).

    
    (* update function that can halt --- This is the one we're using *)
    Definition Update (S I O : Type) := S -> I -> (option S * O).

    Definition MUpdate (S : Type) := Update S msg (@DirectedMsgs pn pm).

    
    Definition haltedProc {I O} : Process I O := proc None.

    Definition counter_update : Update nat nat nat :=
    fun s i => (Some (s + i), s + i).

    Definition counter_proc (s : nat) : Process nat nat :=
    build_process counter_update 0.

    Definition mkSM {I O S} (upd : Update S I O) (s : S) := MkSM false upd s.

    
    
    (* Simple state machines that never halts *)
    Definition SUpdate (S I O : Type) := S -> I -> (S * O).

    Definition MSUpdate (S : Type) := SUpdate S msg (@DirectedMsgs pn pm).

    (* ??? *)
    Definition S2Update {S I O} (upd : SUpdate S I O) : Update S I O :=
    fun s i => let (s',o) := upd s i in (Some s', o).

    Definition mkSSM {I O S} (upd : SUpdate S I O) (s : S) :=
    mkSM (S2Update upd) s.

    Definition NStateMachine S I O := name -> StateMachine S I O.

    
    Definition MStateMachine S := StateMachine S msg DirectedMsgs.

    Definition NMStateMachine S := name -> MStateMachine S.

    
    (* a bunch of coercions to named state machines *)
    Definition StateMachinetoNStateMachine {S I O} (s : StateMachine S I O) : NStateMachine S I O :=
    fun _ => s.

    Definition MStateMachinetoNMStateMachine {S} (s : MStateMachine S) : NMStateMachine S :=
    fun _ => s.

    Definition MStateMachinetoNStateMachine {S} (s : MStateMachine S) :  NStateMachine S msg DirectedMsgs :=
    fun _ => s.

    Definition sm2option {S I O} (s : StateMachine S I O) : option (StateMachine S I O) :=
    if sm_halted s then None else Some s.

    Definition haltedSM {S I O} (s : S) (o : O) : StateMachine S I O :=
    MkSM true (fun _ _ => (None, o)) s.

    Definition LhaltedSM {S I O} (s : S) : StateMachine S I (list O) := haltedSM s [].

    Definition MhaltedSM {S} (s : S) : MStateMachine S := LhaltedSM s.

    Definition updState {S I O}
    (c : StateMachine S I O)
    (s : S) : StateMachine S I O :=
    MkSM (sm_halted c) (sm_update c) s.

    Definition halts {S I O} (c : StateMachine S I O) : StateMachine S I O :=
    MkSM true (sm_update c) (sm_state c).

    Definition force_sm {S I O T} (sm : StateMachine S I O) (F : StateMachine S I O -> T) : T :=
    match sm with
    | MkSM h upd st => F (MkSM h upd st)
    end.

    Definition run_sm {S I O}
    (c : StateMachine S I O)
    (i : I) : option (StateMachine S I O * O) :=
    if sm_halted c then None
    else
    match sm_update c (sm_state c) i with
    | (Some s, o) => force_sm (updState c s) (fun sm => Some (sm, o))
    | (None, o) => force_sm (halts c) (fun sm => Some (sm, o))
    end.

    Definition lrun_sm {S I O}
    (c : StateMachine S I (list O))
    (i : I) : StateMachine S I (list O) * list O :=
    if sm_halted c then (c, [])
    else
    match sm_update c (sm_state c) i with
    | (Some s, o) => force_sm (updState c s) (fun sm => (sm, o))
    | (None, o) => force_sm (halts c) (fun sm => (sm, o))
    end.

    Definition ret {I T} (a : T) : StateMachine unit I (list T) :=
    mkSM (fun state msg => (None, [a])) tt.

    Definition nret {I T} (a : T) : NStateMachine unit I (list T) :=
    fun slf => ret a.

    Definition counter_sm : StateMachine nat nat nat :=
    mkSM (fun s i => (Some (s + i), s)) 0.

    Definition counter_sm2 : StateMachine nat nat nat :=
    updState counter_sm 10.

    Definition USystem (F : name -> Type) I O : Type :=
    forall n : name, StateMachine (F n) I O.

    Definition MUSystem (F : name -> Type) : Type := USystem F msg (@DirectedMsgs pn pm).

    
    (* first update the current state, and then apply some function f to the result of
    update and return that optput
    e.
g.
 state is counter; increment it, but as output send only digest of counter *)
    Definition OnUpdate {S A B C} (f : B -> C) (upd : Update S A B) : Update S A C :=
    fun s a =>
    match upd s a with
    | (s',b) => (s',f b)
    end.

    Definition MLoop : MProcess := looping_process msg (@DirectedMsgs pn pm) [].

    *)
    
    Definition System := name -> MProcess.

    Definition app_proc {A B} (p : Process A B) (a : A) : option (Process A B * B) :=
    match p with
    | proc o => option_map (fun f => f a) o
    end.

    Definition app_proc_def {A B} (p : Process A B) (a : option A) (b : B) : Process A B * B :=
    match a with
    | Some a =>
    match p with
    | proc (Some f) => f a
    | _ => (p, b)
    end
    | None => (p,b)
    end.

    Definition oplist (A : Type) := list (option A).

    
    Fixpoint run_process_on_list {A B} (p : Process A B) (l : oplist A) : Process A B :=
    match l with
    | [] => p
    | Some a :: l =>
    match app_proc p a with
    | Some (p, _) => run_process_on_list p l
    | None => haltedProc
    end
    | None :: _ => haltedProc
    end.

    Definition build_process_opt {S I O}
    (upd : Update S I O)
    (sop : option S) : Process I O :=
    match sop with
    | Some s => build_process upd s
    | None => haltedProc
    end.

    Definition run_process_on_event
    (p  : MProcess)
    {eo : EventOrdering}
    (e  : Event) : MProcess * DirectedMsgs :=
    app_proc_def
    (run_process_on_list
    p
    (map trigger (@localPreds pn pk pm eo e)))
    (trigger e)
    [].

    Definition output_process_on_event
    (p  : MProcess)
    {eo : EventOrdering}
    (e  : Event) : DirectedMsgs :=
    snd (run_process_on_event p e).

    Definition op_update {S I O}
    (p : Update S I O)
    (s : S)
    (o : option I) : option (option S * O) :=
    match o with
    | Some i => Some (p s i)
    | None => None
    end.

    Definition op_output {S I O}
    (p : Update S I O)
    (s : S)
    (o : option I) : option O :=
    option_map snd (op_update p s o).

    Definition op_state {S I O}
    (p : Update S I O)
    (s : S)
    (o : option I) : option S :=
    map_option fst (op_update p s o).

    Definition run_update_on_event {S O}
    (s  : S)
    (p  : Update S msg O)
    {eo : EventOrdering}
    (e  : Event) : option (option S * O) :=
    map_option
    (fun s' => op_update p s' (trigger e)) (*???*)
    (run_update_on_list s p (map trigger (@localPreds pn pk pm eo e))).

    Definition output_update_on_event {S O}
    (s  : S)
    (p  : Update S msg O)
    {eo : EventOrdering}
    (e  : Event) : option O :=
    option_map snd (run_update_on_event s p e).

    Definition state_sm_before_event {S O}
    (c  : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event) : option S :=
    run_update_on_list
    (sm_state c)
    (sm_update c)
    (map trigger (@localPreds pn pk pm eo e)).

    Definition run_sm_on_event_state {S O}
    (c  : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event) : option (option S * O) :=
    run_update_on_event
    (sm_state c)
    (sm_update c)
    e.

    Definition state_sm_on_event {S O}
    (sm : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event) : option S :=
    map_option fst (run_sm_on_event_state sm e).

    Definition run_sm_on_event {S O}
    (c  : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event) : option (StateMachine S msg O * O) :=
    match run_sm_on_event_state c e with
    | Some (Some s, o) => Some (mkSM (sm_update c) s, o)
    | Some (None, o) => Some (halts c, o)
    | None => None
    end.

    Definition output_sm_on_event {S O}
    (c  : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event) : option O :=
    option_map snd (run_sm_on_event_state c e).

    Definition run_system_on_event_sm {F O}
    (s  : USystem F msg O)
    {eo : EventOrdering}
    (e  : Event) : option (StateMachine (F (loc e)) msg O * O) :=
    run_sm_on_event (s (loc e)) e.

    Definition output_system_on_event {S O}
    (s  : USystem S msg O)
    {eo : EventOrdering}
    (e  : Event) : option O :=
    option_map snd (run_system_on_event_sm s e).

    Definition run_sm_on_list {S I O}
    (c : StateMachine S I O)
    (l : oplist I) : option S :=
    run_update_on_list (sm_state c) (sm_update c) l.

    Definition state_of_sm_at_start_of_event {S O}
    (c  : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event) : option S :=
    run_sm_on_list c (map trigger (@localPreds pn pk pm eo e)).

    Definition process_satisfies_observer
    (n   : name)
    (p   : MProcess)
    (obs : Observer) :=
    forall (eo : EventOrdering) e,
    n = loc e
    -> obs eo e = output_process_on_event p e.

    Definition system_satisfies_observer
    (sys : System)
    (obs : Observer) :=
    forall (eo : EventOrdering) e,
    obs eo e = output_process_on_event (sys (loc e)) e.

    Definition process2observer (n : name) (p : MProcess) : Observer :=
    fun (eo : EventOrdering) (e : Event) =>
    if name_dec n (loc e)
    then output_process_on_event p e
    else [].

    Definition process_satisfies_process2observer :
    forall (p : MProcess) n,
    process_satisfies_observer n p (process2observer n p).

    Definition authenticated_messages_were_sent_or_byz_proc
    (eo : EventOrdering) (p : MProcess) :=
    @authenticated_messages_were_sent_or_byz
    pd
    pn
    pk
    pat
    paf
    pm
    eo
    pda
    cad
    gms
    (*      authMsg2Msg*)
    (fun eo e => @output_process_on_event p eo e).

    Definition authenticated_messages_were_sent_non_byz_proc
    (eo : EventOrdering) (p : MProcess) :=
    @authenticated_messages_were_sent_non_byz
    pd
    pn
    pk
    pm
    pat
    paf
    pda
    cad
    gms
    eo
    (fun eo e => @output_process_on_event p eo e).

    Definition authenticated_messages_were_sent_or_byz_sys
    (eo : EventOrdering) (sys : System) :=
    forall n : name, authenticated_messages_were_sent_or_byz_proc eo (sys n).

    Definition authenticated_messages_were_sent_non_byz_sys
    (eo : EventOrdering) (sys : System) :=
    forall n : name, authenticated_messages_were_sent_non_byz_proc eo (sys n).

    (*  Definition DUSystem := USystem Data (@LDirectedData Data n).
*)
    
    (* apply history with last event *)
    Definition output_system_on_event_ldata {S}
    (s  : MUSystem S)
    {eo : EventOrdering}
    (e  : Event) : DirectedMsgs :=
    olist2list (output_system_on_event s e).

    Definition loutput_sm_on_event {S O}
    (c  : StateMachine S msg (list O))
    {eo : EventOrdering}
    (e  : Event) : list O :=
    olist2list (output_sm_on_event c e).

    Definition ooutput_sm_on_event {S O}
    (c  : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event) : list O :=
    opt2list (output_sm_on_event c e).

    Definition op_outputs {S I O}
    (p : Update S I (list O))
    (s : S)
    (o : option I) : list O :=
    match option_map snd (op_update p s o) with
    | Some l => l
    | None => []
    end.

    Definition option_compose {A B C} (f : B -> C) (g : A -> option B) (a : A) : option C :=
    match g a with
    | Some b => Some (f b)
    | None => None
    end.

    Definition authenticated_messages_were_sent_or_byz_usys
    {S} (eo : EventOrdering) (s : MUSystem S) :=
    @authenticated_messages_were_sent_or_byz
    pd
    pn
    pk
    pat
    paf
    pm
    eo
    pda
    cad
    gms
    (fun eo e => @output_system_on_event_ldata _ s eo e).

    Definition authenticated_messages_were_sent_non_byz_usys
    {S} (eo : EventOrdering) (s : MUSystem S) :=
    @authenticated_messages_were_sent_non_byz
    pd
    pn
    pk
    pm
    pat
    paf
    pda
    cad
    gms
    eo
    (fun eo e => @output_system_on_event_ldata _ s eo e).

    Definition internal_messages_were_sent_usys
    {S} (eo : EventOrdering) (s : MUSystem S) :=
    @internal_messages_were_sent
    pn
    pk
    pm
    eo
    gms
    (fun eo e => @output_system_on_event_ldata _ s eo e).

    Definition sm_on_list {S I O}
    (sm : StateMachine S I O)
    (l  : oplist I) : StateMachine S I O :=
    match run_sm_on_list sm l with
    | Some s => updState sm s
    | None => halts sm
    end.

    Definition option_compose2 {A B C} (f : B -> option C) (g : A -> option B) (a : A) : option C :=
    match g a with
    | Some b => f b
    | None => None
    end.

    Definition ite_first {A} {eo : EventOrdering} (e : Event) (a b : A) : A :=
    if dec_isFirst e then a else b.

    (*Definition state_sm_on_local_pred_event {S O}
    (sm : StateMachine S msg O)
    (eo : EventOrdering)
    (e  : Event) :=
    ite_first
    e
    (Some (sm_state sm))
    (state_sm_on_event sm eo (local_pred e)).
*)
    Definition opt_val {T} (top : option T) (d : T) : T :=
    match top with
    | Some t => t
    | None => d
    end.

    Definition SM_state_before_event {S SX U}
    (sm : StateMachine (S * SX) msg U)
    {eo : EventOrdering}
    (e  : Event)
    (s  : S) : Prop :=
    match state_sm_before_event sm e with
    | Some (x,_) => x = s
    | None => False
    end.

    Definition SM_state_on_event {S SX U}
    (sm : StateMachine (S * SX) msg U)
    {eo : EventOrdering}
    (e  : Event)
    (s  : S) : Prop :=
    match state_sm_on_event sm e with
    | Some (x,_) => x = s
    | None => False
    end.

    Definition no_loutput_sm_on_event_prior_to {S O}
    (X  : StateMachine S msg (list O))
    {eo : EventOrdering}
    (e  : Event) : Prop :=
    forall e' x, e' ⊏ e -> ~ In x (loutput_sm_on_event X e').

    Definition state_sm_before_event_exists {S O}
    (X  : StateMachine S msg (list O))
    {eo : EventOrdering}
    (e  : Event) : Prop :=
    exists s,  state_sm_before_event X e = Some s.

### Inductive


    CoInductive Process (I O : Type) : Type :=
    | proc (f : option (I -> (Process I O * O))).

### Lemma


    Require Export EventOrderingLemmas.

    
    
    Section Process.

    Lemma run_process_on_list_haltedProc :
    forall {I O} l, @run_process_on_list I O haltedProc l = haltedProc.

    Lemma run_process_eq {A B S} :
    forall (upd : Update S A B) (l : oplist A) s,
    build_process_opt upd (run_update_on_list s upd l)
    = run_process_on_list (build_process upd s) l.

    Lemma output_sm_on_event_as_run {S O} :
    forall (c  : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event),
    output_sm_on_event c e
    = option_map snd (run_sm_on_event c e).

    Lemma output_sm_on_event_eq {S O} :
    forall (c  : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event),
    output_sm_on_event c e
    = map_option
    (fun s => op_output c s (trigger e))
    (state_of_sm_at_start_of_event c e).

    Lemma run_update_on_list_snoc :
    forall {S I O} L x st (upd : Update S I O),
    run_update_on_list st upd (snoc L x)
    = map_option (fun s => op_state upd s x) (run_update_on_list st upd L).

    Lemma update_unroll {S I O} :
    forall (eo  : EventOrdering)
    (e   : Event)
    (F   : Event -> option I)
    (upd : Update S I O)
    (st  : S),
    ~ isFirst e
    -> run_update_on_list
    st
    upd
    (map F (localPreds e))
    = map_option
    (fun s => op_state upd s (F (local_pred e)))
    (run_update_on_list
    st
    upd
    (map F (localPreds (local_pred e)))).

    Lemma option_map_map_option :
    forall {A B C} (f : B -> C) (g : A -> option B) (o : option A),
    option_map f (map_option g o)
    = map_option (option_compose f g) o.

    Lemma map_option_Some :
    forall {A B} (f : A -> option B) (o : option A) (b : B),
    map_option f o = Some b
    <-> exists a, o = Some a /\ Some b = f a.

    Lemma op_state_Some :
    forall {S I O} (p : Update S I O) s o s',
    op_state p s o = Some s'
    -> exists x, op_update p s o = Some (Some s', x).

    Lemma option_compose_snd_op_update_implies :
    forall {S I O} (sm : Update S I (list O)) i a l,
    option_compose snd (fun s' : S => op_update sm s' i) a = Some l
    -> l = op_outputs sm a i.

    Lemma op_update_Some :
    forall {S I O} (p : Update S I O) s o x,
    op_update p s o = Some x
    -> op_state p s o = fst x.

    Lemma op_update_some_iff :
    forall {S I O} (p : Update S I O) s o x,
    op_update p s o = Some x
    <-> exists i, o = Some i /\ x = p s i.

    Lemma op_state_some_iff :
    forall {S I O} (p : Update S I O) s o x,
    op_state p s o = Some x
    <-> exists i, o = Some i /\ fst (p s i) = Some x.

    Lemma in_op_outputs_iff :
    forall {S I O} (p : Update S I (list O)) s o x,
    In x (op_outputs p s o)
    <-> exists i, o = Some i /\ In x (snd (p s i)).

    Lemma in_output_sm_on_event :
    forall {S O}
    (sm  : StateMachine S msg (list O))
    {eo  : EventOrdering}
    (e   : Event)
    (out : O),
    In out (loutput_sm_on_event sm e)
    <->
    if dec_isFirst e
    then In out (op_outputs sm (sm_state sm) (trigger e))
    else exists s',
    state_sm_on_event sm (local_pred e) = Some s'
    /\ In out (op_outputs sm s' (trigger e)).

    Lemma MhaltedSM_doesnt_output :
    forall {S} m (s : S) {eo : EventOrdering} (e : Event),
    ~ In m (loutput_sm_on_event (MhaltedSM s) e).

    Lemma in_output_system_on_event_ldata :
    forall {S}
    (s  : MUSystem S)
    {eo : EventOrdering}
    (e  : Event)
    (m  : DirectedMsg),
    In m (output_system_on_event_ldata s e)
    <->
    In m (loutput_sm_on_event (s (loc e)) e).

    Lemma output_system_on_event_ldata_as_loutput :
    forall {S}
    (s  : MUSystem S)
    {eo : EventOrdering}
    (e  : Event),
    output_system_on_event_ldata s e
    = loutput_sm_on_event (s (loc e)) e.

    Lemma implies_authenticated_messages_were_sent_non_byz_usys :
    forall {S} (eo : EventOrdering) (P : MUSystem S),
    authenticated_messages_were_sent_or_byz_usys eo P
    -> authenticated_messages_were_sent_non_byz_usys eo P.

    Lemma map_option_map_option :
    forall {A B C} (f : B -> option C) (g : A -> option B) (o : option A),
    map_option f (map_option g o)
    = map_option (option_compose2 f g) o.

    Lemma equal_map_options :
    forall {A B} (f g : A -> option B) (o : option A),
    (forall a, o = Some a -> f a = g a)
    -> map_option f o = map_option g o.

    Lemma state_sm_on_event_unroll {S O} :
    forall (sm : StateMachine S msg O)
    {eo  : EventOrdering}
    (e   : Event),
    state_sm_on_event sm e
    = if dec_isFirst e
    then op_state sm (sm_state sm) (trigger e)
    else map_option
    (fun s => op_state sm s (trigger e))
    (state_sm_on_event sm (local_pred e)).

    Lemma fold_ite_first :
    forall {A} {eo : EventOrdering} (e : Event) (a b : A),
    (if dec_isFirst e then a else b) = ite_first e a b.

    Lemma output_sm_on_event_unroll {S O} :
    forall (sm : StateMachine S msg O)
    {eo  : EventOrdering}
    (e   : Event),
    output_sm_on_event sm e
    = if dec_isFirst e
    then op_output sm (sm_state sm) (trigger e)
    else map_option
    (fun s => op_output sm s (trigger e))
    (state_sm_on_event sm (local_pred e)).

    Lemma state_sm_before_event_unroll {S O} :
    forall (sm : StateMachine S msg O)
    {eo  : EventOrdering}
    (e   : Event),
    state_sm_before_event sm e
    = if dec_isFirst e
    then Some (sm_state sm)
    else map_option
    (fun s => op_state sm s (trigger (local_pred e)))
    (state_sm_before_event sm (local_pred e)).

    Lemma state_sm_before_event_as_state_sm_on_event_pred :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e : Event),
    ~ isFirst e
    -> state_sm_before_event X e = state_sm_on_event X (local_pred e).

    Lemma ite_first_state_sm_on_event_as_before {S O} :
    forall (sm : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event),
    ite_first
    e
    (Some (sm_state sm))
    (state_sm_on_event sm (local_pred e))
    = state_sm_before_event sm e.

    Lemma state_sm_on_event_unroll2 {S O} :
    forall (sm : StateMachine S msg O)
    {eo : EventOrdering}
    (e  : Event),
    state_sm_on_event sm e
    = map_option
    (fun s => op_state sm s (trigger e))
    (state_sm_before_event sm e).

    Lemma olist2list_map_option_op_output_as_olist2list_option_map_op_outputs :
    forall {S O} (sm : StateMachine S msg (list O)) i o,
    olist2list (map_option (fun s : S => op_output sm s i) o)
    = olist2list (option_map (fun s : S => op_outputs sm s i) o).

    Lemma loutput_sm_on_event_unroll {S O} :
    forall (sm : StateMachine S msg (list O))
    {eo  : EventOrdering}
    (e   : Event),
    loutput_sm_on_event sm e
    = if dec_isFirst e
    then op_outputs sm (sm_state sm) (trigger e)
    else olist2list
    (option_map
    (fun s => op_outputs sm s (trigger e))
    (state_sm_on_event sm (local_pred e))).

    Lemma loutput_sm_on_event_unroll2 {S O} :
    forall (sm : StateMachine S msg (list O))
    {eo  : EventOrdering}
    (e   : Event),
    loutput_sm_on_event sm e
    = olist2list
    (map_option
    (fun s => op_output sm s (trigger e))
    (state_sm_before_event sm e)).

    (*  Lemma mkSSM_output_iff :
    forall {T} {eo : EventOrdering} (e : Event) (t : T) (init : T) upd,
    In t (loutput_sm_on_event (mkSSM upd init) e)
    <->
    exists s,
    (if dec_isFirst e
    then s = init
    else state_sm_on_event (mkSSM upd init) (local_pred e) = Some s)
    /\ In t (snd (upd s (trigger e))).

    (*  Lemma state_sm_before_event_some_implies :
    forall {S O}
    (X   : StateMachine S msg O)
    {eo  : EventOrdering}
    (e   : Event)
    (s   : S),
    state_sm_before_event X e = Some s
    -> state_sm_on_event X e = fst (sm_update X s (trigger e))
    /\ output_sm_on_event X e = Some (snd (sm_update X s (trigger e))).

    Lemma state_sm_before_event_as_initial :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e : Event),
    isFirst e
    -> state_sm_before_event X e = Some (sm_state X).

    Lemma state_sm_on_event_as_update_initial :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e : Event),
    isFirst e
    -> state_sm_on_event X e = op_state X (sm_state X) (trigger e).

    Lemma implies_eq_fst :
    forall (A B : Type) (x y : A * B), x = y -> fst x = fst y.

    Lemma implies_eq_snd :
    forall (A B : Type) (x y : A * B), x = y -> snd x = snd y.

    Lemma SM_state_before_event_implies_exists :
    forall {S SX U}
    (sm : StateMachine (S * SX) msg U)
    {eo : EventOrdering}
    (e  : Event)
    (s  : S),
    SM_state_before_event sm e s
    -> exists sx, state_sm_before_event sm e = Some (s, sx).

    Lemma state_sm_on_event_if_before_event_direct_pred :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) st,
    (e1) ⊂ (e2)
    -> state_sm_before_event sm e2 = Some st
    -> state_sm_on_event sm e1 = Some st.

    Lemma output_sm_on_event_none_implies_state_sm_before_event_none :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e : Event),
    all_correct eo
    -> output_sm_on_event X e = None
    -> state_sm_before_event X e = None.

    Lemma state_sm_on_event_mkSSM :
    forall {S O} {eo : EventOrdering} (e : Event) (upd : SUpdate S msg O) (init : S),
    all_correct eo
    -> ~ (state_sm_on_event (mkSSM upd init) e = None).

    Lemma state_sm_on_event_none_monotonic :
    forall {S O} (X : StateMachine S msg O) {eo : EventOrdering} (e e' : Event),
    e' ⊑ e
    -> state_sm_on_event X e' = None
    -> state_sm_on_event X e = None.

    Lemma state_sm_before_event_sub_sub_so_as_sub_eo :
    forall {S SX O}
    (X   : StateMachine (S * SX) msg O)
    {eo  : EventOrdering}
    (e   : Event)
    (e'  : subEventOrdering_type e)
    (e'' : @subEventOrdering_type pn pk pm (subEventOrdering e) e'),
    loc e' = loc e''
    -> @state_sm_before_event
    _ _ X
    (@subEventOrdering pn pk pm (@subEventOrdering pn pk pm eo e) e')
    e''
    =
    @state_sm_before_event
    _ _ X
    (@subEventOrdering pn pk pm eo e')
    (sub_sub_event2sub_event eo e e' e'').

    Lemma SM_state_before_event_sub_sub_so_as_sub_eo :
    forall {S SX O}
    (X   : StateMachine (S * SX) msg O)
    {eo  : EventOrdering}
    (e   : Event)
    (e'  : subEventOrdering_type e)
    (e'' : @subEventOrdering_type pn pk pm (subEventOrdering e) e')
    (s   : S),
    loc e' = loc e''
    -> @SM_state_before_event
    _ _ _ X
    (@subEventOrdering pn pk pm (@subEventOrdering pn pk pm eo e) e')
    e''
    s
    <->
    @SM_state_before_event
    _ _ _ X
    (@subEventOrdering pn pk pm eo e')
    (sub_sub_event2sub_event eo e e' e'')
    s.

    Lemma MhaltedSM_output :
    forall {S} {eo : EventOrdering} (e : Event) (s : S) m,
    ~ In m (loutput_sm_on_event (MhaltedSM s) e).

    Lemma Deq_unit : Deq unit.

    Proof.

    Lemma SM_state_on_event_implies_exists :
    forall {S SX U}
    (sm : StateMachine (S * SX) msg U)
    {eo : EventOrdering}
    (e  : Event)
    (s  : S),
    SM_state_on_event sm e s
    -> exists sx, state_sm_on_event sm e = Some (s, sx).

    Lemma state_sm_before_event_if_on_event_direct_pred :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) st,
    (e1) ⊂ (e2)
    -> state_sm_on_event sm e1 = Some st
    -> state_sm_before_event sm e2 = Some st.

    Lemma state_sm_before_event_some_between :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
    e1 ⊑ e2
    -> ~ isFirst e1
    -> state_sm_before_event sm e2 = Some s
    -> exists s', state_sm_before_event sm e1 = Some s'.

    Lemma state_sm_on_event_some_between :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
    e1 ⊑ e2
    -> ~ isFirst e1
    -> state_sm_on_event sm e2 = Some s
    -> exists s', state_sm_on_event sm e1 = Some s'.

    Lemma state_sm_on_event_some_between2 :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
    e1 ⊑ e2
    -> state_sm_on_event sm e2 = Some s
    -> exists s', state_sm_on_event sm e1 = Some s'.

    Lemma state_sm_before_event_some_between2 :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
    e1 ⊑ e2
    -> state_sm_before_event sm e2 = Some s
    -> exists s', state_sm_before_event sm e1 = Some s'.

    Lemma state_sm_before_event_some_between3 :
    forall {S O} {eo : EventOrdering} (e1 e2 : Event) (sm : StateMachine S msg O) s,
    e1 ⊑ e2
    -> state_sm_on_event sm e2 = Some s
    -> exists s', state_sm_before_event sm e1 = Some s'.

    Lemma output_system_on_event_ldata_implies_state_sm_on_event :
    forall {S} (s : MUSystem S) {eo : EventOrdering} (e  : Event) m,
    In m (output_system_on_event_ldata s e)
    -> (forall x i, exists s', fst (sm_update (s (loc e)) x i) = Some s')
    -> exists st, state_sm_on_event (s (loc e)) e = Some st.

    Lemma state_sm_on_event_some_implies_has_correct_trace_before :
    forall {S O} (sm : StateMachine S msg O) (eo : EventOrdering) (e : Event) i s,
    loc e = i
    -> state_sm_on_event sm e = Some s
    -> has_correct_trace_before e i.

    Lemma isCorrect_first_implies_has_correct_trace_before :
    forall (eo : EventOrdering) (e : Event),
    isCorrect e
    -> isFirst e
    -> has_correct_trace_before e (loc e).

    Lemma state_sm_before_event_some_implies_has_correct_trace_before :
    forall {S O} (sm : StateMachine S msg O) (eo : EventOrdering) (e : Event) s,
    isCorrect e
    -> state_sm_before_event sm e = Some s
    -> has_correct_trace_before e (loc e).

    Lemma state_sm_on_event_some_implies_node_has_correct_trace_before :
    forall {S O} (sm : StateMachine S msg O) (eo : EventOrdering) (e : Event) i s,
    loc e = node2name i
    -> state_sm_on_event sm e = Some s
    -> node_has_correct_trace_before e i.

    Lemma isCorrect_first_implies_node_has_correct_trace_before :
    forall (eo : EventOrdering) (e : Event) i,
    loc e = node2name i
    -> isCorrect e
    -> isFirst e
    -> node_has_correct_trace_before e i.

    Lemma state_sm_before_event_some_implies_node_has_correct_trace_before :
    forall {S O} (sm : StateMachine S msg O) (eo : EventOrdering) (e : Event) i s,
    loc e = node2name i
    -> isCorrect e
    -> state_sm_before_event sm e = Some s
    -> node_has_correct_trace_before e i.

## ComponentExample1.v
### Definition


    Definition m_counter_update : M_Update 0 nat :=
    fun (s : nat) (i : cio_I) => ret _ (Some (s + i), s + i).

    Definition A : M_Process 1 :=
    build_m_process m_counter_update 0.

    Definition B_update : M_Update 1 nat :=
    fun s i =>
    (call_proc "A" i)
    >>= fun out =>
    ret _ (Some (s + out + 1), s + out + 1).

    Definition B : M_Process 2 :=
    build_m_process B_update 0.

    Definition C_update : M_Update 2 nat :=
    fun s i =>
    (call_proc "B" i)
    >>= fun out1 =>
    (call_proc "B" i)
    >>= fun out2 =>
    ret _ (Some (s + out1 + out2 + 2), s + out1 + out2 + 2).

    Definition C : M_Process 3 :=
    build_m_process C_update 0.

    Definition M_update : M_Update 3 unit :=
    fun s i =>
    (call_proc "C" i)
    >>= (fun out => ret _ (Some s, out)).

    Definition M : M_Process 4 :=
    build_m_process M_update tt.

    Definition progs : n_procs 3 :=
    [("A",incr_n_proc (incr_n_proc A)),
    ("B",incr_n_proc B),
    ("C",C)].

### Instance


    Instance CIOnat : ComponentIO :=
    BuildComponentIO nat nat 0.

## EventOrdering.v
### Definition


    Definition Qpos := {q : Q | Qle 0 q}.

    
    Definition Qpos_lt (q1 q2 : Qpos) := Qlt (proj1_sig q1) (proj1_sig q2).

    Definition trigger_info := option msg.

    
    Class EventOrdering :=
    {
    Event          :> Type;                     (* Type of Events *)
    
    happenedBefore : Event -> Event -> Prop;    (* Causal ordering between events *)
    (* QUESTION: shouldn't loc have type Event -> iname?  Do we care about the events that happen outside the system *)
    loc            : Event -> name;             (* Each event happens at a node (location) *)
    direct_pred    : Event -> option Event;     (* Each event is either the first at a node or it has a local predecessor *)
    trigger        : Event -> trigger_info;     (* Each event is triggered the receipt of a message *)
    time           : Event -> Qpos;             (* Each event happens at a time w.
r.
t.
 a global clock *)
    Definition local_pred (e : Event) : Event :=
    match direct_pred e with
    | Some e' => e'
    | None => e
    end.

    Definition happenedBeforeLe (a b : Event) : Prop :=
    (a ≺ b) \/ a = b.

    Definition isCorrectCut (n : name) (L : list Event) : Prop :=
    forall e e1 e2,
    In e L
    -> e1 ≼ e
    -> e2 ≼ e
    -> loc e1 = n
    -> loc e2 <> n
    -> disjoint
    (map dsk_key (lkm_sending_keys (keys e1)))
    (map dsk_key (lkm_sending_keys (keys e2))).

    Definition isCorrect0 (e : Event) : Prop :=
    isCorrectCut (loc e) [e].

    Definition isCorrect (e : Event) : Prop :=
    match trigger e with
    | Some _ => True
    | _ => False
    end.

    (*  Definition isCorrect (e : Event) : Prop :=
    mode e = correct.
*)
    (*  Definition isCrashed (e : Event) : Prop :=
    mode e = faulty crashed.
*)
    Definition isByz (e : Event) : Prop :=
    ~ isCorrect e.

    (*  Definition isByz (e : Event) : Prop :=
    mode e = faulty byzantine.
*)
    Definition localHappenedBefore (a b : Event) : Prop :=
    (a ≺ b) /\ loc a = loc b.

    Definition localHappenedBeforeLe (a b : Event) : Prop :=
    (a ≼ b) /\ loc a = loc b.

    Definition isFirst (e : Event) : Prop :=
    direct_pred e = None.

    Definition localPreds (e : Event) : list Event :=
    projT1 (localPreds_lem e).

    Definition get_first (e : Event) : Event :=
    match localPreds e with
    | [] => e
    | e' :: _ => e'
    end.

    Definition is_first (e : Event) : bool :=
    match direct_pred e with
    | Some _ => false
    | None => true
    end.

    Definition if_not_first (e : Event) (P : Prop) : Prop:=
    ~ isFirst e -> P.

    Definition subEventOrdering_cond (e e' : Event) : Prop :=
    loc e' = loc e -> e ≼ e'.

    Definition subEventOrdering_cond_bool (e e' : Event) : Prop :=
    (if subEventOrdering_cond_dec e e' then true else false) = true.

    Definition mkSubOrderingLe {e e' : Event} (p : e ⊑ e') : subEventOrdering_type e.

    Proof.

    Definition subEventOrdering_happenedBefore (e : Event) :
    subEventOrdering_type e
    -> subEventOrdering_type e
    -> Prop.

    Definition subEventOrdering_loc (e : Event) :
    subEventOrdering_type e -> name.

    Definition subEventOrdering_direct_pred (e : Event) :
    subEventOrdering_type e -> option (subEventOrdering_type e).

    Definition subEventOrdering_direct_pred (e : Event) :
    subEventOrdering_type e -> option (subEventOrdering_type e).

    Definition subEventOrdering_trigger (e : Event) :
    subEventOrdering_type e -> trigger_info.

    Definition subEventOrdering_time (e : Event) :
    subEventOrdering_type e -> Qpos.

    (*  Definition subEventOrdering_mode (e : Event) :
    subEventOrdering_type e -> EventStatus.

    Definition subEventOrdering_keys (e : Event) :
    subEventOrdering_type e -> local_key_map.

    Definition subEventOrdering (e : Event) : EventOrdering.

    Proof.

    Definition localPredsLe (e : Event) : list Event := snoc (localPreds e) e.

    
    (*
    Record DirectedData :=
    MkDData
    {
    ddDst  : name;
    ddData : Data
    }.

    Definition LDirectedData := list DirectedData.
*)
    
    Definition Observer := forall eo : EventOrdering, @Event eo -> DirectedMsgs.

    Definition check_auth_data
    (src dst : Event) (* Byzantine source [src] *) : Prop :=
    forall m : AuthMsg,
    In m (get_contained_auth_data (data dst))
    -> verify_auth_msg m (keys src)
    ->
    (* then we have to make sure that s had enough information to generate the
    authenticated message *)
    (
    (* either [src] got the authenticated message from someone else *)
    in_trace m src
    
    \/
    
    (* or it is able to authenticate the message with one of its keys *)
    verify_keys m (keys src)
    ).
*)
    Definition is_protocol_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_PROTOCOL => true
    | MSG_STATUS_INTERNAL => true
    | MSG_STATUS_EXTERNAL => false
    end.

    Definition is_internal_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_PROTOCOL => false
    | MSG_STATUS_INTERNAL => true
    | MSG_STATUS_EXTERNAL => false
    end.

    Definition is_external_message (m : msg) : bool :=
    match get_msg_status m with
    | MSG_STATUS_PROTOCOL => false
    | MSG_STATUS_INTERNAL => false
    | MSG_STATUS_EXTERNAL => true
    end.

    Definition auth_data_in_trigger (a : AuthenticatedData) (e : Event) : Prop :=
    match trigger e with
    | Some msg => In a (get_contained_authenticated_data msg)
    | None => False
    end.

    Definition bind_op_list {A B} (F : A -> list B) (i : option A) : list B :=
    match i with
    | Some a => F a
    | None => []
    end.

    Definition authenticated_messages_were_sent_or_byz
    (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e (a : AuthenticatedData),
    In a (bind_op_list get_contained_authenticated_data (trigger e))
    (* if we didn't verify the message then it could come from a Byzantine
    node that is impersonating someone else, without the logic knowing it *)
    -> verify_authenticated_data (loc e) a (keys e) = true
    -> exists e',
    e' ≺ e (* event e was triggered by an earlier send event e' *)
    
    (* e' generated the authentication code *)
    (* QUESTION: Should we say instead that the message was authenticated
    using a subset of the keys? *)
    /\ am_auth a = authenticate (am_data a) (keys e')
    
    /\
    (
    (
    exists m dst delay,
    
    In a (get_contained_authenticated_data m)
    
    /\
    (* e' sent the message to some node "dst"
    following the protocol as described by F
    (only if the message is the message is internal though),
    which eventually got to e *)
    (is_protocol_message m = true -> In (MkDMsg m dst delay) (F eo e'))
    
    /\
    (* e' is the node mentioned in the authenticated message *)
    data_auth (loc e) (am_data a) = Some (loc e')
    )
    
    \/
    
    (* e' is not the node mentioned in the authenticated message
    because he got the keys of some other e''
    *)
    (
    exists e'',
    e'' ≼ e'
    /\
    (* e' is byzantine because it's using the keys of e'' *)
    isByz e'
    /\
    (* e'' is byzantine because it lost it keys *)
    isByz e''
    /\
    (* the sender mentioned in m is actually e'' and not e' but e' sent the message impersonating e''.
.
.
what a nerve! *)
    Definition is_internal_trigger (e : Event) : bool :=
    match trigger e with
    | Some msg => is_internal_message msg
    | None => false
    end.

    Definition event_triggered_by_message (e : Event) (m : msg) : Prop :=
    trigger e = Some m.

    Definition internal_messages_were_sent
    (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e m,
    event_triggered_by_message e m
    -> is_internal_message m = true
    -> isCorrect e
    ->
    exists e' dst delay,
    e' ⊏ e (* event e was triggered by an earlier send event e' *)
    /\ In (loc e) dst
    /\ In (MkDMsg m dst delay) (F eo e').

    Definition simple_sent_byz
    (F : forall (eo : EventOrdering) (e : Event), DirectedMsgs) :=
    forall e (a : AuthenticatedData),
    In a (get_contained_authenticated_data (trigger e))
    ->
    exists e' m,
    e' ≺ e (* event e was triggered by an earlier send event e' *)
    
    /\
    In a (get_contained_authenticated_data m)
    
    /\
    (
    (exists dst delay, In (MkDMsg m dst delay) (F eo e'))
    
    \/
    
    isByz e'
    ).

    Definition authenticated_messages_were_sent_or_byz_observer
    (s : Observer)
    := authenticated_messages_were_sent_or_byz s.

    Definition failures_dont_change :=
    forall e1 e2,
    e1 ⊏ e2
    ->
    (
    (*        (isCrashed e1 -> isCrashed e2)
    /\*)
    (isByz e1 -> isByz e2)
    ).

### Inductive


    Inductive Faulty :=
    (*  | crashed   : Faulty*)
    | byzantine : Faulty.

    Inductive EventStatus :=
    | correct
    | faulty (f : Faulty).

    Inductive msg_status :=
    (* messages sent by the system from one replica to another (possibly the same replica) *)
    | MSG_STATUS_PROTOCOL
    (* internal message sent the system sent by one replica to itself *)
    | MSG_STATUS_INTERNAL
    (* external messages are sent by processes not specified by the protocol *)
    | MSG_STATUS_EXTERNAL.

### Lemma


    Lemma correct_is_not_byzantine :
    forall (e : Event), isCorrect e -> ~ isByz e.

    Lemma happenedBeforeLe_refl :
    forall e, e ≼ e.

    Lemma localHappenedBeforeLe_refl :
    forall (e : Event), e ⊑ e.

    Lemma eo_causal : well_founded happenedBefore.

    Proof.

    Lemma local_implies_loc :
    forall (e1 e2 : Event), e1 ⊏ e2 -> loc e1 = loc e2.

    Lemma localLe_implies_loc :
    forall (e1 e2 : Event), e1 ⊑ e2 -> loc e1 = loc e2.

    Lemma localLe_implies_causalLe :
    forall (e1 e2 : Event), e1 ⊑ e2 -> e1 ≼ e2.

    Lemma pred_implies_causal :
    forall (e1 e2 : Event), e1 ⊂ e2 -> e1 ≺ e2.

    Lemma pred_implies_loc :
    forall (e1 e2 : Event), e1 ⊂ e2 -> loc e1 = loc e2.

    Lemma pred_implies_local :
    forall (e1 e2 : Event), e1 ⊂ e2 -> e1 ⊏ e2.

    Lemma local_implies_causal :
    forall (e1 e2 : Event), e1 ⊏ e2 -> e1 ≺ e2.

    Lemma HappenedBeforeInd :
    forall P : Event -> Prop,
    (forall e, (forall e', e' ≺ e -> P e') -> P e)
    -> forall e, P e.

    Lemma HappenedBeforeInd_type :
    forall P : Event -> Type,
    (forall e, (forall e', e' ≺ e -> P e') -> P e)
    -> forall e, P e.

    Lemma causal_trans :
    forall (e1 e2 e3 : Event),
    e1 ≺ e2 -> e2 ≺ e3 -> e1 ≺ e3.

    Lemma causal_le_r_trans :
    forall (e1 e2 e3 : Event),
    e1 ≺ e2 -> e2 ≼ e3 -> e1 ≺ e3.

    Lemma causal_le_l_trans :
    forall (e1 e2 e3 : Event),
    e1 ≼ e2 -> e2 ≺ e3 -> e1 ≺ e3.

    Lemma local_trans :
    forall (e1 e2 e3 : Event),
    e1 ⊏ e2 -> e2 ⊏ e3 -> e1 ⊏ e3.

    Lemma local_trans_le_r :
    forall (e1 e2 e3 : Event),
    e1 ⊏ e2 -> e2 ⊑ e3 -> e1 ⊏ e3.

    Lemma local_trans_le_l :
    forall (e1 e2 e3 : Event),
    e1 ⊑ e2 -> e2 ⊏ e3 -> e1 ⊏ e3.

    Lemma local_implies_le :
    forall (e1 e2 : Event), e1 ⊏ e2 -> e1 ⊑ e2.

    Lemma local_pred_le :
    forall (e : Event), (local_pred e) ⊑ e.

    Lemma localHappenedBeforeInd :
    forall P : Event -> Prop,
    (forall e, (forall e', e' ⊏ e -> P e') -> P e)
    -> forall e, P e.

    Lemma localHappenedBeforeInd_type :
    forall P : Event -> Type,
    (forall e, (forall e', e' ⊏ e -> P e') -> P e)
    -> forall e, P e.

    Lemma dec_isFirst :
    forall e, decidable (isFirst e).

    Lemma local_pred_is_direct_pred :
    forall e,
    ~ isFirst e
    -> (local_pred e) ⊂ e .

    Lemma local_pred_is_localCausal :
    forall e,
    ~ isFirst e
    -> (local_pred e) ⊏ (e).

    Lemma local_pred_is_causal :
    forall e,
    ~ isFirst e
    -> (local_pred e) ≺ (e).

    Lemma predHappenedBeforeInd :
    forall P : Event -> Prop,
    (forall e, (forall e', e' ⊂ e -> P e') -> P e)
    -> forall e, P e.

    Lemma predHappenedBeforeInd_local_pred :
    forall P : Event -> Prop,
    (forall e, (~ isFirst e -> P (local_pred e)) -> P e)
    -> forall e, P e.

    Lemma predHappenedBeforeInd_type :
    forall P : Event -> Type,
    (forall e, (forall e', e' ⊂ e -> P e') -> P e)
    -> forall e, P e.

    Lemma predHappenedBeforeInd_local_pred_type :
    forall P : Event -> Type,
    (forall e, (~ isFirst e -> P (local_pred e)) -> P e)
    -> forall e, P e.

    Lemma not_direct_pred :
    forall (e e1 e2 : Event),
    e1 ⊂ e
    -> e2 ⊏ e
    -> e1 <> e2
    -> e2 ⊏ e1.

    Lemma causal_anti_reflexive :
    forall (e : Event), ~ e ≺ e.

    Lemma localCausal_anti_reflexive :
    forall (e : Event), ~ e ⊏ e.

    Lemma pred_anti_reflexive :
    forall (e : Event), ~ e ⊂ e.

    Lemma local_implies_pred_or_local :
    forall (e1 e2 : Event),
    e1 ⊏ e2
    -> (e1 ⊂ e2 [+] {e : Event & e ⊂ e2 /\ e1 ⊏ e}).

    Lemma local_implies_local_or_pred :
    forall (e1 e2 : Event),
    e1 ⊏ e2
    -> (e1 ⊂ e2 [+] {e : Event & e1 ⊂ e /\ e ⊏ e2}).

    Lemma snoc_inj :
    forall {A} (l k : list A) a b,
    snoc l a = snoc k b
    -> l = k /\ a = b.

    Lemma localPreds_lem :
    forall (e : Event),
    {l : list Event
    & forall a b, adjacent a b (snoc l e) <-> (a ⊂ b /\ a ⊏ e) }.

    Lemma snoc_as_app {T} :
    forall (a : T) (l : list T),
    snoc l a = l ++ [a].

    Lemma localPreds_prop1 :
    forall (e e' : Event),
    In e' (localPreds e) <-> e' ⊏ e.

    Lemma if_not_first_if_first :
    forall e P,
    isFirst e
    -> if_not_first e P.

    Lemma if_not_first_implies_or :
    forall e P,
    if_not_first e P
    -> (isFirst e \/ (~ isFirst e /\ P)).

    Lemma localPreds_cond_implies_in :
    forall a b e l,
    adjacent a b l
    -> (forall a b : Event, adjacent a b (snoc l e) -> (a) ⊂ (b) /\ (a) ⊏ (e))
    -> (b) ⊏ (e).

    Lemma localPreds_cond_implies_in2 :
    forall b l x,
    In b l
    -> (forall a b : Event, adjacent a b (snoc l x) -> (a) ⊂ (b))
    -> (b) ⊏ (x).

    Lemma localPreds_cond_implies_in3 :
    forall l2 l1 b,
    In b l1
    -> (forall a b : Event, adjacent a b (l1 ++ l2) -> (a) ⊂ (b))
    -> forall x, In x l2 -> (b) ⊏ (x).

    Lemma localPreds_cond_implies_in4 :
    forall b l x,
    In b l
    -> (forall a b : Event, adjacent a b (x :: l) -> (a) ⊂ (b))
    -> (x) ⊏ (b).

    Lemma adjacent_single :
    forall {T} (a b c : T), ~ adjacent a b [c].

    Lemma pred_implies_local_pred :
    forall a b, (a) ⊂ (b) -> a = local_pred b.

    Lemma pred_implies_not_first :
    forall a b,
    a ⊂ b ->  ~ isFirst b.

    Lemma local_causal_implies_not_first :
    forall a b,
    a ⊏ b ->  ~ isFirst b.

    Lemma isFirst_implies_local_pred_eq :
    forall e, isFirst e -> local_pred e = e.

    Lemma isFirst_implies_localPreds_eq :
    forall e, isFirst e -> localPreds e = [].

    Lemma loc_local_pred :
    forall (e : Event), loc (local_pred e) = loc e.

    Lemma localHappenedBefore_if_isFirst :
    forall e1 e2,
    loc e1 = loc e2
    -> isFirst e1
    -> e1 <> e2
    -> e1 ⊏ e2.

    Lemma causalLe_trans :
    forall (e1 e2 e3 : Event),
    e1 ≼ e2 -> e2 ≼ e3 -> e1 ≼ e3.

    Lemma isFirst_loc_implies_causal :
    forall (e e' : Event),
    isFirst e
    -> loc e = loc e'
    -> e ≼ e'.

    Lemma no_local_predecessor_if_first :
    forall (e e' : Event),
    isFirst e
    -> ~ (e' ⊏ e).

    Lemma tri_if_same_loc :
    forall e1 e2,
    loc e1 = loc e2
    -> (e1 ⊏ e2 \/ e1 = e2 \/ e2 ⊏ e1).

    Lemma causal_implies_causalLe :
    forall (e1 e2 : Event), e1 ≺ e2 -> e1 ≼ e2.

    Lemma localLe_trans :
    forall (e1 e2 e3 : Event),
    e1 ⊑ e2 -> e2 ⊑ e3 -> e1 ⊑ e3.

    Lemma subEventOrdering_causalLe_loc_dec :
    forall e e', loc e = loc e' -> decidable (e ≼ e').

    Lemma subEventOrdering_cond_dec :
    forall e e', decidable (subEventOrdering_cond e e').

    Lemma subEventOrdering_cond_bool_iff :
    forall e e',
    subEventOrdering_cond_bool e e'
    <-> subEventOrdering_cond e e'.

    Lemma subEventOrdering_cond_bool_local_pred :
    forall (e e' : Event),
    subEventOrdering_cond_bool e e'
    -> loc e' = loc e
    ->  e <> e'
    -> subEventOrdering_cond_bool e (local_pred e').

    Lemma diff_first_iff_not_first :
    forall (e : Event), e <> get_first e <-> ~ isFirst e.

    Lemma eq_first_iff_first :
    forall (e : Event), e = get_first e <-> isFirst e.

    Lemma subEventOrdering_Deq : forall (e : Event), Deq (subEventOrdering_type e).

    Proof.

    Lemma subEventOrdering_wf : forall (e : Event), well_founded (subEventOrdering_happenedBefore e).

    Proof.

    Lemma subEventOrdering_trans :
    forall (e : Event),
    transitive (subEventOrdering_type e) (subEventOrdering_happenedBefore e).

    Lemma subEventOrdering_direct_pred_some_implies :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e1 = Some e2
    -> direct_pred e1 = Some (sub_eo_event e e2).

    Lemma subEventOrdering_direct_pred_some_iff :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e1 = Some e2
    <-> direct_pred e1 = Some (sub_eo_event e e2).

    Lemma subEventOrdering_axiom_direct_pred_local :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e1 = Some e2
    -> subEventOrdering_loc e e1 = subEventOrdering_loc e e2.

    Lemma subEventOrdering_axiom_direct_pred_ord :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e1 = Some e2
    -> subEventOrdering_happenedBefore e e2 e1.

    Lemma loc_get_first :
    forall (e : Event), loc (get_first e) = loc e.

    Lemma get_first_le :
    forall (e e' : Event), loc e = loc e'-> (get_first e) ≼ e'.

    Lemma get_first_get_first_eq :
    forall (e e' : Event), loc e = loc e'-> get_first e = get_first e'.

    Lemma adjacent_one_element:
    forall a b e, adjacent a b [e] -> a = Nome /\ b = None.

    Lemma subEventOrdering_axiom_direct_pred_first :
    forall (e : Event),
    forall e0 : subEventOrdering_type e,
    subEventOrdering_direct_pred e e0 = None
    ->
    (forall e' : subEventOrdering_type e,
    subEventOrdering_loc e e' = subEventOrdering_loc e e0
    -> e0 <> e'
    -> subEventOrdering_happenedBefore e e0 e').

    Lemma happenedBeforeLe_implies_eq :
    forall e1 e2, (e1) ≼ (e2) -> (e2) ≼ (e1) -> e1 = e2.

    Lemma subEventOrdering_axiom_direct_pred_inj :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_loc e e1 = subEventOrdering_loc e e2
    -> subEventOrdering_direct_pred e e1 = subEventOrdering_direct_pred e e2
    -> e1 = e2.

    Lemma subEventOrdering_axiom_local_order :
    forall (e : Event),
    forall e1 e2 e0 : subEventOrdering_type e,
    subEventOrdering_loc e e1 = subEventOrdering_loc e e2
    -> subEventOrdering_happenedBefore e e1 e2
    -> subEventOrdering_direct_pred e e2 = Some e0
    -> e0 = e1 [+] subEventOrdering_happenedBefore e e1 e0.

    Lemma subEventOrdering_axiom_causal_time :
    forall (e : Event),
    forall e1 e2 : subEventOrdering_type e,
    subEventOrdering_happenedBefore e e1 e2
    -> Qpos_lt (subEventOrdering_time e e1) (subEventOrdering_time e e2).

    Lemma trigger_mkSubOrderingLe :
    forall (e e' : Event) (p : e ⊑ e'),
    @trigger (subEventOrdering e) (mkSubOrderingLe p) = trigger e'.

    Lemma trigger_in_subEventOrdering :
    forall (e : Event) (e' : subEventOrdering_type e),
    @trigger (subEventOrdering e) e' = trigger e'.

    Lemma subEventOrdering_loc_as_loc :
    forall (e : Event) (e' : subEventOrdering_type e),
    subEventOrdering_loc e e' = loc e'.

    Lemma localPreds_cond_pred :
    forall l e,
    (forall a b : Event,
    adjacent a b (snoc (snoc l (local_pred e)) e) <-> (a) ⊂ (b) /\ (a) ⊏ (e))
    -> forall a b : Event,
    adjacent a b (snoc l (local_pred e)) <-> (a) ⊂ (b) /\ (a) ⊏ (local_pred e).

    Lemma localPreds_unroll :
    forall e,
    ~ isFirst e
    -> localPreds e
    = snoc (localPreds (local_pred e)) (local_pred e).

    Lemma in_bind_op_list_as_auth_data_in_trigger :
    forall a (e : Event),
    In a (bind_op_list get_contained_authenticated_data (trigger e))
    <-> auth_data_in_trigger a e.

    Lemma in_bind_op_list_implies_auth_data_in_trigger :
    forall a (e : Event),
    In a (bind_op_list get_contained_authenticated_data (trigger e))
    -> auth_data_in_trigger a e.

    Lemma auth_data_in_trigger_implies_in_bind_op_list :
    forall a (e : Event),
    auth_data_in_trigger a e
    -> In a (bind_op_list get_contained_authenticated_data (trigger e)).

    Lemma event_triggered_by_message_implies_auth_data_in_trigger :
    forall (e : Event) m a,
    event_triggered_by_message e m
    -> In a (get_contained_authenticated_data m)
    -> auth_data_in_trigger a e.

    Lemma event_triggered_by_message_implies_in_bind_op_list :
    forall (e : Event) m a,
    event_triggered_by_message e m
    -> In a (get_contained_authenticated_data m)
    -> In a (bind_op_list get_contained_authenticated_data (trigger e)).

## Crypto.v
### Definition


    Definition sending_keys   := list sending_key.

    Definition receiving_keys := list receiving_key.

    Definition key_map := name (* Src *) -> local_key_map.

    
    (*  Definition lookup_dskey (km : local_key_map) (h : name) : option DSKey :=
    find
    (fun dk => if in_dec name_dec h (dsk_dst dk) then true else false)
    (lkm_sending_keys km).
*)
    Definition lookup_dskeys (km : local_key_map) (h : name) : list DSKey :=
    filter
    (fun dk => if in_dec name_dec h (dsk_dst dk) then true else false)
    (lkm_sending_keys km).

    (*  Definition lookup_sending_key (km : local_key_map) (h : name) : option sending_key :=
    option_map
    (fun dk => dsk_key dk)
    (lookup_dskey km h).
*)
    Definition lookup_drkeys (km : local_key_map) (h : name) : list DRKey :=
    filter
    (fun dk => if in_dec name_dec h (drk_dst dk) then true else false)
    (lkm_receiving_keys km).

    (*  Definition lookup_drkey (km : local_key_map) (h : name) : option DRKey :=
    find
    (fun dk => if in_dec name_dec h (drk_dst dk) then true else false)
    (lkm_receiving_keys km).
*)
    (*  Definition lookup_receiving_key (km : local_key_map) (h : name) : option receiving_key :=
    option_map
    (fun dk => drk_key dk)
    (lookup_drkey km h).
*)
    Definition lookup_receiving_keys (km : local_key_map) (h : name) : list receiving_key :=
    map drk_key (lookup_drkeys km h).

    (*Definition has_sending_key (km : local_key_map) (h : name) : Prop :=
    lookup_dskeys km h <> [].
*)
    Definition has_receiving_key (km : local_key_map) (h : name) : Prop :=
    lookup_drkeys km h <> [].

    Definition got_key_for (n : name) (kmsrc kmdst : local_key_map) : Prop :=
    exists k,
    In k (map dsk_key (lookup_dskeys kmsrc n))
    /\ In k (map dsk_key (lookup_dskeys kmdst n)).

    Definition Tokens := list Token.

    
    Lemma Tokens_dec : Deq Tokens.

    Definition authenticate
    (d   : data)
    (*             (dst : name)*)
    (km  : local_key_map) : Tokens :=
    create d (map dsk_key (lkm_sending_keys km)).

### Lemma


    Lemma Tokens_dec : Deq Tokens.

    Proof.

## ComponentSM2.v
### Definition


    Definition CompName := String.
string.

    
    Definition p_nproc (p : CompName -> Type) := { cn : CompName & p cn }%type.

    Definition p_procs (p : CompName -> Type) := list (p_nproc p).

    
    Definition M_p (p : CompName -> Type) (PO : Type) := p_procs p -> (p_procs p * PO)%type.

    Definition MP_Update (p : CompName -> Type) (I O S : Type) := S -> I -> M_p p (option S * O).

    
    Record ComponentIO :=
    MkComponentIO
    {
    cio_I : Type;
    cio_O : Type;
    cio_default_O : cio_O;
    }.

    Definition n_proc := M_StateMachine.

    Definition n_nproc (n : nat) := {cn : CompName & n_proc n cn }.

    Definition n_procs (n : nat) := list (n_nproc n).

    
    Definition M_n (n : nat) (PO : Type) := n_procs n -> (n_procs n * PO)%type.

    Definition M_Update (n : nat) (nm : CompName) (S : Type) :=
    S -> cio_I (fio nm) -> M_n n (option S * cio_O (fio nm)).

    Definition ret {A} (n : nat) (a : A) : M_n n A := fun s => (s, a).

    
    Definition bind {A B} {n:nat} (m : M_n n A) (f : A -> M_n n B) : M_n n B :=
    fun s =>
    let (s1,a) := m s in
    let (s2,b) := f a s1 in
    (s2,b).

    Definition MP_haltedSM {S}
    (n  : nat)
    (nm : CompName)
    (d  : S) : MP_StateMachine (n_proc n) nm :=
    MkMPSM
    S
    true
    (fun s i p => (p, (None, cio_default_O (fio nm))))
    d.

    Definition M_haltedSM {S}
    (nm : CompName)
    (d  : S) : M_StateMachine 0 nm :=
    MkMPSM
    S
    true
    (fun s i p => (p, (None, cio_default_O (fio nm))))
    d.

    Definition incr_n_proc {n} {nm} (p : n_proc n nm) : n_proc (S n) nm := inr p.

    
    Definition incr_n_nproc {n} (p : n_nproc n) : n_nproc (S n) :=
    match p with
    | existT _ m q =>
    existT _ m (incr_n_proc q)
    end.

    Definition incr_n_procs {n} (ps : n_procs n) : n_procs (S n) :=
    map incr_n_nproc ps.

    Definition decr_n_proc {n} {nm} : n_proc n nm -> option (n_proc (Init.
Nat.
pred n) nm) :=
    match n with
    | 0 => fun p => Some p
    | S m => fun p =>
    match p with
    | inl _ => None
    | inr q => Some q
    end
    end.

    Definition decr_n_nproc {n} (np : n_nproc n) : option (n_nproc (Init.
Nat.
pred n)) :=
    match np with
    | existT _ m p =>
    match decr_n_proc p with
    | Some q => Some (existT _ m q)
    | None => None
    end
    end.

    Definition decr_n_procs {n} (ps : n_procs n) : n_procs (Init.
Nat.
pred n) :=
    mapOption decr_n_nproc ps.

    Definition incr_pred_n_proc {n} {nm} : n_proc (pred n) nm -> n_proc n nm :=
    match n with
    | 0 => fun p => p
    | S m => inr
    end.

    Definition incr_pred_n_nproc {n} (p : n_nproc (pred n)) : n_nproc n :=
    match p with
    | existT _ m q =>
    existT _ m (incr_pred_n_proc q)
    end.

    Definition incr_pred_n_procs {n} (ps : n_procs (pred n)) : n_procs n :=
    map incr_pred_n_nproc ps.

    Definition lift_M {m} {nm} {O}
    (x : M_p (n_proc m) (MP_StateMachine (n_proc m) nm * O))
    : M_n m (M_StateMachine (S m) nm * O) :=
    fun ps =>
    let (k, qo) := x ps in
    let (q, o) := qo in
    (k, (injL(q), o)).

    Definition lift_M2 {n} {nm} {O} (m : M_n (pred n) (M_StateMachine n nm * O))
    : M_n (pred (S n)) (M_StateMachine (S n) nm * O) :=
    fun (ps : n_procs n) =>
    match m (decr_n_procs ps) with
    | (ps',(p',o)) => (incr_pred_n_procs ps', (incr_n_proc p',o))
    end.

    Definition sm_s_to_sm {m} {nm}
    (sm : MP_StateMachine (n_proc m) nm)
    (x : M_p (n_proc m) (option (sm_S sm) * cio_O (fio nm)))
    : M_p (n_proc m) (MP_StateMachine (n_proc m) nm * cio_O (fio nm)) :=
    fun ps =>
    let (ps', so) := x ps in
    let (ops,o) := so in
    match ops with
    | Some s =>
    (ps',
    (MkMPSM
    (sm_S      sm)
    (sm_halted sm)
    (sm_update sm)
    s,o))
    | None =>
    (ps',
    (MkMPSM
    (sm_S      sm)
    true
    (sm_update sm)
    (sm_state  sm),
    o))
    end.

    Definition call_proc {n:nat} (nm : CompName) (i : cio_I (fio nm)) : M_n n (cio_O (fio nm)) :=
    fun (l : n_procs n) =>
    match find_name nm l with
    | Some pr =>
    match app_m_proc pr i with
    | Some f =>
    match f (decr_n_procs l) with
    | (l',(pr',o)) => (replace_subs (replace_name pr' l) l',o)
    end
    | None => (l,cio_default_O (fio nm))
    end
    | None => (l,cio_default_O (fio nm))
    end.

    Definition build_mp_sm {n}
    {S}
    {nm  : CompName}
    (upd : M_Update n nm S)
    (s   : S) : MP_StateMachine (n_proc n) nm :=
    MkMPSM S false upd s.

    Definition build_m_sm {n}
    {St}
    {nm  : CompName}
    (upd : M_Update n nm St)
    (s   : St) : M_StateMachine (S n) nm :=
    inl (build_mp_sm upd s).

## list_util1.v
### Lemma


    Lemma norepeatsb_as_no_repeats :
    forall {A} (deq : Deq A) l,
    norepeatsb deq l = true <-> no_repeats l.

    Lemma norepeatsb_implies_no_repeats :
    forall {A} (deq : Deq A) l, norepeatsb deq l = true -> no_repeats l.

    Lemma no_repeats_mapin :
    forall {A B} (l : list A) (F : forall a (i : In a l), B),
    no_repeats l
    -> (forall a b (i : In a l) (j : In b l), F a i = F b j -> a = b)
    -> no_repeats (mapin l F).

    Lemma no_repeats_seq :
    forall l n, no_repeats (seq n l).

    Lemma no_repeats_NRlist :
    forall {A} (l : NRlist A), no_repeats l.

    Lemma in_remove_iff :
    forall {A} (dec : Deq A) x a l,
    In x (remove dec a l) <-> (In x l /\ x <> a).

    Lemma length_remove_le :
    forall {A} (dec : Deq A) a (l : list A),
    length (remove dec a l) <= length l.

    Lemma length_remove_lt :
    forall {A} (dec : Deq A) a (l : list A),
    In a l
    -> length (remove dec a l) < length l.

    Lemma member_of_larger_list :
    forall {A} (dec : Deq A) (l2: NRlist A) l1,
    length l1 < length l2
    -> exists x, In x l2 /\ ~ In x l1.

    Lemma member_of_larger_list2 :
    forall {A} (dec : Deq A) (l2 l1 : list A),
    no_repeats l2
    -> length l1 < length l2
    -> exists x, In x l2 /\ ~ In x l1.

    Lemma in_remove :
    forall {T} x y eq (l : list T),
    In x (remove eq y l) <-> (x <> y /\ In x l).

    Lemma in_diff :
    forall {T} (l1 l2 : list T) x eq,
    In x (diff eq l1 l2)
    <->
    (In x l2 /\ ~In x l1).

    Lemma subset_diff :
    forall {A} eq (l1 l2 l3 : list A),
    subset (diff eq l1 l2) l3
    <->
    subset l2 (l3 ++ l1).

    Lemma subset_diff_l_same_r :
    forall {A} eq (l1 l2 : list A),
    subset (diff eq l1 l2) l2.

    Lemma remove_comm :
    forall {T} eq (l : list T) x y,
    remove eq x (remove eq y l) = remove eq y (remove eq x l).

    Lemma diff_remove :
    forall {T} eq (l1 l2 : list T) x,
    diff eq l1 (remove eq x l2) = remove eq x (diff eq l1 l2).

    Lemma disjoint_remove_l :
    forall {A} eq x (l1 l2 : list A),
    disjoint (remove eq x l1) l2 <-> disjoint l1 (remove eq x l2).

    Lemma disjoint_diff_l :
    forall {A} eq (l1 l2 l3 : list A),
    disjoint (diff eq l1 l2) l3 <-> disjoint l2 (diff eq l1 l3).

    Lemma diff_nil_if_subset :
    forall {A} eq (l1 l2 : list A),
    subset l2 l1
    -> diff eq l1 l2 = [].

    Lemma diff_same :
    forall {A} eq (l : list A),
    diff eq l l = [].

    Lemma disjoint_nil_r :
    forall {T} (l : list T), disjoint l [].

    Lemma disjoint_diff_l_same_l :
    forall {A} eq (l1 l2 : list A),
    disjoint (diff eq l1 l2) l1.

    Lemma implies_no_repeats_remove :
    forall {T} dec a (l : list T),
    no_repeats l
    -> no_repeats (remove dec a l).

    Lemma implies_no_repeats_diff :
    forall {T} dec (l1 l2 : list T),
    no_repeats l2 -> no_repeats (diff dec l1 l2).

    Lemma length_remove_if_no_repeats :
    forall {T} deq (a : T) l,
    no_repeats l
    -> length (remove deq a l)
    = if in_dec deq a l
    then pred (length l)
    else length l.

    Lemma no_repeats_implies_le_length_diff :
    forall {A} dec (l1 l2 : list A),
    no_repeats l2
    -> length l2 - length l1 <= length (diff dec l1 l2).

    Lemma members_of_larger_list :
    forall {A} (dec : Deq A) (l2 l1 : list A),
    no_repeats l2
    -> exists l,
    subset l l2
    /\ disjoint l l1
    /\ no_repeats l
    /\ length l2 - length l1 <= length l.

    Lemma members_of_larger_list_2 :
    forall {A} (dec : Deq A) (l2 l1 : NRlist A),
    exists l,
    subset l l2
    /\ disjoint l l1
    /\ no_repeats l
    /\ length l2 - length l1 <= length l.

    Lemma subset_cons_l_implies_in :
    forall {A} (a : A) l1 l2,
    subset (a :: l1) l2
    -> In a l2.

## EventOrderingLemmas.v
### Definition


    Definition eq_MkSubEvent
    (eo : EventOrdering)
    (e e1 e2 : Event)
    (b1 : subEventOrdering_cond_bool e e1)
    (b2 : subEventOrdering_cond_bool e e2)
    (eqe : e1 = e2)
    (eqc : match eqe in _ = e2 return subEventOrdering_cond_bool e e2 with eq_refl => b1 end = b2)
    : MkSubEvent e e1 b1 = MkSubEvent e e2 b2
    := match eqe as eqe
    in _ = e2
    return forall b2 : subEventOrdering_cond_bool e e2,
    match eqe in _ = e2 return subEventOrdering_cond_bool e e2
    with eq_refl => b1 end = b2
    -> MkSubEvent e e1 b1 = MkSubEvent e e2 b2
    with
    | eq_refl => fun e2 eqc => match eqc with eq_refl => eq_refl (MkSubEvent e e1 b1) end
    end b2 eqc.

    Definition sub_sub_event2sub_event
    (eo  : EventOrdering)
    (e   : Event)
    (e'  : subEventOrdering_type e)
    (e'' : @subEventOrdering_type pn pk pm (subEventOrdering e) e')
    : @subEventOrdering_type pn pk pm eo e'.

    Definition all_correct (eo : EventOrdering) := forall (e : Event), isCorrect e.

    
    Lemma isCorrect_implies_msg :
    forall (eo : EventOrdering)  (e : Event),
    isCorrect e -> exists m, trigger e = Some m.

### Lemma


    Section EventOrderingLemmas.

    Context { pd  : @Data }.

    Lemma isFirst_mkSubOrderingLe_eq :
    forall {eo : EventOrdering} {e : Event} (p : e ⊑ e),
    @isFirst _ _ _ (subEventOrdering e) (mkSubOrderingLe p).

    Lemma not_first_sub_event_ordering :
    forall (eo : EventOrdering) (e e' : Event) (p : (e') ⊑ (e)),
    ~ isFirst e
    -> (e') ⊑ (local_pred e)
    -> ~ @isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p).

    Lemma local_mkSubOrderingLe :
    forall {eo : EventOrdering}
    {e e' : Event}
    (q : (e') ⊑ (e))
    (p : (e') ⊑ (local_pred e)),
    @local_pred _ _ _ (subEventOrdering e') (mkSubOrderingLe q)
    = mkSubOrderingLe p.

    Lemma localHappenedBeforeLe_subEventOrdering_implies :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
    @localHappenedBeforeLe pn pk pm (subEventOrdering e) e1 e2
    -> @localHappenedBeforeLe pn pk pm eo e1 e2.

    Lemma implies_localHappenedBeforeLe_subEventOrdering :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
    @localHappenedBeforeLe pn pk pm eo e1 e2
    -> @localHappenedBeforeLe pn pk pm (subEventOrdering e) e1 e2.

    Lemma localHappenedBeforeLe_subEventOrdering_iff :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
    @localHappenedBeforeLe pn pk pm (subEventOrdering e) e1 e2
    <->
    @localHappenedBeforeLe pn pk pm eo e1 e2.

    Lemma localHappenedBefore_subEventOrdering_implies :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
    @localHappenedBefore pn pk pm (subEventOrdering e) e1 e2
    -> @localHappenedBefore pn pk pm eo e1 e2.

    Lemma implies_localHappenedBefore_subEventOrdering :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
    @localHappenedBefore pn pk pm eo e1 e2
    -> @localHappenedBefore pn pk pm (subEventOrdering e) e1 e2.

    Lemma localHappenedBefore_subEventOrdering_iff :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
    @localHappenedBefore pn pk pm (subEventOrdering e) e1 e2
    <->
    @localHappenedBefore pn pk pm eo e1 e2.

    Lemma isFirst_mkSubOrderingLe :
    forall (eo : EventOrdering) (e e' : Event) (q : (e') ⊑ (e)),
    @isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe q)
    -> e' = e.

    Lemma event_le_local_pred :
    forall (eo : EventOrdering) (e : Event),
    (e) ⊑ (local_pred e)
    -> isFirst e.

    Lemma localHappenedBeforeLe_implies_or :
    forall {eo : EventOrdering} {e' e : Event} (p : e' ⊑ e),
    e' = e \/ e' ⊑ (local_pred e).

    Lemma not_isFirst_implies_le_local_pred :
    forall (eo : EventOrdering) (e' e : Event) (p : e' ⊑ e),
    ~ @isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)
    -> e' ⊑ (local_pred e).

    Lemma isFirst_localHappenedBeforeLe_implies_eq :
    forall {eo : EventOrdering} {e' e : Event} (p : e' ⊑ e),
    isFirst e -> e' = e.

    Lemma not_isFirst_mkSubOrderingLe_implies_isFirst :
    forall (eo : EventOrdering) (e' e : Event) (p : e' ⊑ e),
    ~ @isFirst _ _ _ (subEventOrdering e') (mkSubOrderingLe p)
    -> ~ isFirst e.

    Lemma localHappenedBeforeLe_implies_or2 :
    forall (eo : EventOrdering) (e e' : Event),
    e ⊑ e' <-> (e = e' \/ e ⊏ e').

    Lemma localHappenedBeforeLe_local_pred_implies_localHappenedBefore :
    forall (eo : EventOrdering) (e e' : Event),
    ~ (isFirst e)
    -> e' ⊑ (local_pred e)
    -> e' ⊏ e.

    Lemma localHappenedBefore_implies_le_local_pred :
    forall (eo : EventOrdering) (e e' : Event),
    e ⊏ e'
    -> e ⊑ (local_pred e').

    Lemma happenedBeforeLe_subEventOrdering_implies :
    forall (eo : EventOrdering) (e : Event) (e1 e2 : subEventOrdering_type e),
    @happenedBeforeLe pn pk pm (subEventOrdering e) e1 e2
    -> @happenedBeforeLe pn pk pm eo e1 e2.

    Lemma isFirstSubEvent_implies :
    forall (eo : EventOrdering) (e : Event) (e' : subEventOrdering_type e),
    @isFirst _ _ _ (@subEventOrdering _ _ _ eo e) e' ->
    if name_dec (loc e) (loc e')
    then e = e'
    else isFirst (sub_eo_event e e').

    Lemma implies_isFirstSubEvent :
    forall (eo : EventOrdering) (e : Event) (e' : subEventOrdering_type e),
    (if name_dec (loc e) (loc e') then e = e' else isFirst (sub_eo_event e e'))
    -> @isFirst _ _ _ (@subEventOrdering _ _ _ eo e) e'.

    Lemma isFirstSubEvent_iff :
    forall (eo : EventOrdering) (e : Event) (e' : subEventOrdering_type e),
    @isFirst _ _ _ (@subEventOrdering _ _ _ eo e) e'
    <->
    if name_dec (loc e) (loc e')
    then e = e'
    else isFirst (sub_eo_event e e').

    Lemma subEventOrdering_trigger_sub_eo :
    forall (eo  : EventOrdering)
    (e   : Event)
    (e'  : subEventOrdering_type e)
    (e'' : @subEventOrdering_type _ _ _ (subEventOrdering e) e'),
    @subEventOrdering_trigger _ _ _ (@subEventOrdering _ _ _ eo e) e' e''
    = @subEventOrdering_trigger _ _ _ eo (@sub_eo_event _ _ _ eo e e') (sub_sub_event2sub_event eo e e' e'').

    Lemma subEventOrdering_trigger_sub_eo2 :
    forall (eo  : EventOrdering)
    (e   : Event)
    (e'  : subEventOrdering_type e),
    subEventOrdering_trigger e e'
    = trigger e'.

    Lemma sub_eo_event_sub_sub_event2sub_event :
    forall (eo  : EventOrdering)
    (e   : Event)
    (e'  : subEventOrdering_type e)
    (e'' : @subEventOrdering_type _ _ _ (subEventOrdering e) e'),
    @sub_eo_event
    _ _ _
    eo
    (@sub_eo_event pn pk pm eo e e')
    (sub_sub_event2sub_event eo e e' e'')
    = sub_eo_event _ (sub_eo_event _ e'').

    Lemma implies_eq_in_sub_eo :
    forall (eo : EventOrdering)
    (e : Event)
    (e1 e2 : subEventOrdering_type e),
    sub_eo_event e e1 = sub_eo_event e e2
    -> e1 = e2.

    Lemma sub_eo_local_pred_if_not_first :
    forall (eo : EventOrdering)
    (e  : Event)
    (e' : subEventOrdering_type e),
    ~ @isFirst _ _ _ (@subEventOrdering _ _ _ eo e) e'
    ->
    @sub_eo_event
    _ _ _ eo e
    (@local_pred
    _ _ _
    (@subEventOrdering pn pk pm eo e) e')
    = @local_pred _ _ _ eo (@sub_eo_event _ _ _ eo e e').

    Lemma subEventOrdering_loc_local_pred :
    forall (eo : EventOrdering) (e : Event) (e' : subEventOrdering_type e),
    subEventOrdering_loc e (@local_pred _ _ _ (@subEventOrdering pn pk pm eo e) e')
    = loc e'.

    Lemma sub_sub_event2sub_event_mkSubEventOrderingLe :
    forall (eo  : EventOrdering)
    (e   : Event)
    (e'  : Event)
    (e'' : subEventOrdering_type e')
    (p   : e' ⊑ e)
    (q   : e'' ⊑ e)
    (p0  : @localHappenedBeforeLe _ _ _ (subEventOrdering e') e'' (mkSubOrderingLe p)),
    @sub_sub_event2sub_event
    eo e' e''
    (@mkSubOrderingLe
    _ _ _
    (subEventOrdering e')
    e''
    (mkSubOrderingLe p)
    p0)
    = mkSubOrderingLe q.

    Lemma isCorrect_implies_msg :
    forall (eo : EventOrdering)  (e : Event),
    isCorrect e -> exists m, trigger e = Some m.

    End EventOrderingLemmas.

    
    
    Hint Resolve isFirst_mkSubOrderingLe_eq : eo.

## Quorum.v
### Definition


    Definition nat_n (n : nat) : Set := {m : nat | m <? n = true}.

    
    Record bijective {A B} (f : A -> B) :=
    {
    bij_inv : B -> A;
    bij_id1 : forall x : A, bij_inv (f x) = x;
    bij_id2 : forall y : B, f (bij_inv y) = y;
    }.

    Definition injective {A B} (F : A -> B) :=
    forall n m, F n = F m -> n = m.

    Definition mk_nat_n {x n : nat} (p : x < n) : nat_n n :=
    exist _ x (leb_correct _ _ p).

    Definition nodes : list node_type :=
    mapin
    (seq 0 num_nodes)
    (fun n i => bij_inv node_bij (mk_nat_n (seq_0_lt i))).

### Lemma


    Lemma nat_n_deq: forall n, Deq (nat_n n).

    Proof.

    Lemma nodes_no_repeats : no_repeats nodes.

    Proof.

    Lemma length_nodes : length nodes = num_nodes.

    Proof.

    Lemma nodes_prop : forall (x : node_type), In x nodes.

    Proof.

    Lemma num_nodes_list_le :
    forall (l : NRlist node_type), length l <= num_nodes.

    Lemma overlapping_quorums :
    forall (l1 l2 : NRlist node_type) n m,
    n <= length l1
    -> m <= length l2
    -> exists good,
    (n + m) - num_nodes <= length good
    /\ no_repeats good
    /\ subset good l1
    /\ subset good l2.

    Lemma overlapping_quorums_same_size :
    forall (l1 l2 : NRlist node_type) n,
    n <= length l1
    -> n <= length l2
    -> exists l,
    (2 * n) - num_nodes <= length l
    /\ no_repeats l
    /\ subset l l1
    /\ subset l l2.

    Lemma overlapping_quorums_different_sizes :
    forall (l1 l2 : NRlist node_type) n m,
    num_nodes - n < m
    -> n <= length l1
    -> m <= length l2
    -> exists good,
    1 <= length good
    /\ no_repeats good
    /\ subset good l1
    /\ subset good l2.

