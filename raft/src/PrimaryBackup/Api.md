# API Documentation file

It gives a rough overview about the provided types, lemmas and definitions.

## PrimaryBackup.v
### Definition


    Definition PB_msg_status (m : PBmsg) : msg_status :=
    match m with
    | PBinput _   => MSG_STATUS_EXTERNAL
    | PBforward _ => MSG_STATUS_INTERNAL
    | PBackn _    => MSG_STATUS_INTERNAL
    | PBreply _   => MSG_STATUS_INTERNAL
    end.

    Definition primary_upd : MSUpdate PBprimary_state :=
    fun state input =>
    match state, input with
    (* if locked, then we're waiting for an acknowledgment *)
    | PBpst PBlocked counter, PBackn n =>
    (PBpst PBfree (counter + n), [MkDMsg (PBreply n) [PBc] 0])
    
    (* if the message is not an acknowledgment, we ignore it *)
    | PBpst PBlocked _, _ => (state, [])
    
    (* if free and message is an input then forward it to backup *)
    | PBpst PBfree counter, PBinput n => (state, [MkDMsg (PBforward n) [PBbackup] 0])
    
    (* otherwise ignore message *)
    | _, _ => (state, [])
    end.

    Definition backup_upd : MSUpdate PBbackup_state :=
    fun state input =>
    match state, input with
    (* if we get a forward message then we store the value and send back and acknowledgment *)
    | PBbst counter, PBforward n =>
    (PBbst (counter + n), [MkDMsg (PBackn n) [PBprimary] 0])
    
    (* otherwise ignore message *)
    | _, _ => (state, [])
    end.

    Definition PBprimarySM : MStateMachine PBprimary_state :=
    mkSSM primary_upd (PBpst PBfree 0).

    Definition PBbackupSM : MStateMachine PBbackup_state :=
    mkSSM backup_upd (PBbst 0).

    Definition PBstate (n : name) :=
    match n with
    | PBprimary => PBprimary_state
    | PBbackup => PBbackup_state
    | _ => unit
    end.

    Definition PBusys : MUSystem PBstate :=
    fun name =>
    match name return StateMachine (PBstate name) msg DirectedMsgs with
    | PBprimary => PBprimarySM
    | PBbackup => PBbackupSM
    | _ => MhaltedSM tt
    end.

    Definition PBsys : System :=
    fun name =>
    match name with
    | PBprimary => build_sprocess primary_upd (PBpst PBfree 0)
    | PBbackup => build_sprocess backup_upd (PBbst 0)
    | _ => haltedProc
    end.

    Definition PBdata_auth : name -> PBmsg -> option name :=
    fun n m => (* n is not used because no message sent to itself *)
    match m with
    | PBinput   _ => Some PBc
    | PBforward _ => Some PBprimary
    | PBackn    _ => Some PBbackup
    | PBreply   _ => Some PBprimary
    end.

    Definition PBhold_keys (eo : EventOrdering) :=
    forall (e : Event),
    match loc e with
    | PBprimary => has_receiving_key (keys e) PBbackup
    | PBbackup  => has_receiving_key (keys e) PBprimary
    | _ => True
    end.

    Definition PBall_correct (eo : EventOrdering) :=
    forall (e : Event), (loc e = PBprimary \/ loc e = PBbackup) -> isCorrect e.

### Inductive


    Inductive PBnode :=
    | PBprimary
    | PBbackup
    | PBc.

    Inductive PBmsg :=
    | PBinput   (n : nat)
    | PBforward (n : nat)
    | PBackn    (n : nat)
    | PBreply   (n : nat).

    Inductive PBprimary_status :=
    | PBlocked
    | PBfree.

    Inductive PBprimary_state :=
    | PBpst (status : PBprimary_status) (counter : nat).

    Inductive PBbackup_state :=
    | PBbst (counter : nat).

### Instance


    Instance PB_I_Node : Node := MkNode PBnode Deq_PBnode.

    
    Instance PB_I_Msg : Msg := MkMsg PBmsg.

    Instance PB_I_MsgStatus : MsgStatus := MkMsgStatus PB_msg_status.

    
    Definition primary_upd : MSUpdate PBprimary_state :=
    fun state input =>
    match state, input with
    (* if locked, then we're waiting for an acknowledgment *)
    | PBpst PBlocked counter, PBackn n =>
    (PBpst PBfree (counter + n), [MkDMsg (PBreply n) [PBc] 0])
    
    (* if the message is not an acknowledgment, we ignore it *)
    | PBpst PBlocked _, _ => (state, [])
    
    (* if free and message is an input then forward it to backup *)
    | PBpst PBfree counter, PBinput n => (state, [MkDMsg (PBforward n) [PBbackup] 0])
    
    (* otherwise ignore message *)
    | _, _ => (state, [])
    end.

    Instance PB_I_Key : Key := MkKey unit unit.

    
    Instance PB_I_Data : Data := MkData PBmsg.

    Instance PB_I_AuthTok : AuthTok := MkAuthTok unit Deq_unit.

    
    Instance PB_I_AuthFun : AuthFun :=
    MkAuthFun
    (fun _ _ => [tt])
    (fun _ _ _ _ => true).

    Instance PB_I_DataAuth : DataAuth := MkDataAuth PBdata_auth.

    
    Instance PB_I_ContainedAuthData : ContainedAuthData :=
    MkContainedAuthData
    (fun m => [MkAuthData m [tt]]) (* tt here says that the data is authenticated *)
    (*(fun a => match a with | MkAuthData m _ => m end)*).

### Lemma


    Lemma Deq_PBnode : Deq PBnode.

    Proof.

    Lemma PBoutput_iff :
    forall (eo : EventOrdering) e m l d,
    In (MkDMsg m l d) (output_system_on_event_ldata PBusys e)
    <->
    (
    (
    exists n,
    m = PBforward n
    /\ l = [PBbackup]
    /\ d = 0
    /\ loc e = PBprimary
    /\ if_not_first
    e
    (exists counter,
    state_sm_on_event PBprimarySM (local_pred e)
    = Some (PBpst PBfree counter))
    /\ event_triggered_by_message e (PBinput n)
    )
    
    \/
    (
    exists n counter,
    m = PBreply n
    /\ l = [PBc]
    /\ d = 0
    /\ loc e = PBprimary
    /\ ~ isFirst e
    /\ state_sm_on_event PBprimarySM (local_pred e)
    = Some (PBpst PBlocked counter)
    /\ event_triggered_by_message e (PBackn n)
    )
    
    \/
    (
    exists n,
    m = PBackn n
    /\ l = [PBprimary]
    /\ d = 0
    /\ loc e = PBbackup
    /\ if_not_first
    e
    (exists counter,
    state_sm_on_event PBbackupSM (local_pred e)
    = Some (PBbst counter))
    /\ event_triggered_by_message e (PBforward n)
    )
    ).

    Lemma PBkey_primary :
    forall (eo : EventOrdering) e,
    loc e = PBprimary
    -> PBhold_keys eo
    -> {k : receiving_key & In k (lookup_receiving_keys (keys e) PBbackup)}.

    Lemma PBkey_backup :
    forall (eo : EventOrdering) e,
    loc e = PBbackup
    -> PBhold_keys eo
    -> {k : receiving_key & In k (lookup_receiving_keys (keys e) PBprimary)}.

    Lemma PBvalidity :
    forall (eo : EventOrdering),
    authenticated_messages_were_sent_or_byz_usys eo PBusys
    -> PBhold_keys eo
    -> PBall_correct eo
    -> forall (e : Event) (n : nat) (dst : list name) (d : nat),
    In (MkDMsg (PBreply n) dst d) (output_system_on_event_ldata PBusys e)
    -> exists e',
    e' ≺ e
    /\ event_triggered_by_message e' (PBinput n).

