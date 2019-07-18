(*
 * This file defines an instance of the simple PrimaryBackup
 * example to show the simulation of a defined protocol.
 *)

Require Export Simulator.
Require Export Protocols.PrimaryBackup.PrimaryBackup.
Require Export Ascii String.

(* define the instance *)
Section PrimaryBackupInstance.
  (* simply concatenate multiple strings *)
  Fixpoint str_concat (l : list String.string) : String.string :=
    match l with
    | [] => ""
    | s :: ss => String.append s (str_concat ss)
    end.

  (* ================== TIME ================== *)

  Definition time_I_type : Set := unit.

  Definition time_I_get_time : unit -> time_I_type := fun _ => tt.

  Definition time_I_sub : time_I_type -> time_I_type -> time_I_type := fun _ _ => tt.

  Definition time_I_2string : time_I_type -> string := fun _ => "".

  Global Instance TIME_I : Time.
  Proof.
    exists time_I_type.
    { exact time_I_get_time. }
    { exact time_I_sub. }
    { exact time_I_2string. }
  Defined.

  (* ================== PRETTY PRINTING ================== *)

  (* FIX: to replace when extracting *)
  Definition print_endline : string -> unit := fun _ => tt.
  Definition nat2string (n : nat) : string := "-".

  Definition CR : string := String (ascii_of_nat 13) "".

  Definition nat_n2string {m} (n : nat_n m) : string := nat2string (proj1_sig n).

  Definition msg2string (m : PBmsg) : string :=
    match m with
    |PBinput n => str_concat ["Input ", nat2string n]
    | PBforward n => str_concat ["Forward ", nat2string n]
    | PBackn n => str_concat ["Ackn ", nat2string n]
    | PBreply n => str_concat ["Reply", nat2string n]
    end.

  Definition name2string (n : PBnode) : string :=
    match n with
    | PBprimary => "Primary"
    | PBbackup => "Backup"
    | PBc => "Client"
    end.

  Fixpoint names2string (l : list PBnode) : string :=
    match l with
    | [] => ""
    | [n] => name2string n
    | n :: ns => str_concat [name2string n, ",", names2string ns]
    end.

  Definition delay2string (delay : nat) : string := nat2string delay.

  Definition DirectedMsg2string (dm : DirectedMsg) : string :=
    match dm with
    | MkDMsg msg dst delay =>
       str_concat ["Msg [", msg2string msg, "; Dest ", "[", names2string dst, "];", " Delay ", delay2string delay, "]"]
    end.

  Fixpoint DirectedMsgs2string (l : DirectedMsgs) : string :=
    match l with
    | [] => ""
    | [dm] => DirectedMsg2string dm
    | dm :: dmsgs => str_concat [DirectedMsg2string dm, CR, DirectedMsgs2string dmsgs]
    end.

  Definition TimedDirectedMsg2string (m : TimedDirectedMsg) : string :=
    match m with
    | MkTimedDMsg dm time => str_concat [DirectedMsg2string dm, ":", time_I_2string time]
    end.

  Fixpoint TimedDirectedMsgs2string (l : TimedDirectedMsgs) : string :=
    match l with
    | [] => ""
    | [dm] => TimedDirectedMsg2string dm
    | dm :: dmsgs => str_concat [TimedDirectedMsg2string dm, CR, TimedDirectedMsgs2string dmsgs]
    end.

  Definition MonoSimulationState2string (s : MonoSimulationState) : string :=
    match s with
    | MkMonoSimState ty sys step out_inflight in_inflight delivered =>
      str_concat
        [CR,
         "====== STEP ======",
         CR,
         nat2string step,
         CR,
         "====== IN FLIGHT (from outside the system) ======",
         CR,
         DirectedMsgs2string out_inflight,
         CR,
         "====== IN FLIGHT (from inside the system) ======",
         CR,
         DirectedMsgs2string in_inflight,
         CR,
         "====== DELIVERED ======",
         (* CR, *)
         (* TimedDirectedMsgs2string delivered, *)
         CR
        ]
    end.


  (* Definition primary_state2string (s : PBprimary_state):= *)
  (*   match s with *)
  (*   | PBpst p n => "Primary" *)
  (*   end. *)

  (* Definition backup_state2string (s : PBbackup_state) := *)
  (*   match s with *)
  (*   | PBbst n => "Backup" *)
  (*   end. *)

  Definition state2string (s : PB_state) : string :=
    match s with
    | PBpst p n => str_concat ["Primary ", nat2string n,
                              match p with
                              | PBfree => " free"
                              | PBlocked => " locked"
                              end]
    | PBbst n => str_concat ["Backup ", nat2string n]
    end.

  (* ================== SYSTEM ================== *)


  Definition dummy_initial_state : PB_state :=
    PBpst PBfree 0.

  Definition PBdummySM : MStateMachine PB_state :=
    MhaltedSM dummy_initial_state.

  Definition PBmono_sys : NMStateMachine PB_state :=
    fun name =>
      match name with
      | PBprimary => PBprimarySM
      | PBbackup => PBbackupSM
      | _ => MhaltedSM dummy_initial_state
      end.

  Definition mk_request_to (rep : PBnode) (ts : nat) (opr : nat) : DirectedMsg :=
    (* let ts   := time_stamp ts in *)
    (* let breq := bare_req (opr_add opr) ts (client0 C) in *)
    let dst  := PBprimary in (* the leader *)
    (* let toks := [ pbft_token_stub ] : Tokens in (* we just send empty lists here to authenticate messages *) *)
    (* let req  := req breq toks in *)
    let msg  := PBinput opr in
    MkDMsg msg [dst] 0.

  Definition mk_request (ts : nat) (opr : nat) : DirectedMsg :=
    mk_request_to PBprimary ts opr.

  (* n request starting with number start *)
  Fixpoint mk_requests_start (n start opr : nat) : DirectedMsgs :=
    match n with
    | 0 => []
    | S m => List.app (mk_requests_start m start opr) [mk_request (n + start) opr]
    end.

  Definition mk_requests (n opr : nat) : DirectedMsgs :=
    mk_requests_start n 0 opr.

  Record InitRequests :=
    MkInitRequests
      {
        num_requests     : nat;
        starting_seq_num : nat;
        req_operation    : nat;
      }.

  Definition PBinit_msgs (msgs : DirectedMsgs) : MonoSimulationState :=
    MkInitMonoSimState PBmono_sys msgs.

  Definition PBinit (init : InitRequests) : MonoSimulationState :=
    PBinit_msgs
      (mk_requests_start
         (num_requests init)
         (starting_seq_num init)
         (req_operation init)).

  Definition PBsimul_list (init : InitRequests) (L : list nat) : MonoSimulationState :=
    mono_run_n_steps L (PBinit init).

  Definition PBsimul_list_msgs (msgs : DirectedMsgs) (L : list nat) : MonoSimulationState :=
    mono_run_n_steps L (PBinit_msgs msgs).

  (* [switch] is the list of steps at which we want to switch to sending messages *)
  (*  coming from the outside (from clients) instead of keeping on sending messages *)
  (*  coming from the inside (from replicas). *)
  Definition PBsimul_n
             (init     : InitRequests) (* This is to generate an initial list of requests *)
             (rounds   : Rounds)
             (switches : Switches) : MonoSimulationState :=
    mono_iterate_n_steps rounds switches (PBinit init).

  Definition PBsimul_n_msgs
             (msgs     : DirectedMsgs)
             (rounds   : Rounds)
             (switches : Switches) : MonoSimulationState :=
    mono_iterate_n_steps rounds switches (PBinit_msgs msgs).

End PrimaryBackupInstance.

(* ================== EXTRACTION ================== *)


Extraction Language Ocaml.

(* printing stuff *)
Extract Inlined Constant print_endline => "Prelude.print_coq_endline".
Extract Inlined Constant nat2string    => "Prelude.char_list_of_int".
Extract Inlined Constant CR            => "['\n']".

(* numbers *)
Extract Inlined Constant Nat.modulo    => "(mod)".

(* lists *)
Extract Inlined Constant forallb => "List.for_all".
Extract Inlined Constant existsb => "List.exists".
Extract Inlined Constant length  => "List.length".
Extract Inlined Constant app     => "List.append".
Extract Inlined Constant map     => "List.map".
Extract Inlined Constant filter  => "List.filter".

(* timing stuff *)
Extract Inlined Constant time_I_type     => "float".
Extract Inlined Constant time_I_get_time => "Prelude.Time.get_time".
Extract Inlined Constant time_I_sub      => "Prelude.Time.sub_time".
Extract Inlined Constant time_I_2string  => "Prelude.Time.time2string".

Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.

Definition local_replica (n : name) :=
  match n with
  | PBprimary => @PBprimarySM
  | PBbackup => @PBbackupSM
  | _ => @PBbackupSM
  end.

Extraction "PbReplicaEx.ml" state2string lrun_sm MonoSimulationState2string PBdummySM local_replica.
