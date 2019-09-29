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

  (* Definition time_I_type : Set := unit. *)

  (* Definition time_I_get_time : unit -> time_I_type := fun _ => tt. *)

  (* Definition time_I_sub : time_I_type -> time_I_type -> time_I_type := fun _ _ => tt. *)

  (* Definition time_I_2string : time_I_type -> string := fun _ => "". *)

  (* Global Instance TIME_I : Time. *)
  (* Proof. *)
  (*   exists time_I_type. *)
  (*   { exact time_I_get_time. } *)
  (*   { exact time_I_sub. } *)
  (*   { exact time_I_2string. } *)
  (* Defined. *)

  (* ================== PRETTY PRINTING ================== *)

  (* FIX: to replace when extracting *)
  Definition print_endline : string -> unit := fun _ => tt.
  Definition nat2string (n : nat) : string := "-".
  Definition CR : string := String (ascii_of_nat 13) "".

  Definition msg2string (m : PBmsg) : string :=
    match m with
     |PBinput n => str_concat ["Input ", nat2string n]
     | PBforward n => str_concat ["Forward ", nat2string n]
     | PBackn n => str_concat ["Ackn ", nat2string n]
     | PBreply n => str_concat ["Reply ", nat2string n]
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
       str_concat ["[Msg ", msg2string msg, "; Dest ", "[", names2string dst, "];", " Delay ", delay2string delay, "]"]
    end.

  Fixpoint DirectedMsgs2string (l : DirectedMsgs) : string :=
    match l with
    | [] => ""
    | [dm] => DirectedMsg2string dm
    | dm :: dmsgs => str_concat [DirectedMsg2string dm, CR, DirectedMsgs2string dmsgs]
    end.

  Definition state2string (s : PB_state) : string :=
    match s with
    | PBpst p n => str_concat ["Primary",
                              match p with
                              | PBfree => "(free)"
                              | PBlocked => "(locked)"
                              end, " ", nat2string n]
    | PBbst n => str_concat ["Backup ", nat2string n]
    end.

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
(* Extract Inlined Constant time_I_type     => "float". *)
(* Extract Inlined Constant time_I_get_time => "Prelude.Time.get_time". *)
(* Extract Inlined Constant time_I_sub      => "Prelude.Time.sub_time". *)
(* Extract Inlined Constant time_I_2string  => "Prelude.Time.time2string". *)

Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.


Definition local_replica (n : name) :=
  match n with
  | PBprimary => @PBprimarySM
  | PBbackup => @PBbackupSM
  | _ => @PBbackupSM
  end.

Extraction "PbReplicaEx.ml" state2string lrun_sm local_replica names2string name2string DirectedMsgs2string.
