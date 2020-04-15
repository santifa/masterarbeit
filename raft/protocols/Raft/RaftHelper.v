(*! This file is part of the raft implementation with velisarios. !*)

(** These definitions are small helper function used for the realization. **)
Require Export  Strings.String.

Section RaftHelper.

  Definition option2bool {A : Type} (s : option A) : bool :=
    match s with
    | None => false
    | Some _ => true
    end.

  (** concat a list of string to one string. **)
  Fixpoint str_concat (l : list String.string) : String.string :=
    match l with
    | [] => ""
    | s :: ss => String.append s (str_concat ss)
    end.

  (** auxilary function which converts a list of some type to its representation. **)
  Fixpoint list2string_aux {A : Type} (l : list A) (s : A -> string) : string :=
    match l with
    | [] => ""
    | [x] => s x
    | x :: xs => str_concat [s x, ", ", list2string_aux xs s]
    end.

  (** Convert a list to a string according the rules. **)
  Definition list2string {A : Type} (l : list A) (s : A -> string) : string :=
    str_concat ["[", list2string_aux l s, "]"].

  (** The next three functions are placeholder functions which are later
   ** replaced by real ocaml function within the extraction process. **)
  (** line feed **)
  Definition LF : string := String (ascii_of_nat 10) "".
  Definition print_endline : string -> unit := fun _ => tt.
  Definition nat2string (n : nat) : string := "-".

End RaftHelper.
