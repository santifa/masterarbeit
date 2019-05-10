(* A simple test on how to extract code from something written in coq *)
Section square_root.
Require Import Compare_dec.

(* define the search of some nat with the prop n*n <= m -> n is square of m *)
Fixpoint square_root (n:nat) (m:nat): nat :=
  if le_lt_dec (n*n) m then
  if le_lt_dec (S n * S n) m then S n else n
  else
    match n with
    | 0 => 0
    | 1 => 1
    | (S (S n')) => square_root n' m
    end.

(* define some handy call *)
Definition square (n:nat) : nat := square_root n n.

(* test some examples which get not extracted *)
Compute (square 0).
Compute (square 1).
Compute (square 4).
Compute (square 16).
Compute (square 6).
Compute (square 250).
Compute (square 400).
Compute (square 600).

End square_root.


Require Extraction.
Extraction Language Ocaml.
Set Extraction AccessOpaque.

(* extract the specs *)
Extraction "square_root.ml" square.
(* also generates some interface file mli with the type definitions *)