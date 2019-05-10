Require Import List ssreflect ssrbool.
From mathcomp Require Import eqtype ssrnat.
(* Require Import ssreflect ssrbool eqtype ssrnat. (* For Coq < 8.5 *) *)


(* Let's see how one would define insertion sort in OCaml:

   let rec insert n l =
     match l with
       | [] -> [n]
       | x::xs -> if n <= x then n::x::xs else x::(insert n xs)

   let rec sort l =
     match l with
       | [] -> []
       | x::xs -> insert x (sort xs)

   As you saw during the lesson, the [insert] function is just some
   particular proof of [nat -> list nat -> list nat]: it is the proof
   that builds a new list by inserting its first arguments into its
   second one. As any proof, it thus can be defined in Coq using tactics.
 *)

Definition insert (n:nat) (l:list nat) : list nat.
Proof.
  (* The OCaml program is a recursive definition over l. I just do
     exactly the same with the elim tactic. The induction hypothesis ih
     is a proof of insert n xs : in fact it is the recursive call. *)
  elim:l => [|x xs ih].
  (* We start with the base case: we return the singleton list
     containing only n. *)
    apply:(n::nil).
  (* We are now in the recursive case. We need to distinguish two cases
     whether n <= x or not. *)
  case h:(n <= x).
  (* We are in the branch where n <= x. In this case, we can immediately
     return the list n::x::xs *)
    apply:(n::x::xs).
  (* We now are in the branch where n > x. In this case, we want to
     return x::(insert n xs). As we said, the recursive call is in fact
     ih. *)
  apply:(x::ih).
  (* Our function is now defined using tactics. [Defined] checks that it
     actually have the right type and defines it. *)
 Defined.


(* We can check on some examples that it is indeed the insert function
   we add in mind. Coq can actually compute with it! *)

Compute (insert 5 (1::2::3::4::6::7::8::9::nil)).
Compute (insert 5 (1::2::3::4::nil)).


(* Now do the same for the sort function, and test it on some examples.
   Hint: it takes only three tactics to define it! *)

Definition sort (l:list nat) : list nat.
Proof.
  elim:l => [|x xs ih].
  apply:nil.
  apply:(insert x ih).
Defined.


Compute (sort (7::9::5::3::0::4::2::1::8::6::nil)).
(* Add your own examples... *)


(* Ok, so far we have understood that we can define function using
   tactics. But our sorting function is no more that the OCaml version:
   we did not prove it was actually returning a list that is sorted!
   With tactics, we will be able to build the sorting function AND proof
   its correctness at the same time... *)


(* First, we need to define for a list of integers what it means to be
   sorted: each element is smaller than all the following elements *)

Fixpoint smaller n l : Prop :=
  match l with
    | nil => true
    | x::xs => n <= x /\ smaller n xs
  end.


Fixpoint sorted l : Prop :=
  match l with
    | nil => true
    | x::xs => smaller x xs /\ sorted xs
  end.


(* We give a very simple fact about smaller: if a is smaller than all
   the elements of a list l, and n <= a, then n is also smaller than all
   the elements of l. *)

Lemma smaller_trans n a l : smaller a l -> n <= a -> smaller n l.
Proof.
  elim:l => /=.
    done.
  move => b l ih [h1 h2] h3.
  split.
    move/(_ a n b):leq_trans => h4.
    by apply:h4.
  by apply:ih.
Defined.


(* For a matter of time, we also give you some arithmetic lemmas that
   you will need:

   o leq_false_lt m n : (m <= n) = false -> (n < m)
   o leq_false_leq n x : (n <= x) = false -> x <= n
   o eq_refl (n:nat) : n == n
   o gtn_eqF m n : m < n -> n == m = false
   o leq_false_neq n a : (n <= a) = false -> n == a = false

   Do not look at the proofs, just look at the statements above. *)

Lemma leq_trans n m p : m <= n -> n <= p -> m <= p.
Proof.
  elim: n m p => [|i IHn] [|m] [|p]; try reflexivity.
        move => h _. apply:h.
      compute. discriminate.
    move => _. compute => h. apply:h.
  by move/(_ m p):IHn.
Defined.


Lemma ltnW m n : m < n -> m <= n.
Proof. by apply:leq_trans. Defined.


Lemma leq_false_lt m n : (m <= n) = false -> (n < m).
Proof.
  elim: m n => [|m IHm] [|n].
        compute. discriminate.
      compute. discriminate.
    reflexivity.
  by move/(_ n):IHm.
Defined.


Lemma leq_false_leq n x : (n <= x) = false -> x <= n.
Proof.
  move => h.
  apply:ltnW.
  by apply:leq_false_lt.
Defined.


Lemma eq_refl (n:nat) : n == n.
Proof.
  elim:n => [|n ih].
    reflexivity.
  exact:ih.
Defined.


Lemma leqNgt m n : (m <= n) = ~~ (n < m).
Proof. by elim: m n => [|m IHm] [|n] //; exact: IHm n. Defined.


Lemma eqn_leq m n : (m == n) = (m <= n <= m).
Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Defined.


Lemma gtn_eqF m n : m < n -> n == m = false.
Proof. by rewrite eqn_leq (leqNgt n) => ->. Defined.


Lemma leq_false_neq n a : (n <= a) = false -> n == a = false.
Proof.
  move => h.
  apply:gtn_eqF.
  by apply: leq_false_lt.
Defined.


(* We are now ready to build the insert function and prove its
   correctness at the same time. To do so, the Coq writing {l | P l}
   that designates a list l that satisfies the predicate P: P is the
   specification of the function.

   The specification of the insert function is the following:
   o if a is smaller that all the elements of l and a <= n then a is
     smaller than all the elements of (insert n l)
   o if l is sorted then (insert n l) is sorted *)

Definition insert_spec n l :
  {l' |
    (forall a, smaller a l -> a <= n -> smaller a l') /\
    (sorted l -> sorted l')}.
Proof.
  (* The proof is a refinement of the proof of [insert], in which we
     also build the proof of the specification of the function. So like
     for defining [insert], we do an induction. *)
  elim:l => [|x xs ih].
  (* We present the base case. The answer is the singleton list
     containing only n, together with a proof that this list satisfies
     the specification. We first give the list, using the exists tactic.
     *)
  exists (n::nil).
  (* Let's now prove the specification. It is a conjunction. *)
  split.
  (* On the first branch, we introduce a. *)
  move => a.
  (* We can simplify this goal: we know what [smaller a nil] and
         [smaller a (n :: nil)] mean. *)
  simpl.
  (* In fact, this goal is trivially proved with done. *)
  done.
  (* Let's simplify the second branch: we know what [sorted nil] and
         [sorted (n :: nil)] mean. *)
  simpl.
  (* In fact, this goal is trivially proved with done. *)
  done.
  (* Now do the recursive case. Do not forget to make a case analysis
       whether n <= x or not. You can destruct a proof of {l | P l}
       using the [case] tactic as usual. *)
  case:ih => [l4 [ih1 ih3]] /=.
  case h:(n <= x).
  exists (n::x::xs) => /=.
  split => //.
  move => [h1 h2].
  do 2 (split => //).
  apply:(smaller_trans _ _ _ h1 h).
  exists (x::l4) => /=.
  split.
  move => a [h1 h2] h3.
  split => //.
    by apply:ih1.
  move => [h1 h2].
  split.
  apply:ih1 => //.
    by apply:leq_false_leq.
      by apply:ih3.
Defined.


(* Let do the same for the sort function. *)

Definition sort_spec (l:list nat) : {l' | sorted l'}.
Proof.
  elim:l => [|x xs [l4 ih]].
    by exists nil.
  case:(insert_spec x l4) => [l5 [_ h2]].
  exists l5.
  by apply:h2.
Defined.

(* We now have defined functions that are correct (with respect to our
   specification) by construction. Finally, Coq offers an extraction
   mechanism, that automatically export them to OCaml, so we are sure
   that the OCaml program is correct by construction. *)

Require Extraction.
Extraction Language Ocaml.
Set Extraction AccessOpaque.


Extraction "insert_sort.ml" sort_spec.


(* Have a look at the file "insert_sort.mli". You observe that the
   function [sort_spec] has type [nat list -> nat list]: the extraction
   mechanism "forgets" the proof of the correctness of this function,
   since it has no signification in OCaml. You can test this extracted
   function using the file "test_sort.ml". *)


(* TO GO FURTHER *)


(* I am sure you all have noticed that our specification is incomplete:
   the sort function must not only return a sorted list, but this list
   must be a permutation of the initial list! We now do the same job
   with a complete specification. *)

(* We first define our notion of permutation: (x::xs) and l2 are a
   permutation if and only if xs and (remove x l2) are. *)

Fixpoint remove a (l:list nat) :=
  match l with
    | nil => None
    | x::xs =>
      if a == x then
        Some xs
      else
        match remove a xs with
          | Some xs' => Some (x::xs')
          | None => None
        end
  end.


Fixpoint permutation l1 l2 : Prop :=
  match l1, l2 with
    | nil, nil => true
    | nil, _ => False
    | x::xs, _ =>
      match remove x l2 with
        | Some l2' => permutation xs l2'
        | None => False
      end
  end.


(* First prove that this relation is reflexive. *)

Lemma permutation_refl l: permutation l l.
Proof.
  elim:l => [|x xs ihxs] //=.
  by rewrite eq_refl.
Defined.


(* Now define insertion and sort with the complete specification. *)

Definition insert_complete n l :
  {l' |
    (forall a, smaller a l -> a <= n -> smaller a l') /\
    (remove n l' = Some l) /\
    (sorted l -> sorted l' /\ permutation (n::l) l')}.
Proof.
  elim:l => [|x xs [l4 [ih1 [ih2 ih3]]]] /=.
    exists (n::nil) => /=.
    split => //.
    split.
      by rewrite eq_refl.
    move => _.
    split => //.
    by rewrite eq_refl.
  case h:(n <= x).
    exists (n::x::xs) => /=.
    split => //.
    rewrite eq_refl.
    split => //=.
    move => [h1 h2].
    split.
      do 2 (split => //).
      apply:(smaller_trans _ _ _ h1 h).
    rewrite eq_refl.
    apply:permutation_refl.
  exists (x::l4) => /=.
  split.
    move => a [h1 h2] h3.
    split => //.
    by apply:ih1.
  split.
    rewrite gtn_eqF.
      by rewrite ih2.
    by apply:leq_false_lt.
  move => [h1 h2].
  split.
    move/(_ h2):ih3 => /= [h3 _].
    split => //.
    apply:ih1 => //.
    by apply:leq_false_leq.
  rewrite leq_false_neq //.
  rewrite ih2 /= eq_refl.
  apply:permutation_refl.
Defined.


Definition sort_complete (l:list nat) : {l' | sorted l' /\ permutation l l'}.
Proof.
  elim:l => [|x xs [l4 [ih1 ih2]]] /=.
    exists nil => //.
  case:(insert_complete x l4) => [l5 [_ [h2 h3]]].
  exists l5.
  move/(_ ih1):h3 => [h3 _].
  split => //.
  rewrite h2.
  apply:ih2.
Defined.


Extraction Language Ocaml.
Set Extraction AccessOpaque.


Extraction "insert_sort.ml" sort_complete.
