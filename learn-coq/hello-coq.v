(* tutorial: https://coq.inria.fr/tutorial/1-basic-predicate-calculus 
 * Some notices from the basic tutorial to the coq language Gallina *)

(* Scope the code with sections *)
Section Declaration.
(* Declare basic variables by associating names with specifications.
 * Specifications (types of gallina) are:
 * logical propositions: Prop
 * mathematical collections: Set
 * abstract types: Type 
 *)
(* let n be a natural number *)
Variable n: nat.

(* let n be a positive natural number *)
Hypothesis Pos_n: (gt n 0).
(* gt is a function which signature is a composition 
 * of two abstract types to produce a proposition. *)
Check gt.
(* Defintions are used to introduce links between names and well-typed values.
 * A definition may take arguments and type specification. *)
(* let one be the successor of zero *)
Definition one := (S 0).
(* let two be the successor of one *)
Definition two: nat := (S one).
(* let double take one argument and return the number of twice the argument *)
Definition double (m : nat) := plus m m : nat.
Check double.

(* let add_n take one arg and return add the argument 
 * to the global variable n *)
Definition add_n (m:nat) := plus m n.
(* Quantify a proposition with the universal argument 
 * which has an explicit type*)
Check (forall m:nat, gt m 0).
(* Leave a scope *)
End Declaration.

Section Minimal_logic.
Variables A B C: Prop.

(* Symbols may be overloaded *)
Check (A->B).

(* Start the proof engine with the Goal keyword and some conjecture
 * the proof mode show the judgment which is the declarations along with 
 * the local hypothesis. Under the line the goal is shown. 
 * the proof mode allows tactics which are primitives for combining proofs *)
Goal (A -> B -> C) -> (A -> B) -> A -> C.
(* intro breaks up implication goals using the lhs as local hyptohesis *)
intro H.
(* Apply multiple times in one step. *)
intros H' HA.
(* apply the hypothesis H and try to provide the truth for A and B *)
apply H.
(* solve the first subgoal with the hypothesis HA *)
exact HA.
(* solve the second subgoal *)
apply H'.
(* use the local assumptions for solving the rest *)
assumption.
(* finish the proof and end the proof engine *)
Qed.

(* A lemma binds a name to a conjecture *)
Lemma distr_impl: ((A->(B->C))->(A->B)->(A->C)).
(* let the system generate local hypothesis names *)
intros.
(* compose tactics togehter with tactic combinators 
 * T1 ; T2 - apply T1 and afterwards T2 to all subgoals 
 * T ; [T1|..|Tn] - apply T and T1 to the first subgoal ... 
 * Tn to the nth subgoal *) 
apply H; [ assumption | apply H0 ; assumption].
(* apply H. exact H1. apply H0. assumption. *)
Qed.

(* simple conjectures can be proved by the auto tactic *)
Lemma distr_impl2: ((A->(B->C))->(A->B)->(A->C)).
auto.
(* intros. apply H; [assumption | apply H0; assumption]. *)
Qed.

Lemma and_commutative : A /\ B -> B /\ A.
intro H.
(* break up the conjunction H and use it to construct the goal *)
elim H.
(* use the intros tactic and split up a conjunction *)
split.
apply H1.
apply H0.
Qed.

Lemma or_commutative: A \/ B -> B \/ A.
(* or use the desctruct. tactic to to combine elim intro and clear *)
intro; elim H.

intro HA.
(* remove a local hyptothesis *)
clear H.
(* use the tactics left or right to the choose the subgoal 
 * for the disjunction proof  *)
right.
exact HA.

(* or use the tactic trival. to apply tactics that can solve 
 * the goal in one step *)
intro HA; clear H.
left; exact HA.
Qed.

Lemma distr_and: A -> B /\ C -> (A -> B) /\ (A -> C).
(* auto. can not solve some simple tautologies because it
 * does not try elim tactics, so there is a tauto. tactic for this case. *)
tauto.
Qed.

(* inspect the proof tree which is the corresponding lambda term *)
Print or_commutative.
End Minimal_logic.

Section club.
(* an example of classical propositional reasoning *)
Variable Scottish RedSocks WearKilt Married OutSunday : Prop.
Hypothesis rule1 : ~ Scottish -> WearKilt.
Hypothesis rule2 : WearKilt \/ ~ RedSocks.
Hypothesis rule3 : Married -> ~ OutSunday.
Hypothesis rule4 : OutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> Scottish /\ Married.
Hypothesis rule6 : Scottish -> WearKilt.

(* assume the rules are to strict for any member *)
Lemma NoMember : False.
tauto.
Qed.

Print NoMember.
End club.
(* after ending the sections and removing the hypothesis and variables 
 * the type of NoMember gets generalized *)
Check NoMember.

(* The essence of predicate calculus is to prove theorems by 
 * formal manipulations of uninterpreted functions and predicate symbols. *)
Section Predicate_calculus.
(* The domain of discourse *)
Variable D: Set.
(* the predicate symbol which is a binary relation *)
Variable R: D -> D -> Prop.
(* assume that R is symmetric and transitive *)
Section R_sym_trans.
Hypothesis R_symmetric : forall x y: D, R x y -> R y x.
Hypothesis R_transitive: forall x y z: D, R x y -> R y z -> R x z.

(* proof that R is reflexiv 
 * exists is the expression for existential quantification
 * and povides a witness a : D for the propostion along with the 
 * assumption that a varifies P *)
Lemma refl_if: forall x: D, (exists y, R x y) -> R x x.
(* also processes universal quantification *)
intros x x_rlinked.
(* convert existential quantification into an universal one 
 * and use it on the goal*)
elim x_rlinked.
(* process forall and implcation *)
intros y Rxy.
apply R_transitive with y.
assumption.
apply R_symmetric.
assumption.
Qed.
End R_sym_trans.

(* declare an unary predicate and a constant *)
Variable P: D -> Prop.
Variable d: D.

(* proof that a universal predicate is non-empty or existential quantification
 * follows from universal one *)
Lemma weird: (forall x: D, P x) -> exists a, P a.
intros univP.
exists d; trivial.
Qed.

(* Smullyan's drinkers paradox:
 * In an non-empty bar, there is a person such that if she drinks, 
 * everyone drinks. 
 * Model: bar - Set D ; drinking - Predicate P ; *)
(* local hypothesis for the excluded middle *)
Hypothesis EM: forall A: Prop, A \/ ~ A.
Lemma drinker: exists x: D , P x -> forall x: D, P x.
(* the proofs direction is wether or not someones doesn't drink *)
elim (EM (exists x, ~P x)).
intros (Tom, Tom_doesnt_drink).
exists Tom.
intro Tom_drinks.
(* use coq to figure out the contradictions. *)
contradiction.
(* second case: any person is drinking *)
intro No_nondrinker.
exists d.
intro d_drinks.
intro Dick.
elim (EM (P Dick)).
trivial.
intro dick_doesnt_drink.
absurd (exists x, ~ P x).
trivial.
exists Dick.
trivial.
Qed.

End Predicate_calculus.
(* show the generated proofs of the section *)
Check refl_if.
Check weird.
Check drinker.

Section Predicate_Calculus.
Variables P Q: nat -> Prop.
Variables R: nat -> nat -> Prop.

Lemma PQR:
  forall x y:nat, (R x x -> P x -> Q x) -> P x -> R x y -> Q x.
intros.
(* reintroduce a local assummption into the goal *)
generalize H0.
(* state an intermediate fact which introduces a new subgoal *)
enough (R x x) by auto.
(* clean the goals *)
Abort.
End Predicate_Calculus.

(* Equality is provided in coq in terms of leibniz equality.
 * x = y if x and y are two expressions with the type of the same set *)
Section Equality.
Variable f: nat -> nat.
Hypothesis foo: f 0 = 0.
(* proof conditional equality *)
Lemma L1: forall k:nat, k = 0 -> f k = k.
intros k E.
(* use equation E for left-to-right rewriting 
 * use rewrite <- E for right-to-left rewriting *)
rewrite E.
apply foo.
Qed.

Hypothesis f10: f 1 = f 0.

Lemma L2: f (f 1) = 0.
(* replace some snippet with another and introduce this as another subgoal *)
replace (f 1) with 0.
apply foo.
transitivity (f 0).
symmetry.
exact foo.
symmetry.
exact f10.
Qed.

End Equality.

(* The formal development has two parts to process abstractions.
 * First, proves abstract statements within the predicate calculus 
 * and second, use definitions, which utilize the structure of 
 * mathematical values. *)
Section Definitions.
(* define some universe and develop the theory of sets represented
 * as characteristic predicates from that universe *)
Variable U: Type.
Definition set := U -> Prop.
Definition element (x : U) (S : set) := S x.
Definition subset (A B : set) := 
  forall x : U, element x A -> element x B.

Definition transitive (T : Type) (R : T -> T -> Prop) :=
  forall x y z : T, R x y -> R y z -> R x z.

(* proof that subset is a transitive relation *)
Lemma subset_transitive: transitive set subset.
unfold transitive.
unfold subset at 2.
intros.
unfold subset in H.
(* only unfolds goals head occurence *)
red.
auto.
Qed.

End Definitions.

(* Proof irrelevance: a lemma is considered an opaque definition *)

Section Induction.
(* Enter the realm of inductive types which specifies the existence of
 * concrete mathematical constructions *)

(* declare a Set named bool, the constructors true and false,
 * the proof combinator bool_ind to reason about cases,
 * the if-then-else construct bool_rec and
 * a type level combinator bool_rec *)
Inductive bool: Set := true | false.
Check bool_ind.
Check bool_rect.
Check bool_rec.

(* prove that every boolean is either true or false *)
Lemma duality: forall b: bool, b = true \/ b = false.
intro.
elim b.
left; trivial.
right; trivial.
Qed.

(* define natural numbers as zero or successor *)
Inductive nat: Set := O : nat | S : nat -> nat.
Check nat_ind.
Check nat_rec.

(* define the standard primitive recursion over the more general nat_rec *)
(*Definition prim_rec := nat_rec (fun i : nat => nat).*)
Definition prim_rec := Eval compute in nat_rec (fun i : nat => nat).
(* check the type of prim_rec *)
About prim_rec.

(* program addition with prim_rec *)
Definition addition (n m : nat) :=
  prim_rec m (fun p rec : nat => S rec) n.
Eval compute in (addition (S (S O)) (S (S (S O)))).

(* coq provides the special syntax fixpoint/match for generic primitiv recur *) 
Fixpoint plus (n m : nat) {struct n} : nat := 
  match n with
    | O => m
    | S p => S (plus p m)
  end.
End Induction.

Section Proofs_induction.
Hypothesis eq_S: forall x y : nat, x = y -> S x = S y.

(*Section proofs_by_induction.*)
(* proof n = n + 0 *)
Lemma plus_n_0: forall n: nat, n = plus n O.
intro.
(* split the goal predicate P into the base (P O) and
 * the inductive step forall: y : nat, P y -> P (S y) *)
elim n.
(* simplify with primitive recursion *)
simpl.
trivial.
(* apply the plus constructor *)
simpl.
(* test *)
intros.
elim n0.
trivial.
simpl.
(* end test *)
auto.
Qed.

(* declare plus_n_0 as hint for the auto tactic *)
Hint Resolve plus_n_0.

Lemma plus_n_S: forall n m: nat, S (plus n m) = plus n (S m).
induction n.
simpl.
trivial.
intro.
simpl.
elim IHn.
trivial.
Qed.

Hint Resolve plus_n_S.

(* prove the commutativity of plus *)
Lemma plus_com : forall n m: nat, plus n m = plus m n.
induction m as [ | m IHm ].
simpl.
auto.
simpl.
rewrite <- IHm.
elim plus_n_S.
trivial.
Qed.

End Proofs_induction.

Section Discriminate.
(* define proposition with primitive recursion
 * this one discriminates between the constructors *)
Definition Is_S (n : nat) := 
  match n with
  | O => False
  | S p => True
  end.

Lemma S_Is_S : forall n: nat, Is_S (S n).
simpl.
trivial.
Qed.

(* prove that 0 and S construct different values *)
Lemma no_confusion: forall n: nat, O <> S n.
intros n H.
change (Is_S O).
rewrite H.
simpl.
trivial.
Qed.

Section Logic_programming.
(* define the predicate <= over the type nat *)
Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m: nat, le n m -> le n (S m).
Check le.
Check le_ind.

(* Show n <= m -> n + 1 <= m + 1 *)
Lemma le_n_S: forall n m: nat, le n m -> le (S n) (S m).
intros n m n_le_m.
elim n_le_m.
apply le_n.
intros.
apply le_S.
trivial.
Qed.

(* give the tactics hints about the inductive constructors *)
Hint Constructors le.

(* prove n <= 0 -> n = 0 *)
Lemma tricky: forall n: nat, le n O -> n = O.
intros.
inversion_clear H.
trivial.
Qed.

End Logic_programming.

Section Modules.
(* load modules with the require command. module names resemble the fs *)
Require Import Arith.

(* use Required Export M if the content of the submodule M required
 * by module N should be visible from the calling module. *)

(* Search facts concerning a given predicate *)
Search S le.

(* display only lemmas where the predicate is found in the head *)
SearchHead le.

(* Search allows searching for patterns *)
Search (_ + _).

End Modules.
(* End of the coq tutorial which shows the most basics ideas 
 * and language constructs *)

(* Tutorial: https://coq.inria.fr/tutorial-nahas *)
Section Tutorial_nahas.
(* if you have a prove you have a proof *)
Theorem first_proof: forall A: Prop, A -> A.
Proof.
intros.
trivial.
Qed.

(* forward proof *)
Theorem forward_small: forall A B: Prop, A -> (A -> B) -> B.
Proof.
intros.
pose (proof_B := H0 H).
exact proof_B.
Qed.

(* backward proof *)
Theorem backward_huge: forall A B C: Prop, A -> (A -> B) -> (A -> B -> C) -> C.
Proof.
intros A B C.
intros proof_A A_imp_B A_imp_B_imp_C.
refine (A_imp_B_imp_C _ _).
 exact proof_A.

 refine (A_imp_B _).
 exact proof_A.
Qed.

Require Import Bool.

Theorem or_com: forall A B: Prop, A \/ B -> B \/ A.
Proof.
intros A B Or.
case Or.
 + intros. refine (or_intror H).
 + intros. refine (or_introl H).
Qed.

(* mostly like the first tutorial,
 * so there is nothing really new to note. *)

(* Names:
"Theorem" starts a proof.
"Qed" ends a proof.
"Admitted" ends an incomplete proof.
"Definition" declares a function.
"Fixpoint" declares a recursive function.
"Inductive" declares data types.
"Notation" creates new operators.
"Infix" also creates new operators.
"Show Proof" prints out the current state of the proof.
"Require Import" reads in definitions from a file.
"Check" prints out a description of a type.
"Compute" prints out the result of a function call.
*)


(* Tactics:
RULE: If the subgoal starts with "(forall <name> : <type>, ..." Then use tactic "intros <name>.".
RULE: If the subgoal starts with "<type> -> ..." Then use tactic "intros <name>.".
RULE: If the subgoal matches an hypothesis, Then use tactic "exact <hyp_name>.".
RULE: If you have an hypothesis "<hyp_name>: <type1> -> <type2> -> ... -> <result_type>" OR an hypothesis "<hyp_name>: (forall <obj1>:<type1>, (forall <obj2>:<type2>, ... <result_type> ...))" OR any combination of "->" and "forall", AND you have hypotheses of type "type1", "type2"..., Then use tactic "pose" to create something of type "result_type".
RULE: If you have subgoal "<goal_type>" AND have hypothesis "<hyp_name>: <type1> -> <type2> -> ... -> <typeN> -> <goal_type>", Then use tactic "refine (<hyp_name> _ ...)." with N underscores.
RULE: If your subgoal is "True", Then use tactic "exact I.".
RULE: If your subgoal is "~<type>" or "~(<term>)" or "(not <term>)", Then use tactic "intros".
RULE: If any hypothesis is "<name> : False", Then use tactic "case <name>.".
RULE: If the current subgoal contains a function call with all its arguments, Then use the tactic "simpl.".
RULE: If there is a hypothesis "<name>" of a created type AND that hypothesis is used in the subgoal, Then you can try the tactic "case <name>.".
RULE: If the subgoal's top-most term is a created type, Then use "refine (<name_of_constructor> _ ...).".
RULE: If a hypothesis "<name>" is a created type with only one constructor, Then use "destruct <name> as <arg1> <arg2> ... ." to extract its arguments.
RULE: If a hypothesis "<name>" contain a function call with all its arguments, Then use the tactic "simpl in <name>.".
RULE: If you have a subgoal that you want to ignore for a while, Then use the tactic "admit.".
RULE: If the current subgoal starts "exists <name>, ..." Then create a witness and use "refine (ex_intro _ witness _).".
RULE: If you have a hypothesis "<name> : <a> = <b>" AND "<a>" in your current subgoal Then use the tactic "rewrite <name>.".
RULE: If you have a hypothesis "<name> : <a> = <b>" AND "<b>" in your current subgoal Then use the tactic "rewrite <- <name>.".
RULE: If you have a hypothesis "<name> : (<constructor1> ...) = (<constructor2> ...) OR "<name> : <constant1> = <constant2> Then use the tactic "discriminate <name>.".
RULE: If there is a hypothesis "<name>" of a created type AND that hypothesis is used in the subgoal, AND the type has a recursive definition Then you can try the tactic "elim <name>.".
*)

(* last tutorial: https://www.lri.fr/~paulin/LASER/course-notes.pdf 
 * material: https://www.lri.fr/~paulin/LASER/ *)
Section Tutorial_nahas.
