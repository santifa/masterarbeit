# API Documentation file

It gives a rough overview about the provided types, lemmas and definitions.

## list_util.v
### Definition


    Definition subset {T} (l1 l2 : list T) :=
    forall v, List.
In v l1 -> List.
In v l2.

    Definition disjoint {T} (l1 l2 : list T) :=
    forall v, List.
In v l1 -> not (List.
In v l2).

    Definition eqset {T} (l1 l2 : list T) :=
    forall x, List.
In x l1 <-> List.
In x l2.

    Definition norepeats {T} (d : Deq T) (l : list T) : Prop :=
    norepeatsb d l = true.

    Definition null {T} (l : list T) : Prop :=
    l = [].

    Definition nullb {T} (l : list T) : bool :=
    if l then true else false.

    Definition map_option {T U} (f : T -> option U) (top : option T) : option U :=
    match top with
    | Some t => f t
    | None => None
    end.

    Definition olist2list {T} (o : option (list T)) : list T :=
    match o with
    | Some l => l
    | None => []
    end.

    Definition opt2list {T} (top : option T) : list T :=
    match top with
    | Some t => [t]
    | None => []
    end.

    Definition contains_only {T} (l : list T) (x : T) : Prop :=
    forall a, In a l -> a = x.

### Inductive


    Inductive sublist {A} : list A -> list A -> Prop :=
    | sublist_nil : forall l, sublist [] l
    | sublist_in  : forall v l1 l2, sublist l1 l2 -> sublist (v :: l1) (v :: l2)
    | sublist_out : forall v l1 l2, sublist l1 l2 -> sublist l1 (v :: l2).

    Inductive no_repeats {T} : list T -> Prop :=
    | no_rep_nil : no_repeats []
    | no_rep_cons :
    forall x xs,
    ~ In x xs
    -> no_repeats xs
    -> no_repeats (x :: xs).

    Inductive adjacent {T} (a b : T) : list T -> Prop :=
    | adjacent_head : forall l, adjacent a b (a :: b :: l)
    | adjacent_tail : forall l c, adjacent a b l -> adjacent a b (c :: l).

    Inductive hasn {A} (a : A) : list A -> nat -> Prop :=
    | hasn_nil : hasn a [] 0
    | hasn_in  : forall l n, hasn a l n -> hasn a (a :: l) (S n)
    | hasn_out : forall v l n, hasn a l n -> a <> v -> hasn a (v :: l) n.

    Inductive has_at_least_n {A} (a : A) : list A -> nat -> Prop :=
    | has_at_least_n_nil : has_at_least_n a [] 0
    | has_at_least_n_in  : forall l n, has_at_least_n a l n -> has_at_least_n a (a :: l) (S n)
    | has_at_least_n_out : forall v l n, has_at_least_n a l n -> has_at_least_n a (v :: l) n.

### Lemma


    Lemma subset_nil_l :
    forall {T} (l : list T), subset [] l.

    Lemma subset_nil_l_iff :
    forall {T} (l : list T), subset [] l <-> True.

    Lemma subset_cons_l :
    forall {T} v (l1 l2 : list T),
    subset (v :: l1) l2 <-> (List.
In v l2 /\ subset l1 l2).

    Lemma subset_refl : forall {T} (l : list T), subset l l.

    Proof.

    Lemma sublist_nil_r :
    forall T (l : list T), sublist l [] <-> l = [].

    Lemma sublist_app_r_weak :
    forall {T} (l l1 l2 : list T),
    sublist l l2
    -> sublist l (l1 ++ l2).

    Lemma sublist_cons_l :
    forall T v (l1 l2 : list T),
    sublist (v :: l1) l2
    <-> exists la lb, l2 = la ++ (v :: lb) /\ sublist l1 lb.

    Lemma sublist_app_l :
    forall T (l l1 l2 : list T),
    sublist (l1 ++ l2) l
    <-> exists la lb, l = la ++ lb /\ sublist l1 la /\ sublist l2 lb.

    Lemma sublist_refl : forall {T} (l : list T), sublist l l.

    Proof.

    Lemma sublist_trans :
    forall {T} (l1 l2 l3 : list T),
    sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.

    Lemma sublist_cons_r :
    forall T v (l1 l2 : list T),
    sublist l1 (v :: l2)
    <->
    (
    l1 = []
    \/
    (exists l, l1 = v :: l /\ sublist l l2)
    \/
    sublist l1 l2
    ).

    Lemma disjoint_nil_l :
    forall {T} (l : list T), disjoint [] l.

    Lemma disjoint_nil_l_iff :
    forall {T} (l : list T), disjoint [] l <-> True.

    Lemma disjoint_sym_impl :
    forall {T} (l1 l2 : list T),
    disjoint l1 l2 -> disjoint l2 l1.

    Lemma disjoint_sym :
    forall {T} (l1 l2 : list T),
    disjoint l1 l2 <-> disjoint l2 l1.

    Lemma disjoint_cons_l :
    forall {T} v (l1 l2 : list T),
    disjoint (v :: l1) l2 <-> ((not (List.
In v l2)) /\ disjoint l1 l2).

    Lemma disjoint_cons_r :
    forall (T : Type) (v : T) (l1 l2 : list T),
    disjoint l1 (v :: l2) <-> disjoint l1 l2 /\ ~ In v l1.

    Lemma list_ind_len :
    forall (A : Type) (P : list A -> Prop),
    (forall l, (forall k, (List.
length k < List.
length l)%nat -> P k) -> P l) ->
    Lemma last_snoc :
    forall {T} (l : list T) v w,
    last (snoc l v) w = v.

    Lemma removelast_snoc :
    forall {T} (l : list T) v, removelast (snoc l v) = l.

    Lemma snoc_cases :
    forall {T} (l : list T),
    l = [] [+] {a : T $ {k : list T $ l = snoc k a}}.

    Lemma length_snoc :
    forall T (n : T) (l : list T),
    length (snoc l n) = S (length l).

    Lemma list_ind_snoc :
    forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (snoc l a)) ->
    forall l : list A, P l.

    Lemma in_snoc :
    forall {T} (a b : T) l,
    In a (snoc l b) <-> (In a l \/ a = b).

    Lemma disjoint_snoc_r :
    forall {T} (a : T) l1 l2,
    disjoint l1 (snoc l2 a)
    <-> (disjoint l1 l2 /\ ~ In a l1).

    Lemma app_snoc :
    forall {T} (a : T) l1 l2,
    (l1 ++ snoc l2 a)%list = snoc (l1 ++ l2) a.

    Lemma sublist_in_implies :
    forall {T} (l1 l2 : list T) v,
    sublist l1 l2 -> In v l1 -> In v l2.

    Lemma eqset_refl :
    forall {T} (l : list T), eqset l l.

    Lemma eqset_trans :
    forall {T} (l1 l2 l3 : list T),
    eqset l1 l2
    -> eqset l2 l3
    -> eqset l1 l3.

    Lemma eqset_cons_swap :
    forall {T} a b (l : list T),
    eqset (a :: b :: l) (b :: a :: l).

    Lemma remove_duplicates_eqset :
    forall {T} dec (l : list T), eqset (remove_duplicates dec l) l.

    Lemma eqset_redundant_left :
    forall {T} (v : T) l1 l2,
    eqset (v :: l1) l2
    -> List.
In v l1
    Lemma in_remove_elt :
    forall {T} (x v : T) dec l,
    List.
In x (remove_elt dec v l)
    Lemma eqset_not_redundant_left :
    forall {T} (v : T) l1 l2 dec,
    eqset (v :: l1) l2
    -> ~ List.
In v l1
    Lemma remove_elt_if_not_in :
    forall {T} (v : T) l dec,
    ~ List.
In v l
    Lemma not_in_remove_elt :
    forall {T} (v : T) l dec,
    ~ In v (remove_elt dec v l).

    Lemma snoc_cons :
    forall {T} (a b : T) l, snoc (a :: l) b = a :: snoc l b.

    Lemma length_list_const :
    forall {T} n (x : T), length (list_const n x) = n.

    Lemma disjoint_app_r :
    forall {T} (l1 l2 l3 : list T),
    disjoint l1 (l2 ++ l3) <-> (disjoint l1 l2 /\ disjoint l1 l3).

    Lemma sublist_app_r :
    forall (T : Type) (l1 l2 l : list T),
    sublist l (l1 ++ l2)
    <->
    exists la lb, l = (la ++ lb)%list /\ sublist la l1 /\ sublist lb l2.

    Lemma disjoint_sublist_app_l_implies :
    forall {T} (l1 l2 l : list T),
    disjoint l l1
    -> sublist (l1 ++ l2) l
    -> l1 = [].

    Lemma disjoint_sublist_app_implies :
    forall {T} (la lb l1 l2 : list T),
    disjoint lb l1
    -> sublist (l1 ++ l2) (la ++ lb)
    -> exists l l', l2 = (l ++ l')%list /\ sublist (l1 ++ l) la /\ sublist l' lb.

    Lemma disjoint_app_l:
    forall (T : Type) (l1 l2 l : list T),
    disjoint (l1 ++ l2) l <-> (disjoint l1 l /\ disjoint l2 l).

    Lemma disjoint_sublist_implies_nil :
    forall {T} (l1 l2 : list T),
    sublist l1 l2
    -> disjoint l1 l2
    -> l1 = [].

    Lemma disjoint_eq_app_implies :
    forall {T} (la lb l1 l2 : list T),
    disjoint lb l1
    -> (l1 ++ l2)%list = (la ++ lb)%list
    -> exists l, l2 = (l ++ lb)%list /\ la = (l1 ++ l)%list.

    Lemma sublist_cons_app_prop1 :
    forall {T} (v1 v2 : T) l1 l2 la lb,
    ~ In v2 lb
    -> disjoint lb l1
    -> sublist (v1 :: (l1 ++ l2)%list) (v2 :: (la ++ lb)%list)
    ->
    (
    (In v1 lb /\ l1 = [])
    \/
    (In v1 (v2 :: la) /\ sublist (v1 :: l1) (v2 :: la))
    ).

    Lemma sublist_implies_le_length :
    forall {T} (l1 l2 : list T),
    sublist l1 l2 -> length l1 <= length l2.

    Lemma implies_sublist_cons_r_weak :
    forall {T} (v : T) l1 l2,
    sublist l1 l2
    -> sublist l1 (v :: l2).

    Lemma implies_sublist_snoc_r_weak :
    forall {T} (v : T) l1 l2,
    sublist l1 l2
    -> sublist l1 (snoc l2 v).

    Lemma norepeatsb_is_no_repeats :
    forall {T} (d : Deq T) (l : list T),
    norepeats d l <-> no_repeats l.

    Lemma norepeatsb_proof_irrelevance :
    forall {T} (d : Deq T) (l : list T) (x y : norepeats d l), x = y.

    Lemma subset_trans :
    forall {T} (l1 l2 l3 : list T),
    subset l1 l2
    -> subset l2 l3
    -> subset l1 l3.

    Lemma nullb_prop :
    forall {T} (l : list T), nullb l = true <-> null l.

    Lemma null_app :
    forall {T} (l1 l2 : list T),
    null (l1 ++ l2) <-> (null l1 /\ null l2).

    Lemma implies_subset_app_lr :
    forall (T : Type) (l1 l2 la lb : list T),
    subset l1 la
    -> subset l2 lb
    -> subset (l1 ++ l2) (la ++ lb).

    Lemma implies_subset_app_r :
    forall (T : Type) (l1 l2 l : list T),
    (subset l l1 \/ subset l l2)
    -> subset l (l1 ++ l2).

    Lemma implies_subset_map_lr :
    forall {A B} (l1 l2 : list A) (f : A -> B),
    subset l1 l2
    -> subset (map f l1) (map f l2).

    Lemma subset_eqset_l :
    forall {T} (l1 l2 l3 : list T),
    subset l1 l2
    -> eqset l1 l3
    -> subset l3 l2.

    Lemma eqset_sym :
    forall {T} (l1 l2 : list T), eqset l1 l2 -> eqset l2 l1.

    Lemma implies_eqset_app_lr :
    forall {T} (l1 l2 l3 l4 : list T),
    eqset l1 l2
    -> eqset l3 l4
    -> eqset (l1 ++ l3) (l2 ++ l4).

    Lemma subset_app_l :
    forall {T} (l1 l2 : list T) l,
    subset (l1 ++ l2) l <-> (subset l1 l /\ subset l2 l).

    Lemma adjacent_in_left :
    forall T a b (l : list T),
    adjacent a b l -> In a l.

    Lemma adjacent_in_left2 :
    forall T a b c (l : list T),
    adjacent a b (snoc l c) -> In a l.

    Lemma adjacent_in_right :
    forall T a b (l : list T),
    adjacent a b l -> In b l.

    Lemma adjacent_app :
    forall T a b (l1 l2 : list T),
    adjacent a b (l1 ++ l2)
    <-> (adjacent a b l1
    \/ adjacent a b l2
    \/ exists l k, l1 = snoc l a /\ l2 = b :: k).

    Lemma adjacent_snoc :
    forall T a b (l : list T) t,
    adjacent a b (snoc l t)
    <-> (adjacent a b l
    \/ exists k, l = snoc k a /\ t = b).

    Lemma in_implies_adjacent :
    forall A (l1 l2 : list A) a,
    0 < length l2
    -> In a l1
    -> exists b, adjacent a b (l1 ++ l2).

    Lemma map_snoc :
    forall {A B} (l : list A) a (F : A -> B),
    map F (snoc l a) = snoc (map F l) (F a).

    Lemma map_option_option_map :
    forall {A B C} (f : B -> option C) (g : A -> B) (o : option A),
    map_option f (option_map g o)
    = map_option (compose f g) o.

    Lemma option_map_option_map :
    forall {T A B} (f : T -> A) (g : A -> B) (top : option T),
    option_map g (option_map f top) = option_map (compose g f) top.

    Lemma seq_n_lt :
    forall m x n, In x (seq n m) -> x < n + m.

    Lemma seq_0_lt :
    forall {x n}, In x (seq 0 n) -> x < n.

    Lemma map_as_mapin :
    forall {A B} (l : list A) (f : A -> B),
    map f l = mapin l (fun a _ => f a).

    Lemma in_mapin :
    forall {A B}
    (l : list A)
    (f : forall a : A, In a l -> B)
    (b : B),
    In b (mapin l f) <-> exists a i, b = f a i.

    Lemma ap_in_mapin :
    forall {A B}
    (l : list A)
    (f : forall a : A, In a l -> B)
    (a : A)
    (i : In a l),
    In (f a i) (mapin l f).

    Lemma mapin_mapin :
    forall {A B C}
    (l : list A)
    (f : forall a : A, In a l -> B)
    (g : forall b : B, In b (mapin l f) -> C),
    mapin (mapin l f) g = mapin l (fun a i => g (f a i) (ap_in_mapin l f a i)).

    Lemma eq_mapins :
    forall {A B}
    (l : list A)
    (f g : forall a : A, In a l -> B),
    (forall (a : A) (i : In a l), f a i = g a i)
    -> mapin l f = mapin l g.

    Lemma in_olist2list :
    forall {T} (o : option (list T)) (x : T),
    In x (olist2list o) <-> exists l, o = Some l /\ In x l.

    Lemma flat_map_map :
    forall A B C ,
    forall f : B -> list C,
    forall g : A -> B,
    forall l : list A,
    flat_map f (map g l) = flat_map (compose f g) l.

    Lemma null_cons :
    forall T x (l : list T),
    ~ null (x :: l).

    Lemma null_flat_map :
    forall (A B : Type) (f : A -> list B) (l : list A),
    null (flat_map f l)
    <-> (forall a : A, In a l -> null (f a)).

    Lemma not_null_flat_map_implies :
    forall {A B} (f : A -> list B) (l : list A),
    ~ null (flat_map f l) <-> exists a, In a l /\ ~ null (f a).

    Lemma flat_map_app:
    forall (A B : Type) (f : A -> list B) (l l' : list A),
    flat_map f (l ++ l') = flat_map f l ++ flat_map f l'.

    Lemma nullb_true_iff :
    forall {T} (l : list T), nullb l = true <-> l = [].

    Lemma mapOption_map :
    forall {A B C} (l : list A) (f : A -> B) (g : B -> option C),
    mapOption g (map f l)
    = mapOption (compose g f) l.

    Lemma mapOption_app :
    forall {A B} (l1 l2 : list A) (f : A -> option B),
    mapOption f (l1 ++ l2)
    = mapOption f l1 ++ mapOption f l2.

    Lemma in_mapOption :
    forall {A B} (l : list A) (f : A -> option B) (b : B),
    In b (mapOption f l)
    <-> exists a, In a l /\ f a = Some b.

    Lemma mapOption_nil :
    forall {A B} (l : list A) (f : A -> option B),
    mapOption f l = []
    <-> forall a, In a l -> f a = None.

    Lemma in_olist2list_option_map_opt2list :
    forall {T} (top : option (option T)) t,
    In t (olist2list (option_map opt2list top))
    <-> top = Some (Some t).

    Lemma no_repeats_cons :
    forall T (x : T) l,
    no_repeats (x :: l) <-> (no_repeats l /\ ~ In x l).

    Lemma no_repeats_app :
    forall T (l1 l2 : list T),
    no_repeats (l1 ++ l2) <-> (no_repeats l1 /\ no_repeats l2 /\ disjoint l1 l2).

    Lemma existsb_false :
    forall {T} (l : list T) f,
    existsb f l = false <-> (forall x, In x l -> f x = false).

    Lemma length_mapin :
    forall {A B} (l : list A) (f : forall (a : A), In a l -> B),
    length (mapin l f) = length l.

    Lemma in_remove_repeats :
    forall {T} deq x (l : list T),
    In x (remove_repeats deq l) <-> In x l.

    Lemma no_repeats_remove_repeats :
    forall {T} deq (l : list T),
    no_repeats (remove_repeats deq l).

    Lemma length_remove_repeats_le :
    forall {T} deq (l : list T),
    length (remove_repeats deq l) <= length l.

    Lemma decidable_no_repeats :
    forall {T} (deq : Deq T) (l : list T), decidable (no_repeats l).

    Lemma decidable_subset :
    forall {T} (deq : Deq T) (l1 l2 : list T), decidable (subset l1 l2).

    Lemma in_keep :
    forall {T} (deq : Deq T) a (l1 l2 : list T),
    In a (keep deq l1 l2) <-> (In a l1 /\ In a l2).

    Lemma implies_no_repeats_keep :
    forall {T} (deq : Deq T) (l1 l2 : list T),
    no_repeats l1 -> no_repeats (keep deq l1 l2).

    Lemma subset_keep_left :
    forall {T} (deq : Deq T) (l1 l2 : list T),
    subset (keep deq l1 l2) l1.

    Lemma subset_keep_right :
    forall {T} (deq : Deq T) (l1 l2 : list T),
    subset (keep deq l1 l2) l2.

    Lemma subset_remove_repeats_l :
    forall {T} (deq : Deq T) (l : list T),
    subset (remove_repeats deq l) l.

    Lemma keep_remove_repeats :
    forall {T} (deq : Deq T) l1 l2,
    keep deq (remove_repeats deq l1) l2
    = remove_repeats deq (keep deq l1 l2).

    Lemma remove_list_nil_r :
    forall {T} (deq : Deq T) l,
    remove_list deq l [] = l.

    Lemma remove_list_cons_r :
    forall {T} (deq : Deq T) l1 l2 a,
    remove_list deq l1 (a :: l2) = remove_elt deq a (remove_list deq l1 l2).

    Lemma remove_list_cons_r_in :
    forall {T} (deq : Deq T) l1 l2 a,
    In a l2
    -> remove_list deq l1 (a :: l2) = remove_list deq l1 l2.

    Lemma remove_repeats_app :
    forall {T} (deq : Deq T) l1 l2,
    remove_repeats deq (l1 ++ l2)
    = remove_list deq (remove_repeats deq l1) l2 ++ remove_repeats deq l2.

    Lemma split_length_as_keep_remove_list :
    forall {T} (deq : Deq T) (l1 l2 : list T),
    length l1 = length (keep deq l1 l2) + length (remove_list deq l1 l2).

    Lemma subset_nil_r :
    forall {T} (l : list T), subset l [] <-> l = [].

    Lemma implies_no_repeats_remove_elt :
    forall {T} (deq : Deq T) x (l : list T),
    no_repeats l -> no_repeats (remove_elt deq x l).

    Lemma no_repeats_implies_remove_repeats_eq :
    forall {T} deq (l : list T),
    no_repeats l
    -> remove_repeats deq l = l.

    Lemma remove_repeats_remove_elt :
    forall {T} deq (a : T) l,
    remove_repeats deq (remove_elt deq a l)
    = remove_elt deq a (remove_repeats deq l).

    Lemma length_remove_elt_if_no_repeats :
    forall {T} deq (a : T) l,
    no_repeats l
    -> length (remove_elt deq a l)
    = if in_dec deq a l
    then pred (length l)
    else length l.

    Lemma subset_implies_eq_length_remove_repeats :
    forall {T} deq (l1 l2 : list T),
    subset l1 l2
    -> length (remove_repeats deq l1) <= length (remove_repeats deq l2).

    Lemma length_find_positions_if_subset_and_no_repeats :
    forall {T} (deq : Deq T) l1 l2,
    subset l2 l1
    -> no_repeats l2
    -> length (find_positions deq l1 l2) = length l2.

    Lemma sublist_map_nth_find_positions_if_same_length :
    forall {A B} (deq : Deq A) (l1 l2 : list A) (l : list B) x,
    length l1 <= length l
    -> sublist (map (fun i => nth i l x) (find_positions deq l1 l2)) l.

    Lemma in_find_positions_implies_lt :
    forall {T} (deq : Deq T) l1 l2 x,
    In x (find_positions deq l1 l2)
    -> x < length l1.

    Lemma in_find_positions_implies_nth_in :
    forall {T} (deq : Deq T) l1 l2 x t,
    In x (find_positions deq l1 l2)
    -> In (nth x l1 t) l2.

    Lemma sublist_singleton_r :
    forall {T} (l : list T) x,
    sublist l [x] <-> (l = [] \/ l = [x]).

    Lemma cons_as_snoc_if_all_same :
    forall {T} (l : list T) z,
    (forall a, In a l -> a = z)
    -> z :: l = snoc l z.

    Lemma implies_sublist_snoc :
    forall {T} (l k : list T) z,
    sublist l k
    -> sublist (snoc l z) (snoc k z).

    Lemma subset_cons_r_snoc_if_all_same :
    forall {T} z x (l k : list T),
    sublist l (x :: k)
    -> (forall a, In a l -> a = z)
    -> sublist l (snoc k x).

    Lemma subset_cons_r_not_in_implies :
    forall {T} c z (l k : list T),
    sublist l (z :: k)
    -> (forall a, In a l -> a = c)
    -> z <> c
    -> sublist l k.

    Lemma count_in_pos_implies :
    forall {T} (deq : Deq T) l x,
    0 < count_in deq l x
    -> In x l.

    Lemma implies_count_out_pos :
    forall {T} (deq : Deq T) l x y,
    In y l
    -> x <> y
    -> 0 < count_out deq l x.

    Lemma count_out_0_implies :
    forall {T} (deq : Deq T) l x y,
    count_out deq l x = 0
    -> x <> y
    -> ~ In y l.

    Lemma unique_largest_count_in :
    forall {T} (deq : Deq T) l x y k,
    x <> y
    ->
    (
    (count_out deq l x + k = count_in deq l x
    -> count_in deq l y + k <= count_out deq l y)
    
    /\
    
    (count_out deq l x = count_in deq l x + k
    -> count_in deq l y <= count_out deq l y + k)
    ).

    Lemma unique_largest_count_in2 :
    forall {T} (deq : Deq T) l x y,
    x <> y
    -> count_out deq l x < count_in deq l x
    -> count_in deq l y < count_out deq l y.

    Lemma contains_only_cons :
    forall {T} (x : T) l a,
    contains_only (x :: l) a
    <-> (contains_only l a /\ x = a).

    Lemma sublist_implies_count_in :
    forall {T} (deq : Deq T) l2 l1 x,
    sublist l1 l2
    -> contains_only l1 x
    -> length l1 <= count_in deq l2 x.

    Lemma length_count_in_out :
    forall {T} (deq : Deq T) x l,
    length l = count_in deq l x + count_out deq l x.

    Lemma implies_subset_cons_lr_same :
    forall {T} (x : T) l1 l2,
    subset l1 l2
    -> subset (x :: l1) (x :: l2).

    Lemma implies_subset_cons_r_weak :
    forall {T} (x : T) l1 l2,
    subset l1 l2
    -> subset l1 (x :: l2).

    Lemma has_at_least_0 :
    forall {A} (a : A) l, has_at_least_n a l 0.

    Lemma has_at_least_le :
    forall {A} (a : A) l n m,
    m <= n
    -> has_at_least_n a l n
    -> has_at_least_n a l m.

## tactics_util.v
## LibTactics.v
### Definition


    [Definition mydatabase := True.
]
    
    Then, to map [mykey] to [myvalue], write the hint:
    [Hint Extern 1 (Register mydatabase mykey) => Provide myvalue.
]
    Definition ltac_database (D:Boxer) (T:Boxer) (A:Boxer) := True.

    
    Notation "'Register' D T" := (ltac_database (boxer D) (boxer T) _) 
    (at level 69, D at level 0, T at level 0).

    Definition rm (A:Type) (X:A) := X.

    
    (** [rm_term E] removes one hypothesis that admits the same
    type as [E].
 *)
    Definition ltac_nat_from_int (x:BinInt.
Z) : nat :=
    match x with
    | BinInt.
Z0 => 0%nat
    Definition ltac_tag_subst (A:Type) (x:A) := x.

    
    (** [ltac_to_generalize] is a specific marker for hypotheses 
    to be generalized.
 *)
    Definition ltac_to_generalize (A:Type) (x:A) := x.

    
    Ltac gen_to_generalize :=
    repeat match goal with 
    H: ltac_to_generalize _ |- _ => generalize H; clear H end.

    Definition eq' := @eq.
 
    
    Hint Unfold eq'.

    (** ** Definitions of automation tactics *)
    
    (** The two following tactics defined the default behaviour of 
    "light automation" and "strong automation".
 These tactics
    (** ** Definitions for parsing compatibility *)
    
    Tactic Notation "f_equal" :=
    f_equal.

    Definition ltac_something (P:Type) (e:P) := e.

    
    Notation "'Something'" := 
    (@ltac_something _ _).

### Inductive


    Inductive Boxer : Type :=
    | boxer : forall (A:Type), A -> Boxer.

    Inductive ltac_No_arg : Set := 
    | ltac_no_arg : ltac_No_arg.

    Inductive ltac_Wild : Set := 
    | ltac_wild : ltac_Wild.

    Inductive ltac_Wilds : Set := 
    | ltac_wilds : ltac_Wilds.

    Inductive ltac_Mark : Type :=
    | ltac_mark : ltac_Mark.

### Lemma


    Lemma ltac_database_provide : forall (A:Boxer) (D:Boxer) (T:Boxer),
    ltac_database D T A.

    Lemma dup_lemma : forall P, P -> P -> P.

    Proof.
 auto.
 Qed.

    Section equatesLemma.

    Variables
    (A0 A1 : Type)
    (A2 : forall (x1 : A1), Type)
    (A3 : forall (x1 : A1) (x2 : A2 x1), Type)
    (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type)
    (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type)
    (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

    Lemma equates_0 : forall (P Q:Prop),
    P -> P = Q -> Q.

    Lemma equates_1 : 
    forall (P:A0->Prop) x1 y1,
    P y1 -> x1 = y1 -> P x1.

    Lemma equates_2 : 
    forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
    P y1 x2 -> x1 = y1 -> P x1 x2.

    Lemma equates_3 : 
    forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
    P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.

    Lemma equates_4 :
    forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
    P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.

    Lemma equates_5 :
    forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3),Prop) x1 x2 x3 x4 x5,
    P y1 x2 x3 x4 x5 -> x1 = y1 -> P x1 x2 x3 x4 x5.

    Lemma equates_6 :
    forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3)(x5:A5 x4),Prop) 
    x1 x2 x3 x4 x5 x6,
    P y1 x2 x3 x4 x5 x6 -> x1 = y1 -> P x1 x2 x3 x4 x5 x6.

    End equatesLemma.

    
    Ltac equates_lemma n :=
    match nat_from_number n with
    | 0 => constr:(equates_0)
    | 1 => constr:(equates_1)
    | 2 => constr:(equates_2)
    | 3 => constr:(equates_3)
    | 4 => constr:(equates_4)
    | 5 => constr:(equates_5)
    | 6 => constr:(equates_6)
    end.
  
    Lemma iff_intro_swap : forall (P Q : Prop), 
    (Q -> P) -> (P -> Q) -> (P <-> Q).

    Lemma ltac_something_eq : forall (e:Type),
    e = (@ltac_something _ e).

    Lemma ltac_something_hide : forall (e:Type),
    e -> (@ltac_something _ e).

    Lemma ltac_something_show : forall (e:Type),
    (@ltac_something _ e) -> e.

## tactics.v
### Definition


    Definition ltac_something (P:Type) (e:P) := e.

    
    Notation "'Something'" := 
    (@ltac_something _ _).

### Lemma


    Lemma tr1 : texists n, n=1.

    Proof.
 exintro 1.
 reflexivity.

    Lemma iff_symm : forall a b, (a <-> b) <-> (b <-> a).

    Proof.

    Lemma prod_sym : forall a b, a ## b -> b ## a.

    Proof.

    Lemma sum_sym : forall a b, a [+] b -> b [+] a.

    Proof.

    Lemma hide_hyp :
    forall (P : Type),
    P <o> (P ## True).

    Lemma ltac_something_eq : forall (e:Type),
    e = (@ltac_something _ e).

    Lemma ltac_something_hide : forall (e:Type),
    e -> (@ltac_something _ e).

    Lemma ltac_something_show : forall (e:Type),
    (@ltac_something _ e) -> e.

## eq_rel.v
### Definition


    Definition decidable (P: Type):= (P + (notT P))%type.

    Definition d2b {x} (d : decidable x) : bool := if d then true else false.

    Definition dassert {x} (d : decidable x) : Prop := d2b d = true.

    
    Inductive void : Type := .

    (*Definition t_iff A B := (A -> B) # (B -> A).
*)
    
    Inductive t_iff (A B : Type) : Type :=
    | t_iff_cons : (A -> B) -> (B -> A) -> t_iff A B.

    Definition tiff_fst :=
    fun {A B : Type} (p : A <o> B) => let (x, _) := p in x.

    Definition tiff_snd :=
    fun {A B : Type} (p : A <o> B) => let (_, y) := p in y.

    Definition c_t_iff : relation Type :=
    fun A B : Type => Cast (A <o> B).

    Definition t_c_iff : relation Type :=
    fun A B : Type => Cast (A -> B) /\ Cast (B -> A).

### Inductive


    Inductive void : Type := .

    
    
    (* ========= Here is a constuctive iff ======== *)
    
    (*Definition t_iff A B := (A -> B) # (B -> A).
*)
    Inductive t_iff (A B : Type) : Type :=
    | t_iff_cons : (A -> B) -> (B -> A) -> t_iff A B.

    Inductive Cast (t : Type) : Prop :=
    | cast : t -> Cast t.

    Inductive Cast2 (p : Prop) : Type :=
    | cast2 : p -> Cast2 p.

### Lemma


    Lemma tiff_trans :
    forall a b c, (a <o> b) -> (b <o> c) -> (a <o> c).

    Lemma tiff_is_prod_implies1 :
    forall A B,
    (A <o> B) <o> ((A -> B) ## (B -> A)).

    Lemma tiff_is_prod_implies2 :
    forall A B : Type,
    ((A -> B) ## (B -> A)) <o> (A <o> B).

    Lemma combine_t_iff_proofs_imp :
    forall {A B A' B' : Type},
    (A <o> A') -> (B <o> B') -> ((A -> B) <o> (A' -> B')).

    Lemma combine_t_iff_proofs_t_iff :
    forall {A B A' B'},
    (A <o> A')
    -> (B <o> B')
    -> ((A <o> B) <o> (A' <o> B')).

    Lemma combine_t_iff_proofs_prod :
    forall {A B A' B'},
    (A <o> A')
    -> (B <o> B')
    -> ((A ## B) <o> (A' ## B')).

    Lemma combine_t_iff_proofs_sum :
    forall {A B A' B'},
    (A <o> A')
    -> (B <o> B')
    -> ((A [+] B) <o> (A' [+] B')).

    Lemma combine_t_iff_proofs_not :
    forall {A A'},
    (A <o> A')
    -> (notT A <o> notT A').

    Lemma t_iff_refl :
    forall A, A <o> A.

    Lemma t_iff_sym :
    forall {A B}, (A <o> B) -> (B <o> A).

    Lemma CType_S : Setoid_Theory Type c_t_iff.

    Proof.

    Lemma TypeC_S : Setoid_Theory Type t_c_iff.

    Proof.

    Lemma test :
    forall a b (*c f*), (a <o> b) -> Cast a.
 (*.
  ## { x : c | f x }.
*)
## UsefulTypes.v
### Definition


    Definition deceq {T : Type} (x y : T) := {x = y} + {x <> y}.

    Definition Deq (T : Type) := forall (x y : T), deceq x y.

    Definition assert (b : bool) : Prop := b = true.

    
    Lemma assert_true : assert true.

    Definition eq_dep_eq_dec'
    (A : Type)
    (dec_eq : forall a b : A, {a = b} + {a <> b})
    (X : A -> Type)
    (a : A)
    (x y : X a)
    (e : eq_dep A X a x a y) : x = y
    := (match e in eq_dep _ _ _ _ a' y' return
    forall e' : a = a',
    (match e' in _ = a' return X a' with
    eq_refl => x
    end) = y'
    with
    | eq_dep_intro =>
    fun e : a = a =>
    match dec_eq_eq A dec_eq a a (eq_refl a) e
    in _ = e
    return match e in _ = a' return X a' with eq_refl => x end = x with
    | eq_refl => eq_refl x
    end
    end) (eq_refl a).

    Definition isInl {A B : Type} 
    (d : A + B) : bool :=
    match d with
    | inl _ => true
    | inr _ => false
    end.

    Definition isInr {A B : Type} 
    (d : A + B) : bool :=
    match d with
    | inl _ => false
    | inr _ => true
    end.

    Definition isInlInl {A B C D: Type} 
    (d : (A + B) + (C + D)) : bool :=
    match d with
    | inl (inl _) => true
    | _ => false
    end.

    Definition liftNth {A: Type} 
    (f : A-> bool) (l : list A ) (n:nat) : bool :=
    match (nth_error l n) with
    | Some x => f x
    | None => false
    end.

    Definition liftInl {A B : Type} 
    (f : A -> bool) (d : A + B) : bool :=
    match d with
    | inl a => f a
    | inr _ => false
    end.

    Definition eq_existsT (A : Type)
    (B : A -> Type)
    (a a' : A)
    (b : B a)
    (b' : B a')
    (ea : a = a')
    (eb : match ea in _ = a' return B a' with eq_refl => b end = b')
    : existT B a b = existT B a' b'
    := match ea as ea
    in _ = a'
    return forall b' : B a',
    match ea in _ = a' return B a' with eq_refl => b end = b'
    -> existT B a b = existT B a' b'
    with
    | eq_refl => fun b' eb => match eb with eq_refl => eq_refl (existT B a b) end
    end b' eb.

    Definition transport {T:Type} {a b:T} {P:T -> Type} (eq:a=b) (pa: P a) : (P b):=
    @eq_rect T a P pa b eq.

    Definition typeCast {A B:Type}  (eq:A=B) (pa: A) : (B):=
    @eq_rect Type A (fun X => X) pa B eq.

    Definition injective_fun {A B: Type} (f: A->B)  :=
    forall (a1 a2: A), (f a1= f a2) -> a1=a2.

    Definition left_identity {S T : Type} (f: S -> T) (g: T-> S): Type :=
    forall s: S , (g (f s)) = s.

    Definition bijection  {S T : Type} (f: S -> T) (g: T-> S) : Type
    := prod (left_identity f g)  (left_identity g f).

    Definition injection {S T : Type} (f: S -> T) :=
    forall (s1 s2 : S), (f s1 = f s2) -> s1=s2.

    Definition equipollent (A B : Type)
    := {f : A -> B $ { g : B -> A $ bijection f g }}.

    Definition Csurjection {S T : Type} (f: S -> T) :=
    forall (t : T), {s : S $ f s =t}.

    Definition Fin (n:nat)
    := {m:nat & if lt_dec m n then unit else void}.

    Definition Finite (T : Type) :=
    {n:nat $ equipollent ( Fin n) T}.

    Definition DeqP (A : Type):=
    forall x0 y0 : A, x0 = y0 \/ x0 <> y0.

    Definition constantFn {A B : Type} (f: A-> B): Type :=
    forall a1 a2, f a1 = f a2.

    Definition DeqBool : Deq bool := bool_dec.

    
    Hint Resolve  deq_prod DeqBool: Deq.

    Definition sigTDeq
    {A : Type} (deq : Deq A)
    (P : A -> Type)
    (deqf : forall (a:A), Deq (P a)) :
    Deq (sigT P).

    Definition Deq2Bool {A : Type} (deq : Deq A) (a b : A)
    : bool.

    Definition is_none {T} (o : option T) : bool :=
    match o with
    | Some _ => false
    | _ => true
    end.

    Definition is_some {T} (o : option T) : bool :=
    match o with
    | Some _ => true
    | _ => false
    end.

### Lemma


    Lemma deq_prod :
    forall (A B : Type), Deq A -> Deq B -> Deq (A * B).

    Lemma assert_true : assert true.

    Proof.

    Lemma not_assert_false : notT(assert false).

    Proof.

    Lemma fold_assert :
    forall b,
    (b = true) = assert b.

    Lemma assert_orb :
    forall a b,
    assert (a || b) -> assert a + assert b.

    Lemma assert_andb :
    forall a b,
    assert (a && b) <-> assert a /\ assert b.

    Lemma assert_of_andb :
    forall a b,
    assert (a && b) <o> assert a ## assert b.

    Lemma not_assert :
    forall b, b = false <-> ~ assert b.

    Lemma not_of_assert :
    forall b, b = false <o> notT (assert b).

    Lemma andb_true :
    forall a b,
    a && b = true <-> a = true /\ b = true.

    Lemma andb_eq_true :
    forall a b,
    a && b = true <o> (a = true) ## (b = true).

    Lemma max_prop1 :
    forall a b, a <= max a b.

    Lemma max_prop2 :
    forall a b, b <= max a b.

    Lemma max_or :
    forall a b,
    (max a b = a) \/ (max a b = b).

    Lemma trivial_if :
    forall T,
    forall b : bool,
    forall t : T,
    (if b then t else t) = t.

    Lemma minus0 :
    forall n, n - 0 = n.

    Lemma pair_inj :
    forall A B,
    forall a c : A,
    forall b d : B,
    (a, b) = (c, d) -> a = c /\ b = d.

    Lemma S_inj :
    forall a b, S a = S b -> a = b.

    Lemma S_le_inj :
    forall a b, S a <= S b -> a <= b.

    Lemma S_lt_inj :
    forall a b, S a < S b -> a < b.

    Lemma not_or :
    forall a b,
    ~ (a \/ b) -> ~ a /\ ~ b.

    Lemma not_over_or :
    forall a b,
    notT(a [+] b) <o> notT a ## notT b.

    Lemma sum_assoc :
    forall a b c,
    (a [+] (b [+] c)) <o> ((a [+] b) [+] c).

    Lemma dep_pair_eq :
    forall {T : Type} {a b : T} (eq : a = b) (P : T -> Prop) (pa : P a) (pb : P b),
    @eq_rect T a P pa b eq = pb
    -> exist P a pa = exist P b pb.

    Lemma min_eq : forall n1 n2,
    n1=n2 -> min n1 n2 = n2.

    Lemma negb_eq_true :
    forall b, negb b = true <o> notT (assert b).

    Lemma left_id_injection: forall {S T : Type} (f: S -> T) (g: T-> S),
    left_identity f g -> injection f.

    Lemma injection_surjection_equipollent
    : forall {S T : Type} (f: S -> T) ,
    injection f
    -> Csurjection f
    -> equipollent S T.

    Lemma Fin_eq:
    forall (n: nat) (fa fb : Fin n),
    (projT1 fa) = (projT1 fb)
    -> fa = fb.

    Lemma Fin_decidable : forall (n:nat), Deq (Fin n).

    Proof.

    Lemma equipollent_Deq : forall (A B:Type),
    Deq A
    -> equipollent A B
    -> Deq B.

    Lemma bool2_Equi :
    equipollent bool (Fin 2).

    Lemma Finite_Deq : forall (A:Type),
    Finite A
    -> Deq A.

    Lemma prod_assoc :
    forall a b c,
    (a ## b) ## c <o> a ## (b ## c).

    Lemma prod_comm :
    forall a b,
    a ## b <o> b ## a.

    Lemma or_true_l :
    forall t, True [+] t <o> True.

    Lemma or_true_r :
    forall t, t [+] True <o> True.

    Lemma or_false_r : forall t, t [+] False <o> t.

    Proof.
 sp; split; sp.
 Qed.

    Lemma or_false_l : forall t, False [+] t <o> t.

    Proof.
 sp; split; sp.
 Qed.

    Lemma and_true_l :
    forall t, True ## t <o> t.

    Lemma not_false_is_true : (notT False) <o> True.

    Proof.
 sp; split; sp.
 Qed.

    Lemma forall_num_lt_d : forall m P,
    (forall n, n < S m -> P n)
    -> P 0 ## (forall n, n <  m -> P (S n) ).

    Lemma not_over_and :
    forall a b,
    decidable a -> (notT(a ## b) <o> notT a [+] notT b).

    Lemma decidable_prod : forall
    (P Q: Type),
    decidable P
    -> decidable Q
    -> decidable (P * Q).

    Lemma UIPReflDeq: forall { A : Type} (deq : Deq A)
    (a: A) (p: a=a), p = eq_refl.

    Lemma DeqDeqp : forall {A : Type},
    Deq A -> DeqP A.

    Lemma DeqTrue:  forall {A} (d : Deq A) (a : A),
    (d a a) = (left (@eq_refl A a)).

    Lemma DeqSym:  forall {A} T (deq : Deq A) (a b: A)
    (f : (a=b) -> T) (c:T),
    match deq a b with
    | left p => f p
    | _ => c
    end
    =
    match deq b a with
    | left p => f (eq_sym p)
    | _ => c
    end.

    Lemma constantMapEq :
    forall {A B : Type} (f: A-> B),
    constantFn f
    -> forall l1 l2,
    length l1 = length l2
    -> map f l1 = map f l2.

    Lemma and_true_r :
    forall t, t ## True <o> t.

    Lemma true_eq_same : forall T (t : T), t = t <o> True.

    Proof.
 sp; split; sp.
 Qed.

    Lemma option_map_Some :
    forall {A B} (f : A -> B) (o : option A) (b : B),
    option_map f o = Some b
    <-> exists a, o = Some a /\ b = f a.

    Lemma is_none_true_iff :
    forall {T} (x : option T), is_none x = true <-> x = None.

    Lemma is_none_false_iff :
    forall {T} (x : option T), is_none x = false <-> exists t, x = Some t.

## universe.v
## tactics2.v
