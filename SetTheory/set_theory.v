Require Import Classical.

Module SetTheory.

Parameter set : Set.
Parameter IN : set->set->Prop.

Definition EQUAL (x y : set) :=
  (forall z, IN z x <-> IN z y) /\
  (forall w, IN x w <-> IN y w)
.
Notation "x 'in' y" := (IN x y) (at level 10, left associativity).

Axiom AXIOM_OF_EXTENSIONALITY :
  forall x y,
    (forall z, z in x <-> z in y) -> x = y
.
Axiom AXIOM_OF_THE_UNORDERED_PAIR :
  forall a b,
    {c : set | forall x,
      x in c <-> x = a \/ x = b}
.
Axiom AXIOM_OF_SUBSETS :
  forall prop x,
    {y : set | forall u,
      u in y <-> u in x /\ (prop u)}
.
Axiom AXIOM_OF_THE_SUM_SET :
  forall x,
    {y : set | forall u,
      u in y <-> (exists z, z in x /\ u in z)}
.
Axiom AXIOM_OF_THE_POWER_SET :
  forall x,
    {y : set | forall z,
      z in y <-> (forall u, u in z -> u in x)}
.
Axiom AXIOM_OF_INFINITY :
  {s : set | exists x,
    x in s /\ (forall y, ~(y in x)) /\
         (forall y, y in s ->
                         (forall z, (forall w, w in z <-> w in y \/ w = y) ->
  z in s))}
.
Axiom AXIOM_OF_REPLACEMENT :
  forall (prod : set->set->Prop) A,
    (forall x y z, x in A /\ prod x y /\ prod x z -> y = z) ->
    {B : set | forall y, y in B -> (exists x, prod x y)}
.
Axiom AXIOM_OF_FOUNDATION :
  forall x, {a : set | a in x} ->
    {y : set | y in x /\ ~(exists z, z in y /\ z in x)}
.
Axiom AXIOM_OF_CHOICE :
  forall x, {e : set | e in x} ->
    {f : set->set | forall e, e in x /\ (f e) in e}
.

Theorem AXIOM_OF_THE_EMPTY_SET :
  {s | forall a, ~(a in s)}
.
Proof.
  destruct AXIOM_OF_INFINITY as [infset].
  destruct (AXIOM_OF_SUBSETS (fun _ : set => False) infset) as [EMPTYSET].
  exists EMPTYSET.
  intros a H'.
  apply i in H'.
  destruct H' as [_ Hr].
  apply Hr.
Qed.

Theorem emptyset_uniqueness : forall x y,
  (forall e, ~(e in x)) /\ (forall e, ~(e in y)) -> x = y
.
Proof.
  intros x y [Hl Hr].
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  apply Hl in H. destruct H.
  apply Hr in H. destruct H.
Qed.

Definition EMPTYSET : set.
  destruct AXIOM_OF_THE_EMPTY_SET as [S].
  exact S.
Defined.

Theorem EQUAL_definition : forall a b : set,
  EQUAL a b <-> a = b
.
Proof.
  intros a b. split; intros H.
  - destruct H as [Hl Hr].
    apply AXIOM_OF_EXTENSIONALITY.
    intros z. split; intros H';
    apply Hl; apply H'.
  - subst. split; intros x; split; intros H'; apply H'.
Qed.

Theorem no_set_contains_itself : forall S, ~(S in S).
Proof.
  intros S H.
  destruct (AXIOM_OF_THE_UNORDERED_PAIR S S) as [A HA].
  destruct (AXIOM_OF_FOUNDATION A) as [B [Hl Hr]].
  exists S. apply HA. left. reflexivity.
  apply Hr. apply HA in Hl. destruct Hl;
  subst; exists S; split; try (apply H);
  apply HA; left; reflexivity.
Qed.

Theorem no_set_contains_every_set : forall S, exists A, ~(A in S).
Proof.
  intros S. exists S.
  apply no_set_contains_itself.
Qed.

Theorem no_set_is_in_emptyset : forall e, ~(e in EMPTYSET).
Proof.
  intros e H.
  unfold EMPTYSET in H.
  destruct AXIOM_OF_THE_EMPTY_SET.
  apply n in H. destruct H.
Qed.

Definition CUP : set->set->set.
  intros a b.
  destruct (AXIOM_OF_THE_UNORDERED_PAIR a b) as [A HA].
  destruct (AXIOM_OF_THE_SUM_SET A) as [B HB].
  exact B.
Defined.

Definition CAP : set->set->set.
  intros a b.
  destruct (AXIOM_OF_SUBSETS (fun x => x in b) a) as [S _].
  exact S.
Defined.

Definition DIFFERENCE : set->set->set.
  intros a b.
  destruct (AXIOM_OF_SUBSETS (fun x => ~ x in b) a) as [S _].
  exact S.
Defined.

Definition bigcap (total_set : set) : set->set.
  intros A.
  destruct (AXIOM_OF_SUBSETS (fun x => forall a, a in A -> x in a) total_set) as [S _].
  exact S.
Defined.

Definition bigcup : set->set.
  intros A.
  destruct (AXIOM_OF_THE_SUM_SET A) as [S _].
  exact S.
Defined.

Definition subset : set->set->Prop.
  intros a b.
  exact (forall e, e in a -> e in b).
Defined.

Definition SYMM_DIFF : set->set->set.
  intros a b.
  exact (CUP (DIFFERENCE a b) (DIFFERENCE b a)).
Defined.

Definition powerset : set->set.
  intros s.
  destruct (AXIOM_OF_THE_POWER_SET s) as [S _].
  exact S.
Defined.

Definition singleton_set : set->set.
  intros a.
  destruct (AXIOM_OF_THE_UNORDERED_PAIR a a) as [A _].
  exact A.
Defined.

Notation "x 'cup' y" := (CUP x y)(at level 30) : type_scope.
Notation "x 'cap' y" := (CAP x y)(at level 30) : type_scope.
Notation "x '\' y" := (DIFFERENCE x y)(at level 30) : type_scope.
Notation "x 'subseteq' y" := (subset x y)(at level 30) : type_scope.
Notation "x 'subsetneq' y" := ((subset x y) /\ ~(x = y))(at level 30) : type_scope.
Notation "x 'Delta' y" := (SYMM_DIFF x y)(at level 30) : type_scope.

Theorem cup_definition : forall a b e,
  e in (a cup b) <-> e in a \/ e in b
.
Proof.
  intros a b e. split; intros H.
  - unfold CUP in H.
    destruct AXIOM_OF_THE_UNORDERED_PAIR as [A HA].
    destruct AXIOM_OF_THE_SUM_SET as [B HB].
    apply HB in H. destruct H as [z [H1 H2]].
    apply HA in H1. destruct H1; subst;
    [left | right]; apply H2.
  - unfold CUP.
    destruct AXIOM_OF_THE_UNORDERED_PAIR as [A HA].
    destruct AXIOM_OF_THE_SUM_SET as [B HB].
    apply HB. destruct H; [exists a | exists b]; split;
    try (apply HA || apply H); [left | right]; reflexivity.
Qed.

Theorem cap_definition : forall a b e,
  e in (a cap b) <-> e in a /\ e in b
.
Proof.
  intros a b e. split; intros H;
  unfold CAP in *;
  destruct AXIOM_OF_SUBSETS as [A HA];
  apply HA, H.
Qed.

Theorem difference_definition : forall a b e,
  e in (a \ b) <-> e in a /\ ~(e in b)
.
Proof.
  intros a b e. split; intros H;
  unfold DIFFERENCE in *;
  destruct AXIOM_OF_SUBSETS as [A HA];
  apply HA, H.
Qed.

Theorem bigcap_definition : forall total_set a e,
  e in (bigcap total_set a) <-> e in total_set /\ (forall s, s in a -> e in s)
.
Proof.
  intros total_set a e.
  unfold bigcap.
  destruct AXIOM_OF_SUBSETS as [A HA].
  split; intros H; apply HA, H.
Qed.

Theorem bigcup_definition : forall a e,
  e in (bigcup a) <-> (exists s, s in a /\ e in s)
.
Proof.
  intros a e.
  unfold bigcup.
  destruct AXIOM_OF_THE_SUM_SET as [A HA].
  split; intros H; apply HA, H.
Qed.

Theorem powerset_definition : forall a e,
  e in (powerset a) <-> e subseteq a
.
Proof.
  intros a e. split; intros H;
  try (intros e'); unfold powerset in *;
  destruct AXIOM_OF_THE_POWER_SET as [A HA];
  apply HA, H.
Qed.

Theorem singleton_set_definition : forall a e,
  e in (singleton_set a) <-> e = a
.
Proof.
  intros a e. split; intros H.
  - unfold singleton_set in H.
    destruct AXIOM_OF_THE_UNORDERED_PAIR as [A HA].
    apply AXIOM_OF_EXTENSIONALITY.
    destruct (HA e).
    intros z. split; intros H2;
    apply H0 in H; destruct H; subst; apply H2.
  - unfold singleton_set.
    destruct AXIOM_OF_THE_UNORDERED_PAIR as [A HA].
    apply HA; left; apply H.
Qed.

Theorem subseteq_antisymmetric : forall a b,
  a subseteq b -> b subseteq a -> a = b
.
Proof.
  intros a b H1 H2.
  unfold subset in *.
  apply AXIOM_OF_EXTENSIONALITY.
  intros e. split; intros H'. apply H1, H'. apply H2, H'.
Qed.

Theorem subseteq_transitive : forall a b c,
  a subseteq b -> b subseteq c -> a subseteq c
.
Proof.
  intros a b c H1 H2 e H3.
  unfold subset in *.
  apply H2, H1, H3.
Qed.

Theorem emptyset_subseteq_any_set : forall s, EMPTYSET subseteq s.
Proof.
  intros s e H.
  apply no_set_is_in_emptyset in H.
  destruct H.
Qed.

Definition set_constraint (S' : set) (constr : set->Prop) : set.
  destruct (AXIOM_OF_SUBSETS constr S') as [S _].
  exact S.
Defined.

Notation "'{{' '}}'" := EMPTYSET : type_scope.
Notation "'{{' x , .. , y '}}'" := (CUP (singleton_set x) (..(CUP (singleton_set y) {{}})..))(x at level 99) : type_scope.
Notation "'\{' 'x' 'in' S : sP '\}'" := (set_constraint S sP)(S at level 99, sP at level 99) : type_scope.

Example powerset_of_emptyset : powerset {{}} = singleton_set {{}}.
Proof.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply singleton_set_definition.
    apply powerset_definition in H.
    unfold subset in H.
    apply AXIOM_OF_EXTENSIONALITY.
    intros e. split; intros H0.
    + apply H, H0.
    + apply no_set_is_in_emptyset in H0.
      destruct H0.
  - apply powerset_definition.
    apply singleton_set_definition in H.
    subst. intros e H. apply H.
Qed.

Example element_already_in_set : forall s e,
  s cup {{e}} = s <-> e in s
.
Proof.
  intros s e. split; intros H.
  - rewrite <- H. clear H.
    apply cup_definition.
    right. apply cup_definition.
    left. apply singleton_set_definition.
    reflexivity.
  - apply AXIOM_OF_EXTENSIONALITY.
    intros z. split; intros H0.
    + apply cup_definition in H0.
      destruct H0. apply H0.
      apply cup_definition in H0.
      destruct H0.
      apply singleton_set_definition in H0.
      subst. apply H.
      apply no_set_is_in_emptyset in H0.
      destruct H0.
    + apply cup_definition. left. apply H0.
Qed.

Example set_is_singleton_set : forall a b,
  a = {{b}} -> b in a
.
Proof.
  intros a b H. subst.
  apply cup_definition.
  left. apply singleton_set_definition.
  reflexivity.
Qed.

Lemma e_in_S_iff_singleton_set_e_in_powerset_S : forall e S,
  e in S <-> {{e}} in (powerset S)
.
Proof.
  intros e S. split; intros H.
  - apply powerset_definition.
    intros a H0.
    apply cup_definition in H0.
    destruct H0.
    + apply singleton_set_definition in H0.
      subst. apply H.
    + apply no_set_is_in_emptyset in H0. destruct H0.
  - apply powerset_definition in H.
    unfold subset in H.
    apply H, cup_definition.
    left. apply singleton_set_definition.
    reflexivity.
Qed.

Lemma S_subseteq_T_iff_powerset_S_subseteq_powerset_T : forall S T,
  S subseteq T <-> (powerset S) subseteq (powerset T)
.
Proof.
  intros S T. split; intros H e H0.
  - apply powerset_definition.
    apply powerset_definition in H0.
    apply subseteq_transitive with S.
    apply H0. apply H.
  - apply e_in_S_iff_singleton_set_e_in_powerset_S.
    apply e_in_S_iff_singleton_set_e_in_powerset_S in H0.
    apply H, H0.
Qed.

Lemma S_equal_T_iff_powerset_S_equal_powerset_T : forall S T,
  S = T <-> powerset S = powerset T
.
Proof.
  intros S T. split; intros H.
  - subst. reflexivity.
  - apply AXIOM_OF_EXTENSIONALITY.
    intros z. split; intros H0;
    apply e_in_S_iff_singleton_set_e_in_powerset_S;
    apply e_in_S_iff_singleton_set_e_in_powerset_S in H0;
    rewrite H || rewrite <- H;
    apply H0.
Qed.

Lemma singleton_set_is_single_element_set : forall a,
  {{a}} = singleton_set a
.
Proof.
  intros a.
  apply AXIOM_OF_EXTENSIONALITY.
  intros e. split; intros H.
  - apply cup_definition in H.
    destruct H. apply H.
    apply no_set_is_in_emptyset in H.
    destruct H.
  - apply cup_definition.
    left. apply H.
Qed.

Example equal_iff_singleton_equal : forall a b,
  a = b <-> {{a}} = {{b}}
.
Proof.
  intros a b. split; intros H.
  - subst. reflexivity.
  - apply EQUAL_definition in H.
    unfold EQUAL in H.
    destruct H as [H _]. destruct (H a) as [H0 _].
    apply singleton_set_definition.
    rewrite <- singleton_set_is_single_element_set.
    apply H0. rewrite singleton_set_is_single_element_set.
    apply singleton_set_definition. reflexivity.
Qed.

Example subset_of_emptyset : forall s,
  s subseteq {{}} -> s = {{}}
.
Proof.
  intros s H.
  unfold subset in H.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split. apply H.
  intros H'. apply no_set_is_in_emptyset in H'.
  destruct H'.
Qed.

Definition disjoint (a b : set) : Prop := a cap b = {{}}.

Theorem subset_cup : forall a b, a subseteq (a cup b).
Proof.
  intros a b e H.
  apply cup_definition.
  left. apply H.
Qed.

Theorem cap_subset : forall a b, (a cap b) subseteq a.
Proof.
  intros a b e H.
  apply cap_definition in H.
  destruct H as [H _].
  apply H.
Qed.

Theorem cup_cap_becomes_itself : forall a b, a cup (a cap b) = a.
Proof.
  intros a b. symmetry.
  apply AXIOM_OF_EXTENSIONALITY.
  intros e. split; intros H.
  - apply cup_definition. left. apply H.
  - apply cup_definition in H.
    destruct H. apply H.
    apply cap_definition in H.
    destruct H as [H _].
    apply H.
Qed.

Theorem cup_commutative : forall a b, a cup b = b cup a.
Proof.
  intros a b.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H;
  apply cup_definition;
  apply cup_definition in H;
  destruct H;
  try (left; apply H);
  right; apply H.
Qed.

Theorem cap_commutative : forall a b, a cap b = b cap a.
Proof.
  intros a b.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H;
  apply cap_definition;
  apply cap_definition in H;
  destruct H; split;
  try (apply H); apply H0.
Qed.

Theorem cup_idempotent : forall a, a cup a = a.
Proof.
  intros a. symmetry.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cup_definition.
    left. apply H.
  - apply cup_definition in H.
    destruct H; apply H.
Qed.

Theorem cap_idempotent : forall a, a cap a = a.
Proof.
  intros a. symmetry.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cap_definition.
    split; apply H.
  - apply cap_definition in H.
    destruct H. apply H.
Qed.

Theorem cup_associative : forall a b c, a cup (b cup c) = (a cup b) cup c.
Proof.
  intros a b c.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cup_definition.
    apply cup_definition in H.
    destruct H.
    left. apply cup_definition.
    left. apply H.
    apply cup_definition in H.
    destruct H. left.
    apply cup_definition. right.
    apply H.
    right. apply H.
  - apply cup_definition.
    apply cup_definition in H.
    destruct H.
    apply cup_definition in H.
    destruct H. left. apply H.
    right. apply cup_definition.
    left. apply H.
    right. apply cup_definition.
    right. apply H.
Qed.

Theorem cap_associative : forall a b c, a cap (b cap c) = (a cap b) cap c.
Proof.
  intros a b c.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cap_definition.
    apply cap_definition in H.
    destruct H.
    apply cap_definition in H0.
    destruct H0.
    split. apply cap_definition.
    split. apply H. apply H0. apply H1.
  - apply cap_definition.
    apply cap_definition in H.
    destruct H.
    apply cap_definition in H.
    destruct H.
    split. apply H.
    apply cap_definition. split.
    apply H1. apply H0.
Qed.

Theorem cup_cap_distributive : forall a b c,
  a cup (b cap c) = (a cup b) cap (a cup c)
.
Proof.
  intros a b c.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cap_definition.
    apply cup_definition in H.
    split; destruct H.
    + apply cup_definition. left. apply H.
    + apply cap_definition in H. destruct H.
      apply cup_definition. right. apply H.
    + apply cup_definition. left. apply H.
    + apply cap_definition in H. destruct H.
      apply cup_definition. right. apply H0.
  - apply cup_definition.
    apply cap_definition in H.
    destruct H.
    apply cup_definition in H.
    apply cup_definition in H0.
    destruct H, H0;
    try (left; apply H || apply H0).
    right. apply cap_definition.
    split. apply H. apply H0.
Qed.

Theorem cap_cup_distributive : forall a b c,
  a cap (b cup c) = (a cap b) cup (a cap c)
.
Proof.
  intros a b c.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cup_definition.
    apply cap_definition in H.
    destruct H.
    apply cup_definition in H0.
    destruct H0.
    + left. apply cap_definition.
      split. apply H. apply H0.
    + right. apply cap_definition.
      split. apply H. apply H0.
  - apply cap_definition.
    apply cup_definition in H.
    split; destruct H.
    + apply cap_definition in H.
      destruct H. apply H.
    + apply cap_definition in H.
      destruct H. apply H.
    + apply cap_definition in H.
      apply cup_definition.
      destruct H. left. apply H0.
    + apply cap_definition in H.
      apply cup_definition.
      destruct H. right. apply H0.
Qed.

Example a_in_A_then_a_subseteq_bigcup_A : forall a A, a in A -> a subseteq (bigcup A).
Proof.
  intros a A H e H0.
  apply bigcup_definition.
  exists a. split. apply H. apply H0.
Qed.

Example set_subseteq_powerset_of_its_sets : forall a, a subseteq (powerset (bigcup a)).
Proof.
  intros a e H.
  apply powerset_definition.
  intros f H0.
  apply bigcup_definition.
  exists e. split. apply H. apply H0.
Qed.

Lemma powerset_cap_is_cap_powerset : forall a b,
  (powerset a) cap (powerset b) = powerset (a cap b)
.
Proof.
  intros a b.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply powerset_definition.
    apply cap_definition in H.
    destruct H.
    intros e H1.
    apply cap_definition.
    apply powerset_definition in H.
    apply powerset_definition in H0.
    split. apply H, H1. apply H0, H1.
  - apply cap_definition.
    apply powerset_definition in H.
    split.
    + apply powerset_definition.
      intros e H0.
      apply (cap_subset _ b), H, H0.
    + apply powerset_definition.
      intros e H0.
      apply (cap_subset b a).
      rewrite cap_commutative.
      apply H, H0.
Qed.

Lemma bigcup_powerset_is_itself : forall a, bigcup (powerset a) = a.
Proof.
  intros a. symmetry.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply bigcup_definition.
    exists a. split.
    + apply powerset_definition.
      intros e H'. apply H'.
    + apply H.
  - apply bigcup_definition in H.
    do 2 (destruct H).
    apply powerset_definition in H.
    apply H, H0.
Qed.

Lemma bigcap_powerset_is_emptyset : forall total_set a, bigcap total_set (powerset a) = {{}}.
Proof.
  intros total_set a. symmetry.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply no_set_is_in_emptyset in H.
    destruct H.
  - apply bigcap_definition in H.
    destruct H.
    apply H0, powerset_definition.
    intros e H1.
    apply no_set_is_in_emptyset in H1.
    destruct H1.
Qed.

Definition ordered_pair (a b : set) : set := {{{{a}}, {{a, b}}}}.
Definition ordered_pair_hausdorff (a b : set) : set := {{{{a, {{}}}}, {{b, {{{{}}}}}}}}.

Theorem ordered_pair_definition : forall a b e,
  e in (ordered_pair a b) <-> e = {{a}} \/ e = {{a, b}}
.
Proof.
  intros a b e. split; intros H.
  - apply cup_definition in H.
    destruct H.
    + left.
      apply singleton_set_definition, H.
    + right. apply cup_definition in H.
      destruct H.
      apply singleton_set_definition, H.
      apply no_set_is_in_emptyset in H.
      destruct H.
  - apply cup_definition.
    destruct H.
    + left. apply singleton_set_definition, H.
    + right. apply cup_definition.
      left. apply singleton_set_definition, H.
Qed.

Lemma ordered_pair_equality_lemma : forall a b,
  a = {{b}} \/ a = {{b, b}} -> a = {{b}}
.
Proof.
  intros a b [H | H].
  - apply H.
  - subst.
    apply AXIOM_OF_EXTENSIONALITY.
    intros z. split; intros H.
    + apply cup_definition in H.
      rewrite singleton_set_is_single_element_set.
      destruct H. apply H.
      rewrite singleton_set_is_single_element_set in H.
      apply H.
    + apply cup_definition. right. apply H.
Qed.

Theorem ordered_pair_equality : forall a b c d,
  (ordered_pair a b) = (ordered_pair c d) <-> a = c /\ b = d
.
Proof.
  intros a b c d. split; intros H.
  - apply EQUAL_definition in H.
    destruct H as [H _].
    destruct (H {{a}}) as [H0 _].
    destruct (H {{a, b}}) as [H1 _].
    destruct (H {{c}}) as [_ H2].
    destruct (H {{c, d}}) as [_ H3].
    clear H.
    assert({{a}} in (ordered_pair c d)). {
      apply H0, ordered_pair_definition.
      left. reflexivity.
    } clear H0.
    assert({{a, b}} in (ordered_pair c d)). {
      apply H1, ordered_pair_definition.
      right. reflexivity.
    } clear H1.
    assert({{c}} in (ordered_pair a b)). {
      apply H2, ordered_pair_definition.
      left. reflexivity.
    } clear H2.
    assert({{c, d}} in (ordered_pair a b)). {
      apply H3, ordered_pair_definition.
      right. reflexivity.
    } clear H3.
    apply ordered_pair_definition in H.
    destruct H.
    apply EQUAL_definition in H.
    destruct H as [H _].
    destruct (H c) as [_ H3].
    assert(c in {{a}}). {
      apply H3, cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
    } clear H3.
    rewrite singleton_set_is_single_element_set in H4.
    apply singleton_set_definition in H4.
    subst. split. reflexivity. clear H H1.
    apply ordered_pair_definition in H2.
    destruct H2; apply EQUAL_definition in H;
    destruct H as [H _].
    + destruct (H d) as [H1 _].
      assert(d in {{a}}). {
        apply H1, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H2.
      destruct H2.
      apply singleton_set_definition in H2.
      subst. clear H H1.
      apply ordered_pair_definition in H0.
      apply ordered_pair_equality_lemma in H0.
      apply EQUAL_definition in H0.
      destruct H0 as [H _].
      destruct (H b) as [H0 _].
      assert(b in {{a}}). {
        apply H0, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      rewrite singleton_set_is_single_element_set in H1.
      apply singleton_set_definition, H1.
      apply no_set_is_in_emptyset in H2. destruct H2.
    + destruct (H d) as [H1 _].
      destruct (H b) as [_ H2].
      assert(d in {{a, b}}). {
        apply H1, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H1.
      assert(b in {{a, d}}). {
        apply H2, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H2.
      apply cup_definition in H3.
      apply cup_definition in H1.
      destruct H1.
      * apply singleton_set_definition in H1.
        subst. destruct H3.
        apply singleton_set_definition in H1.
        subst. reflexivity.
        rewrite singleton_set_is_single_element_set in H1.
        apply singleton_set_definition in H1.
        subst. reflexivity.
      * destruct H3.
        apply singleton_set_definition in H2.
        subst. apply cup_definition in H1. destruct H1.
        apply singleton_set_definition in H1.
        apply H1. apply no_set_is_in_emptyset in H1.
        destruct H1.
        rewrite singleton_set_is_single_element_set in H1.
        apply singleton_set_definition in H1.
        apply H1.
    + apply EQUAL_definition in H.
      destruct H as [H _].
      destruct (H a) as [H3 _].
      assert(a in {{c, d}}). {
        apply H3, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H4.
      destruct H4.
      apply singleton_set_definition in H4.
      split; subst. reflexivity. clear H3 H1.
      apply ordered_pair_definition in H2.
      destruct H2.
      * apply EQUAL_definition in H1.
        destruct H1 as [H1 _].
        destruct (H1 d) as [H2 _].
        assert(d in {{c}}). {
          apply H2, cup_definition. right.
          apply cup_definition. left.
          apply singleton_set_definition.
          reflexivity.
        } clear H2.
        rewrite singleton_set_is_single_element_set in H3.
        apply singleton_set_definition in H3.
        subst. clear H1 H.
        apply ordered_pair_definition in H0.
        destruct H0. apply EQUAL_definition in H.
        destruct H as [H _].
        destruct (H b) as [H0 _].
        assert(b in {{c}}). {
          apply H0, cup_definition. right.
          apply cup_definition. left.
          apply singleton_set_definition.
          reflexivity.
        }
        rewrite singleton_set_is_single_element_set in H1.
        apply singleton_set_definition, H1.
        apply EQUAL_definition in H.
        destruct H as [H _].
        destruct (H b) as [H0 _].
        assert(b in {{c, c}}). {
          apply H0, cup_definition. right.
          apply cup_definition. left.
          apply singleton_set_definition.
          reflexivity.
        }
        apply cup_definition in H1.
        destruct H1. apply singleton_set_definition, H1.
        rewrite singleton_set_is_single_element_set in H1.
        apply singleton_set_definition, H1.
      * destruct (H d) as [_ H2].
        assert(d in {{c}}). {
          apply H2, cup_definition. right.
          apply cup_definition. left.
          apply singleton_set_definition.
          reflexivity.
        }
        rewrite singleton_set_is_single_element_set in H3.
        apply singleton_set_definition in H3.
        subst. clear H0 H H2.
        apply EQUAL_definition in H1.
        destruct H1 as [H _].
        destruct (H b) as [_ H0].
        assert (b in {{c, c}}). {
          apply H0, cup_definition. right.
          apply cup_definition. left.
          apply singleton_set_definition.
          reflexivity.
        }
        apply cup_definition in H1.
        destruct H1. apply singleton_set_definition, H1.
        apply cup_definition in H1.
        destruct H1. apply singleton_set_definition, H1.
        apply no_set_is_in_emptyset in H1.
        destruct H1.
      * rewrite singleton_set_is_single_element_set in H4.
        apply singleton_set_definition in H4. subst.
        clear H3. assert (c in {{d}}). {
          apply H, cup_definition. left.
          apply singleton_set_definition.
          reflexivity.
        }
        rewrite singleton_set_is_single_element_set in H3.
        apply singleton_set_definition in H3.
        subst. split. reflexivity.
        clear H2 H.
        apply ordered_pair_definition in H0.
        apply ordered_pair_equality_lemma in H0.
        apply EQUAL_definition in H0.
        destruct H0 as [H _].
        assert (b in {{d}}). {
          apply H, cup_definition. right.
          apply cup_definition. left.
          apply singleton_set_definition.
          reflexivity.
        }
        rewrite singleton_set_is_single_element_set in H0.
        apply singleton_set_definition, H0.
  - destruct H. subst. reflexivity.
Qed.

Notation "'\(' x , y '\)'" := (ordered_pair x y)(x at level 99, y at level 99) : type_scope.
Notation "'\(' x , y , .. , z '\)'" := (ordered_pair (..(ordered_pair x y) ..) z)(x at level 99, y at level 99, z at level 99) : type_scope.

Definition cartesian_product : set->set->set.
  intros a b.
  exact \{ x in powerset (powerset (a cup b)) : fun x => exists c d, x = \(c, d\) /\ c in a /\ d in b\}.
Defined.

Theorem cartesian_product_definition : forall a b e,
  e in (cartesian_product a b) <-> (exists c d, e = \(c, d\) /\ c in a /\ d in b)
.
Proof.
  intros a b e.
  unfold cartesian_product.
  split; intros H.
  - unfold set_constraint in H.
    destruct AXIOM_OF_SUBSETS as [A HA].
    apply HA in H.
    destruct H. apply H0.
  - unfold set_constraint.
    destruct AXIOM_OF_SUBSETS as [A HA].
    apply HA. split.
    + destruct H as [c H].
      destruct H as [d H].
      destruct H, H0.
      apply powerset_definition.
      intros f H2.
      apply powerset_definition.
      intros g H3.
      apply cup_definition.
      subst. apply ordered_pair_definition in H2.
      destruct H2.
      * subst. rewrite singleton_set_is_single_element_set in H3.
        apply singleton_set_definition in H3.
        subst. left. apply H0.
      * subst. apply cup_definition in H3.
        destruct H3. apply singleton_set_definition in H.
        subst. left. apply H0.
        rewrite singleton_set_is_single_element_set in H.
        apply singleton_set_definition in H.
        subst. right. apply H1.
    + apply H.
Qed.

Theorem cartesian_product_cap_distributive : forall a b c,
  cartesian_product a (b cap c) = (cartesian_product a b) cap (cartesian_product a c)
.
Proof.
  intros a b c.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cap_definition.
    apply cartesian_product_definition in H.
    do 3 (destruct H). destruct H0.
    subst. apply cap_definition in H1.
    destruct H1. split;
    apply cartesian_product_definition.
    exists x, x0; split. reflexivity. split. apply H0. apply H.
    exists x, x0. split. reflexivity. split. apply H0. apply H1.
  - apply cartesian_product_definition.
    apply cap_definition in H.
    destruct H.
    apply cartesian_product_definition in H.
    apply cartesian_product_definition in H0.
    do 3 (destruct H, H0). destruct H1, H2.
    subst. apply ordered_pair_equality in H0.
    destruct H0. subst.
    exists x0, x2. split. reflexivity.
    split. apply H2. apply cap_definition.
    split. apply H3. apply H4.
Qed.

Theorem cartesian_product_cup_distributive : forall a b c,
  cartesian_product a (b cup c) = (cartesian_product a b) cup (cartesian_product a c)
.
Proof.
  intros a b c.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cup_definition.
    apply cartesian_product_definition in H.
    do 3 (destruct H). destruct H0.
    apply cup_definition in H1.
    destruct H1;
    [left | right]; apply cartesian_product_definition;
    subst; exists x, x0;
    split; try reflexivity; split; apply H0 || apply H1.
  - apply cartesian_product_definition.
    apply cup_definition in H.
    destruct H; apply cartesian_product_definition in H;
    do 3 (destruct H); destruct H0; exists x, x0; subst;
    split; try reflexivity; split; apply H0 || apply cup_definition;
    [left | right]; apply H1.
Qed.

Theorem cap_cartesian_product_distributive : forall a b c,
  cartesian_product (a cap b) c = (cartesian_product a c) cap (cartesian_product b c)
.
Proof.
  intros a b c.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cap_definition.
    apply cartesian_product_definition in H.
    do 3 (destruct H). destruct H0.
    apply cap_definition in H0.
    destruct H0.
    split; apply cartesian_product_definition;
    exists x, x0; split; subst;
    try reflexivity; split; try (apply H1).
    apply H0. apply H2.
  - apply cartesian_product_definition.
    apply cap_definition in H.
    destruct H.
    apply cartesian_product_definition in H.
    apply cartesian_product_definition in H0.
    do 3 (destruct H, H0). destruct H1, H2.
    subst. apply ordered_pair_equality in H0.
    destruct H0. subst.
    exists x0, x2. split. reflexivity.
    split. apply cap_definition. split.
    apply H1. apply H2. apply H4.
Qed.

Theorem cup_cartesian_product_distributive : forall a b c,
  cartesian_product (a cup b) c = (cartesian_product a c) cup (cartesian_product b c)
.
Proof.
  intros a b c.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cup_definition.
    apply cartesian_product_definition in H.
    do 3 (destruct H). destruct H0.
    apply cup_definition in H0.
    destruct H0; [left | right];
    apply cartesian_product_definition;
    exists x, x0; subst; split; try reflexivity;
    split; apply H0 || apply H1.
  - apply cartesian_product_definition.
    apply cup_definition in H.
    destruct H; apply cartesian_product_definition in H;
    do 3 (destruct H); destruct H0; subst;
    exists x, x0; split; try reflexivity;
    split; apply H1 || apply cup_definition;
    [left | right]; apply H0.
Qed.

Theorem cartesian_product_of_subseteq_set : forall a b c d,
  a subseteq b -> c subseteq d ->
  (cartesian_product a c) subseteq (cartesian_product b d)
.
Proof.
  intros a b c d H1 H2 e H.
  apply cartesian_product_definition.
  apply cartesian_product_definition in H.
  do 3 (destruct H). destruct H0.
  subst. exists x, x0.
  split. reflexivity. split.
  apply H1, H0. apply H2, H3.
Qed.

Theorem ordered_pair_hausdorff_definition : forall a b e,
  e in (ordered_pair_hausdorff a b) <-> e = {{a, {{}}}} \/ e = {{b, {{{{}}}}}}
.
Proof.
  intros a b e. split; intros H.
  - apply cup_definition in H.
    destruct H; [left | right].
    apply singleton_set_definition, H.
    rewrite singleton_set_is_single_element_set in H.
    apply singleton_set_definition, H.
  - apply cup_definition. destruct H;
    [left | right].
    apply singleton_set_definition, H.
    rewrite singleton_set_is_single_element_set.
    apply singleton_set_definition, H.
Qed.

Theorem ordered_pair_hausdorff_equality : forall a b c d,
  ordered_pair_hausdorff a b = ordered_pair_hausdorff c d <-> a = c /\ b = d
.
Proof.
  intros a b c d. split; intros H.
  - apply EQUAL_definition in H.
    destruct H as [H _].
    destruct (H {{a, {{}}}}) as [H0 _].
    destruct (H {{b, {{{{}}}}}}) as [H1 _].
    destruct (H {{c, {{}}}}) as [_ H2].
    destruct (H {{d, {{{{}}}}}}) as [_ H3].
    clear H.
    assert({{a, {{}}}} in (ordered_pair_hausdorff c d)). {
      apply H0, cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
    } clear H0.
    assert({{b, {{{{}}}}}} in (ordered_pair_hausdorff c d)). {
      apply H1, cup_definition. right.
      apply cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
    } clear H1.
    assert({{c, {{}}}} in (ordered_pair_hausdorff a b)). {
      apply H2, cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
    } clear H2.
    assert({{d, {{{{}}}}}} in (ordered_pair_hausdorff a b)). {
      apply H3, cup_definition. right.
      apply cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
    } clear H3.
    apply ordered_pair_hausdorff_definition in H.
    destruct H;
    apply EQUAL_definition in H;
    destruct H as [H _].
    + destruct (H a) as [H3 _].
      assert(a in {{c, {{}}}}). {
        apply H3, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H3.
      apply cup_definition in H4.
      destruct H4.
      apply singleton_set_definition in H3.
      subst. clear H1 H. split. reflexivity.
      apply ordered_pair_hausdorff_definition in H0.
      destruct H0; apply EQUAL_definition in H;
      destruct H as [H _].
      destruct (H c) as [_ H0].
      assert (c in {{b, {{{{}}}}}}). {
        apply H0, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H0.
      apply cup_definition in H1.
      destruct H1.
      apply singleton_set_definition in H0.
      subst. destruct (H {{}}) as [_ H0].
      assert({{}} in {{b, {{{{}}}}}}). {
        apply H0, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H0.
      apply cup_definition in H1.
      destruct H1. apply singleton_set_definition in H0.
      subst. apply ordered_pair_hausdorff_definition in H2.
      destruct H2; apply EQUAL_definition in H0;
      destruct H0 as [H0 _].
      destruct (H0 {{}}) as [_ H1].
      assert({{}} in {{d, {{{{}}}}}}). {
        apply H1, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H1.
      apply cup_definition in H2.
      destruct H2. apply singleton_set_definition in H1.
      apply H1.
      apply cup_definition in H1.
      destruct H1. apply singleton_set_definition in H1.
      apply EQUAL_definition in H1.
      destruct H1 as [H1 _].
      destruct (H1 {{}}) as [_ H2].
      assert({{}} in {{}}). {
        apply H2, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H2.
      apply no_set_is_in_emptyset in H3.
      destruct H3.
      apply no_set_is_in_emptyset in H1.
      destruct H1.
      destruct (H0 {{}}) as [_ H1].
      assert({{}} in {{d, {{{{}}}}}}). {
        apply H1, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H1.
      apply cup_definition in H2.
      destruct H2. apply singleton_set_definition in H1.
      apply H1. apply cup_definition in H1.
      destruct H1. apply singleton_set_definition in H1.
      apply EQUAL_definition in H1.
      destruct H1 as [H1 _].
      destruct (H1 {{}}) as [_ H2].
      assert({{}} in {{}}). {
        apply H2, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H2.
      apply no_set_is_in_emptyset in H3.
      destruct H3.
      apply no_set_is_in_emptyset in H1.
      destruct H1.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0.
      apply EQUAL_definition in H0.
      destruct H0 as [H0 _].
      destruct (H0 {{}}) as [_ H1].
      assert({{}} in {{}}). {
        apply H1, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H1.
      apply no_set_is_in_emptyset in H3.
      destruct H3.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0.
      subst. destruct (H b) as [H0 _].
      assert(b in {{{{{{}}}}, {{}}}}). {
        apply H0, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H0.
      apply cup_definition in H1.
      destruct H1. apply singleton_set_definition in H0.
      subst.
      assert({{}} in {{{{{{}}}}, {{{{}}}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H.
      apply cup_definition in H0.
      destruct H0.
      apply singleton_set_definition, EQUAL_definition in H.
      destruct H as [H _].
      assert({{}} in {{}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H.
      apply no_set_is_in_emptyset in H0.
      destruct H0.
      rewrite singleton_set_is_single_element_set in H.
      apply singleton_set_definition in H.
      apply EQUAL_definition in H.
      destruct H as [H _].
      assert({{}} in {{}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H.
      apply no_set_is_in_emptyset in H0.
      destruct H0.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0.
      subst. clear H. apply ordered_pair_hausdorff_definition in H2.
      destruct H2; apply EQUAL_definition in H;
      destruct H as [H _].
      assert({{}} in {{d, {{{{}}}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H.
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition, H.
      rewrite singleton_set_is_single_element_set in H.
      apply singleton_set_definition in H.
      apply EQUAL_definition in H.
      destruct H as [H _].
      assert({{}} in {{}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H.
      apply no_set_is_in_emptyset in H0.
      destruct H0.
      assert({{}} in {{d, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition, H0.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0.
      apply EQUAL_definition in H0.
      destruct H0 as [H0 _].
      assert({{}} in {{}}). {
        apply H0, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      } clear H0.
      apply no_set_is_in_emptyset in H1.
      destruct H1.
      assert(b in {{d, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition, H0.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0. subst.
      assert(d in {{{{{{}}}}, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in H0. subst. reflexivity.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0.
      subst. reflexivity.
      rewrite singleton_set_is_single_element_set in H3.
      apply singleton_set_definition in H3. subst.
      assert(c in {{{{}}, {{}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H3.
      destruct H3. apply singleton_set_definition in H3. subst.
      split. reflexivity. clear H.
      apply ordered_pair_hausdorff_definition in H2.
      destruct H2; apply EQUAL_definition in H;
      destruct H as [H _].
      assert({{{{}}}} in {{{{}}, {{}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H2.
      destruct H2. apply singleton_set_definition in H2.
      apply EQUAL_definition in H2.
      destruct H2 as [H2 _].
      assert({{}} in {{}}). {
        apply H2, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply no_set_is_in_emptyset in H3.
      destruct H3.
      apply no_set_contains_itself in H2.
      destruct H2.
      assert(b in {{d, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H2.
      destruct H2. apply singleton_set_definition, H2.
      rewrite singleton_set_is_single_element_set in H2.
      apply singleton_set_definition in H2. subst.
      assert(d in {{{{{{}}}}, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H2.
      destruct H2. apply singleton_set_definition in H2.
      subst. reflexivity.
      rewrite singleton_set_is_single_element_set in H2.
      apply singleton_set_definition in H2.
      subst. reflexivity.
      rewrite singleton_set_is_single_element_set in H3.
      apply singleton_set_definition in H3.
      subst. split. reflexivity.
      apply ordered_pair_hausdorff_definition in H2.
      destruct H2; apply EQUAL_definition in H2;
      destruct H2 as [H2 _].
      assert({{{{}}}} in {{{{}}, {{}}}}). {
        apply H2, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H3.
      destruct H3. apply singleton_set_definition in H3.
      apply EQUAL_definition in H3.
      destruct H3 as [H3 _].
      assert({{}} in {{}}). {
        apply H3, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply no_set_is_in_emptyset in H4.
      destruct H4.
      apply no_set_contains_itself in H3.
      destruct H3. clear H.
      assert(b in {{d, {{{{}}}}}}). {
        apply H2, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H.
      destruct H. apply singleton_set_definition, H.
      rewrite singleton_set_is_single_element_set in H.
      apply singleton_set_definition in H. subst.
      assert(d in {{{{{{}}}}, {{{{}}}}}}). {
        apply H2, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H.
      destruct H. apply singleton_set_definition in H. subst. reflexivity.
      rewrite singleton_set_is_single_element_set in H.
      apply singleton_set_definition in H. subst. reflexivity.
    + assert(d in {{a, {{}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H3.
      destruct H3. apply singleton_set_definition in H3. subst.
      assert({{}} in {{a, {{{{}}}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H3.
      destruct H3. apply singleton_set_definition in H3. symmetry in H3. subst.
      assert({{{{}}}} in {{{{}}, {{}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H3.
      destruct H3. apply singleton_set_definition in H3.
      apply EQUAL_definition in H3.
      destruct H3 as [H3 _].
      assert({{}} in {{}}). {
        apply H3, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply no_set_is_in_emptyset in H4.
      destruct H4.
      apply no_set_contains_itself in H3.
      destruct H3.
      rewrite singleton_set_is_single_element_set in H3.
      apply singleton_set_definition in H3.
      apply EQUAL_definition in H3.
      destruct H3 as [H3 _].
      assert({{}} in {{}}). {
        apply H3, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply no_set_is_in_emptyset in H4.
      destruct H4.
      rewrite singleton_set_is_single_element_set in H3.
      apply singleton_set_definition in H3. subst.
      assert(a in {{{{}}, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H3.
      destruct H3. apply singleton_set_definition in H3. subst.
      assert({{{{}}}} in {{{{}}, {{}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H3.
      destruct H3. apply singleton_set_definition, EQUAL_definition in H3.
      destruct H3 as [H3 _].
      assert({{}} in {{}}). {
        apply H3, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply no_set_is_in_emptyset in H4.
      destruct H4.
      apply no_set_contains_itself in H3.
      destruct H3.
      rewrite singleton_set_is_single_element_set in H3.
      apply singleton_set_definition in H3. subst. clear H.
      apply ordered_pair_hausdorff_definition in H0.
      destruct H0; apply EQUAL_definition in H;
      destruct H as [H _].
      assert(b in {{c, {{}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in H0. subst.
      assert({{{{}}}} in {{c, {{}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0.
      apply singleton_set_definition in H0.
      symmetry in H0. subst. split. reflexivity.
      assert({{}} in {{{{{{}}}}, {{{{}}}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in H0.
      symmetry. apply H0.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0.
      symmetry. apply H0.
      apply no_set_contains_itself in H0.
      destruct H0.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0. subst.
      assert(c in {{{{}}, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in H0. subst.
      assert({{{{}}}} in {{{{}}, {{}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in H0.
      split. apply H0. reflexivity.
      apply no_set_contains_itself in H0.
      destruct H0.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0.
      subst. split; reflexivity.
      assert(b in {{{{}}, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in H0. subst. clear H.
      apply ordered_pair_hausdorff_definition in H1.
      destruct H1; apply EQUAL_definition in H;
      destruct H as [H _].
      assert(c in {{{{{{}}}}, {{}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in H0.
      subst. split; reflexivity.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0. subst.
      assert({{{{}}}} in {{{{}}, {{}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in H0.
      split. apply H0. reflexivity.
      apply no_set_contains_itself in H0.
      destruct H0.
      assert(c in {{{{}}, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0.
      apply singleton_set_definition in H0. subst.
      assert({{{{}}}} in {{{{}}, {{}}}}). {
        apply H, cup_definition. right.
        apply cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0.
      apply singleton_set_definition in H0.
      split. apply H0. reflexivity.
      apply no_set_contains_itself in H0.
      destruct H0.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0.
      subst. split; reflexivity.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition in H0. subst.
      assert({{}} in {{{{{{}}}}, {{{{}}}}}}). {
        apply H, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply cup_definition in H0.
      destruct H0. apply singleton_set_definition in  H0.
      apply EQUAL_definition in H0.
      destruct H0 as [H0 _].
      assert({{}} in {{}}). {
        apply H0, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply no_set_is_in_emptyset in H3.
      destruct H3.
      rewrite singleton_set_is_single_element_set in H0.
      apply singleton_set_definition, EQUAL_definition in H0.
      destruct H0 as [H0 _].
      assert({{}} in {{}}). {
        apply H0, cup_definition. left.
        apply singleton_set_definition.
        reflexivity.
      }
      apply no_set_is_in_emptyset in H3.
      destruct H3.
  - destruct H. subst. reflexivity.
Qed.

Example cartesian_product_emptyset : forall a b,
  cartesian_product a b = {{}} <-> a = {{}} \/ b = {{}}
.
Proof.
Admitted.

End SetTheory.
