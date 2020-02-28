From SetTheory Require Import set_theory.
Import SetTheory.

Module NaturalNumber.

Definition successor (s : set) := s cup {{s}}.

Theorem successor_definition : forall s x, x in (successor s) <-> x in s \/ x = s.
Proof.
  intros s x. split; intros H.
  - apply cup_definition in H.
    destruct H. left. apply H.
    right. rewrite singleton_set_is_single_element_set in H. apply singleton_set_definition, H.
  - apply cup_definition. destruct H.
    left. apply H. right. subst. apply cup_definition. left. apply singleton_set_definition. reflexivity.
Qed.

Record inductive_set : Set := inductive_set_init {
  ind_set : set;
  ind_set_cond : {{}} in ind_set /\ (forall x, x in ind_set -> (successor x) in ind_set);
}.

Theorem exists_inductive_set : exists s : set, {{}} in s /\ (forall x, x in s -> (successor x) in s).
Proof.
  destruct AXIOM_OF_INFINITY as [s [emptyset [H [Hempty H0]]]].
  exists s.
  assert(emptyset = {{}}). {
    apply AXIOM_OF_EXTENSIONALITY.
    intros z. split; intros H'.
    - apply Hempty in H'. destruct H'.
    - apply no_set_is_in_emptyset in H'.
      destruct H'.
  } subst.
  split. apply H.
  intros x H1.
  apply H0 with x. apply H1.
  intros w. split; intros H2.
  - apply cup_definition in H2.
    destruct H2.
    + left. apply H2.
    + right. rewrite singleton_set_is_single_element_set in H2.
      apply singleton_set_definition, H2.
  - apply cup_definition. destruct H2.
    + left. apply H2.
    + right. subst.
      apply cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
Qed.

Definition inductive_set_to_set (ind : inductive_set) := ind_set ind.
Coercion inductive_set_to_set : inductive_set >-> set.

Inductive is_NAT : set->Prop :=
  | NAT_zero : is_NAT {{}}
  | NAT_succ : forall s : set, is_NAT s -> is_NAT (successor s)
.

Lemma NATset_lemma : forall S : inductive_set,
    {{}} in \{x in S : fun x => is_NAT x\} /\
    (forall x, x in \{x in S : fun x => is_NAT x\} ->
                    (successor x) in \{x in S : fun x => is_NAT x\})
.
Proof.
  split.
  - unfold set_constraint.
    destruct AXIOM_OF_SUBSETS as [A HA].
    apply HA. split; try (apply NAT_zero).
    destruct (ind_set_cond S) as [HS _].
    apply HS.
  - intros x H.
    unfold set_constraint.
    destruct AXIOM_OF_SUBSETS as [A HA].
    apply HA. unfold set_constraint in H.
    destruct AXIOM_OF_SUBSETS as [B HB].
    apply HB in H. destruct H.
    split. apply (ind_set_cond S). apply H. apply NAT_succ, H0.
Qed.

Definition NATset : inductive_set.
  destruct AXIOM_OF_INFINITY as [S' HS'].
  assert({S : inductive_set | S' = S}). {
    assert({{}} in S' /\ (forall x, x in S' -> (successor x) in S')). {
      destruct HS' as [emptyset [H [H0 H1]]].
      assert(emptyset = {{}}). {
        apply AXIOM_OF_EXTENSIONALITY.
        intros z. split; intros H2.
        - apply H0 in H2. destruct H2.
        - apply no_set_is_in_emptyset in H2. destruct H2.
      } subst. split. apply H.
      intros x H2. apply H1 with x. apply H2.
      intros w. split; intros H3.
      - apply cup_definition in H3. destruct H3.
        + left. apply H3.
        + right. rewrite singleton_set_is_single_element_set in H3.
          apply singleton_set_definition, H3.
      - apply cup_definition. destruct H3.
        + left. apply H3.
        + right. subst. apply cup_definition. left.
          apply singleton_set_definition. reflexivity.
    }
    exists (inductive_set_init S' H). reflexivity.
  }
  destruct H as [S HS].
  exact (inductive_set_init \{x in S : fun x => is_NAT x\} (NATset_lemma S)).
Defined.
Theorem NATset_definition : forall s, s in NATset <-> is_NAT s.
Proof.
  intros s. split; intros H.
  - unfold NATset in H.
    destruct AXIOM_OF_INFINITY as [INF HINF].
    unfold set_constraint in H.
    simpl in H.
    destruct AXIOM_OF_SUBSETS as [B HB].
    apply HB, H.
  - unfold NATset.
    destruct AXIOM_OF_INFINITY as [INF HINF].
    unfold set_constraint. simpl.
    destruct AXIOM_OF_SUBSETS as [N HN].
    apply HN. destruct HINF as [emptyset [H0 [H1 H2]]].
    assert(emptyset = {{}}). {
      apply AXIOM_OF_EXTENSIONALITY.
      intros z. split; intros H3.
      - apply H1 in H3. destruct H3.
      - apply no_set_is_in_emptyset in H3. destruct H3.
    } subst. split.
    + induction H. apply H0. apply H2 with s.
      apply IHis_NAT. intros w. split; intros H3.
      * apply cup_definition in H3.
        destruct H3. left. apply H3.
        rewrite singleton_set_is_single_element_set in H3.
        right. apply singleton_set_definition, H3.
      * apply cup_definition. destruct H3.
        left. apply H3.
        right. subst. apply cup_definition. left.
        apply singleton_set_definition. reflexivity.
    + apply H.
Qed.

Record NAT : Set := NAT_init {
  N_set : set;
  N_set_cond : N_set in NATset;
}.
Axiom NAT_equal : forall n m : NAT, n = m <-> N_set n = N_set m.
Definition NAT_to_set (n : NAT) := N_set n.
Coercion NAT_to_set : NAT >-> set.

Lemma all_NAT_in_NATset : forall n : NAT, n in NATset.
Proof. intros [n Hn]. apply Hn. Qed.

Lemma is_NAT_iff_in_NATset : forall s, is_NAT s <-> s in NATset.
Proof. intros s. split; intros H; apply NATset_definition, H. Qed.


Lemma NAT_is_0_or_has_Pred : forall n : NAT, {{}} = n \/ (exists m, successor m = n).
Proof.
  intros [N HN].
  assert(is_NAT N). apply NATset_definition, HN.
  destruct H. left. reflexivity.
  right. exists s. reflexivity.
Qed.

Definition Succ : NAT->NAT.
  intros [n Hn].
  assert((successor n) in NATset). apply NATset_definition, NAT_succ, NATset_definition, Hn.
  exact (NAT_init (successor n) H).
Defined.

Theorem Succ_definition : forall m (n : NAT), m in (Succ n) <-> m in n \/ m = n.
Proof.
  intros m n. split; intros H.
  - destruct n as [n Hn]. simpl in H. apply successor_definition in H. simpl.
    destruct H. left. apply H. right. subst. reflexivity.
  - destruct n as [n Hn]. simpl in *. apply successor_definition. destruct H.
    left. apply H. right. apply H.
Qed.

Lemma NAT_ZERO_lemma : {{}} in NATset. 
Proof. apply NATset_definition, NAT_zero. Qed.  
Definition NAT_ZERO := (NAT_init {{}} NAT_ZERO_lemma).

Theorem mathematical_induction_property : forall A,
    A subseteq NATset ->
    {{}} in A ->
    (forall s, s in A -> (successor s) in A) ->
    A = NATset
.
Proof.
  intros A H H0 H1.
  apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H2.
  { apply H, H2. }
  apply NATset_definition in H2.
  induction H2. apply H0. apply H1, IHis_NAT.
Qed.

Lemma NAT_equality : forall s H H', (NAT_init s H) = (NAT_init s H').
Proof. intros s H H'. apply NAT_equal. reflexivity. Qed.

Corollary mathematical_induction : forall (P : NAT->Prop),
    P NAT_ZERO -> (forall n : NAT, P n -> P (Succ n)) ->
    forall n : NAT, P n
.
Proof.
  intros P Hzero HPn [n Hn].
  assert(is_NAT n). apply NATset_definition, Hn.
  induction H. rewrite (NAT_equality {{}} Hn NAT_ZERO_lemma). apply Hzero.
  apply NATset_definition in H.
  assert(Succ (NAT_init s H) = (NAT_init (successor s) Hn)). apply NAT_equal. reflexivity.
  rewrite <- H0. apply HPn, IHis_NAT.
Qed.

Record transitive_set : Set := transitive_set_init {
  trans_set : set;
  trans_set_cond : forall x, x in trans_set -> x subseteq trans_set;
}.
Definition transitive_set_to_set (trans : transitive_set) := trans_set trans.
Coercion transitive_set_to_set : transitive_set >-> set.

Theorem transitive_set_definition : forall S : set,
  (exists trans : transitive_set, S = trans) <->
  (forall x y, x in y -> y in S -> x in S)
.
Proof.
  intros S. split; intros H.
  - intros x y H0 H1.
    destruct H as [trans Htrans].
    subst. apply (trans_set_cond trans) with y.
    apply H1. apply H0.
  - assert(forall x, x in S -> x subseteq S).
    intros x H0 e H1. apply H with x. apply H1. apply H0.
    exists (transitive_set_init S H0). reflexivity.
Qed.

Theorem NATset_is_transitive_set : exists N : transitive_set, ind_set NATset = trans_set N.
Proof.
  assert(forall x, x in NATset -> x subseteq NATset). {
    intros x H e H0.
    apply NATset_definition.
    apply NATset_definition in H.
    induction H.
    { apply no_set_is_in_emptyset in H0. destruct H0. }
    apply cup_definition in H0. destruct H0.
    apply IHis_NAT, H0.
    rewrite singleton_set_is_single_element_set in H0.
    apply singleton_set_definition in H0. subst. apply H.
  }
  exists (transitive_set_init (ind_set NATset) H).
  reflexivity.
Qed.

Theorem NAT_is_transitive : forall m n : NAT, m in n -> m subseteq n.
Proof.
  intros m.
  apply (mathematical_induction (fun x : NAT => m in x -> m subseteq x)).
  - intros H. apply no_set_is_in_emptyset in H. destruct H.
  - intros n IHn H e H0.
    apply Succ_definition in H. apply Succ_definition.
    destruct H. left. apply IHn. apply H. apply H0.
    left. rewrite H in H0. apply H0.
Qed.

Theorem no_NAT_is_its_successor : forall n : NAT, Succ n <> n.
Proof.
  intros n H. apply NAT_equal, EQUAL_definition in H.
  destruct H as [H _].
  destruct (H n) as [H0 _].
  apply no_set_contains_itself in H0. apply H0.
  apply Succ_definition. right. reflexivity.
Qed.

Lemma emptyset_in_Succ : forall n : NAT, {{}} in (Succ n).
Proof.
  intros [n Hn]. apply Succ_definition.
  assert(is_NAT n). apply NATset_definition, Hn.
  induction H. right. reflexivity.
  left. apply NATset_definition in H. destruct (IHis_NAT H).
  simpl. apply successor_definition. left. apply H0.
  simpl in *. apply successor_definition. right. apply H0.
Qed.


Theorem nat_subsetneq_implies_in : forall m n : NAT, m subsetneq n -> m in n.
Proof. Admitted.

Theorem NAT_subsetneq_then_Succ_subseteq : forall m n : NAT, m subsetneq n -> (Succ m) subseteq n.
Proof.
  intros m n [H H0] e H1.
  apply Succ_definition in H1.
  destruct H1. apply H, H1.
  subst. apply nat_subsetneq_implies_in.
  split. apply H. apply H0.
Qed.

Theorem NAT_subsetneq_iff_in : forall m n : NAT, m subsetneq n <-> m in n.
Proof.
  intros m n. split; intros H.
  apply nat_subsetneq_implies_in. split.
  apply H. intros H'. destruct H. apply H0, H'.
  split. apply NAT_is_transitive. apply H.
  intros H'. subst. apply (no_set_contains_itself n), H.
Qed.

Lemma subseteq_of_singleton_set : forall s t, s subseteq {{t}} -> s = {{}} \/ s = {{t}}.
Proof. Admitted.


Definition Pred : NAT->NAT.
  assert(forall n : NAT, (bigcup \{x in NATset : fun x => x subsetneq n\}) in NATset). {
    apply mathematical_induction.
    - unfold set_constraint.
      destruct AXIOM_OF_SUBSETS as [A HA].
      apply NATset_definition.
      assert(forall u, u in A <-> False). {
        intros u. split; intros H.
        apply HA in H. destruct H as [H [H0 H1]].
        apply subset_of_emptyset in H0.
        subst. apply H1. reflexivity.
        destruct H.
      } clear HA.
      unfold bigcup. destruct AXIOM_OF_THE_SUM_SET as [B HB].
      assert(forall u, u in B <-> False). {
        intros u. split; intros H0.
        apply HB in H0. destruct H0 as [x [H0 H1]].
        apply (H x), H0. destruct H0.
      } clear HB.
      assert(B = {{}}). {
        apply AXIOM_OF_EXTENSIONALITY.
        intros z. split; intros H1.
        apply H0 in H1. destruct H1.
        apply no_set_is_in_emptyset in H1. destruct H1.
      } subst. apply NAT_zero.
    - intros [n Hn] H.
      apply NATset_definition in H.
      apply NATset_definition.
      assert(is_NAT n). apply NATset_definition, Hn.
      induction H0.
      + simpl. unfold bigcup. destruct AXIOM_OF_THE_SUM_SET as [A HA].
        unfold set_constraint in HA.
        destruct AXIOM_OF_SUBSETS as [B HB].
        assert(successor {{}} = {{{{}}}}). {
          apply AXIOM_OF_EXTENSIONALITY.
          intros z. split; intros H0.
          - apply successor_definition in H0.
            apply cup_definition. destruct H0.
            right. apply H0. subst. left.
            apply singleton_set_definition. reflexivity.
          - apply successor_definition.
            apply cup_definition in H0. destruct H0.
            apply singleton_set_definition in H0.  right. apply H0.
            left. apply H0.
        } rewrite H0 in *. clear H0.
        assert(A = {{}}). {
          apply AXIOM_OF_EXTENSIONALITY.
          intros z. split; intros H0.
          apply HA in H0. destruct H0 as [x [H0 H1]].
          apply HB in H0. destruct H0 as [H0 [H2 H3]].
          apply subseteq_of_singleton_set in H2.
          destruct H2; subst. apply H1. exfalso. apply H3. reflexivity.
          apply no_set_is_in_emptyset in H0. destruct H0.
        } subst. apply NAT_zero.
      + simpl in *. apply NATset_definition in H0.
        assert((bigcup \{x in NATset : fun x => x subseteq (successor (successor s)) /\
                                                (x <> successor (successor s))\}) = successor s). admit.
        rewrite H1. apply NATset_definition, Hn.
  }
  intros n. exact (NAT_init (bigcup \{x in NATset : fun x => x subsetneq n\}) (H n)).
Admitted.

Fixpoint nat_to_NAT (n : nat) := match n with
  | 0     => NAT_ZERO
  | S n'  => Succ (nat_to_NAT n')
  end
.

Theorem nat_to_NAT_bijective :
  (forall m n : nat, (nat_to_NAT m) = (nat_to_NAT n) -> m = n) /\
  (forall N : NAT, exists n : nat, (nat_to_NAT n) = N)
.
Proof.
  split. {
  intros m. induction m.
  - intros n H. simpl in H.
    unfold nat_to_NAT in H.
    destruct n. reflexivity.
    apply NAT_equal, EQUAL_definition in H.
    destruct H as [H _]. destruct (H {{}}) as [_ H0].
    simpl in H0. assert({{}} in {{}}). apply H0, emptyset_in_Succ.
    apply no_set_contains_itself in H1. destruct H1.
  - intros n H. destruct n.
    apply NAT_equal, EQUAL_definition in H.
    destruct H as [H _]. destruct (H {{}}) as [H1 _].
    assert({{}} in {{}}). apply H1, emptyset_in_Succ.
    apply no_set_contains_itself in H0. destruct H0.
    apply NAT_equal, EQUAL_definition in H.
    destruct H as [H _].
    assert(forall n : nat, (nat_to_NAT m) = (nat_to_NAT n) -> S m = S n). {
      intros m' H0. apply IHm in H0. subst. reflexivity.
    } clear IHm. apply H0. clear H0.
    apply NAT_equal, AXIOM_OF_EXTENSIONALITY.
    intros z. split; intros H0; simpl in H; admit.
} intros [N HN].
  assert(is_NAT N). apply NATset_definition, HN.
  induction H. exists 0. apply NAT_equality.
  apply NATset_definition in H.
  destruct (IHis_NAT H) as [n Hn].
  exists (S n). simpl. apply NAT_equal.
  rewrite Hn. reflexivity.
Admitted.

Coercion nat_to_NAT : nat >-> NAT.

End NaturalNumber.
