From SetTheory Require Import set_theory.
Import SetTheory.

Module NaturalNumber.

Definition Successor (s : set) := s cup {{s}}.

Fixpoint nat_to_set (n : nat) :=
  match n with
    | 0     => {{}}
    | S n'  => Successor (nat_to_set n')
  end
.
Coercion nat_to_set : nat >-> set.

Lemma nat_in_its_successor : forall n : nat, n in (Successor n).
Proof.
  intros n.
  apply cup_definition. right.
  apply cup_definition. left.
  apply singleton_set_definition.
  reflexivity.
Qed.
Lemma nat_subsetneq_its_successor : forall n : nat, (nat_to_set n) subsetneq (Successor n).
Proof.
  intros n. split.
  - intros e H.
    apply cup_definition.
    left. apply H.
  - intros H.
    apply EQUAL_definition in H.
    destruct H as [H _].
    destruct (H n) as [_ H0].
    assert(n in (Successor n)).
      apply nat_in_its_successor.
    apply H0 in H1.
    apply no_set_contains_itself in H1.
    apply H1.
Qed.

Record inductive_set : Set := inductive_set_init {
  ind_set : set;
  ind_set_cond : {{}} in ind_set /\ (forall x, x in ind_set -> (Successor x) in ind_set);
}.
Definition inductive_set_to_set (id : inductive_set) := ind_set id.
Coercion inductive_set_to_set : inductive_set >-> set.

Lemma NATset_lemma : {N : inductive_set |
  forall x, x in N <->
  (forall id : inductive_set, x in id)}
. Proof. Admitted.

Definition NATset : inductive_set.
  destruct NATset_lemma as [N _].
  exact N.
Defined.
Theorem NATset_definition : forall s,
  s in NATset <-> (exists n : nat, s = n)
. Proof. Admitted.

Theorem NATset_property : forall A,
  A subseteq NATset ->
  0 in A /\ (forall s, s in A -> (Successor s) in A) ->
  A = NATset
.
Proof.
  intros A H [H0 H1].
  assert(exists A' : inductive_set, A = A'). {
    assert({{}} in A /\ (forall x, x in A -> (Successor x) in A)).
    { split. apply H0. intros x H'. apply H1, H'. }
    exists (inductive_set_init A H2). reflexivity.
  }
  destruct H2. subst.
  assert(NATset subseteq x). admit.
  Search subset.
  apply (subseteq_antisymmetric x NATset).
  apply H. apply H2.
Admitted.

(* THIS NEEDS BETTER PROOF *)
Corollary mathematical_induction : forall (P : set->Prop),
  P 0 /\ (forall n : nat, P n -> P (S n)) ->
  forall n : nat, P n
. 
Proof.
  intros P H n.
  remember \{x in NATset : fun x => P x\} as N.
  destruct H. induction n. apply H.
  apply H0, IHn.
Qed.

Record transitive_set : Set := transitive_set_init {
  trans_set : set;
  trans_set_cond : forall x, x in trans_set -> x subseteq trans_set;
}.
Definition transitive_set_to_set (tr : transitive_set) := trans_set tr.
Coercion transitive_set_to_set : transitive_set >-> set.

Theorem transitive_set_property : forall s : set,
  (exists tr : transitive_set, s = tr) <->
  (forall x y, x in y /\ y in s -> x in s)
. Proof. Admitted.

Theorem NATset_is_transitive_set : exists N : transitive_set, (ind_set NATset) = N.
Proof. Admitted.

End NaturalNumber.