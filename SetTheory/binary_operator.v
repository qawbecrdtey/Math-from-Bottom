Require Import set_theory.
Import SetTheory.

Module BinaryRelation.

Record binary_relation : Set := binary_relation_init {
  relation : set;
  relation_cond : forall e, e in relation -> exists a b, \(a, b\) = e
}.
Definition binary_relation_to_set (R : binary_relation) : set := relation R.
Coercion binary_relation_to_set : binary_relation >-> set.
Axiom binary_relation_equality : forall R1 R2, R1 = R2 <-> relation R1 = relation R2.

Theorem binary_relation_definition : forall (R : binary_relation) e, e in R <->  e in R /\ exists a b, \(a, b\) = e.
Proof.
  intros R e. split; intros H.
  - split. apply H. apply (relation_cond R), H.
  - destruct H. apply H.
Qed.

Lemma membership_relation_lemma : forall S e,
  e in \{x in (cartesian_product S S) :
    fun x => exists a b, \(a, b\) = x /\ a in b
  \} ->
  exists a b, \(a, b\) = e
.
Proof.
  intros S e H.
  unfold set_constraint in H.
  destruct AXIOM_OF_SUBSETS as [A HA].
  apply HA in H.
  destruct H. do 3 (destruct H0). subst.
  apply cartesian_product_definition in H.
  do 3 (destruct H).
  apply ordered_pair_equality in H.
  destruct H, H0. subst.
  exists x1, x2. reflexivity.
Qed.
Definition membership_relation (S : set) : binary_relation :=
  binary_relation_init
    \{x in (cartesian_product S S) : fun x => exists a b, \(a, b\) = x /\ a in b\}
    (membership_relation_lemma S)
.

Lemma identity_relation_lemma : forall S e,
  e in \{x in (cartesian_product S S) :
    fun x => exists a, \(a, a\) = x
  \} ->
  exists a b, \(a, b\) = e
.
Proof.
  intros S e H.
  unfold set_constraint in H.
  destruct AXIOM_OF_SUBSETS as [A HA].
  apply HA in H.
  destruct H. destruct H0.
  exists x, x.
  apply H0.
Qed.
Definition identity_relation (S : set): binary_relation :=
  binary_relation_init
    \{x in (cartesian_product S S) : fun x => exists a, \(a, a\) = x\}
    (identity_relation_lemma S)
.

Definition related a (R : binary_relation) b := \(a, b\) in R.
Notation "a '/>' R '<\' b" := (related a R b) (at level 30, no associativity) : type_scope.

Theorem membership_relation_definition : forall S a b, a />(membership_relation S)<\ b <-> a in S /\ b in S /\ a in b.
Proof.
  intros S a b. split; intros H;
  unfold related, membership_relation, set_constraint in *; simpl in *;
  destruct AXIOM_OF_SUBSETS as [A HA].
  - apply HA in H. destruct H.
    do 3 (destruct H0).
    apply ordered_pair_equality in H0.
    destruct H0. subst.
    apply cartesian_product_definition in H.
    do 3 (destruct H).
    apply ordered_pair_equality in H.
    destruct H. subst. destruct H0.
    split. apply H. split. apply H0. apply H1.
  - apply HA. split.
    apply cartesian_product_definition. exists a, b. split. reflexivity.
    destruct H. destruct H0. split. apply H. apply H0.
    exists a, b. split. reflexivity. destruct H, H0. apply H1.
Qed.
Theorem identity_relation_definition : forall S a b, a />(identity_relation S)<\ b <-> a in S /\ a = b.
Proof.
  intros S a b. split; intros H;
  unfold related, identity_relation, set_constraint in *; simpl in *;
  destruct AXIOM_OF_SUBSETS as [A HA].
  - apply HA in H. destruct H, H0.
    apply ordered_pair_equality in H0.
    destruct H0. subst.
    apply cartesian_product_definition in H.
    do 3 (destruct H). destruct H0.
    apply ordered_pair_equality in H.
    destruct H. subst. split. apply H0. reflexivity.
  - apply HA. destruct H. subst. split.
    apply cartesian_product_definition. exists b, b. split.
    reflexivity. split; apply H. exists b. reflexivity.
Qed.

Definition domain (R : binary_relation) : set := \{x in bigcup (bigcup R) : fun x => exists y, y in (bigcup (bigcup R)) /\ x />R<\ y\}.
Definition image (R : binary_relation) : set := \{x in bigcup (bigcup R) : fun x => exists y, y in (bigcup (bigcup R)) /\ y />R<\ x\}.
Definition upon_relation (R : binary_relation) : set := (domain R) cup (image R).
Theorem domain_definition : forall R e, e in (domain R) <-> exists f, e />R<\ f.
Proof.
  intros R e. split; intros H;
  unfold domain, set_constraint in *;
  destruct AXIOM_OF_SUBSETS as [A HA].
  - apply HA in H. destruct H. destruct H0 as [y [H0 H1]].
    exists y. apply H1.
  - apply HA. split.
    + apply bigcup_definition.
      exists (singleton_set e).
      destruct H as [f H]. split.
      * apply bigcup_definition.
        exists \(e, f\). split. apply H.
        apply cup_definition. left.
        apply singleton_set_definition.
        apply AXIOM_OF_EXTENSIONALITY.
        intros z. split; intros H'.
        rewrite singleton_set_is_single_element_set. apply H'.
        rewrite <- singleton_set_is_single_element_set. apply H'.
      * apply singleton_set_definition. reflexivity.
    + destruct H as [f H]. exists f. split.
      apply bigcup_definition. exists {{e, f}}. split.
      apply bigcup_definition. exists \(e, f\). split.
      apply H. apply cup_definition. right.
      apply cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
      apply cup_definition. right.
      apply cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
      apply H.
Qed.
Theorem image_definition : forall R f, f in (image R) <-> exists e, e />R<\ f.
Proof.
  intros R f. split; intros H;
  unfold image, set_constraint in *;
  destruct AXIOM_OF_SUBSETS as [A HA].  
  apply HA in H. destruct H. destruct H0 as [e [H0 H1]]. exists e. apply H1.
  apply HA. split.
  - destruct H as [e H].
    apply bigcup_definition.
    exists {{e, f}}. split.
    + apply bigcup_definition.
      exists \(e, f\). split. apply H.
      apply cup_definition. right.
      apply cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
    + apply cup_definition. right.
      apply cup_definition. left.
      apply singleton_set_definition.
      reflexivity.
  - destruct H as [e H].
    exists e. split.
    + apply bigcup_definition.
      exists (singleton_set e). split.
      * apply bigcup_definition.
        exists \(e, f\). split. apply H.
        apply cup_definition. left.
        apply singleton_set_definition. symmetry.
        apply singleton_set_is_single_element_set.
      * apply singleton_set_definition. reflexivity.
    + apply H.
Qed.
Theorem upon_relation_definition : forall R e,
  e in (upon_relation R) <-> e in (domain R) \/ e in (image R)
.
Proof.
  intros R e. split; intros H.
  - unfold upon_relation in H.
    apply cup_definition in H. destruct H;
    [left | right]; apply H.
  - unfold upon_relation.
    apply cup_definition. apply H.
Qed.

Lemma inverse_relation_lemma : forall R e,
  e in \{x in (cartesian_product (image R) (domain R)) :
    fun x => forall a b, \(b, a\) = x -> a />R<\ b
  \} ->
  exists a b, \(a, b\) = e
.
Proof.
  intros R e H.
  unfold set_constraint in H.
  destruct AXIOM_OF_SUBSETS as [A HA].
  apply HA in H. destruct H.
  apply cartesian_product_definition in H.
  do 3 (destruct H). subst.
  exists x, x0. reflexivity.
Qed.
Definition inverse_relation (R : binary_relation) :=
  binary_relation_init
    \{x in (cartesian_product (image R) (domain R)) : fun x => forall a b, \(b, a\) = x -> a />R<\ b\}
    (inverse_relation_lemma R)
.
Theorem inverse_relation_definition : forall R a b, a />(inverse_relation R)<\ b <-> b />R<\ a.
Proof.
  intros R a b.
  unfold inverse_relation, set_constraint, related.
  simpl. destruct AXIOM_OF_SUBSETS as [A HA].
  split; intros H.
  - apply HA in H. destruct H.
    apply cartesian_product_definition in H.
    destruct H as [c [d [H' H]]].
    apply ordered_pair_equality in H'.
    destruct H', H. subst.
    apply H0. reflexivity.
  - apply HA. split.
    + apply cartesian_product_definition.
      exists a, b. split. reflexivity. split.
      apply image_definition. exists b. apply H.
      apply domain_definition. exists a. apply H.
    + intros c d H1.
      apply ordered_pair_equality in H1.
      destruct H1. subst. apply H.
Qed.

Lemma compose_relation_lemma : forall R1 R2 e,
  e in \{x in (cartesian_product (domain R1) (image R2)) :
    fun x => exists e f, \(e, f\) = x /\ (exists g, e />R1<\ g /\ g />R2<\ f)
  \} ->
  exists a b, \(a, b\) = e
.
Proof.
  intros R1 R2 e H.
  unfold set_constraint in H.
  destruct AXIOM_OF_SUBSETS as [A HA].
  apply HA in H. destruct H.
  apply cartesian_product_definition in H.
  destruct H as [c [d [H H']]].
  subst. exists c, d. reflexivity. 
Qed.
Definition compose_relation (R1 R2 : binary_relation) : binary_relation :=
  binary_relation_init
  \{x in (cartesian_product (domain R1) (image R2)) : fun x => exists e f, \(e, f\) = x /\ (exists g, e />R1<\ g /\ g />R2<\ f)\}
  (compose_relation_lemma R1 R2)
.
Theorem compose_relation_definition : forall R1 R2 e f,
  e />(compose_relation R1 R2)<\ f <-> (exists g, e />R1<\ g /\ g />R2<\ f)
.
Proof.
  intros R1 R2 e f. split; intros H;
  unfold compose_relation, related, set_constraint in *; simpl in *;
  destruct AXIOM_OF_SUBSETS as [A HA].
  - apply HA in H. destruct H. do 3 (destruct H0).
    apply ordered_pair_equality in H0.
    destruct H0. subst.
    destruct H1. exists x. apply H0.
  - apply HA. split.
    apply cartesian_product_definition.
    exists e, f. split. reflexivity.
    destruct H as [g [Hl Hr]]. split.
    apply domain_definition. exists g. apply Hl.
    apply image_definition. exists g. apply Hr.
    exists e, f. split. reflexivity.
    destruct H as [g H].
    exists g. apply H.
Qed.
Notation "( R1 @ .. @ R2 @ R3 )" := (compose_relation R1 (..(compose_relation R2 R3)..)) : type_scope.

Theorem compose_relation_associative : forall R1 R2 R3, ((R1@R2)@R3) = (R1@(R2@R3)).
Proof.
  intros R1 R2 R3.
  apply binary_relation_equality, AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply binary_relation_definition in H. destruct H.
    destruct H0 as [a [b H0]]. subst.
    apply compose_relation_definition. apply compose_relation_definition in H.
    destruct H as [d [H0 H2]].
    apply compose_relation_definition in H0.
    destruct H0 as [c [H0 H1]].
    exists c. split. apply H0.
    apply compose_relation_definition. exists d.
    split. apply H1. apply H2.
  - apply binary_relation_definition in H. destruct H.
    destruct H0 as [a [b H0]]. subst.
    apply compose_relation_definition. apply compose_relation_definition in H.
    destruct H as [c [H1 H2]].
    apply compose_relation_definition in H2.
    destruct H2 as [d [H2 H3]].
    exists d. split. apply compose_relation_definition.
    exists c. split. apply H1. apply H2. apply H3.
Qed.

Theorem inverse_relation_involutive : forall R, inverse_relation (inverse_relation R) = R.
Proof.
  intros R.
  apply binary_relation_equality, AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply binary_relation_definition in H. destruct H.
    destruct H0 as [a [b H0]]. subst.
    do 2 (apply -> inverse_relation_definition in H).
    apply H.
  - apply binary_relation_definition in H. destruct H.
    destruct H0 as [a [b H0]]. subst.
    do 2 (apply inverse_relation_definition).
    apply H.
Qed.

Lemma inverse_domain_is_image : forall R, domain (inverse_relation R) = image R.
Proof.
  intros R. apply AXIOM_OF_EXTENSIONALITY.
  intros e. split; intros H.
  - apply domain_definition in H.
    destruct H as [f H].
    apply -> inverse_relation_definition in H.
    apply image_definition. exists f. apply H.
  - apply image_definition in H.
    destruct H as [f H].
    apply domain_definition. exists f.
    apply inverse_relation_definition, H.
Qed.
Lemma inverse_image_is_domain : forall R, image (inverse_relation R) = domain R.
Proof.
  intros R. apply AXIOM_OF_EXTENSIONALITY.
  intros e. split; intros H.
  - apply domain_definition.
    apply image_definition in H.
    destruct H as [f H]. exists f.
    apply inverse_relation_definition, H.
  - apply image_definition.
    apply domain_definition in H.
    destruct H as [f H]. exists f.
    apply inverse_relation_definition, H.
Qed.

Lemma cup_relation_lemma : forall (R1 R2 : binary_relation) e, e in (R1 cup R2) -> exists a b, \(a, b\) = e.
Proof.
  intros R1 R2 e H.
  apply cup_definition in H. destruct H.
  - apply (relation_cond R1), H.
  - apply (relation_cond R2), H.
Qed.
Definition cup_relation (R1 R2 : binary_relation) :=
  binary_relation_init
    (R1 cup R2)
    (cup_relation_lemma R1 R2)
.
Theorem cup_relation_definition : forall R1 R2 a b, a />(cup_relation R1 R2)<\ b <-> a />R1<\ b \/ a />R2<\ b.
Proof.
  intros R1 R2 a b.
  unfold cup_relation, set_constraint, related. simpl.
  split; intros H; apply cup_definition, H.
Qed.

Lemma cap_relation_lemma : forall (R1 R2 : binary_relation) e, e in (R1 cap R2) -> exists a b, \(a, b\) = e.
Proof.
  intros R1 R2 e H.
  apply cap_definition in H. destruct H.
  apply (relation_cond R1), H.
Qed.
Definition cap_relation (R1 R2 : binary_relation) :=
  binary_relation_init
    (R1 cap R2)
    (cap_relation_lemma R1 R2)
.
Theorem cap_relation_definition : forall R1 R2 a b, a />(cap_relation R1 R2)<\ b <-> a />R1<\ b /\ a />R2<\ b.
Proof.
  intros R1 R2 a b.
  unfold cap_relation, set_constraint, related. simpl.
  split; intros H; apply cap_definition, H.
Qed.

Theorem cup_compose_relation_distributive : forall R1 R2 R3, ((cup_relation R1 R2)@R3) = cup_relation (R1@R3) (R2@R3).
Proof.
  intros R1 R2 R3. apply binary_relation_equality, AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply binary_relation_definition in H.
    destruct H. destruct H0 as [a [b H0]]. subst.
    apply cup_relation_definition.
    apply compose_relation_definition in H.
    destruct H as [c [H Hr]].
    apply cup_relation_definition in H.
    destruct H; [left | right]; apply compose_relation_definition;
    exists c; split; apply H || apply Hr.
  - apply binary_relation_definition in H.
    destruct H. destruct H0 as [a [b H0]]. subst.
    apply compose_relation_definition.
    apply cup_relation_definition in H. destruct H;
    apply compose_relation_definition in H;
    destruct H as [c [H H0]]; exists c; split;
    apply H0 || apply cup_relation_definition;
    [left | right]; apply H.
Qed.
Theorem cap_inverse_distributive : forall R1 R2,
  inverse_relation (cap_relation R1 R2) = cap_relation (inverse_relation R1) (inverse_relation R2)
.
Proof.
  intros R1 R2. apply binary_relation_equality, AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H;
  apply binary_relation_definition in H; destruct H;
  destruct H0 as [a [b H0]]; subst.
  - apply cap_relation_definition.
    apply -> inverse_relation_definition in H.
    apply cap_relation_definition in H.
    destruct H. split; apply inverse_relation_definition;
    apply H || apply H0.
  - apply inverse_relation_definition, cap_relation_definition.
    apply cap_relation_definition in H.
    destruct H.
    apply -> inverse_relation_definition in H.
    apply -> inverse_relation_definition in H0.
    split; apply H || apply H0.
Qed.

Lemma subseteq_then_inverse_subseteq : forall (R1 R2 : binary_relation),
  R1 subseteq R2 -> (inverse_relation R1) subseteq (inverse_relation R2)
.
Proof.
  intros R1 R2 H e H0.
  apply binary_relation_definition in H0. destruct H0.
  destruct H1 as [a [b H1]]. subst.
  apply inverse_relation_definition.
  apply -> inverse_relation_definition in H0. apply H, H0.
Qed.

Lemma cup_domain_is_domain_cup_relation : forall R1 R2,
  domain (cup_relation R1 R2) = (domain R1) cup (domain R2)
.
Proof.
  intros R1 R2. apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply domain_definition in H.
    destruct H as [f H].
    apply binary_relation_definition in H. destruct H.
    destruct H0 as [a [b H0]].
    apply ordered_pair_equality in H0.
    destruct H0. symmetry in H0, H1. subst.
    apply cup_definition.
    apply cup_relation_definition in H.
    destruct H; [left | right];
    apply domain_definition;
    exists b; apply H.
  - apply domain_definition.
    apply cup_definition in H. destruct H;
    apply domain_definition in H;
    destruct H as [a H]; exists a;
    apply cup_relation_definition;
    [left | right]; apply H.
Qed.

Lemma empty_relation_lemma : forall e, e in {{}} -> exists a b, \(a, b\) = e.
Proof. intros e H. apply no_set_is_in_emptyset in H. destruct H. Qed.
Definition empty_relation :=
  binary_relation_init
    {{}}
    empty_relation_lemma
.
Theorem empty_relation_definition : forall a b, a />empty_relation<\ b <-> False.
Proof.
  intros a b.
  unfold empty_relation, set_constraint, related. simpl.
  split; intros H; try (apply no_set_is_in_emptyset in H); destruct H.
Qed.

Definition reflexive R := forall a, a in (upon_relation R) -> a />R<\ a.
Definition symmetric R := forall a b, a />R<\ b -> b />R<\ a.
Definition antisymmetric R := forall a b, a />R<\ b -> b />R<\ a -> a = b.
Definition asymmetric R := forall a b, a />R<\ b -> ~(b />R<\ a).
Definition transitive R := forall a b c, a />R<\ b -> b />R<\ c -> a />R<\ c.
Definition irreflexive R := forall a, ~(a />R<\ a).
Definition comparable R := forall a b, a in (upon_relation R) -> b in (upon_relation R) -> (a />R<\ b \/ b />R<\ a).
Definition equivalent R := reflexive R /\ symmetric R /\ transitive R.

Record nonstrict_order_relation : Set := nonstrict_order_relation_init {
  NORelation : binary_relation;
  NORelation_cond : reflexive NORelation /\ antisymmetric NORelation /\ transitive NORelation
}.
Definition nonstrict_order_relation_to_binary_relation NOR := NORelation NOR.
Coercion nonstrict_order_relation_to_binary_relation : nonstrict_order_relation >-> binary_relation.

Record loset : Set := loset_init {
  LOSet : nonstrict_order_relation;
  LOSet_cond : forall a b, a in (upon_relation LOSet) ->
                            b in (upon_relation LOSet) ->
                            (a />LOSet<\ b \/ b />LOSet<\ a \/ a = b)
}.
Definition loset_to_nonstrict_order_relation LOS := LOSet LOS.
Coercion loset_to_nonstrict_order_relation : loset >-> nonstrict_order_relation.

Record poset : Set := poset_init {
  POSet : nonstrict_order_relation;
  POSet_cond : ~(forall a b, a in (upon_relation POSet) ->
                              b in (upon_relation POSet) ->
                              (a />POSet<\ b \/ b />POSet<\ a \/ a = b))
}.
Definition poset_to_nonstrict_order_relation POS := POSet POS.
Coercion poset_to_nonstrict_order_relation : poset >-> nonstrict_order_relation.

Record strict_order_relation : Set := strict_order_relation_init {
  SORelation : binary_relation;
  SORelation_cond : irreflexive SORelation /\ asymmetric SORelation /\ transitive SORelation
}.
Definition strict_order_relation_to_binary_relation SOR := SORelation SOR.
Coercion strict_order_relation_to_binary_relation : strict_order_relation >-> binary_relation.

Record strict_linear_order_relation : Set := strict_linear_order_relation_init {
  SLORelation : strict_order_relation;
  SLORelation_cond : comparable SLORelation
}.
Definition strict_linear_order_relation_to_strict_order_relation SLOR := SLORelation SLOR.
Coercion strict_linear_order_relation_to_strict_order_relation : strict_linear_order_relation >-> strict_order_relation.

Record strict_partial_order_relation : Set := strict_partial_order_relation_init {
  SPORelation : strict_order_relation;
  SPORelation_cond : ~comparable SPORelation
}.
Definition strict_partial_order_relation_to_strict_order_relation SPOR := SPORelation SPOR.
Coercion strict_partial_order_relation_to_strict_order_relation : strict_partial_order_relation >-> strict_order_relation.

Definition strictly_ordered {R : strict_order_relation} (a b : set) := a />R<\ b.
Definition nonstrictly_ordered {R : nonstrict_order_relation} (a b : set) := a />R<\ b.
Definition nonstrictly_neq_ordered {R : nonstrict_order_relation} (a b : set) := a />R<\ b /\ a <> b.

Notation "a < b" := (strictly_ordered a b).
Notation "a !< b" := (~strictly_ordered a b)(at level 70).
Notation "a <= b" := (nonstrictly_ordered a b).
Notation "a !<= b" := (~nonstrictly_ordered a b)(at level 70).
Notation "a <!= b" := (nonstrictly_neq_ordered a b)(at level 70).
Notation "a !<!= b" := (~nonstrictly_neq_ordered a b)(at level 70).

Example reflexive_relation_contains_identity_relation : forall R,
  reflexive R -> identity_relation (upon_relation R) subseteq R
.
Proof.
  intros R H e H0.
  unfold reflexive in H.
  apply binary_relation_definition in H0.
  destruct H0. destruct H1 as [a [b H1]]. subst.
  apply identity_relation_definition in H0.
  destruct H0. subst. apply H, H0.
Qed.

Example reflexive_inverse_is_reflexive : forall R, reflexive R -> reflexive (inverse_relation R).
Proof.
  intros R H e H0.
  apply inverse_relation_definition, H.
  apply upon_relation_definition.
  apply upon_relation_definition in H0.
  destruct H0.
  - right. apply domain_definition in H0.
    destruct H0 as [f H0].
    apply -> inverse_relation_definition in H0.
    apply image_definition. exists f. apply H0.
  - left. apply image_definition in H0.
    destruct H0 as [f H0].
    apply -> inverse_relation_definition in H0.
    apply domain_definition. exists f. apply H0.
Qed.

Example symmetric_inverse_is_symmetric : forall R, symmetric R -> symmetric (inverse_relation R).
Proof.
  intros R H a b H0.
  apply inverse_relation_definition.
  apply -> inverse_relation_definition in H0.
  apply H, H0.
Qed.

Example transitive_inverse_is_transitive : forall R, transitive R -> transitive (inverse_relation R).
Proof.
  intros R H a b c H0 H1.
  apply inverse_relation_definition.
  apply -> inverse_relation_definition in H0.
  apply -> inverse_relation_definition in H1.
  apply H with b. apply H1. apply H0.
Qed.

Example asymmetric_then_cap_inverse_is_empty : forall R, asymmetric R -> R cap (inverse_relation R) = {{}}.
Proof.
  intros R H. apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H0.
  - apply cap_definition in H0.
    destruct H0.
    apply binary_relation_definition in H0.
    destruct H0. destruct H2 as [a [b H2]]. subst.
    apply -> inverse_relation_definition in H1.
    apply H in H0. apply H0 in H1. destruct H1.
  - apply no_set_is_in_emptyset in H0. destruct H0.
Qed.

Example equivalent_then_idempotent : forall R, equivalent R -> (R @ R) = R.
Proof.
  intros R H. apply binary_relation_equality, AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H0.
  - apply binary_relation_definition in H0.
    destruct H0. destruct H1 as [a [b H1]]. subst.
    apply compose_relation_definition in H0.
    destruct H0 as [c [H0 H1]].
    destruct H as [H [H2 H3]].
    apply H3 with c. apply H0. apply H1.
  - apply binary_relation_definition in H0.
    destruct H0. destruct H1 as [a [b H1]]. subst.
    apply compose_relation_definition.
    destruct H as [H [H1 H2]].
    exists b. split. apply H0.
    apply H, upon_relation_definition.
    right. apply image_definition. exists a. apply H0.
Qed.

Example relation_subseteq_relation_compose_reflexive : forall (T R : binary_relation),
  reflexive T -> (upon_relation R) = (upon_relation T) -> R subseteq (R @ T)
.
Proof.
  intros T R H H0 e H1.
  apply binary_relation_definition in H1.
  destruct H1. destruct H2 as [a [b H2]]. subst.
  apply compose_relation_definition. exists b. split.
  apply H1. apply H. rewrite <- H0. apply upon_relation_definition.
  right. apply image_definition. exists a. apply H1.
Qed.

Example relateion_subseteq_reflexive_compose_relation : forall (T R : binary_relation),
  reflexive T -> (upon_relation R) = (upon_relation T) -> R subseteq (T @ R)
.
Proof.
  intros T R H H0 e H1.
  apply binary_relation_definition in H1.
  destruct H1. destruct H2 as [a [b H2]]. subst.
  apply compose_relation_definition. exists a. split.
  apply H. rewrite <- H0. apply upon_relation_definition. left.
  apply domain_definition. exists b. apply H1. apply H1.
Qed.

Example poset_inverse_cup_is_identity : forall R : poset,
  R cap (inverse_relation R) = identity_relation (upon_relation R)
.
Proof.
  intros R. apply AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H.
  - apply cap_definition in H. destruct H.
    apply binary_relation_definition in H.
    destruct H. destruct H1 as [a [b H1]]. subst.
    apply -> inverse_relation_definition in H0.
    apply identity_relation_definition. split.
    + apply upon_relation_definition. left.
      apply domain_definition. exists b. apply H.
    + destruct (NORelation_cond R). destruct H2.
      apply H2. apply H. apply H0.
  - apply binary_relation_definition in H.
    destruct H. destruct H0 as [a [b H0]]. subst.
    apply identity_relation_definition in H.
    destruct H. subst. apply upon_relation_definition in H.
    apply cap_definition. destruct H; split;
    apply domain_definition in H || apply image_definition in H;
    destruct H as [f H]; destruct (NORelation_cond R); destruct H1.
    + apply H0, upon_relation_definition. left. apply domain_definition.
      exists f. apply H.
    + apply inverse_relation_definition, H0, upon_relation_definition.
      left. apply domain_definition. exists f. apply H.
    + apply H0, upon_relation_definition. right. apply image_definition.
      exists f. apply H.
    + apply inverse_relation_definition, H0, upon_relation_definition.
      right. apply image_definition. exists f. apply H.
Qed.

Example poset_idempotent : forall R : poset, (R @ R) = R.
Proof.
  intros R. apply binary_relation_equality, AXIOM_OF_EXTENSIONALITY.
  intros z. split; intros H;
  apply binary_relation_definition in H;
  destruct H; destruct H0 as [a [b H0]]; subst.
  - apply compose_relation_definition in H.
    destruct H as [c [H H0]].
    destruct (NORelation_cond R). destruct H2.
    apply H3 with c. apply H. apply H0.
  - apply compose_relation_definition. exists a.
    destruct (NORelation_cond R). destruct H1.
    split. apply H0, upon_relation_definition. left. apply domain_definition. exists b.
    all : apply H.
Qed.

Example poset_inverse_is_poset : forall R : poset, exists S : poset, inverse_relation R = S.
Proof.
  intros R.
  assert(exists T : nonstrict_order_relation, inverse_relation R = T). {
    assert(reflexive (inverse_relation R) /\ antisymmetric (inverse_relation R) /\ transitive (inverse_relation R)). {
      destruct (NORelation_cond R). destruct H0. split; try split.
      - intros e H2. apply inverse_relation_definition. apply H, upon_relation_definition.
        apply upon_relation_definition in H2. destruct H2.
        + apply domain_definition in H2. destruct H2 as [f H2].
          apply -> inverse_relation_definition in H2. right.
          apply image_definition. exists f. apply H2.
        + apply image_definition in H2. destruct H2 as [f H2].
          left. apply -> inverse_relation_definition in H2.
          apply domain_definition. exists f. apply H2.
      - intros a b H2 H3. apply -> inverse_relation_definition in H2. apply -> inverse_relation_definition in H3.
        apply H0. apply H3. apply H2.
      - intros a b c H2 H3. apply inverse_relation_definition.
        apply -> inverse_relation_definition in H2. apply -> inverse_relation_definition in H3.
        apply H1 with b. apply H3. apply H2.
    }
    exists (nonstrict_order_relation_init (inverse_relation R) H). reflexivity.
  }
  destruct H as [T H'].
  
(*  TBD  *)

  exists (poset_init (T) H0).
  }).
Qed.

End BinaryRelation.