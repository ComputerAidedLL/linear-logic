Require Import LinearLogic.

Notation "{{ }}" := (EmptyBag LinProp) (at level 5).

Ltac unique_elt_solve A := now intros B; cbn; destruct (eq_neq_LinProp A B).

Lemma singleton_bag A : (A :: {{ }}) == {{A}}.
Proof. unique_elt_solve A. Qed.

Lemma pair_bag A : (A :: {{A}} U {{ }}) == (A :: {{A}}).
Proof. unique_elt_solve A. Qed.

(* rule Bang_R does not seem to be used in the development *)
Lemma bang_test A : {{ }} |- (A -o !A).
Proof. apply Impl_R, Bang_R, Id, singleton_bag. Qed.

(* Axiom cut_fact does not seem to be used in the development *)
Lemma cut_fact_test A : {{ }} |- (A -o (A ** A)).
Proof.
apply Impl_R.
apply cut_fact with {{A}} (EmptyBag LinProp) A.
{ apply meq_refl. }
- apply Id, meq_refl.
- apply Times_R with {{A}} {{A}}.
  { apply pair_bag. }
  + apply Id, meq_refl.
  + apply Id, meq_refl.
Qed.
