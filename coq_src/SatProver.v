Require Export CnfSpec.
Require Import MSets.MSetPositive.
Import PositiveSet.

Require Import Bool.

Definition concrete_model: Type := PositiveSet.t.

Definition sem_cm: concrete_model -> model :=
 fun cm v => PositiveSet.mem v cm.

Local Open Scope list_scope.
Local Open Scope lazy_bool_scope.

Fixpoint sat_cm (c: clause) cm: bool := 
  match c with
  | nil => false
  | l::c' => eqb (sem_cm cm (ident l)) (is_pos l) ||| sat_cm c' cm
  end.


Lemma lit_cm_m cm a:
  eqb (sem_cm cm (ident a)) (is_pos a) = true -> (sem_cm cm) (ident a) = (is_pos a).
Proof.
  intros; apply eqb_eq.
  destruct (eqb _ _); simpl; discriminate || auto.
Qed.

Lemma lazy_orb_bool (b1 b2: bool): b1 ||| b2 = true <-> b1 = true \/ b2 = true.
Proof.
  destruct b1, b2; intuition.
Qed.

Local Hint Resolve lit_cm_m.

Lemma clause_sat c cm:
  sat_cm c cm = true -> sat c (sem_cm cm).
Proof.
  induction c; simpl.
  + intuition.
  + rewrite lazy_orb_bool.
    intuition eauto.
Qed.


Fixpoint sat_prover (f: cnf) (cm: concrete_model): bool :=
  match f with
  | nil => true
  | c::f' => sat_cm c cm &&& sat_prover f' cm
  end.

Lemma lazy_andb_bool (b1 b2: bool): b1 &&& b2 = true <-> b1 = true /\ b2 = true.
Proof.
  destruct b1, b2; intuition.
Qed.

Local Hint Resolve clause_sat.

Theorem sat_prover_correct f cm:
  sat_prover f cm = true -> sats f (sem_cm cm).
Proof.
  induction f; simpl.
  + intuition.
  + rewrite lazy_andb_bool.
    intuition.
Qed.