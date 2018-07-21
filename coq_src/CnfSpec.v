(** Syntax and Semantics of CNF *)

Require Export BinNums.

Local Open Scope list_scope.

Definition var := positive.

Record literal := { is_pos: bool ; ident: var }.

Definition model := var -> bool.

(* syntactic clause *)
Definition clause := list literal.

Fixpoint sat (c: clause) (m: model): Prop := 
  match c with
  | nil => False
  | l::c' => m (ident l) = is_pos l \/ sat c' m
  end.

Definition cnf := list clause.

(* syntactic cnf *)
Fixpoint sats (f: cnf) (m: model): Prop :=
  match f with
  | nil => True
  | c::f' => sat c m /\ sats f' m 
  end.

Inductive isUnsat (f:cnf): Prop := 
  isUnsat_proof: (forall m, ~(sats f m)) -> isUnsat f.

Definition isSat(f: cnf): Prop := exists m, sats f m.

Lemma isSat_neg_isUnsat (f: cnf): isUnsat f <-> ~(isSat f).
Proof.
  firstorder.
Qed.