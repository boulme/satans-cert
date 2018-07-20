(* 

Extension of Coq language with generic extern operators:
  - a bit of exception-handling
  - (non-terminating) "while"-loop.

*)

Require Export ImpCore.
Require Export ImpPrelude.

Import Notations.
Local Open Scope impure.

(** Printing functions *)

Axiom print: pstring -> ?? unit.
Extract Constant print => "ImpOracles.print".

Axiom println: pstring -> ?? unit.
Extract Constant println => "ImpOracles.println".

Require Import ZArith.
Axiom string_of_Z: Z -> ?? pstring.
Extract Constant string_of_Z => "ImpOracles.string_of_Z".

Axiom timer: forall {A B}, (A -> ?? B)*A -> ?? B.
Extract Constant timer => "ImpOracles.timer".

(** Exception Handling *)

Axiom exit_observer: Type.
Extract Inlined Constant exit_observer => "((unit -> unit) ref)".

Axiom new_exit_observer: (unit -> ??unit) -> ??exit_observer.
Extract Constant new_exit_observer => "ImpOracles.new_exit_observer".

Axiom set_exit_observer: exit_observer * (unit -> ??unit) -> ??unit.
Extract Constant set_exit_observer => "ImpOracles.set_exit_observer".

Axiom exn: Type.
Extract Inlined Constant exn => "exn".

Axiom raise: forall {A}, exn -> ?? A.
Extract Constant raise => "raise".

Axiom exn2string: exn -> ?? pstring.
Extract Constant exn2string => "ImpOracles.exn2string".

Axiom fail: forall {A}, pstring -> ?? A.
Extract Constant fail => "ImpOracles.fail".

Axiom try_with_fail: forall {A}, (unit -> ?? A) * (pstring -> exn -> ??A) -> ??A.
Extract Constant try_with_fail => "ImpOracles.try_with_fail".

Axiom try_with_any: forall {A}, (unit -> ?? A) * (exn -> ??A) -> ??A.
Extract Constant try_with_any => "ImpOracles.try_with_any".

Notation "'RAISE' e" := (DO r <~ raise (A:=False) e ;; RET (match r with end)) (at level 0): impure_scope.
Notation "'FAILWITH' msg" := (DO r <~ fail (A:=False) msg ;; RET (match r with end)) (at level 0): impure_scope.

Notation "'TRY' k1 'WITH_FAIL' s ',' e '=>' k2" := (try_with_fail (fun _ => k1, fun s e => k2))
    (at level 55, k1 at level 53, right associativity): impure_scope.

Notation "'TRY' k1 'WITH_ANY' e '=>' k2" := (try_with_any (fun _ => k1, fun e => k2))
    (at level 55, k1 at level 53, right associativity): impure_scope.

Program Definition assert_b (b: bool) (msg: pstring): ?? b=true :=
  match b with
  | true => RET _
  | false => FAILWITH msg
  end.

Lemma assert_wlp_true msg b: WHEN assert_b b msg ~> _ THEN b=true.
Proof.
  wlp_simplify.
Qed.

Lemma assert_false_wlp msg (P: Prop): WHEN assert_b false msg ~> _ THEN P.
Proof.
  simpl; wlp_simplify.
Qed.

(** While-loop iterations *)

Axiom loop: forall {A B}, A * (A -> ?? (A+B)) -> ?? B.
Extract Constant loop => "ImpOracles.loop".

(** A while loop *)

Record while_loop_invariant {S} (cond: S -> bool) (body: S -> ?? S) (s0: S) (I: S -> Prop): Prop :=
  { while_init: I s0;
    while_preserv: forall s, I s -> cond s = true -> WHEN (body s) ~> s' THEN I s'
  }.
Arguments while_init [S cond body s0 I].
Arguments while_preserv [S cond body s0 I].

Program Definition while {S} cond body s0 (I: S -> Prop | while_loop_invariant cond body s0 I): ?? {s | I s /\ cond s = false}
  := loop (A:={s | I s})
       (s0, 
          fun s =>
          match (cond s) with
          | true => 
             DO s' <~ callproof (body s) ;; 
             RET (inl (A:={s | I s }) s')
          | false => 
             RET (inr (B:={s | I s /\ cond s = false}) s)
          end).
Obligation 1.
  destruct H; auto.
Qed.
Obligation 2.
  eapply (while_preserv H1); eauto.
Qed.
Extraction Inline while.

(** A loop until None (useful to demonstrate a UNSAT property) *)

Program Definition loop_until_None {S} (I: S -> Prop) (body: S -> ?? (option S)) 
  (H:forall s, I s -> WHEN (body s) ~> s' THEN match s' with Some s1 => I s1 | None => False end) (s0:S): ?? ~(I s0)
  := loop (A:={s | I s0 -> I s})
       (s0, 
          fun s =>
          DO s' <~ callproof (body s) ;;
          match s' with
          | Some s1 => RET (inl (A:={s | I s0 -> I s }) s1)
          | None => RET (inr (B:=~(I s0)) _)
          end).
Obligation 2.
  refine (H s _ _ H1). auto.
Qed.
Obligation 3.
  intros X; refine (H s _ _ H0). auto.
Qed.
Extraction Inline loop_until_None.

(********************************)
(* Axioms of Physical equality  *)

Module Type PhysEq.

Axiom phys_eq: forall {A}, A -> A -> ?? bool.

Axiom phys_eq_correct: forall A (x y:A), WHEN phys_eq x y ~> b THEN b=true -> x=y.

End PhysEq.

(* We only check here that above axioms are not trivially inconsistent...
   (but this does not prove the correctness of the extraction directive below).
 *)
Module PhysEqModel: PhysEq.

Definition phys_eq {A} (x y: A) := ret false.

Lemma phys_eq_correct: forall A (x y:A), WHEN phys_eq x y ~> b THEN b=true -> x=y.
Proof.
  wlp_simplify. discriminate.
Qed.

End PhysEqModel.

Export PhysEqModel.

Extract Constant phys_eq => "(==)".
Hint Resolve phys_eq_correct: wlp.


(*********************************************)
(* A generic fixpoint from an equality test  *)


Record answ {A B: Type} {R: A -> B -> Prop} := {
  input: A ;
  output: B ;
  correct: R input output
}.
Arguments answ {A B}.

Definition msg: pstring := "wapply fails".

Definition beq_correct {A} (beq: A -> A -> ?? bool) :=
  forall x y, WHEN beq x y ~> b THEN b=true -> x=y.

Definition wapply {A B} {R: A -> B -> Prop} (beq: A -> A -> ?? bool) (k: A -> ?? answ R) (x:A): ?? B :=
  DO a <~ k x;;
  DO b <~ beq x (input a) ;;
  assert_b b msg;;
  RET (output a).

Lemma wapply_correct A B (R: A -> B -> Prop) (beq: A -> A -> ?? bool)x (k: A -> ?? answ R):
 beq_correct beq
 -> WHEN wapply beq k x ~> y THEN R x y.
Proof.
  unfold beq_correct; wlp_simplify.
  destruct exta; simpl; auto.
Qed.
Local Hint Resolve wapply_correct: wlp.
Global Opaque wapply.

Axiom xrec_set_option: recMode -> ?? unit.
Extract Constant xrec_set_option => "ImpOracles.xrec_set_option".

(* TODO: generalizaton to get beq (and a Hash function ?) in parameters ? *)
Axiom xrec: forall {A B}, ((A -> ?? B) -> A -> ?? B) -> ?? (A -> ?? B).
Extract Constant xrec => "ImpOracles.xrec".

Definition rec_preserv {A B} (recF: (A -> ?? B) -> A -> ?? B) (R: A -> B -> Prop) :=
  forall f x, WHEN recF f x ~> z THEN (forall x', WHEN f x' ~> y THEN R x' y) -> R x z.


Program Definition rec {A B} beq recF (R: A -> B -> Prop) (H1: rec_preserv recF R) (H2: beq_correct beq): ?? (A -> ?? B) :=
  DO f <~ xrec (B:=answ R) (fun f x =>
         DO y <~ callproof (recF (wapply beq f) x) ;;
         RET {| input := x; output := proj1_sig y |});;
  RET (wapply beq f).
Obligation 1.
  eapply H1; eauto. clear H H1.
  wlp_simplify.
Qed.

Lemma rec_correct A B beq recF (R: A -> B -> Prop) (H1: rec_preserv recF R) (H2: beq_correct beq): 
  WHEN rec beq recF R H1 H2 ~> f THEN forall x, WHEN f x ~> y THEN R x y.
Proof.
  wlp_simplify.
Qed.
Hint Resolve rec_correct: wlp.
Global Opaque rec.
