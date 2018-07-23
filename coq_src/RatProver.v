Require Export CnfSpec.

Require Import List.
Require Import RatTheory.

Local Open Scope impure_scope.

Axiom next: forall {C}, (rupLCF C) * (list C) * solver_Input -> ?? (C + RatInput C).
Extract Constant next => "OracleRat.next_rat".

Definition unsatProver_msg: pstring := "UnsatProver.not_empty".

Definition unsatProver_loop_body (input: solver_Input) (f: ccnf): ?? option ccnf :=
      DO step <~ next ((mkNextInput f),input) ;;
      match step with
      | inl c =>  (* check that [next] has found a trivially UNSAT clause *)
         if isEmpty (rep c) 
         then RET None
         else FAILWITH unsatProver_msg
      | inr ri => (* build a new CNF from the RAT bunch *)
          DO f' <~ learnRat ri ;;
          RET (Some f')
       end.
Extraction Inline unsatProver_loop_body.

Local Hint Resolve rep_sat.

Program Definition unsatProver input : forall f, ?? ~(exists m, csats f m) := 
  loop_until_None 
     (fun (f: ccnf) => exists m, csats f m) (* loop invariant *)
     (unsatProver_loop_body input)
     _.
Obligation 1.
  wlp_simplify.
  eapply isEmpty_correct; eauto.
Qed.
