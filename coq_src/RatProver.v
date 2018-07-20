Require Export CnfSpec.

Require Import List.
Require Import RatTheory.

Local Open Scope impure_scope.

Axiom next: forall {C}, (rupLCF C) * (list C) * solver_Input -> ?? (C + RatInput C).
Extract Constant next => "OracleRat.next_rat".

Definition unsatProver_msg: pstring := "UnsatProver.not_empty".

Definition unsatProver_loop (input: solver_Input) (f: ccnf): ?? option ccnf :=
      DO st <~ next ((mkNextInput f),input) ;;
      match st with
      | inl c => 
         if isEmpty (rep c) 
         then RET None
         else FAILWITH unsatProver_msg
      | inr ri =>
          DO f' <~ learnRat ri ;;
          RET (Some f')
       end.
Extraction Inline unsatProver_loop.

Local Hint Resolve rep_sat.

Program Definition unsatProver input := 
  loop_until_None 
     (fun (f: ccnf) => exists m, csats f m)
     (unsatProver_loop input)
     _.
Obligation 1.
  wlp_simplify.
  eapply isEmpty_correct; eauto.
Qed.
