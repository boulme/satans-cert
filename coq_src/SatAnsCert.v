(* Main program of the SatAnsCert *)

Require Export CnfSpec.
Require Import SatProver.
Require Import SolverInterface.
Require Import RatProver.

Require List.
Export List.ListNotations.

Local Open Scope impure_scope.
Local Open Scope string_scope.

Axiom read_input: unit -> ?? solver_Input.
Extract Constant read_input => "OracleInput.read_input".

Axiom finalize: solver_Input -> ?? unit.
Extract Constant finalize => "OracleInput.finalize".

Axiom sat_solver: solver_Input -> ?? solver_Answer.
Extract Constant sat_solver => "OracleSolver.sat_solver".

Local Hint Resolve sat_prover_correct.

(* This is the main execution of the satans-cert tool:

We prove that
 - if "SAT !" is finally printed then the CNF returned by read_input is sat.
 - if "UNSAT !" is finally printed then the CNF returned by read_input is unsat.
*)
Program Definition main: ?? unit :=
  DO o <~ new_exit_observer (fun _ => println "FAILURE WHILE READING INPUT");;
  DO f <~ read_input tt;;
  set_exit_observer (o, fun _ => finalize f;; println "FAILURE OF CERTIFICATION: the checker has aborted");;
  DO a <~ sat_solver f;;
  TRY
     match a with
     | SAT_Answer mc => 
        assert_b (sat_prover (problem f) mc) "Sat-Prover: bad model";;
        finalize f;;
        ASSERT (exists m, sats (problem f) m);;
        set_exit_observer (o, fun _ => println "SAT !") (* TODO print mc *)
     | UNSAT_Answer =>
        RatProver.unsatProver f (RatTheory.cnf_to_ccnf (problem f) (problem_ids f));;
        finalize f;;
        ASSERT (isUnsat (problem f));;
        set_exit_observer (o, fun _ => println "UNSAT !")
     end
  WITH_FAIL s, e => 
     println ("Certification failure: " +; s);;
             raise e.
Obligation 1.
  eauto.
Qed.
Obligation 2.
  constructor 1.
  intros m X. destruct H1.
  eapply ex_intro; eapply RatTheory.cnf_to_ccnf_correct; eauto. 
Qed.