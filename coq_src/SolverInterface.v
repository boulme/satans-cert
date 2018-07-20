(* Data-types to communicate with the OracleSolver in ocaml *)

Require Export Impure.ImpExtern.
Export Impure.ImpCore.Notations.

Require Export CnfSpec.
Require Import SatProver.


Axiom oracle_data : Type.
Extract Constant oracle_data => "OracleData.oracle_data".

Axiom clause_id: Type.
Extract Constant clause_id => "int".

Axiom default_clause_id: clause_id.
Extract Constant default_clause_id => "0".

Record solver_Input := { problem: cnf; problem_ids: list clause_id; name: pstring; global: oracle_data }.

Inductive solver_Answer: Type :=
  | SAT_Answer: concrete_model -> solver_Answer
  | UNSAT_Answer: solver_Answer
.
