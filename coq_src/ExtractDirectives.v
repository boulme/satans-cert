(* Extraction *)

Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.
Require Import SatSolver.

Import ImpConfig.

Extraction Blacklist List String.

Separate Extraction Impure.ImpExtern Rup SatSolver.
