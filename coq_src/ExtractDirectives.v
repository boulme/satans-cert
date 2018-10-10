(* Extraction *)

Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.
Require Import SatAnsCert.

Import ImpConfig.

Extraction Blacklist List String.

Separate Extraction BinIntDef Impure.ImpPrelude Rup SatAnsCert.
