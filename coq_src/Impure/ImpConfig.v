(** Impure Config for UNTRUSTED backend !!! *)

Require Import ImpMonads.
Require Extraction.
(** Pure computations (used for extraction !) 

We keep module [Impure] opaque in order to check that Coq proof do not depend on 
the implementation of [Impure].

*)

Module Impure: MayReturnMonad.
  Include TrivialMonad.
End Impure.
Export Impure.

Extraction Inline ret callproof.

(* WARNING. The following directive is unsound.

  Extraction Inline bind

For example, it may lead to extract the following code as "true" (instead of an error raising code)
  failwith "foo";;true

*)
Extract Inlined Constant bind => "(|>)".

Extract Constant t "" => "". (* TODO: Un peu étrange, non ? *)
Extraction Inline t.

(** Comment the above code and decomment this to test that coq proofs still work with an impure monad !
*)

(*
Module Impure: MayReturnMonad := PowerSetMonad.
Export Impure.
*)

Global Opaque ret bind t mayRet callproof.
