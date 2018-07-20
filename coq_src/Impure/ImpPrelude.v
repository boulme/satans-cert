Require Export String.
Require Export List.
Require Extraction.
Require Import Ascii.
Require Import BinNums.

Axiom caml_string: Type.
Extract Inlined Constant caml_string => "string".

(** New line *)
Definition nl: string := String (ascii_of_pos 10%positive) EmptyString.

Inductive pstring: Type :=
  | Str: string -> pstring
  | CamlStr: caml_string -> pstring
  | Concat: pstring -> pstring -> pstring.

Coercion Str: string >-> pstring.
Bind Scope string_scope with pstring.

Notation "x +; y" := (Concat x y)
    (at level 65, left associativity): string_scope.

(* *)
Inductive recMode:= StdRec | MemoRec | BareRec | BuggyRec.


(* This a copy-paste from definitions in CompCert/Lib/CoqLib.v *)
Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).
