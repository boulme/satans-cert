(** A small example defining "fibonacci" function in a naive style
   from a (possibly memoïzed) generic fixpoint
*)

Require Import ImpExtern.


Import Notations.
Local Open Scope impure.


Require Import ZArith.
Local Open Scope Z.

Module TestFib.

(* Relational Specification of Fibonacci function *)
Inductive isfib: Z -> Z -> Prop :=
 | isfib_base p: (p <= 2) -> isfib p 1
 | isfib_rec p n1 n2: isfib p n1 -> isfib (p+1) n2 -> isfib (p+2) (n1+n2).

(* Implementation of Fibonacci -- parametrized by the equality test *)
Program Definition fib (beq: Z -> Z -> ?? bool) (X: beq_correct beq) (z: Z): ?? Z := 
  DO f <~ rec beq (fun (fib: Z -> ?? Z) p => 
    if p <=? 2
    then RET 1 
    else
      let prev := p-1 in
      DO r1 <~ fib prev ;;
      DO r2 <~ fib (prev-1) ;;
      RET (r2+r1))
    isfib _ X;;
  (f z).
Obligation 1.
  intros f x. wlp_simplify.
  + apply isfib_base.
    generalize (Z.leb_spec x 2).
    rewrite H. intro Y; inversion Y; auto.
  + cutrewrite (x = (x - 1 - 1) + 2).
    eapply isfib_rec; auto.
    * eapply H0; eauto.
    * ring_simplify.
      eapply H0; eauto.
    * ring.
Qed.

(* Fibonacci function using physical equality *)
Program Definition pfib x: ?? Z :=
   fib phys_eq _ x.
Obligation 1.
  unfold beq_correct. apply phys_eq_correct.
Qed.

Lemma pfib_correct (x: Z): WHEN pfib x ~> y THEN isfib x y.
Proof.
  wlp_simplify.
Qed.

(* Fibonacci function using structural equality on Z *)
Program Definition sfib x: ?? Z :=
   fib (fun x y => RET (Z.eqb x y)) _ x.
Obligation 1.
  unfold beq_correct; wlp_simplify.
  generalize (Z.eqb_spec x0 y).
  rewrite H; intro Y; inversion Y; auto.
Qed.

Lemma sfib_correct (x: Z): WHEN sfib x ~> y THEN isfib x y.
Proof.
  wlp_simplify.
Qed.

(* Executable test *)
Definition print_fib (msg: pstring) (fib: Z -> ?? Z) (z: Z): ?? unit :=
  println msg;;
  DO r <~ timer (fib,z);;
  DO s <~ string_of_Z r;;
  println ("result = " +; s);;
  println "".

Definition test: ?? unit :=
  println "";;
  TRY
     xrec_set_option MemoRec;;
     print_fib "starting Memoized fib(40)" sfib 40;;
     print_fib "starting Memoized fib(10000)" sfib 10000;;
     xrec_set_option BareRec;;
     println "# Now computation with naive or buggy fixpoints";;
     print_fib "starting Bare pfib(40)" pfib 40;;
     xrec_set_option StdRec;;
     print_fib "starting Std pfib(40)" pfib 40;;
     xrec_set_option StdRec;;
     print_fib "starting Std sfib(40)" sfib 40;;
     xrec_set_option BuggyRec;;
     print_fib "starting Buggy fib(40)" sfib 40
  WITH_FAIL s, e => 
     println ("Certification failure: " +; s);;
     raise e.

End TestFib.


(*************************)
(* Extraction directives *)

Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.

Import ImpConfig.

Extraction Blacklist List String.

Separate Extraction BinIntDef ImpExtern TestFib.

