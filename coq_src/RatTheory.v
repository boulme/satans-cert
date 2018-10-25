(** First, RAT correctness is generalized into RAT_correct property below. 

Then, we prove the correctness of several tests to discharge the [isPivot] hypothesis...

*)

Require Export CnfSpec.
Require Export Rup.
Require Import PArith.BinPos.
Require Import Bool.

Module S := MSets.MSetPositive.PositiveSet.

(**+ A cnf datatype from cclause *)

Definition ccnf := list (clause_id*cclause).

Fixpoint csats (f: ccnf) (m: model): Prop :=
  match f with
  | nil => True
  | c::f' => csat (snd c) m /\ csats f' m 
  end.

Program Fixpoint cmkInit_r (f: ccnf) (mod: model -> Prop | forall m, mod m -> csats f m) (acc: list (wclause mod))
  : list (wclause mod) :=
  match f with
  | nil => acc
  | (cid,c)::f' =>
     cmkInit_r f' mod ({| id:=cid; rep := c |}::acc)
  end.
Obligation 1.
   simpl in * |- *. firstorder.
Qed.
Obligation 2.
   simpl in * |- *. firstorder.
Qed.

Program Definition cmkInit (f: ccnf): list (wclause (csats f)) := cmkInit_r f (csats f) nil.

Definition mkNextInput (f: ccnf): (rupLCF (wclause (csats f))) * (list (wclause (csats f))) :=
  ({| rup_learn := learn (mod:=(csats f));
      get_id := id |}, (cmkInit f)).

Fixpoint cnf_to_ccnf_rec (f: cnf) (lid: list clause_id) (acc: ccnf): ccnf :=
  match f with
  | nil => acc
  | c::f' => match lid with
             | nil => cnf_to_ccnf_rec f' nil ((default_clause_id,mkClause c)::acc)
             | id::lid' => cnf_to_ccnf_rec f' lid' ((id,mkClause c)::acc)
             end
  end.

Local Hint Resolve mkClause_correct.

Lemma cnf_to_ccnf_rec_correct (f: cnf): forall lid acc m, sats f m -> csats acc m -> csats (cnf_to_ccnf_rec f lid acc) m.
Proof.
  induction f as [ | c f']; simpl; intuition.
  destruct lid; apply IHf'; simpl; auto.
Qed.

Definition cnf_to_ccnf (f: cnf) (lid: list clause_id): ccnf :=
  cnf_to_ccnf_rec f lid [].

Lemma cnf_to_ccnf_correct (f: cnf) (lid: list clause_id): forall m, sats f m -> csats (cnf_to_ccnf f lid) m.
Proof.
  intros; apply cnf_to_ccnf_rec_correct; simpl; auto.
Qed.

Lemma csats_In f m: (forall x, List.In x f -> csat (snd x) m) -> csats f m.
Proof.
  induction f; simpl; intuition.
Qed.

Lemma csats_In_recip f m x: csats f m -> List.In x f -> csat (snd x) m.
Proof.
  induction f; simpl; intuition.
  subst; auto.
Qed.

(**+ RAT property for a bunch of clauses *)

Definition all {mod: model -> Prop} (sc: wclause mod -> Prop) (Q: cclause -> model -> Prop): Prop
  := forall c m, sc c -> mod m -> Q (rep c) m.

Definition assume (l: literal) (m: model): model :=
  fun x => if Pos.eq_dec x (ident l) then is_pos l else m x.

Definition isPivot l c1 c2 m := ~(csat c1 m) -> csat c2 (assume l m).

Definition isPivotB l (f:ccnf) c m := forall x, List.In x f -> isPivot l (snd x) c m.

Definition InB l (f:ccnf) := forall x, List.In x f -> In l (snd x).

Local Hint Resolve rep_sat csat_odef_1 csats_In.

Lemma RAT_correct l f mod (sc: wclause mod -> Prop):
 InB l f -> all sc (isPivotB l f) -> forall m, mod m -> exists m', (m'=m \/ m'=(assume l m)) /\ (csats f m') /\ forall c', sc c' -> csat (rep c') m'.
Proof.
  unfold InB, isPivotB, isPivot, all; induction f as [| x f']; simpl; intros H H0 m H1.
  - eapply ex_intro; intuition eauto.
  - exploit IHf'; clear IHf'; eauto.
    destruct 1 as (m' & H2 & H3 & H4).
    destruct (csat_dec (snd x) m').
      * constructor 1 with (x:=m'); intuition subst; auto.
      * assert (X: assume l m (ident l) = is_pos l).
        { unfold assume. case (Pos.eq_dec (ident l) (ident l)); intuition. }
        destruct H2; subst.
        { constructor 1 with (x:=assume l m). intuition eauto. }
        destruct H5; eauto.
Qed.


(** isPivot from negl_absent *)

Definition mem (l: literal) (c: cclause): bool :=
  if is_pos l then S.mem (ident l) (pos c) else S.mem (ident l) (neg c).

Lemma mem_In l c: mem l c = true -> In l c.
Proof.
  unfold mem, In. destruct (is_pos l); intuition.
Qed.

Lemma csat_negl_assume l c (m: model):
  csat c m -> mem (negl l) c = false -> csat c (assume l m).
Proof.
  unfold mem, negl; simpl; intros H1 H2; destruct H1 as [x H1].
  constructor 1 with (x:=x).
  unfold assume.
  case (Pos.eq_dec x (ident l)); simpl; auto.
  intro; subst.
  unfold S.In in * |- *.
  destruct (is_pos l); simpl in * |- *;
  try rewrite H2 in H1;
  destruct (m (ident l)); simpl in * |- *;
  intuition.
Qed.

Local Hint Resolve csat_negl_assume.

Lemma isPivotB_negl_absent l f c (m: model):
  csat c m -> mem (negl l) c = false -> isPivotB l f c m.
Proof.
  unfold isPivotB, isPivot; auto.
Qed.

Local Hint Resolve isPivotB_negl_absent.

(** isPivot from asymmetric resolution *)

Definition aresol (l:literal) (c1 c2:cclause) :=
  if is_pos l
  then
    {| pos := S.union (pos c1) (pos c2);
       neg := S.union (neg c1) (S.remove (ident l) (neg c2))
     |}
  else
    {| pos := S.union (pos c1) (S.remove (ident l) (pos c2));
       neg := S.union (neg c1) (neg c2)
     |}.

Lemma aresol_sets l l' c1 c2:
  In l' (aresol l c1 c2) -> (In l' c1) \/ ((In l' c2) /\ l' <> (negl l)).
Proof.
  unfold In, aresol, negl.
  destruct l as [b x]; destruct b; simpl;
  destruct l' as [b' x']; destruct b'; simpl;
  try rewrite S.union_spec; try rewrite S.remove_spec; intuition try congruence.
Qed.

Local Hint Resolve csat_odef_1.

Lemma isPivot_aresol l c1 c2 (m: model):
  csat (aresol l c1 c2) m -> (isPivot l c1 c2 m).
Proof.
  intros H H2; destruct (csat_odef_2 _ _ H) as (l' & H0 & H1); clear H.
  destruct (aresol_sets _ _ _ _ H0) as [H | H]; clear H0; intuition.
  - case H2; eauto.
  - eapply csat_odef_1; eauto.
    unfold assume; simpl.
    case (Pos.eq_dec (ident l') (ident l)); simpl; auto.
    destruct l'; destruct l; simpl; intros X.
    unfold In, negl in * |-; simpl in * |-; subst.
    destruct (bool_dec is_pos0 (m ident0)); auto.
    destruct H3.
    destruct is_pos0; destruct (m ident0); simpl; intuition.
Qed.

(** isPivot from trivial redundancy *)

Local Open Scope lazy_bool_scope.

Definition rem (l:literal) (c:cclause) :=
  if is_pos l
  then
    {| pos := S.remove (ident l) (pos c);
       neg := (neg c)
     |}
  else
    {| pos := pos c;
       neg := S.remove (ident l) (neg c)
     |}.

Lemma rem_In c l1 l2: In l1 (rem l2 c) -> In l1 c.
Proof.
  unfold rem, In.
  remember (is_pos l1) as ipl1.
  remember (is_pos l2) as ipl2.
  destruct ipl1, ipl2; simpl; try rewrite S.remove_spec; intuition.
Qed.

Lemma rem_In_excludes c l1 l2: In l1 (rem l2 c) -> l1 = l2 -> False.
Proof.
  intros H1 H2; subst.
  unfold rem, In in H1.
  remember (is_pos l2) as ipl2.
  destruct ipl2; simpl in H1; try rewrite S.remove_spec in H1; simpl in H1; intuition.
Qed.

Fixpoint is_disjoint (m m': S.t) : bool :=
  match m with
  | S.Leaf => true
  | S.Node l o r =>
    match m' with
    | S.Leaf => true
    | S.Node l' o' r' => 
      if (o &&& o') then false else (is_disjoint l l' &&& is_disjoint r r')
    end
  end.

Lemma is_disjoint_spec_false m: forall m', is_disjoint m m' = false -> exists e, S.In e m /\ S.In e m'.
Proof.
  unfold S.In; induction m as [ |l IHl o r IHr]; simpl; try discriminate.
  destruct m' as [|l' o' r']; simpl; try discriminate.
  intros X.
  assert (H: (o = true /\ o'=true) \/ is_disjoint l l' = false \/ is_disjoint r r'=false).
  { destruct o, o', (is_disjoint l l'), (is_disjoint r r'); simpl in X; intuition. }
  clear X; destruct H as [(H1&H2)|[H|H]].
  - subst; apply ex_intro with (x:=1%positive). intuition.
  - destruct (IHl l') as (e & H1 & H2); auto.
    apply ex_intro with (x:=(e~0)%positive). intuition.
  - destruct (IHr r') as (e & H1 & H2). intuition.
    apply ex_intro with (x:=(e~1)%positive). intuition.
Qed.

Definition not_redundant (c1 c2: cclause): bool :=
  (is_disjoint (pos c1) (neg c2)) &&& (is_disjoint (neg c1) (pos c2)).

Lemma lazy_andb_bool2 (b1 b2: bool): b1 &&& b2 = false <-> b1 = false \/ b2 = false.
Proof.
  destruct b1, b2; intuition.
Qed.

Lemma not_redundant_false_sets c1 c2:
  not_redundant c1 c2 = false -> exists l, In l c1 /\ In (negl l) c2.
Proof.
  unfold not_redundant, In, negl; simpl.
  intros H.
  apply lazy_andb_bool2 in H.
  destruct H as [H|H];destruct (is_disjoint_spec_false _ _ H) as (e & H1 & H2); clear H.
  constructor 1 with (x:={| ident:=e;is_pos:= true |}).
  intuition.
  constructor 1 with (x:={| ident:=e;is_pos:= false |}).
  intuition.
Qed.

Local Hint Resolve rem_In rem_In_excludes.

Lemma not_redundant_rem_sets l c1 c2:
  not_redundant (rem l c1) c2 = false -> exists l', l' <> l /\ In l' c1 /\ In (negl l') c2.
Proof.
  intros H; destruct (not_redundant_false_sets _ _ H) as (l' & H1 & H2); clear H.
  eapply ex_intro; intuition eauto.
Qed.

Lemma isPivot_redundant l c1 c2 m:
  not_redundant (rem l c1) c2 = false -> isPivot l c1 c2 m.
Proof.
  unfold isPivot.
  intros H; destruct (not_redundant_rem_sets _ _ _ H) as (l' & H1 & H2 & H3); clear H.
  intros H4; eapply csat_odef_1; eauto. clear H3.
  destruct l as [il xl].
  destruct l' as [il' xl'].
  unfold assume, negl, In in * |- *; simpl in * |- *.
  destruct (Pos.eq_dec xl' xl) as [H | H].
  + subst; destruct il, il'; simpl in * |- *; auto.
    destruct H1; auto.
  + clear H1 H. 
    remember (m xl') as ml'.
    destruct ml', il'; simpl; auto; destruct H4;
    apply ex_intro with (x:=xl'); rewrite <- Heqml'; simpl; auto.
Qed.


(** propagating Unit Clause before "isPivot" 

NB: below, we could generalize RUP.brc_check !

Currently, we fail on non RAT clause...

*)

Local Open Scope impure_scope.


Fixpoint propagate {mod: model -> Prop} (f: list (wclause mod)) (c: cclause): ?? (*option*) cclause :=
  match f with
  | nil => RET (*Some*) c
  | c'::f' =>
    let c0 := diff (rep c') c in
    DO b <~ cpcard c0 ;;
    if b then 
      propagate f' (union c (swap c0))
    else
      FAILWITH "propagate: found a RUP clause !"
      (* RET None *) 
 end.

Lemma union_In1 c1 c2 l: In l c1 -> In l (union c1 c2).
Proof.
  unfold union, In.
  simpl.
  destruct (is_pos l) ; intros ; apply MSetPositive.PositiveSet.union_spec ; eauto.
Qed.

Local Hint Resolve union_In1.

Local Hint Resolve cpcard_correct: wlp.
Local Hint Resolve diff_csat rep_sat f_equal csat_double_neg.
Local Ltac mysimpl := simpl in * |- *; wlp_simplify; subst; congruence || eauto.

Lemma propagate_correct_aux mod (f:list (wclause mod)): 
  forall c, WHEN propagate f c ~> c' THEN forall m, mod m -> ~(csat c m) -> ~(csat c' m).
Proof.
  induction f as [| c' f' IHf']; mysimpl.
  eapply H0; eauto.
  eapply union_ncsat; eauto.
Qed.
Global Opaque propagate.


Section PropagateCorrect.

Local Hint Resolve propagate_correct_aux: wlp.

Lemma propagate_correct mod (f:list (wclause mod)): 
  forall c, WHEN propagate f c ~> c' THEN forall m l c2, mod m -> isPivot l c' c2 m-> isPivot l c c2 m.
Proof.
  unfold isPivot; mysimpl.
Qed.

End PropagateCorrect.
Local Hint Resolve propagate_correct: wlp.




(**+ RatInput *)

(** a single RAT clause to learn *)
Record RatSingle {C}: Type := {
   new_id: clause_id; (* id of the clause to learn *)
   clause_to_learn: cclause;
   propagate_list: list C;
   rup_proofs: list (list C)
}.
Arguments RatSingle: clear implicits.

(** a bunch of RAT clause to learn *)
Record RatInput {C} : Type :=
  {
    pivot: literal;
    remainder: list C;
    basis: list C;
    bunch: list (RatSingle C);
  }.
Arguments RatInput: clear implicits.

(** check remainder *)

Definition remainder_msg :string := "Rat.check_remainder".

Fixpoint check_remainder (l:literal) {mod: model -> Prop} (f:list (wclause mod)): ?? unit :=
  match f with
  | nil => RET tt
  | c::f' => if mem l (rep c) then FAILWITH remainder_msg else check_remainder l f'
  end.

Lemma check_remainder_correct (l:literal) (f1: ccnf) (mod: model -> Prop) (f2:list (wclause mod)):
  WHEN check_remainder (negl l) f2 ~> _ THEN all (fun c => List.In c f2) (isPivotB l f1).
Proof.
  unfold all.
  induction f2; mysimpl.
Qed.

Global Opaque check_remainder.
Local Hint Resolve check_remainder_correct: wlp.

(**+ Check one single rat clause *)

Definition rat_msg1 :string := "Cannot prove Rat !".

Program Definition rat_check_one (l:literal) (c1: cclause) {mod: model -> Prop}  (c2: wclause mod) (brc: list (wclause mod)) : ?? forall m, mod m -> isPivot l c1 (rep c2) m :=
  match brc with
  | nil => match (not_redundant (rem l c1) (rep c2)) with
           | true => FAILWITH rat_msg1
           | false => RET _
           end
  | _ => mk_annot (brc_check brc (aresol l c1 (rep c2)));; RET _
  end.
Obligation 1.
  apply isPivot_redundant; auto.
Qed.
Obligation 2.
  eapply isPivot_aresol.
  eapply brc_check_correct; eauto.
Qed.

Definition rat_msg2 :string := "Rat_check: expect some proof for some basis".

Fixpoint rat_check_prf (l:literal) (c1: cclause) {mod: model -> Prop}  (basis: list (wclause mod)) (proofs: list (list (wclause mod))) {struct basis}: ?? unit :=
  match basis, proofs with
  | nil, _ => RET tt
  | _, nil => FAILWITH rat_msg2
  | c2::b',brc::p' =>
     rat_check_one l c1 c2 brc;;
     rat_check_prf l c1 b' p'
  end.

Lemma rat_check_prf_correct l c1 mod b: forall p, WHEN rat_check_prf l c1 (mod:=mod) b p ~> _ THEN forall m x, List.In x b -> mod m -> isPivot l c1 (rep x) m.
Proof.
  induction b as [| c2 b' IHb']; destruct p as [| brc p']; mysimpl.
Qed.
Global Opaque rat_check_prf.
Local Hint Resolve rat_check_prf_correct: wlp.

Definition rat_check {mod: model -> Prop} l b (rs: RatSingle (wclause mod)): ?? unit :=
  let c1:=(clause_to_learn rs) in
  assert_b (mem l c1) "pivot is not in RAT clause to learn";;
  DO c1' <~ propagate (propagate_list rs) c1;;
  rat_check_prf l c1' b (rup_proofs rs).

Local Hint Resolve mem_In.

Lemma rat_check_correct mod l b rs: WHEN rat_check (mod:=mod) l b rs ~> _ THEN In l (clause_to_learn rs) /\ forall m c, List.In c b -> mod m -> isPivot l (clause_to_learn rs) (rep c) m.
Proof.
  mysimpl. 
Qed.
Global Opaque rat_check.
Local Hint Resolve rat_check_correct: wlp.

Fixpoint rat_checkB {mod: model -> Prop} l b (bunch: list (RatSingle (wclause mod))): ?? unit :=
  match bunch with
  | nil => RET tt
  | rs::bunch' => rat_check l b rs;;rat_checkB l b bunch'
  end.

Lemma rat_checkB_correct mod l b bunch: WHEN rat_checkB (mod:=mod) l b bunch ~> _ THEN forall rs, List.In rs bunch -> In l (clause_to_learn rs) /\ forall m c, List.In c b -> mod m -> isPivot l (clause_to_learn rs) (rep c) m.
Proof.
  induction bunch as [|rs bunch']; mysimpl.
  - exploit H; intuition eauto.
  - exploit H; intuition eauto.
Qed.
Global Opaque rat_checkB.
Local Hint Resolve rat_checkB_correct: wlp.

 
(** Recovering the implicit CNF from RatInput *)

Fixpoint rev_app_map {A B} (f: A -> B) (l: list A) (acc: list B): list B :=
  match l with
  | nil => acc
  | x::l' => rev_app_map f l' ((f x)::acc)
  end.

Lemma rev_app_In A B (f: A -> B) (l: list A):
  forall acc y, List.In y (rev_app_map f l acc) <-> (List.In y acc \/ (exists x, y=(f x) /\ List.In x l)). 
Proof.
  induction l; simpl in * |- *.
  - firstorder.
  - intros acc y; rewrite IHl. clear IHl. simpl in * |- *; firstorder (subst; eauto).
Qed.

Definition ccnf_to_learn {mod: model -> Prop} (R: RatInput (wclause mod)): ccnf :=
  rev_app_map  (fun rs => (new_id rs, clause_to_learn rs)) (bunch R) nil.

Lemma ccnf_from_bunch mod (R: RatInput (wclause mod)):
  forall c, List.In c (ccnf_to_learn R) <-> (exists rs, c=(new_id rs, clause_to_learn rs) /\ List.In rs (bunch R)).
Proof.
  intros; unfold ccnf_to_learn; rewrite rev_app_In. simpl. intuition.
Qed. 


Definition sc_RatInput {mod} (R: RatInput (wclause mod)) (c: wclause mod): Prop 
  := List.In c (remainder R) \/ List.In c (basis R).

Definition all_RatInput {mod} (R: RatInput (wclause mod)) (Q: wclause mod -> Prop) := 
  (forall c, List.In c (remainder R) -> Q c) /\ (forall c, List.In c (basis R) -> Q c).

Lemma all_sc_RatInput mod (R: RatInput (wclause mod)) (Q: wclause mod -> Prop):
  all_RatInput R Q <-> (forall c, (sc_RatInput R c) -> Q c).
Proof.
  unfold sc_RatInput, all_RatInput; firstorder (subst; auto).
Qed.

Lemma all_RatInput_all mod (R: RatInput (wclause mod)) (Q: cclause -> model -> Prop):
  all (sc_RatInput R) Q <-> all_RatInput R (fun c => forall m, mod m -> Q (rep c) m).
Proof.
  rewrite all_sc_RatInput. unfold all; intuition.
Qed.


Definition id_rep {mod} (c: (wclause mod)): clause_id*cclause := (id c, rep c).

Definition ccnf_from_RatInput {mod} (R: RatInput (wclause mod)): ccnf :=
  rev_app_map id_rep (remainder R) (rev_app_map id_rep (basis R) (ccnf_to_learn R)).

Lemma ccnf_from_RatInput_correct mod (R: RatInput (wclause mod)) m:
   (all_RatInput R (fun c => csat (rep c) m)) -> (csats (ccnf_to_learn R) m) -> (csats (ccnf_from_RatInput R) m).
Proof.
  unfold ccnf_from_RatInput, all_RatInput, id_rep.
  intros (H1 & H2) X; apply csats_In.
  intros x H; rewrite! rev_app_In in H; simpl in H.
  destruct H as [ [ Y | (x0 & H3 & H4) ] | (x0 & H3 & H4) ]; subst; simpl; auto.
  eapply csats_In_recip; eauto.
Qed.

Theorem RatInput_correct mod (R: RatInput (wclause mod)):
  InB (pivot R) (ccnf_to_learn R) -> 
  all_RatInput R (fun c => forall m, mod m -> isPivotB (pivot R) (ccnf_to_learn R) (rep c) m) -> 
  forall m, mod m -> exists m', csats (ccnf_from_RatInput R) m'.
Proof.
  rewrite <- all_RatInput_all.
  intros; exploit RAT_correct; eauto.
  destruct 1 as (m' & X1 & X2 & X3); clear X1.
  eapply ex_intro; intuition eauto.
  apply ccnf_from_RatInput_correct.
  rewrite all_sc_RatInput; auto.
  auto.
Qed.

(** learnRat *)

Definition learnRat {mod: model -> Prop} (R: RatInput (wclause mod)): ?? ccnf :=
  let l:=(pivot R) in
  check_remainder (negl l) (remainder R);;
  rat_checkB l (basis R) (bunch R);;
  RET (ccnf_from_RatInput R).

Local Hint Resolve RatInput_correct.

Lemma learnRat_correct (mod: model -> Prop) (R: RatInput (wclause mod)):
  WHEN learnRat R ~> f THEN forall m, mod m -> exists m', csats f m'.
Proof.
  wlp_simplify.
  eapply RatInput_correct; eauto.
  - unfold InB; intros c H2. rewrite ccnf_from_bunch in H2. destruct H2 as (rs & H3 & H4); subst; simpl. exploit H0; intuition eauto.
  - unfold all_RatInput, all, isPivotB in * |- *. intuition eauto.
    rewrite ccnf_from_bunch in H4. destruct H4 as (rs & H5 & H6); subst; simpl.
    exploit H0; intuition eauto.
Qed.

Global Opaque learnRat.
Global Hint Resolve learnRat_correct: wlp.