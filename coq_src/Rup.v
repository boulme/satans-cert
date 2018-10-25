(* Verification RUP clauses using backward resolution chains *)

Require Export SolverInterface.
Require Import SatProver.
Require Import MSets.MSetPositive.
Import PositiveSet.
Require Export CnfSpec.
Require Import Bool.
Require Import PArith.BinPos.

Local Open Scope positive.
Local Open Scope list_scope.

Coercion Is_true: bool >-> Sortclass.
Local Open Scope lazy_bool_scope.

Fixpoint sat_bool (c: clause) (m: model): bool := 
  match c with
  | nil => false
  | l::c' => eqb (m (ident l)) (is_pos l) ||| sat_bool c' m
  end.

Lemma sat_bool_spec c m: if (sat_bool c m) then (sat c m) else ~(sat c m).
Proof.
  induction c; simpl. 
  + intuition.
  + generalize (eqb_true_iff (m (ident a)) (is_pos a)); destruct (eqb (m (ident a)) (is_pos a)); [ tauto |].
    intros; destruct (sat_bool c m); intuition.
Qed.

Record cclause : Type :=
  { pos: PositiveSet.t ; neg: PositiveSet.t }.

Definition csat (c: cclause) (m: model): Prop :=
  exists x, if (m x) then In x (pos c) else In x (neg c).

Definition empty := {| pos:=empty ; neg:=empty |}.

Lemma empty_correct m: ~(csat empty m).
Proof.
  unfold not, csat, empty; simpl.
  destruct 1 as [x H].
  destruct (m x); eapply empty_spec; eauto.
Qed.

Definition isEmpty (c: cclause): bool :=
  is_empty (pos c) &&& is_empty (neg c).

Lemma isEmpty_correct c: isEmpty c = true -> forall m, ~csat c m.
Proof.
  unfold isEmpty, csat; simpl.
  rewrite lazy_andb_bool.
  rewrite !is_empty_spec.
  unfold Empty.
  intros H m. destruct 1 as [x H2].
  destruct (m x); intuition eauto.
Qed.


Definition add (l:literal) (c: cclause): cclause :=
  if is_pos l then
    {| pos:=add (ident l) (pos c) ; neg := neg  c|}
  else
    {| pos:= pos c ; neg := add (ident l) (neg c) |}.

Lemma add_correct_1 l c m:
   csat c m -> csat (add l c) m.
Proof.
  unfold csat, add; simpl.
  destruct 1 as [x H].
  constructor 1 with (x:=x).
  destruct (is_pos l); destruct (m x); simpl; try rewrite add_spec; intuition.
Qed.

Lemma add_correct_2 l c m:
   (m (ident l))=(is_pos l) -> csat (add l c) m.
Proof.
  unfold csat, add; intro H; rewrite <- H.
  constructor 1 with (x:=ident l).
  destruct (m (ident l)); simpl; try rewrite add_spec; intuition.
Qed.

Definition top: cclause :=
  add {| is_pos:= true; ident := xH |} (add {| is_pos:= false; ident := xH |} empty).

Local Hint Resolve add_correct_1 add_correct_2.

Lemma top_correct m: csat top m.
Proof.
  unfold top; assert (H: exists b, m xH = b); try eauto.
  destruct H as [b H]; destruct b; eauto.
Qed.

Fixpoint mkClauseRec (c: clause) (acc: cclause): cclause :=
  match c with
  | nil => acc
  | l::c' => mkClauseRec c' (add l acc)
  end.


Lemma mkClauseRec_correct c:
  forall acc m, sat c m \/ csat acc m -> csat (mkClauseRec c acc) m.
Proof.
  unfold sat; induction c; simpl; intuition auto.
Qed.

Definition mkClause c := mkClauseRec c empty.

Lemma mkClause_correct c m: sat c m -> csat (mkClause c) m.
Proof.
  intros; apply mkClauseRec_correct; intuition.
Qed.

Local Hint Resolve mkClause_correct.

Lemma sat_odef_1 l c (m: model):
  m (ident l) = is_pos l -> List.In l c -> sat c m.
Proof.
  intro H; induction c; simpl; intuition (subst; auto).
Qed.

Local Hint Resolve sat_odef_1.

Lemma sat_odef_2 c m: 
  sat c m -> exists l, List.In l c /\ m (ident l) = is_pos l.
Proof.
  intro H; induction c; simpl in * |-; intuition.
  + eapply ex_intro; intuition (simpl; eauto).
  + destruct H as [l [H H1]]; eapply ex_intro; intuition (simpl; eauto).
Qed.

Definition In (l: literal) (c: cclause): Prop :=
  if is_pos l then In (ident l) (pos c) else In (ident l) (neg c).

Lemma csat_odef_1 l c (m: model):
  m (ident l) = is_pos l -> In l c -> csat c m.
Proof.
  intro H; unfold In; rewrite <- H.
  intros; constructor 1 with (x:=ident l); auto.
Qed.

Local Hint Resolve csat_odef_1.

Lemma csat_odef_2 c m: 
  csat c m -> exists l, In l c /\ m (ident l) = is_pos l.
Proof.
  intro H; destruct H as [x H].
  unfold In.
  constructor 1 with (x:={| ident := x; is_pos := m x |}). simpl.
  intuition.
Qed.

Lemma not_csat c m: csat c m -> (forall l, ~In l c) -> False.
Proof.
  intros H H0.
  destruct (csat_odef_2 c m H) as [l H1].
  firstorder.
Qed.

Definition xsClause b s := List.map (fun x => {| is_pos := b; ident := x |}) (elements s).

Definition xClause c := (xsClause true (pos c)) ++ (xsClause false (neg c)).

Require Import SetoidList.

Lemma xClause_correct_In_1 c l: In l c -> List.In l (xClause c).
Proof.
  unfold xClause. intros H.
  apply List.in_or_app.
  unfold xsClause. unfold In in H.
  destruct l as [b x]; simpl in * |-.
  destruct b; (
  rewrite <- elements_spec1 in H;
  rewrite InA_alt in H;
  destruct H as [y [H H0]]; rewrite <- H in H0; clear y H); 
  [ constructor 1 | constructor 2 ]; apply List.in_map; auto.
Qed.

Local Hint Resolve E.eq_equiv.

Lemma xClause_correct_In_2 c l: List.In l (xClause c) -> In l c.
Proof.
  unfold xClause, xsClause. intros H.
  destruct (List.in_app_or _ _ _ H) as [H0 | H0]; clear H;
  rewrite in_map_iff in H0;
  destruct H0 as [x [H1 H2]]; unfold In; subst; simpl;
  rewrite <- elements_spec1;
  apply In_InA; auto.
Qed.
Local Hint Resolve xClause_correct_In_2 xClause_correct_In_1.

Lemma csat_dec: forall c m, (csat c m) \/ ~(csat c m).
Proof.
  intros c m; generalize (sat_bool_spec (xClause c) m).
  destruct (sat_bool (xClause c) m).
  + constructor 1. 
   destruct (sat_odef_2 _ _ H) as [l [H1 H2]]. 
    eauto.
  + constructor 2. 
    intro X.
    destruct (csat_odef_2 _ _ X) as [l [X1 X2]]. 
    intuition eauto.
Qed.

Local Open Scope impure_scope.

(* computes the "pseudo-cardinal" of a set
  - return false, if the set is empty
  - return true, if the set has one elementUnsatProverLib.v
  - fails, otherwise.

NB: the set is assumed to be canonical (all empty subtrees are only Leaf nodes).
*)

Definition pcard_msg : pstring := "Rup.pcard".

Fixpoint pcard (s: PositiveSet.t): ?? bool :=
 match s with
 | Leaf => RET false
 | Node Leaf true Leaf => RET true
 | Node Leaf false r => pcard r
 | Node l false Leaf => pcard l
 | _ => FAILWITH pcard_msg
 end.

Local Ltac mysimpl := simpl in * |- *; wlp_simplify; subst; congruence || eauto.
Local Hint Resolve f_equal.

Lemma pcard_correct s: WHEN pcard s ~> b THEN 
   if b then 
      exists x, PositiveSet.In x s /\ forall x', PositiveSet.In x' s -> x' = x 
   else 
      forall x, ~PositiveSet.In x s.
Proof.
  unfold PositiveSet.In; induction s as [| l Hl b r Hr].
  - mysimpl.
  - generalize Hl, Hr; clear Hl Hr.
    refine (match l, b, r with
            | Leaf, true, Leaf => _
            | Leaf, false, r' => _
            | l', false, Leaf => _
            | _, _, _ => _
            end); mysimpl.
  + constructor 1 with (x:=1); intuition.
    destruct x'; congruence || auto.
  + destruct exta.
    * destruct H as [x H].
      constructor 1 with (x:=x~1); intuition.
      destruct x'; congruence || auto.
    * destruct x; congruence.
  + destruct exta.
    * destruct H as [x H].
      constructor 1 with (x:=x~0); intuition.
      destruct x'; congruence || auto.
    * destruct x; congruence || eauto.
Qed.
Global Opaque pcard.
Local Hint Resolve pcard_correct: wlp.

Definition cpcard_msg : string := "Rup.cpcard".

Definition cpcard (c: cclause): ?? bool :=
  DO p <~ pcard (pos c);;
  DO n <~ pcard (neg c);;
  match p, n with
  | false, false => RET false
  | true, true => FAILWITH cpcard_msg
  | _, _ => RET true
  end.

Lemma cpcard_correct_aux c: WHEN cpcard c ~> b THEN 
   if b then exists l, In l c /\ forall l', In l' c -> l' = l 
        else forall m, ~csat c m.
Proof.
  unfold In, cpcard; wlp_simplify.
  * destruct H as [x H].
    constructor 1 with (x:={| is_pos:=true; ident:= x|}); simpl.
    intuition.
    destruct l' as [ b l']; simpl in * |- *. destruct b; firstorder.
  * destruct H0 as [x H0].
    constructor 1 with (x:={| is_pos:=false; ident:= x|}); simpl.
    intuition.
    destruct l' as [ b l']; simpl in * |- *. destruct b; firstorder.
  * eapply not_csat; eauto.
    unfold In. intro l; destruct (is_pos l); firstorder.
Qed.
Global Opaque cpcard.

Definition swap c := 
   {| pos := neg c; neg := pos c |}.

Extraction Inline swap.

Definition negl (l: literal): literal :=
  {| is_pos := negb (is_pos l); ident := ident l |}.

Lemma cpcard_swap0 c l l': In l c -> In l' (swap c) ->
   WHEN cpcard c ~> b THEN b = true -> negl l' = l.
Proof.
  intros; generalize (cpcard_correct_aux c); mysimpl.
  destruct H2 as [l0 H2]. intuition.
  assert (X: l=l0). auto. subst.
  apply H4.
  clear H4 H3 H1; unfold swap, negl, In in * |- *.
  simpl in * |- *.
  destruct (is_pos l'); auto.
Qed.

Lemma cpcard_correct c: WHEN cpcard c ~> b THEN 
  if b then 
     forall m, (csat c m) -> ~(csat (swap c) m) 
  else 
     forall m, ~(csat c m).
Proof.
  intros b; destruct b; intro H1. 
  + intros m H; destruct (csat_odef_2 _ _ H) as [l H0]; clear H. destruct H0 as [H H0]. 
  intro H'. destruct (csat_odef_2 _ _ H') as [l' H2]; clear H'.
  destruct H2 as [H3 H4].
  destruct (cpcard_swap0 _ _ _ H H3 _ H1); intuition.
  unfold negl in * |-; subst. simpl in * |-.
  rewrite H0 in H4. destruct (is_pos l'); simpl in * |-; discriminate.
 + intros m H; destruct (cpcard_correct_aux _ _ H1 m). auto.
Qed.

Local Hint Resolve cpcard_correct: wlp.

Definition diff c1 c2 := 
    {| pos := diff (pos c1) (pos c2);
       neg := diff (neg c1) (neg c2)
     |}.

Lemma diff_In c1 c2 l: In l c1 -> ~(In l c2) -> In l (diff c1 c2).
Proof.
  unfold diff, In.
  destruct (is_pos l); simpl; try rewrite diff_spec; auto.
Qed.

Lemma diff_csat c1 c2 m: csat c1 m -> ~(csat c2 m) -> csat (diff c1 c2) m.
Proof.
  intros H1 H2; destruct (csat_odef_2 c1 m H1) as [l H]. intuition.
  eapply csat_odef_1; eauto.
  eapply diff_In; eauto.
Qed.

Definition union c1 c2 :=
    {| pos := union (pos c1) (pos c2);
       neg := union (neg c1) (neg c2)
     |}.

Lemma union_In c1 c2 l: In l (union c1 c2) -> In l c1 \/ In l c2.
Proof.
  unfold union, In.
  destruct (is_pos l); simpl; try rewrite union_spec; intuition.
Qed.

Lemma union_ncsat c1 c2 m: ~(csat c1 m) -> ~(csat c2 m) -> ~(csat (union c1 c2) m).
Proof.
  intros H1 H2 H3; destruct (csat_odef_2 _ _ H3) as [l H]; clear H3. 
  generalize (union_In c1 c2 l); intuition eauto.
Qed.

Local Open Scope list_scope.

(* implementation of "witness" clauses *) 

Record wclause {mod: model -> Prop}: Type := {
  id: clause_id;
  rep: cclause ;
  rep_sat: forall m, mod m -> csat rep m
}.
Arguments wclause: clear implicits.

Definition rup_msg :string := "Rup.rup_checker".

(* checking of "Backward Resolution Chains" *)
Fixpoint brc_check {mod: model -> Prop} (f: list (wclause mod)) (c: cclause): ?? unit :=
  match f with
  | nil => FAILWITH "Rup.rup_checker"
  | c'::f' =>
    let c0 := diff (rep c') c in
    DO b <~ cpcard c0 ;;
    if b then 
      brc_check f' (union c (swap c0))
    else
      RET tt
 end.

Local Hint Resolve diff_csat rep_sat.

Lemma brc_check_correct_aux mod (f:list (wclause mod)) m: forall c, mod m -> WHEN brc_check f c ~> _ THEN ~~(csat c m).
Proof.
  induction f as [| c' f' IHf']; mysimpl. 
  apply H1.
  eapply union_ncsat; eauto.
Qed.
Global Opaque brc_check.


Section brc_check_correct.

Local Hint Resolve brc_check_correct_aux: wlp.

Lemma csat_double_neg c m: ~~(csat c m) -> csat c m.
Proof.
  case (csat_dec c m); intuition.
Qed.

Local Hint Resolve csat_double_neg.

Lemma brc_check_correct mod (f:list (wclause mod)) c m: mod m -> WHEN brc_check f c ~> _ THEN csat c m.
Proof.
  mysimpl.
Qed.

End brc_check_correct.

(* rup learning *)
Program Definition learn {mod: model -> Prop} (f: list (wclause mod)) (cid: clause_id) (c: cclause) : ?? wclause mod 
 := mk_annot (brc_check f c);; RET {| id:= cid; rep := c |}.
Obligation 1.
  eapply brc_check_correct; eauto.
Qed.


Record rupLCF {C} := { 
  rup_learn: (list C) -> clause_id -> cclause -> ?? C;
  get_id: C -> clause_id
}.
Arguments rupLCF: clear implicits.

(*
(* This part was used for a RUP-only checker. This needs to be generalized for the RAT-checker *)
Definition destruct_lid (lid: list clause_id) : clause_id * list clause_id :=
  match lid with
  | nil => (default_clause_id, nil)
  | cid::lid' => (cid, lid')
  end.

(* initial list of wclauses *)
Program Fixpoint mkInit_r (f: cnf) (lid: list clause_id) (mod: model -> Prop | forall m, mod m -> sats f m) (acc: list (wclause mod))
  : list (wclause mod) :=
  match f with
  | nil => acc
  | c::f' =>
     let (cid, lid') := destruct_lid lid in
     mkInit_r f' lid' mod ({| id:=cid; rep := mkClause c |}::acc)
  end.
Obligation 1.
   simpl in * |- *. firstorder.
Qed.
Obligation 2.
  simpl in * |- *. firstorder.
Qed.

Program Definition mkInit (f: cnf) (lid: list clause_id): list (wclause (sats f)) := mkInit_r f lid (sats f) nil.
Global Opaque mkInit_obligation_1.

Local Hint Resolve rep_sat.
Global Opaque rep_sat.

(* input for the solver *)
Definition mkInput (f: cnf) (lid: list clause_id): (rupLCF (wclause (sats f))) * (list (wclause (sats f))) :=
  ({| rup_learn := learn (mod:=(sats f));
      get_id := id |}, (mkInit f lid)).

Lemma certifies_unsat (f : cnf) (c: wclause (sats f)): isEmpty (rep c) = true -> isUnsat f.
Proof.
  intros; apply isUnsat_proof; generalize (isEmpty_correct (rep c)). intuition eauto.
Qed.
*)

