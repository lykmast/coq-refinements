From Equations Require Import Equations.
Set Universe Polymorphism.
Set Equations Transparent.
Require Import Lia.
Require Import ArithRing.

Require Import LibTactics.

Require Import Coq.Logic.ProofIrrelevance.

Require Import Coq.Program.Subset.

Require Import ZArith.
Open Scope Z_scope.
Lemma minus_id : forall m,  (m + 1) - 1 = m. lia. Qed.
(* Lemma succ_plus : forall m, m = m + 1. lia. Qed. *)
(* Lemma plus_rewrite : forall m n,  m + S n = S m + n /\ m  + 0 = m. lia. Qed. *)
Lemma plus_minus : forall m n, m + n - n = m. lia. Qed.
Lemma gt_ge : forall m n, m > n -> m >= n + 1. lia. Qed.
Lemma gt_ge3 : forall m n, m > n - 1 -> m >= n. lia. Qed.

Lemma ge_gt : forall m n, m >= n + 1 <-> m > n.  lia. Qed.
Lemma gt_ge2 : forall m n, m > n -> m >=n. lia. Qed.
Lemma gt_ge_gt: forall m n p, m > n -> n >= p -> m > p. lia. Qed.
Lemma gt_gt_gt: forall m n p, m > n -> n > p -> m > p. lia. Qed.
Lemma ge_ge_ge: forall m n p, m >= n -> n >= p -> m >= p. lia. Qed.
Lemma gt_plus : forall m n p, m > n -> m + p > n + p. lia. Qed.


Opaque Z.add. Opaque Z.mul.
Lemma split_zero_pos m: m>= 0 -> m = 0 \/ m > 0. lia. Qed.
(* Lemma pos_is_suc m : m > 0 -> exists n, S n = m. intro. inversion H; eauto. Qed. *)

Ltac math_rewrites :=
  try rewrite plus_minus;
  try rewrite minus_id.
  (* try rewrite <- succ_plus. *)
Ltac other_math_rewrites :=
  try rewrite plus_minus;
  try rewrite minus_id.
  (* try rewrite succ_plus. *)


  (* Definition lt_n (nn:{n:Z | n >= 0}) (mm:{m:Z | m >= 0}) :Prop  := Z.lt (proj1_sig nn) (proj1_sig mm).
Lemma Z_lt_wf: WellFounded lt_n.
Proof. do 2 red. *)


(* Ltac pos_rewrite := match goal with | H: ?n > 0 |- _ => case (pos_is_suc n H); intros ? <-; clear H end. *)
Ltac before_simp := try math_rewrites. (* ; try repeat pos_rewrite. *)
Ltac ple_old := simpl; math_rewrites.
Ltac smt_trivial_old := ple_old; solve [ assumption | ring_simplify; intuition | intuition | intuition discriminate | easy | lia | nia].
Tactic Notation "ple" ident(f) := repeat (before_simp; simp f).


Tactic Notation "smt_trivial" ident(f) := ple f; smt_trivial_old. (* first [ assumption | intuition discriminate | easy | lia | nia]. *)
Ltac smt_app th := first [ rewrite th | ple_old; rewrite th | apply th | ple_old; apply th | applys_eq th]; try smt_trivial_old.
Ltac smt_solve th := solve [ now rewrite th | now ple_old; rewrite th | now apply th | now ple_old; apply th].

(* Lemma trans_gt_ge:  *)
Ltac Zify.zify_post_hook ::=
  (* try rewrite succ_plus; *)
  try rewrite plus_minus.

Ltac lex_resolve := first [left; try split; lia | right; try split; lia].
Ltac termination_resolve := first [lia | lex_resolve].
(* Equations ack (p: nat*nat) : nat by wf p (lexprod _ _ lt lt) :=
ack (0,n) => n + 1;
ack (S m,0) => ack ((m),1);
ack (S m,S n) => ack ((m), (ack (S m, (n)))).
Print ack. *)
Check WellFounded.
Print WellFounded.
Require Import Coq.ZArith.Zwf.
Require Import Coq.ZArith.ZArith.
(* Require Import Coq.ZArith.Wf_Z. *)
Check Zwf_well_founded.
Print well_founded.
Check Z.lt.
(* Axiom Zwf__ :well_founded Z.lt. *)
#[local]
Instance wf_total_init_compute :  forall c, WellFounded (@Zwf c).
  exact (Zwf_well_founded).
Defined.
From Coq Require Import Program.Wf.
(* Require Import Bool. *)
Search (Z -> Z -> bool).
Require Import Program.Utils. (* for 'dec' *)


Lemma zwf_0_pred n: n - 1 >=? 0 = true -> Zwf 0 (n - 1) n.
unfold Zwf; split; lia. Qed.
Lemma geb_ge n m: Z.geb n m = true -> n >= m. lia. Qed.
(* Program Fixpoint fact (n:Z) {n_nat:n >= 0}  {wf (Zwf 0) n }: Z  :=
  if dec (Z.geb (n-1) 0) then ltac:(refine(n* fact (n-1) _ _); unfold Zwf; lia ) else 1. *)

  Equations? fact' (n:Z) {n_nat:n >= 0}  : Z by wf n (Zwf 0) :=
  fact' n := if dec (Z.eqb n 0) then 1
            else  fact' (n-1).
Proof. lia. unfold Zwf. lia. Qed.
(* Axiom Zpos :forall z:Z, z >= 0. *)
(* Equations? ack (m n:Z) {m_nat:0 <= m} {n_nat:n >= 0}  : Z by wf (m,n) (lexprod Z Z (Zwf 0) (Zwf 0)) :=
ack m n :=
  if dec (Z.eqb m 0) then n+1 else
  if dec (Z.eqb n 0) then ack (m-1) 1
  else ack (m-1) (ack m (n-1)).
Proof.  all:try termination_resolve. apply Zpos. Defined.
Check Z_lt_induction.
Check nat_ind. *)



Definition natZ := {n:Z| 0 <= n}.

Notation "x <| y"  := (proj1_sig x < proj1_sig y) (at level 70).
Notation "x |= y"  := (proj1_sig x = proj1_sig y) (at level 70).

Notation "x |> y"  := (proj1_sig (x:natZ) > proj1_sig (y:natZ)) (at level 70).
Notation "x |>= y"  := (proj1_sig (x:natZ) >= proj1_sig (y:natZ)) (at level 70).

Definition mkNatZ n {H:0 <= n} := exist _ n H:natZ.

Definition times (m n: natZ):natZ.
refine (exist _ (proj1_sig m * proj1_sig n) _).
destruct m; destruct n; simpl; lia.
Defined.


Definition plus (m n:natZ): natZ.
refine (match m with exist _ mval mnat =>
match n with exist _ nval nnat => exist _ (mval + nval) _ end end).
lia.
Defined.

Lemma plus_val (m n: natZ): proj1_sig (plus m n) = proj1_sig m + proj1_sig n.
Proof. destruct m, n; simpl; lia. Qed.


Notation "x |* y" := (times x y) (at level 40, left associativity).
Notation "x |+ y" := (plus x y) (at level 50, left associativity).
Notation "` x" := (proj1_sig x) (at level 10).
Notation "`` x" := (ltac:(refine(mkNatZ x);lia)) (at level 10).

Lemma times_val (m n:natZ): proj1_sig (m |* n) = proj1_sig m * proj1_sig n.
destruct m; destruct n; simpl; lia. Qed.


Definition ref_wf (m n:natZ) := (Zwf 0) (proj1_sig m) (proj1_sig n).

Lemma ref_wf_well_founded: well_founded (ref_wf).
Proof. red; intros.
enough (well_founded (Zwf 0)).

unfold ref_wf.
apply Inverse_Image.Acc_inverse_image. apply H.

apply Zwf_well_founded.
Qed.

#[local] Instance ref_wf_WF : WellFounded ref_wf.
apply ref_wf_well_founded. Qed.
Lemma eq0 {n}: n =? 0 = true -> n = 0. lia. Qed.

#[local] Instance whatever: WellFounded
(Telescopes.tele_measure
   (Telescopes.ext natZ (fun _ : natZ => Telescopes.tip natZ))
   (natZ * natZ) (fun m n : natZ => (m, n))
   (lexprod natZ natZ ref_wf ref_wf)).
    repeat red; intros;
    unfold Telescopes.tele_measure;
    (* constructor. *)
    apply Inverse_Image.Acc_inverse_image;  apply acc_A_B_lexprod; apply ref_wf_WF.
Qed.

Equations ack (m n:natZ)  : natZ by wf (m,n) (lexprod natZ natZ  ref_wf ref_wf) :=
ack m' n' :=
  match m' as m_ref return m' = m_ref -> natZ with exist _ m m_nat =>
    fun (e: m' = exist _ m m_nat) =>
  match n' as n_ref return n' = n_ref -> natZ with exist _ n n_nat =>
    fun (e: n' = exist _ n n_nat) =>
    if dec (Z.eqb m 0) then ``(n+1) else
  if dec (Z.eqb n 0) then ack (``(m-1)) (``1)
  else ack (``(m-1)) (ack m' (``(n-1) )) end eq_refl end eq_refl.

Ltac obl_tac := try (left + right; constructor; simpl); lia.

Next Obligation. obl_tac. Qed.
Next Obligation. obl_tac. Qed.
Next Obligation. obl_tac. Qed.
Print ack_elim.

Section natZ_lt_ind_principle.
  Variable P : natZ -> Prop.

  Hypothesis ind_n : forall n, (forall k, k <| n -> P k) -> P n.

  Theorem natZ_lt_ind (n: natZ) : P n.
    (* enough (H0: forall p, p <= n -> P p).
    - apply H0, le_n. *)
    case n; intros n_val n_ref. generalize n_ref. pattern n_val. apply Z_lt_induction.
    + intros; apply ind_n; intros; destruct k.  simpl in *. apply H. lia.
    + assumption.
  Qed.
End natZ_lt_ind_principle.


Section natZ_ltB_ind_principle.
  Variable P : natZ -> Prop.
  Variable B : natZ.
  Hypothesis ind_n : forall n, (forall k, k |> B -> k <| n -> P k) -> P n.

  Theorem natZ_ltB_ind (n: natZ) : P n.
    (* enough (H0: forall p, p <= n -> P p).
    - apply H0, le_n. *)
    induction n as [n IHn] using natZ_lt_ind. apply ind_n. intros. apply IHn. trivial.
  Qed.
End natZ_ltB_ind_principle.

Definition natZ0: natZ. refine (exist _ 0 _). lia. Defined.



Lemma ge_le {m n}: n <= m -> m >= n. lia. Qed.
Lemma ge_le2 {m n}: n >= m -> m <= n. lia. Qed.
Lemma splitZ_zero_pos (m:natZ): m |= natZ0 \/ m |> natZ0. destruct m. pose (ge_le l).
 case (split_zero_pos x g).
 + intros ->. left. now simpl.
 + intro. right. now simpl.
Qed.

(*
Theorem eq_irr (m n: natZ): m |= n -> m = n. pi_subset_proofs. intro.    destruct m; destruct n. clear_subset_proofs.   simpl in *. rewrite H in l. l0. assert (l = l0). rewrite H in l.  *)

Definition lex_lt (m1 n1 m2 n2: natZ) := m1 <| m2 \/ (m1 = m2 /\ n1 <| n2).
Section natZ_lex_ind_principle.
  Variable P : natZ -> natZ -> Prop.

  Hypothesis true_for_lzero : forall m n, m |= natZ0 -> P m n.
  Hypothesis ind_m : forall m n, m |> natZ0 -> (forall p q, lex_lt p q m n -> P p q) -> P m n.


  Theorem nat_lex_ind (m n: natZ) :  P m n.
  Proof.
    revert n. induction m as [m IHm] using natZ_lt_ind; induction n as [n IHn] using natZ_lt_ind.
    destruct (splitZ_zero_pos m) as [ m_zero | m_pos].
    + apply true_for_lzero. assumption.
    + apply ind_m; trivial. intros p q [ lt_p_m | [-> lt_q_n] ].
      * now apply IHm.
      *  now apply IHn.
  Qed.
End natZ_lex_ind_principle.






Ltac lex_resolve2 := unfold lex_lt; left + right; simpl; try split; now try lia.



Ltac destructZ m m_val m_nat m_eqn :=
  destruct m as [m_val m_nat] eqn: m_eqn;
  assert (m_val = proj1_sig m) by now rewrite m_eqn.




Ltac caseZ x n := destruct (dec (Z.eqb x n)).





Equations? fact (n:natZ)  : Z by wf n ref_wf :=
  fact n' := match n' as n_ref return n' = n_ref -> Z with exist _ n n_nat =>
  fun (e: n' = exist _ n n_nat) =>
    if dec (Z.eqb n 0) then 1
            else  n * fact (``(n-1))
            end eq_refl.
Proof. unfold ref_wf. unfold Zwf. simpl; lia. Qed.

Theorem fact_pos (n:natZ): fact n > 0.
  induction n as [n IHn] using natZ_lt_ind. destructZ n n_val n_nat n_eqn. simp fact. caseZ n_val 0.
  - (* goal : 1 > 0 *)  lia.
  - enough (fact (``(n_val-1)) > 0) by lia; apply (IHn (``(n_val -1))); simpl; lia. Undo.
    pose proof (ltac:(refine(IHn (``(n_val -1)) _); simpl; lia)). lia.
Qed.

Theorem ack_eq m n p q : m |= p -> n |= q -> ack m n |= ack p q.
Proof. revert p q. induction m,n as [m n m_is_0 |m n m_gt_0 ack_eq] using nat_lex_ind.
+ intros.  simp ack. destruct m, n, p, q. simpl in *.
  case (dec (Z.eqb x 0)); case (dec (Z.eqb x1 0)); try lia. intros; simpl in *; lia.
+ intros. simp ack. destruct m as [m m_nat], n as [n n_nat], p as [p p_nat], q as [q q_nat].
  caseZ m 0; caseZ p 0;
  caseZ n 0; caseZ q 0; simpl in *;  try lia.
  - eapply ack_eq; try lex_resolve2; simpl; lia.
  - eapply ack_eq; try lex_resolve2.
    * simpl; lia.
    * eapply ack_eq.
      ++ lex_resolve2.
      ++ easy.
      ++ simpl; lia.
Qed.


Ltac ack_trivial := try repeat apply ack_eq; try repeat rewrite plus_val; simpl in *; try lia.


Theorem ack_gt_snd m n : ack m n |> n.
Proof.
  induction m,n as [m n m_is_0 |m n m_gt_0 ack_gt_snd] using nat_lex_ind;
  simp ack; destructZ m m_val m_nat m_eqn; destructZ n n_val n_nat n_eqn; caseZ m_val 0; ack_trivial.
  caseZ n_val 0.
  * eapply gt_ge_gt. (* trans tactic *)
    ++ applys_eq (ack_gt_snd (``(m_val-1)) (``1));  [ack_trivial | lex_resolve2].
    ++ ack_trivial.
  * eapply gt_ge_gt. (* trans tactic *)
    ++ applys_eq (ack_gt_snd (``(m_val-1)) (ack m (``(n_val-1))));  [ack_trivial | lex_resolve2].
    ++ applys_eq ge_gt. 2:{applys_eq (ack_gt_snd m (``(n_val -1))); lex_resolve2. } ack_trivial.
Qed.

(* Lemma plus_irr (m n p q:natZ): m  *)

Definition case_natZ :=  fun x n => dec (Z.eqb x n).
Definition oneZ: natZ. refine (exist _ 1 _). lia. Defined.

Lemma gt_plus_one : forall n, n + 1 > n. lia. Qed.
Lemma gt_plus_one' : forall n, n + 1 + 1 > n+ 1. lia. Qed.

Notation "x |=? y"  := ((proj1_sig x =? proj1_sig y)) (at level 70).

Theorem ack_snd_plus_one (m n:natZ) : ack m (plus n (``1)) |> ack m n.
Proof.
  intros. remember (ack m n) as p. simp ack. destructZ m m_val m_nat m_eqn; destructZ n n_val n_nat n_eqn. simpl in *.
  caseZ m_val 0.
  + rewrite Heqp. simp ack. caseZ m_val 0; ack_trivial.
  + caseZ (n_val + 1) 0; try lia.  applys_eq (ack_gt_snd (``(m_val-1)) (ack m n));
    try rewrite Heqp; ack_trivial.
Qed.


Lemma eq_ge n p:  n = p ->  n >= p.
Proof. lia. Qed.

Lemma split_gt n p : n |> p -> n |= plus p oneZ \/ n |> plus p oneZ.
Proof. destruct n as [n_val n_ref], p as [p_val p_ref]. simpl. intro. case (dec (Z.eqb n_val (p_val+1))).
  + intro. left. lia.
  + intro. right. lia.
Qed.

Theorem ack_mon_snd (m n p:natZ ): n |> p -> ack m n |> ack m p.
Proof.
  revert n m p. induction n as [n ack_mon_snd] using natZ_lt_ind. intros m p H.
  destructZ n n_val n_nat n_eqn; destructZ p p_val p_nat p_eqn. caseZ n_val (p_val+1).
  +  applys_eq (ack_snd_plus_one m p); repeat apply ack_eq; try rewrite plus_val; simpl;  lia.
  + rewrite <- p_eqn,<- n_eqn in H; pose proof (split_gt n p H) as H2.
    assert (n_val - 1 >= 0) by (case H2; lia). (* automate?? *)
    assert (n_val - 1 > p_val) by (case H2; lia).
    eapply gt_gt_gt.
    * applys_eq (ack_snd_plus_one m (``(n_val-1))); apply ack_eq; simpl; lia.
    *  pose proof (ltac:(refine(ack_mon_snd (``(n_val -1)) _ m p _); simpl; lia)) as IH. applys_eq IH; apply ack_eq; simpl; lia.
Qed.

Theorem ack_mon_eq_snd m n p : n |>= p -> ack m n |>= ack m p.
Proof.
  intro n_ge_p; destructZ n n_val n_nat n_eqn; destructZ p p_val p_nat p_eqn. simpl in *.
  caseZ n_val p_val; [ apply eq_ge; apply ack_eq| apply gt_ge2; apply ack_mon_snd]; simpl; lia.
Qed.

Lemma gt_np1 m n: m > n -> m>= n+1. lia. Qed.

Theorem ack_plus_one_fst_snd m n : ack (plus m (``1)) n |>= ack m (plus n (``1)).
Proof.
  revert n m. induction n as [n ack_plus_one_fst_snd] using natZ_lt_ind. intro m.
  remember (ack m (plus n (``1))) as p. simp ack. set (mp1:= plus m (``1)).
  destructZ mp1 mp1_val mp1_nat mp1_eqn;
  destructZ m m_val m_nat m_eqn;
  destructZ n n_val n_nat n_eqn;
  caseZ n_val 0;
  pose proof mp1_eqn as mp1_eqn'.
  all:caseZ mp1_val 0; (* mp1 > 0. *) unfold mp1 in mp1_eqn'; apply EqdepFacts.eq_sig_fst in mp1_eqn'; try lia.
  + apply eq_ge. rewrite Heqp. ack_trivial.
  + rewrite Heqp. eapply ge_ge_ge.
    - applys_eq (ack_mon_eq_snd m (ack mp1 (``(n_val - 1))) (ack m n)). repeat apply ack_eq;simpl; lia.
      applys_eq (ltac:(refine(ack_plus_one_fst_snd (``(n_val-1)) _ m); simpl; try lia));
      apply ack_eq; try rewrite plus_val; simpl; try lia.
    - applys_eq (ack_mon_eq_snd m (ack m n) (``(n_val +1))). repeat apply ack_eq;simpl; lia.
      apply gt_np1. applys_eq (ack_gt_snd m n). lia.
Qed.



Theorem ack_geq_sum m n: ack m n |>= (plus (plus m n) (``1)).
Proof.
  revert m n.
  induction m as [m ack_geq_sum] using natZ_lt_ind. intro n.
  destructZ m m_val m_nat m_eqn; destructZ n n_val n_nat n_eqn; caseZ m_val 0.
  +  simp ack. caseZ m_val 0; try lia. repeat rewrite plus_val. simpl; lia.
  +
  (* + assert (0 <= m_val - 1) as mm1_nat by lia; set (mm1 := exist _ (m_val - 1) mm1_nat: natZ). *)
    eapply ge_ge_ge.
    - applys_eq (ack_plus_one_fst_snd (``(m_val -1)) n).
      * repeat apply ack_eq; repeat rewrite plus_val; simpl; lia.
    - applys_eq (ltac:(refine(ack_geq_sum (``(m_val-1)) _ (``(n_val + 1))); simpl; lia)).
      * repeat apply ack_eq; repeat rewrite plus_val; simpl; lia.
      * repeat rewrite plus_val; simpl; lia.
Qed.

Theorem ack_mon_fst m n p : m |> p -> ack m n |>= ack p n.
Proof.
  revert m n p.
  induction m as [m ack_mon_fst] using natZ_lt_ind. intros n p m_gt_p.
  destructZ m m_val m_nat m_eqn ; destructZ n n_val n_nat n_eqn; destructZ p p_val p_nat p_eqn; simpl in *.
  (* assert (0 <= p_val + 1) as pp1_nat by lia;
  set (pp1 := exist _ (p_val + 1) pp1_nat: natZ). destructZ pp1 pp1_val _f pp1_eqn. *)
  caseZ m_val (p_val + 1).
  + eapply ge_ge_ge.
    - applys_eq (ack_plus_one_fst_snd p n). ack_trivial.
    - apply gt_ge2.
      applys_eq (ack_mon_snd p (``(n_val+1)) n); ack_trivial.
  +
    (* assert (0 <= m_val - 1) as mm1_nat by lia; set (mm1 := exist _ (m_val - 1) mm1_nat: natZ). *)
    eapply ge_ge_ge.
    - applys_eq (ack_plus_one_fst_snd (``(m_val-1)) n). ack_trivial.
    - eapply ge_ge_ge.
      * apply gt_ge2. applys_eq (ack_mon_snd (``(m_val -1)) (``(n_val + 1)) n); ack_trivial.
      * applys_eq (ltac:(refine(ack_mon_fst (``(m_val - 1)) _ n p); simpl; lia)); ack_trivial.
Qed.
(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrZ. *)

Theorem ack_fst_plus_two m n : ack (m |+ `` 2) n |> ack m (``2 |* n) .
Proof.
  revert n m;
  induction n as [n ack_fst_plus_two] using natZ_lt_ind;
  intro m.
  set (mp2 := m |+ ``2); set (nt2 := ``2 |* n). remember (ack m nt2) as rhs.
  destructZ n n_val n_nat n_eqn; destructZ m m_val m_nat m_eqn.
  destructZ mp2 mp2_val mp2_nat mp2_eqn.
  simp ack.
  caseZ mp2_val 0; try (simpl in *; lia).
  caseZ n_val 0; simpl; try lia.
  + assert (ack (``(mp2_val - 1)) (``0) |= ack m (``1)) as ack_arg
      . remember (ack m (``1)) as p. simp ack; simpl in *; caseZ (mp2_val - 1) 0; try lia. rewrite Heqp. ack_trivial.
    (* simp ack. simpl. caseZ (mp2_val -1) 0; simpl in *; try lia. *)
    (* remember (ack (``(mp2_val-1)) (``1)) as p. simp ack in Heqp. caseZ (mp2_val -1) 0; simpl in *; try lia. rewrite //. destruct (Z.eq_dec (mp2_val - 1) 0); [lia |] . generalize n0 Heqp. simpl. e4 in Heqp. *)
    eapply gt_gt_gt.
    - applys_eq (ack_gt_snd m (ack m (``1))).
      remember (ack m (ack m (``1))) as p; simp ack; simpl in *; caseZ (mp2_val -1) 0; try lia.
      rewrite Heqp. apply ack_eq. simpl in *; lia. applys_eq ack_arg. ack_trivial.
    - rewrite Heqrhs.
      applys_eq (ack_mon_snd m (``1) (``0)).
      ack_trivial.
  + eapply gt_ge_gt.
    - applys_eq (ack_mon_snd (``(m_val + 1)) (ack mp2 (``(n_val-1))) (ack m (`` (2 * n_val - 2))) ); simpl in *; try ack_trivial.
      applys_eq (ltac:(refine(ack_fst_plus_two (``(n_val - 1)) _ m); simpl in *; lia)); ack_trivial.
    - eapply ge_ge_ge.
      * applys_eq (ack_mon_eq_snd (``(m_val+1)) (ack m (`` (2 * n_val - 2))) (``(m_val + 2*n_val-1))).
        applys_eq (ack_geq_sum m (``(2*n_val - 2))). ack_trivial.
      * eapply ge_ge_ge.
        ++  applys_eq (ack_mon_eq_snd (``(m_val + 1)) (``(m_val + 2 * n_val - 1)) (``(2*n_val - 1))). ack_trivial.
        ++ rewrite Heqrhs.  applys_eq (ack_plus_one_fst_snd (``m_val) (``(2*n_val - 1))); ack_trivial.
Qed.