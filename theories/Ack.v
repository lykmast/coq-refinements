Require Import Lia.
Require Import PLF.LibTactics.
Require Import CoqTactical.SimplMatch.
Require Import CoqRefinements.Tactics.
Require Import CoqRefinements.Prelude.
Require Import CoqRefinements.Induction.
Require Import CoqRefinements.Arithmetic.
Require Import CoqRefinements.Types.
Require Import ZArith.
Open Scope Z_scope.

Opaque Z.add.
Opaque Z.mul.
(* Ackermann *)
From Equations Require Import Equations.
Require Import Coq.ZArith.Zwf.
Require Import Program.Utils. (* for 'dec' *)

(* Equations should automatically derive this instance, but for some reason can't. *)
#[local] Instance Zwf_inst : WellFounded
(Telescopes.tele_measure
  (Telescopes.ext Nat (fun _ : Nat => Telescopes.tip Nat))
  (Z * Z) (fun m n : Nat => ((` m)%prg, (` n)%prg))
  (lexprod Z Z (Zwf 0) (Zwf 0))).
  repeat red; intros;
  unfold Telescopes.tele_measure;
  (* constructor. *)
  apply Inverse_Image.Acc_inverse_image;  apply acc_A_B_lexprod; apply Zwf_well_founded.
Qed.


(* Definition test (n:Nat)  *)

Equations? ack (m n:Nat)  : Nat by wf (` m, ` n) (lexprod Z Z (Zwf 0) (Zwf 0)) :=
ack m n := match dec ( `m =? 0) with
  | left em =>
      (upcastDef (add n (`` 1)))
  | right em =>
      match dec (`n =? 0) with
        | left en =>
            ack (upcastDef (sub m (`` 1))) (upcastDef (`` 1))
        | right en =>
            ack (upcastDef (sub m (`` 1))) (ack (upcastDef m) (upcastDef (sub n (``1))))
    end
  end.
Proof.
  all: termination_tac.
Defined.


Theorem ack_gt_snd m n : ` (ack m n) >  ` n.
Proof.
induction m,n as [m n  m_is_0|m n m_gt_0 ack_gt_snd] using nat_lex_ind;
simp ack; case_eq (`m) 0; try my_trivial.
(* *  *)
case_eq (`n) 0; destruct matches; try my_trivial.
* eapply gt_ge_gt.
  ++ apply ack_gt_snd. my_trivial. (*  *)
  ++ my_trivial.
* eapply gt_ge_gt.
  ++ apply ack_gt_snd; my_trivial.
  ++  applys_eq gt_ge4. (* >= n means > n - 1 *)
      applys_eq (ack_gt_snd m (ltac:(infer (sub n (``1))))); my_trivial.
Qed.




(*  This is the cast in the signature of the next theorem.
  It helps to have it as a separate definition
  because it's easier to case split and unfold ack.
*)
Create HintDb ackHintDb.
Lemma addn1_nat (n:Nat) : ` (add n (`` 1)) >= 0.  my_trivial. Qed.
Definition addn1 (n:Nat) := exist _ (` (add n (`` 1))) (addn1_nat n):Nat.

Theorem ack_snd_plus_one (m n: Nat): ` (ack m (addn1 n)) > ` (ack m n).
Proof.
  remember (ack m n) as rhs. (* freeze rhs *)
simp ack. case_eq (`m) 0; destruct matches; try my_trivial.
(* destruct matches helps to take into account n+1 /= 0 which helps with unfolding. *)
+ rewrite Heqrhs; simp ack; case_eq (`m) 0; my_trivial.
+ applys_eq (ack_gt_snd ( ltac:(infer(sub m (``1)))) (ack m n)).
  - my_trivial.
  - rewrite Heqrhs. my_trivial.
Qed.
Theorem ack_mon_snd (m n: Nat) (p: {v:Z| `n > v /\ v >= 0}): ` (ack m n) > ` (ack m (ltac:(infer p))).
Proof.
  revert m p. induction n as [n ack_mon_snd] using nat_lt_ind. intros m p.
  case_eq (`n) (`p+1);  try my_trivial.
  + reft_apply ack_snd_plus_one m p ; my_trivial.
  + set (nm1:= (``(`n-1))). reft_pose ack_snd_plus_one m  nm1.
    reft_pose ack_mon_snd nm1 m p.
    eapply gt_gt_gt.
    * applys_eq H1. resolve_eq.

    * applys_eq H5; resolve_eq.
Qed.


Theorem ack_mon_eq_snd (m:Nat) (n: Nat) (p:{v:Z | `n >= v /\ v >= 0}): ` (ack m n) >= ` (ack m ltac:(infer p)).
Proof.
  case_eq (`n) (`p); try my_trivial.
  + apply eq_ge. my_trivial.
  + apply gt_ge2. reft_apply ack_mon_snd m n p; resolve_eq.
Qed.


(*
Goal True.
match type of ack_mon_eq_snd with
  (forall (m:?t2) (n:?t3) (_:?t4), _) => idtac t4
  | ?t  => idtac t end.

Ltac get_prop x :=
  match x w
Lemma test (x:Nat): True.
 match Nat with
  {v:_| ?P} => set (p := fun v:Z => P)
  end. *)
(* Search (sig ?a ?p -> ?a). *)
(* Ltac inferType x n := assert `x *)

Theorem reorder_forall {A} {B} {P:A -> B -> Prop}: (forall (x:A) (y:B) , P x y) -> forall (y:B) (x:A), P x y.
intro. intros. apply H. Qed.


Theorem ack_plus_one_fst_snd m n : ` (ack (addn1 m) n) >= ` (ack m (addn1 n)).
  revert m. induction n as [n IHn] using nat_lt_ind.
  pose (reorder_forall IHn) as ack_plus_one_fst_snd.
  intro m. remember (ack m (addn1 n)) as rhs. simp ack; case_eq (`n) 0; destruct matches. all:try my_trivial.
  + apply eq_ge. rewrite Heqrhs.  my_trivial.
  + rewrite Heqrhs.

  set (nm1 := `` (`n-1)).
  set (mp1 := ``(`m + 1)).

  reft_set ack (add m (``1)) (sub n (``1)).
  reft_set ack m n.
  assert (`s >= `s0) by (reft_apply ack_plus_one_fst_snd m nm1;
    my_trivial).
  reft_pose ack_mon_eq_snd m s s0.
  eapply ge_ge_ge.

  * applys_eq H7.
  my_trivial.
  (* resolve_eq'. ;easy + solve [apply proof_irrelevance] *)
  * assert (`s0 >= ` (add n (``1))) by (unfold_locals; apply gt_ge; reft_apply ack_gt_snd m n; my_trivial).
    reft_apply ack_mon_eq_snd m s0 (add n (``1)); my_trivial.
Qed.



Theorem ack_geq_sum m n: ` (ack m n) >= ` (add (add m n) (``1) ).
  revert m n. induction m as [m ack_geq_sum] using nat_lt_ind.
  intro n.  case_eq (`m) 0.
  + simp ack. destruct matches. try my_trivial.
  + reft_pose ack_plus_one_fst_snd (sub m (``1)) n.
    reft_pose ack_geq_sum (sub m (``1)) (add n (``1)).
    eapply ge_ge_ge.
    * applys_eq H1; my_trivial.
    * applys_eq H4; my_trivial.
Qed.

Theorem ack_mon_fst m n (p:{v:Z| v >= 0 /\ `m > v }): ` (ack m n) >= ` (ack ltac:(upcast p) n).
Proof.
  revert m n p. induction m as [m ack_mon_fst] using nat_lt_ind. intros n p.
  case_eq (`m) (` (add p (``1))).
  + reft_pose ack_plus_one_fst_snd p n.
    reft_pose ack_mon_eq_snd p (add n (``1)) n.
    eapply ge_ge_ge.
    * applys_eq H1; my_trivial.
    * applys_eq H5; my_trivial.
  + reft_pose ack_plus_one_fst_snd (sub m (``1)) n.
    reft_pose ack_mon_eq_snd (sub m (``1)) (add n (``1)) n.
    reft_pose ack_mon_fst (sub m (``1)) n p.
    eapply ge_ge_ge.
    * applys_eq H1; my_trivial.
    * eapply ge_ge_ge.
      - applys_eq H5; my_trivial.
      - applys_eq H9; my_trivial.
Qed.


Lemma add2_nat (n:Nat) : ` (add n (`` 2)) >= 0.  my_trivial. Qed.
Definition add2 (n:Nat) := exist _ (` (add n (`` 2))) (add2_nat n):Nat.


Lemma mul2_nat (n:Nat) : ` (mul n (`` 2)) >= 0.  my_trivial. Qed.
Definition mul2 (n:Nat) := exist _ (` (mul n (`` 2))) (mul2_nat n):Nat.

Theorem ack_fst_plus_two (m n:Nat) : ` (ack (add2 m) n) > ` (ack m (mul2 n)).
Proof.
  revert m. induction n as [n IHn] using nat_lt_ind.
  pose proof (reorder_forall IHn) as ack_fst_plus_two.
  intro m.
  case_eq (`n) 0.
  + remember  (ack m (mul2 n)) as rhs.
    simp ack; destruct matches; try my_trivial.
    simp ack; destruct matches; try my_trivial.

    reft_set ack m (``1).
    reft_pose ack_gt_snd m s.
    reft_pose ack_mon_snd m (``1) (``0).
    eapply gt_gt_gt.
    * applys_eq H3. repeat f_equal. unfold_locals. simpl.   my_trivial.
      unfold_locals. apply eq_sig. simpl. f_equal. set (lhs := ack (exist (fun v : Z => v >= 0) (` m)%prg H)
      (exist (fun v : Z => v >= 0) 1 H0)).
      reft_set ack (add m (``1)) (``0).
      reft_set ack m (``1).
      assert (s0 = s1) by (unfold s0; simp ack; destruct matches; my_trivial).
      applys_eq H12; my_trivial.
    * rewrite Heqrhs. applys_eq H7;  my_trivial.
  + remember  (ack m (mul2 n)) as rhs. simp ack; destruct matches; try my_trivial.
    (* reft_pose ack_fst_plus_two m (sub n (``1)). *)
    reft_set ack (add m (``2)) (sub n (``1)).
    reft_set ack m (sub ( mul (``2) n) (``2)).
    assert (`s > `s0) by (reft_apply ack_fst_plus_two m (sub n (``1));
    my_trivial).
    reft_pose ack_mon_snd (add m (``1)) s s0.
    assert (`s0 >= ` (add m (sub ( mul (``2) n) (``1)))) by (
      reft_apply ack_geq_sum m (sub ( mul (``2) n) (``2)); my_trivial).
    reft_pose ack_mon_eq_snd (add m (``1)) s0 (add m (sub ( mul (``2) n) (``1))).

    reft_pose ack_mon_eq_snd (add m (``1)) (add m (sub ( mul (``2) n) (``1))) (sub ( mul (``2) n) (``1)).
    reft_pose ack_plus_one_fst_snd m (sub ( mul (``2) n) (``1)).

    eapply gt_ge_gt.
    * applys_eq H7; my_trivial.
    * eapply ge_ge_ge.
      - applys_eq H12; my_trivial.
      - eapply ge_ge_ge.
        ++  applys_eq H16; my_trivial.
        ++ rewrite Heqrhs. applys_eq H19.
            -- my_trivial.
            (* my_trivial (resolve_eq) cannot solve next goal because f_equal is applied
                more times than it should i.e. inside mul2 and addn1
                  (locals defined out of the proof)
                ===> Stop f_equal from going into ``local'' definitions (How?)
                ===> Backtrack f_equal if solve fails (Could case infinite loops :/)
            *)
            (* if we un*)
            --  unfold_locals.
                (* - manually f_equal only as far as necessary. *)
                f_equal; f_equal; reft_eq. Undo.
                (* - or, first unfold mul2, addn1 then my_trivial. *)
                unfold mul2; unfold addn1; my_trivial.

Qed.