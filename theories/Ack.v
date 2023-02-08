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

#[local] Hint Extern 4 => unfold addn1: ackHintDb.
#[local] Hint Extern 4 => my_trivial: ackHintDb.

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
  + applys_eq (ack_snd_plus_one m (ltac:(upcast p))); try unfold addn1; my_trivial.
  + eapply gt_gt_gt.
Require Import ProofIrrelevance.
    * applys_eq (ack_snd_plus_one m (ltac:(infer (``(`n - 1))))).
      destructRef n; destructRef m. repeat f_equal. apply subset_eq_compat. simpl in *. lia.
    * applys_eq (ack_mon_snd ltac:(infer (``(`n-1))) m (ltac:(refine (exist _ (` p) _); destructRef p; smt_infer)))
      ; destructRef m; destructRef n; destructRef p; repeat f_equal; apply subset_eq_compat; simpl in *. all:lia.
Qed.


Theorem ack_mon_eq_snd (m:Nat) (n: Nat) (p:{v:Z | `n >= v /\ v >= 0}): ` (ack m n) >= ` (ack m ltac:(infer p)).
Proof.
  case_eq (`n) (`p); try my_trivial.
  + apply eq_ge. my_trivial.
  + apply gt_ge2. applys_eq (ack_mon_snd m n ltac:(infer p)). my_trivial.
Qed.

Check Nat.
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


(* Lemma gt_ *)

Theorem ack_plus_one_fst_snd m n : ` (ack (addn1 m) n) >= ` (ack m (addn1 n)).
  revert m. induction n as [n IHn] using nat_lt_ind.
  pose (reorder_forall IHn) as ack_plus_one_fst_snd.
  intro m. remember (ack m (addn1 n)) as rhs. simp ack; case_eq (`n) 0; destruct matches. all:try my_trivial.
  + apply eq_ge. rewrite Heqrhs. unfold addn1. my_trivial.
  + rewrite Heqrhs.
  assert (`n - 1 >= 0 /\ `n-1 < `n) by (destructAllRefts; smt_infer).
  set (nm1 := ltac:(exists (`n-1); assumption):{v:Z| v>=0 /\ v < (`n)} ).
  (* pose proof (ack_plus_one_fst_snd m nm1) as lem1. *)
  assert ((fun v => v >= 0) (`m+1)) by (destructAllRefts; smt_infer).
  set (app1 := ltac:(exists (`m+1); assumption) :Nat ).
  assert ((fun v => v >= 0) (`n-1)) by (destructAllRefts; smt_infer).
  set (app2 := ltac:(exists (`n-1); assumption) :Nat ).
  (* set (mid := ack app1 app2). *)
  (* #[local] Hint Extern 4 => unfold mid: ackHintDb. *)
  assert (` (ack app1 app2) >= ` (ack m n) /\ ` (ack m n) >= 0)
    by (split ;
    [ applys_eq (ack_plus_one_fst_snd m nm1); repeat f_equal; destructAllRefts; apply subset_eq_compat; simpl in *; lia
    | now destruct (ack m n)
    ]) .
  set (app3 := ltac:(exists (` (ack m n)); assumption):{v:Z| ` (ack app1 app2) >= v /\ v >= 0}).

  eapply ge_ge_ge.
  * applys_eq (ack_mon_eq_snd m (ack app1 app2)  app3). resolve_eq.
  * assert (` (ack m n) >= 0) by ( smt_infer).
    set (app4 := ltac:(exists (` (ack m n)); assumption):Nat).
    assert  ( `app4 >= `n+1 /\ `n +1  >= 0).
    - split.
      -- apply gt_ge. applys_eq (ack_gt_snd m n).
      -- smt_infer.


    - set (app5 := ltac:( exists (`n + 1); assumption): {v:Z| ` app4 >= v /\ v >= 0}).
      applys_eq (ack_mon_eq_snd m app4 app5); auto with ackHintDb.
Qed.


