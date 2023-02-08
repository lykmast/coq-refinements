Require Import CoqRefinements.Types.
Require Import ProofIrrelevance.
Require Import ZArith.
Require Import Lia.
Require Import CoqRefinements.Common.
Require Import CoqRefinements.Tactics.
Require Import PLF.LibTactics.
Require Import Program.Utils. (* for 'dec' *)

Open Scope Z_scope.
Section nat_lt_ind_principle.
Variable P : Nat -> Prop.


Hypothesis ind_n : forall n:Nat, (forall k:{v:Z | v >= 0 /\ v < `n}, P ltac:(upcast k)) -> P n.

Theorem nat_lt_ind (n: Nat) : P n.

  (* enough (H0: forall p, p <= n -> P p).
  - apply H0, le_n. *)
  case n; intros n_val n_ref. generalize n_ref. pattern n_val. apply Z_lt_induction.
  + intros; apply ind_n; intros; destruct k.   apply H. simpl in *.  lia.
  + lia.
Qed.
End nat_lt_ind_principle.


Section natZ_lex_ind_principle.
Variable P : Nat -> Nat -> Prop.

Hypothesis true_for_lzero : forall m n:Nat, `m = 0 -> P m n.
Hypothesis ind_m : forall m n,  `m > 0  -> (forall p q, lex_lt p q m n -> P p q) -> P m n.

Theorem nat_lex_ind (m n: Nat) :  P m n.
Proof.
  (* destruct (splitZ_zero_pos m) as [ m_zero | m_pos]. *)
  revert n; induction m as [m IHm] using nat_lt_ind.

  destruct (dec (`m =? 0)).
  + intro; apply true_for_lzero; lia.
  +  induction n as [n IHn] using nat_lt_ind. apply ind_m.
    * destruct m; simpl in *; try lia.
    * intros p q [ lt_p_m | [eq_p_m lt_q_n] ].
      ++  applys_eq (IHm ltac:(infer p) q); reft_eq.
      ++  enough (p = m) as -> by (applys_eq (IHn ltac:(infer q)); reft_eq); reft_eq.
Qed.
End natZ_lex_ind_principle.

