
Require Import Lia.
Require Import ZArith.
Open Scope Z_scope.
(* Goal transforming inequalities + transitivities. *)
Lemma gt_ge : forall m n, m > n -> m >= n + 1. lia. Qed.
Lemma gt_ge2 : forall m n, m > n -> m >=n. lia. Qed.
Lemma gt_ge3 : forall m n, m > n - 1 -> m >= n. lia. Qed.
Lemma gt_ge4 : forall m n, m > n - 1 -> m >= n. lia. Qed.

Lemma ge_gt : forall m n, m >= n + 1 <-> m > n.  lia. Qed.
Lemma ge_gt_l : forall m n, m > n -> m >= n + 1.  lia. Qed.
Lemma eq_ge: forall m n, m = n -> m >= n. lia. Qed.

Lemma gt_ge_gt: forall m n p, m > n -> n >= p -> m > p. lia. Qed.
Lemma gt_gt_gt: forall m n p, m > n -> n > p -> m > p. lia. Qed.
Lemma ge_ge_ge: forall m n p, m >= n -> n >= p -> m >= p. lia. Qed.
Lemma gt_plus : forall m n p, m > n -> m + p > n + p. lia. Qed.
