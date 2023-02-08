Require Import CoqRefinements.Types.
Require Import ZArith.
Open Scope Z_scope.
Definition lex_lt (m1 n1 m2 n2: Nat) := `m1 < `m2 \/ `m1 = `m2 /\ `n1 < `n2.
