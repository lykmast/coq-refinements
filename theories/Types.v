Require Import ZArith.
Open Scope Z_scope.
(* Types *)
Notation Int P := {v:Z|P v}.
(* Notation RefZ P  := (sig P Z). *)

Notation Nat := ({v:Z| v >= 0}).
Definition Bool {b:bool} := {v:bool | v = b}.

Notation "` x" := (proj1_sig x) (at level 10).