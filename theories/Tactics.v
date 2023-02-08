Require Import Lia.
Require Import ZArith.
Require Import PLF.LibTactics.
Require Import CoqTactical.SimplMatch.
Require Import CoqRefinements.Types.
Require Import CoqRefinements.Common.
Require Import ProofIrrelevance.
Require Import Program.Utils. (* for 'dec' *)

Open Scope Z_scope.


(* Destruct Refinements *)

Ltac destructRef m :=
  let m_val := fresh "val" in
  let m_eqn := fresh "eqn" in
  destruct m as [m_val ?] eqn: m_eqn;
  assert (m_val = proj1_sig m) by now rewrite m_eqn.


(*
We need to do this complex thing in order to apply destruct once to each refinement.
  - Push BLOCK and then every reft to goal.
  - then intro each reft and destruct it until BLOCK is found.
*)
Definition BLOCK := True.

Ltac repeat_until_block tac :=
lazymatch goal with
| [ |- BLOCK -> _ ] => intros _ + (simpl; intros _)
(* simpl in case BLOCK is in the conclusion ^^ *)
| [ |- _ ] => tac (); repeat_until_block tac
end.

Ltac destructAllRefts :=
generalize (I : BLOCK) + generalize dependent (I:BLOCK);
repeat match goal with
        | [ H : _ |- _ ] =>
          revert H (* revert all Hypotheses *)
        end;
repeat_until_block
  ltac:(fun _
        => intro;
            lazymatch goal with
            | [ m : _ |- _ ]
            =>  match type of m with
                | {_ | _}
                =>  try destructRef m (* destruct refinements *)
                | _ => idtac
                end
            end)
.


Ltac repeat_until_block_debug tac :=
lazymatch goal with
| [ |- BLOCK -> _ ] => idtac "Found block"; intros _ + (simpl; intros _) + idtac "Couldn't remove block."
| [ |- _ ] => idtac "repeating"; tac (); repeat_until_block_debug tac
end.

Ltac destructAllReftsDebug :=
generalize (I : BLOCK) + generalize dependent (I:BLOCK);
idtac "generalized";
repeat match goal with
        | [ H : _ |- _ ] =>
          idtac "reverting " H;
          revert H (* revert all Hypotheses *)
        end;
repeat_until_block_debug
  ltac:(fun _
        => intro;
            lazymatch goal with
            | [ m : _ |- _ ]
            =>  match type of m with
                | {_ | _}
                => idtac "destructing " m;  destructRef m (* destruct refinements *)
                | _ => idtac "leaving " m " alone"
                end
            end)
.

(* Refinement Type tactics *)

(* - Upcast *)
Definition upcastDef {A} {P Q:A -> Prop} {H: forall a, P a -> Q a} (n:{v:A | P v }):{v:A| Q v}.
destruct n. apply H in p. exact (exist Q x p). Defined.

Ltac smt_upcast := simpl in *;lia.
Ltac upcast n := destructRef n; refine (upcastDef n); try smt_upcast.

(* - Strengthen *)
Definition strengthenDef {A} {P Q:A -> Prop} (n:{v:A | P v }) (H:Q (proj1_sig n)):{v:A| P v /\ Q v /\ v = proj1_sig n}.
 refine (exist _ (proj1_sig n) _). destruct n; repeat split; trivial.
Defined.

Ltac strengthen n H := pattern (proj1_sig n) in H; try refine (strengthenDef n H).

(* - Trivial *)
Definition triv {A} (x:A) := exist _ x eq_refl :{v:A| v = x}.
Check (triv 1).

Notation "`` x" := (triv x) (at level 10).

Ltac smt_infer := smt_upcast.
Ltac infer x := solve [upcast x | refine (exist _ (` x) _); destructAllRefts; smt_infer].

Ltac termination_tac := try (left + right; constructor; simpl); lia.



(* Resolve lexicographic comparison constraints. *)
Ltac lex_resolve := unfold lex_lt;  left + right; simpl; try split; now try lia.

(* Resolve equality of refinements constraints. *)
Ltac reft_eq := destructAllRefts; ((apply subset_eq_compat; simpl in *; lia) + solve [apply proof_irrelevance]). (* ;easy + solve [apply proof_irrelevance]*)

(* Resolve equality of refinement functions. *)
Ltac resolve_eq :=
  repeat f_equal;
  reft_eq.

(* Case split on equality of Zs. *)
Ltac case_eq n1 n2 := destruct (dec (n1 =? n2)).


(* Emulating LH trivial. Combination of:
    * destruct everything and lia
    * lex comparison
    * refinement functions equality
*)
Ltac my_trivial := first [destructAllRefts;simpl in *; now try lia | lex_resolve | resolve_eq].

(*
Ltac test f := match f with f => idtac "yes" | _ => idtac "no" end.

Goal True. set (hey:=2). test hey. *)