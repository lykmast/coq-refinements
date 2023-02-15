Require Import Lia.
Require Import ZArith.
Require Import PLF.LibTactics.
Require Import CoqTactical.SimplMatch.
Require Import CoqRefinements.Types.
Require Import CoqRefinements.Common.
Require Import CoqRefinements.MapTactics.
Require Import ProofIrrelevance.
Require Import Program.Utils. (* for 'dec' *)

Open Scope Z_scope.


Ltac unfold_locals :=
  repeat
  match goal with
  | x : _ |- _ => progress unfold x
  end.

Lemma eq_sig {A:Type} {P:A -> Prop}:
forall u v : {a : A | P a}, (` u)%prg = (` v)%prg -> u = v.
 apply eq_sig_hprop; intros; apply proof_irrelevance.
Qed.

(* Destruct Refinements *)

Ltac destructReft m :=
  match type of m with
  | {_ | _} => try
    (let m_val := fresh "val" in
    let m_eqn := fresh "eqn" in
    destruct m as [m_val ?] eqn: m_eqn;
    assert (m_val = proj1_sig m) by now rewrite m_eqn)
  | _ => idtac
  end.

Ltac destructAllRefts := exec (destructReft) on hyps.

(* Refinement Type tactics *)

(* - Upcast *)
Definition upcastDef {A} {P Q:A -> Prop} {H: forall a, P a -> Q a} (n:{v:A | P v }):{v:A| Q v}.
destruct n. apply H in p. exact (exist Q x p). Defined.

Ltac smt_upcast := simpl in *;lia.
Ltac upcast n := destructReft n; refine (upcastDef n); try smt_upcast.

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

Ltac resolve_eq' := unfold_locals; repeat f_equal;
  simpl; reft_eq'
with reft_eq' := destructAllRefts;
  ((apply subset_eq_compat; simpl in *; lia)
  + solve [apply proof_irrelevance]
  + (apply eq_sig; simpl; resolve_eq')).
  (* Case split on equality of Zs. *)
Ltac case_eq n1 n2 := destruct (dec (n1 =? n2)).


(* Emulating LH trivial. Combination of:
    * destruct everything and lia
    * lex comparison
    * refinement functions equality
*)
Ltac my_trivial := first [destructAllRefts;simpl in *; now try lia | lex_resolve | resolve_eq'].


(* Apply Tactics *)


Ltac prop t :=
  lazymatch t with
  | fun (x:?X) (y:?Y) (z:?Z) => sig ?p => constr:(fun (x:X) (y:Y) (z:Z) => p)
  | fun (x:?X) (y:?Y) => sig ?p => constr:(fun (x:X) (y:Y) => p)
  | fun (x:?X) => sig ?p => constr:(fun (x:X) => p)
  |  sig ?p  =>  p
  end.

Ltac arg_tac := (* tactic that makes sure argument fits *)
  destructAllRefts;
  smt_infer.

Ltac apply_arg x x' t p :=
  assert (p (` x)) by arg_tac;
  set (x' := ltac:(exists (`x); assumption):t).


Ltac apply1 tac l x1 :=
lazymatch type of l with
| forall (a1:?t1), _ =>
    let x1' := fresh "app" in
    let p1:= prop t1 in

    apply_arg x1 x1' t1 p1;

    tac (l x1')
| ?t => fail "not one argument lemma but" t
end.

Ltac apply2 tac l x1 x2 :=
lazymatch type of l with
| forall (a1:?t1) (a2:?t2), _ =>
    let x1' := fresh "app" in
    let x2' := fresh "app" in

    let t2' := constr:(fun a1:t1 => t2) in

    let p1:= prop t1 in

    apply_arg x1 x1' t1 p1;

    let t2'' := constr:(t2' x1') in
    let p2 := prop t2' in
    let p2' := constr:(p2 x1') in
    apply_arg x2 x2' t2'' p2';

    tac (l x1' x2')
| ?t => fail "not two argument lemma but" t
end.

Ltac apply3 tac l x1 x2 x3:=
lazymatch type of l with
| forall (a1:?t1) (a2:?t2) (a3:?t3), _ =>
    let x1' := fresh "app" in
    let x2' := fresh "app" in
    let x3' := fresh "app" in

    let t2' := constr:(fun a1:t1 => t2) in
    let t3' := constr:(fun (a1:t1) (a2:(t2' a1)) => t3) in

    let p1:= prop t1 in

    apply_arg x1 x1' t1 p1;

    let t2'' := constr:(t2' x1') in
    let p2 := prop t2' in
    let p2' := constr:(p2 x1') in
    apply_arg x2 x2' t2'' p2';

    let t3'' := constr:(t3' x1' x2') in
    let p3 := prop t3' in
    let p3' := constr:(p3 x1' x2') in
    apply_arg x3 x3' t3'' p3';

    tac (l x1' x2' x3')
| ?t => fail "not three argument lemma but" t
end.

Ltac apply4 tac l x1 x2 x3 x4:=
  lazymatch type of l with
  forall (a1:?t1) (a2:?t2) (a3:?t3) (a4:?t4), _ =>
    let x1' := fresh "app" in
    let x2' := fresh "app" in
    let x3' := fresh "app" in
    let x4' := fresh "app" in

    let t2' := constr:(fun a1:t1 => t2) in
    let t3' := constr:(fun (a1:t1) (a2:(t2' a1)) => t3) in
    let t4' := constr:(fun (a1:t1) (a2:(t2' a1)) (a3:(t3' a1 a2)) => t4) in

    let p1:= prop t1 in

    apply_arg x1 x1' t1 p1;

    let t2'' := constr:(t2' x1') in
    let p2 := prop t2' in
    let p2' := constr:(p2 x1') in
    apply_arg x2 x2' t2'' p2';

    let t3'' := constr:(t3' x1' x2') in
    let p3 := prop t3' in
    let p3' := constr:(p3 x1' x2') in
    apply_arg x3 x3' t3'' p3';

    let t4'' := constr:(t4' x1' x2' x3') in
    let p4 := prop t4' in
    let p4' := constr:(p4 x1' x2' x3') in
    apply_arg x4 x4' t4'' p4';

    tac (l x1' x2' x3' x4')
| ?t => fail "not four argument lemma but" t
end.


Ltac just_pose m := pose m.
Ltac my_pose_proof H := pose proof H.
Ltac my_applys H := applys_eq H.

Tactic Notation "reft_apply" constr(l) constr(x1) := apply1 my_applys l x1.
Tactic Notation "reft_apply" constr(l) constr(x1) constr(x2) := apply2 my_applys l x1 x2.
Tactic Notation "reft_apply" constr(l) constr(x1) constr(x2) constr(x3) := apply3 my_applys l x1 x2 x3.
Tactic Notation "reft_apply" constr(l) constr(x1) constr(x2) constr (x3) constr(x4) := apply4 my_applys l x1 x2 x3 x4.

Tactic Notation "reft_pose" constr(l) constr(x1) := apply1 my_pose_proof l x1.
Tactic Notation "reft_pose" constr(l) constr(x1) constr(x2) := apply2 my_pose_proof l x1 x2.
Tactic Notation "reft_pose" constr(l) constr(x1) constr(x2) constr(x3) := apply3 my_pose_proof l x1 x2 x3.
Tactic Notation "reft_pose" constr(l) constr(x1) constr(x2) constr (x3) constr(x4) := apply4 my_pose_proof l x1 x2 x3 x4.

Tactic Notation "reft_set" constr(l) constr(x1) := apply1 just_pose l x1.
Tactic Notation "reft_set" constr(l) constr(x1) constr(x2) := apply2 just_pose l x1 x2.
Tactic Notation "reft_set" constr(l) constr(x1) constr(x2) constr(x3) := apply3 just_pose l x1 x2 x3.
Tactic Notation "reft_set" constr(l) constr(x1) constr(x2) constr (x3) constr(x4) := apply4 just_pose l x1 x2 x3 x4.
