Require Import Lia.
Require Import ZArith.
Require Import PLF.LibTactics.
Require Import CoqTactical.SimplMatch.
Require Import CoqRefinements.Tactics.
Require Import CoqRefinements.Types.
Require Import Program.Utils. (* for 'dec' *)

Open Scope Z_scope.






(* Refined Int Functions *)
Definition add {P Q} (m:Int P)  (n:Int Q) :=
exist _ (` m + ` n) eq_refl
: Int (fun v => v = ` m + ` n).

Definition sub {P Q} (m:Int P) (n:Int Q) :=
  exist _ (` m - ` n) eq_refl
: Int (fun v => v = ` m - ` n).


Definition mul {P Q} (m:Int P) (n:Int Q) :=
  exist _ (` m * ` n) eq_refl
:Int (fun v => v = ` m * ` n).


Definition eq_p {P Q} (m:Int P) (n:Int Q) :=
  (Z.eqb (` m) (` n)):bool.

Definition neq_p {P Q} (m:Int P) (n:Int Q) :=
  negb (Z.eqb (` m) (` n)):bool.

Definition leq_p {P Q} (m:Int P) (n:Int Q) :=
 Z.leb (` m) (` n).

Definition geq_p {P Q} (m:Int P) (n:Int Q) :=
 Z.geb (` m) (` n).

Definition lt_p {P Q} (m:Int P) (n:Int Q) :=
 Z.ltb (` m) (` n).

Definition gt_p {P Q} (m:Int P) (n:Int Q) :=
Z.gtb (` m) (` n).

Definition eq {P Q} (m:Int P) (n:Int Q) :=
  exist _ (eq_p m n) eq_refl
:@Bool ( eq_p m n).

Check Z.eqb.

Definition neq {P Q} (m:Int P) (n:Int Q) :=
  exist _ (neq_p m n) eq_refl
:@Bool (neq_p m n).

Definition leq {P Q} (m:Int P) (n:Int Q) :=
  exist _ (leq_p m n) eq_refl
:@Bool ( leq_p m n).

Definition geq {P Q} (m:Int P) (n:Int Q) :=
exist _ (geq_p m n) eq_refl
:@Bool ( geq_p m n).

Definition lt {P Q} (m:Int P) (n:Int Q) :=
  exist _ (lt_p m n) eq_refl
:@Bool ( lt_p m n).

Definition gt {P Q} (m:Int P) (n:Int Q) :=
  exist _ (gt_p m n) eq_refl
:@Bool ( gt_p m n).


(* TESTS *)
Definition ge5_ge0 (n:{v:Z| v>=5}) : {v:Z| v>=0}. upcast n. Defined.

Definition add_nats_nat (m n:Nat):Nat.
infer (add m n).
Defined.


Notation refl := (fun v => v = v).

Notation rInt := (Int refl).
Definition max (x y: rInt) :=
  match dec(` x >? ` y) with
  | left e => ltac:(infer x)
  | right e => ltac: (infer y)
  end  : {v:Z | v>= ` x /\ v >= ` y}.

Definition abs (x:rInt) :=
  match dec (` x >=? 0) with
  | left e => ltac:(infer x)
  | right e => ltac:(infer (sub (triv 0) x))
  end
: {v:Z | v>= 0 /\  v >= (` x) }.
Require Import ssreflect.

Definition sub_5_4_nat: {v:Z | v<>0}. upcast (sub (triv 5) (triv 4)). Defined.

Definition mul_nats_nat (m n:Nat):Nat.
infer (mul m n).
Defined.

Definition gem1_ltm1_nat (m:{v:Z| v>= -1}) (H: ` m > -1): Nat. exists (`m). lia. Defined.

