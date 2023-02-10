(* Posted by Eric Jaeger in:
 * https://coq-club.inria.narkive.com/84wy4cCg/ltac-iteration-on-all-hypothesis
*)
(* Basic
definition ------------------------------------------------------------------------------*)

Definition typeof(T:Type)(t:T) := T.
Arguments typeof [T].
(* (typeof t) is similar to (type of t) but is an expression instead of a
tactic. This for example
allow for using (unify (typeof t) T) instead of let T':=type of t in
unify T' T. *)

(* Application to a given
hypothesis -------------------------------------------------------------*)

Inductive _context_ :=
| _ctx_nil_ : _context_
| _ctx_cns_ : forall (T:Type), T -> _context_ -> _context_.
(* A type to store coq proof contexts *)

Ltac _ctx_mem_ T t c :=
match c with
| _ctx_nil_ => false
| _ctx_cns_ ?T' ?t' ?c' => match T with
| T' => match t with t' => true | _ => _ctx_mem_
T t c' end
| _ => _ctx_mem_ T t c'
end
end.
(* Test whether or not (T,t) is a member of context c *)

Ltac _ctx_lgt_ c :=
match c with
| _ctx_nil_ => constr:(0)
| _ctx_cns_ _ _ ?c' => let l := _ctx_lgt_ c' in constr:(S l)
end.
(* Returns the length of context c *)

Ltac build_context_ acc :=
match goal with
| [ H:?T|-_ ] => match _ctx_mem_ T H acc with false => build_context_
(_ctx_cns_ T H acc) end
| _ => acc
end.
(* Returns a context (a list of type,value pairs) with all hypotheses; note
that we browse hyps
using backtracking, and that to avoid to use the tactic fail (not
compatible with this tactic
returning a value) backtracking is caused by incomplete pattern matching
*)

Ltac get_nth_ n :=
let ctx := build_context_ _ctx_nil_ in
let rec gn_ n c :=
match c with _ctx_cns_ ?t' ?h' ?c' => match n with 1 => h' | S ?n' => gn_
n' c' end end
in gn_ n ctx.
(* Returns the identifier of the "n"th hypothesis in the context (first at
top) *)

Tactic Notation "exec" tactic(T) "on" "hyp" constr(E) := let H := get_nth_ E
in T H.

(* Mapping to all
hypotheses ---------------------------------------------------------------------*)

Ltac map_hyps_ T :=
let c := build_context_ _ctx_nil_ in
let rec mh_ c := match c with _ctx_cns_ ?t' ?h' ?c' => mh_ c'; T h' |
_ctx_nil_ => idtac end
in mh_ c.
(* Note that we prefer to build the context once and to use it, rather than
invoking get_nth_ that
rebuilds the context each time *)

Tactic Notation "exec" tactic(T) "on" "hyps" := map_hyps_ ltac:(T).
(* In a context "H1 ... Hn", invoke "T Hn", ..., "T H1" *)

Tactic Notation "exec" tactic(T) "on" "hyps" "except" ident(I) :=
map_hyps_ ltac:(fun X=>match X with I => idtac | _ => T X end).
(* In a context "H1 ... Hx ... Hn", invoke "T Hn", ..., "T Hx+1", "T Hx-1",
..., "T H1" *)

Tactic Notation "exec" tactic(T) "on" "hyps" "in" constr(E) :=
map_hyps_ ltac:(fun X=>try (unify (typeof X) E; T X)).
(* In a context "H1 ... Hn", invoke "T Hn" if "Hn:E", ..., "T H1" if "H1:E"
*)

(* Mapping to pairs of
hypotheses ----------------------------------------------------------------*)

Ltac map_pairs_ T :=
let c := build_context_ _ctx_nil_ in
let rec mp_ c1 c2 :=
match c1 with
| _ctx_cns_ ?t1' ?h1' ?c1' => match c2 with
| _ctx_cns_ ?t2' ?h2' ?c2' => mp_ c1 c2';
match h1' with
|
h2' => idtac
|
_ => T h1' h2'
end
| _ctx_nil_ => mp_ c1' c1'
end
| _ctx_nil_ => idtac
end
in mp_ c c.

Tactic Notation "exec" tactic(T) "on" "pairs" := map_pairs_ ltac:(T).
(* In a context "H1 ... Hn", invoke "T Hn-1 Hn", "T Hn-2 Hn", "T Hn-2 Hn-1",
..., "T H1 H2",
"T H1 H1" (that is invocation over all pairs "Hi" and "Hj" with i<j) *)

Tactic Notation "exec" tactic(T) "on" "pairs" "in" constr(E) :=
map_pairs_ ltac:(fun X Y=>try (first [ unify (typeof X) E | unify (typeof
Y) E ]; T X Y)).
(* As for "exec on pairs", except that at least one of the components has to
be in "E" *)

Tactic Notation "exec" tactic(T) "on" "pairs" "in" constr(E1) "and"
constr(E2) :=
map_pairs_ ltac:(fun X Y=>try (first [ unify (typeof X) E1; unify (typeof
Y) E2
| unify (typeof X) E2; unify (typeof
Y) E1]; T X Y)).
(* As for "exec on pairs", except that one component has to be in "E1" and
the other in "E2" *)

(* Mapping to couples of
hypotheses --------------------------------------------------------------*)

Ltac map_couples_ T :=
let c := build_context_ _ctx_nil_ in
let rec mc_ c1 c2 :=
match c1 with
| _ctx_cns_ ?t1' ?h1' ?c1' => match c2 with
| _ctx_cns_ ?t2' ?h2' ?c2' => mc_ c1 c2'; T
h1' h2'
| _ctx_nil_ => mc_ c1' c
end
| _ctx_nil_ => idtac
end
in mc_ c c.

Tactic Notation "exec" tactic(T) "on" "couples" := map_couples_ ltac:(T).
(* In a context "H1 ... Hn", invoke "T Hn Hn", "T Hn Hn-1", ..., "T Hn H1",
"T Hn-1 Hn", ...,
"T H1 Hn", ... "T H1 H1" *)

Tactic Notation "exec" tactic(T) "on" "true" "couples" :=
map_couples_ ltac:(fun X Y=>match X with Y => idtac | _ => T X Y end).
(* In a context "H1 ... Hn", invoke "T Hn Hn-1", ..., "T Hn H1", "T Hn-1
Hn", "T Hn-1 Hn-2", ...,
"T H1 Hn", ... "T H1 H2" (all couples except the reflexive ones) *)

Tactic Notation "exec" tactic(T) "on" "couples" "in" constr(E1) "*"
constr(E2) :=
map_couples_ ltac:(fun X Y=>try (unify (typeof X) E1; unify (typeof Y) E2;
T X Y)).
(* As for "exec on couples" except the pair has to be in E1*E2 *)

Tactic Notation "exec" tactic(T) "on" "true" "couples" "in" constr(E1) "*"
constr(E2) :=
map_couples_ ltac:(fun X Y=>match X with
| Y => idtac
| _ => try (unify (typeof X) E1; unify (typeof
Y) E2; T X Y)
end).
(* As for "exec on true couples" except the pair has to be in E1*E2 *)

Tactic Notation "exec" tactic(T) "on" "couples" "in" constr(E) "*" "_" :=
map_couples_ ltac:(fun X Y=>try (unify (typeof X) E; T X Y)).

Tactic Notation "exec" tactic(T) "on" "true" "couples" "in" constr(E) "*"
"_" :=
map_couples_ ltac:(fun X Y=>match X with
| Y => idtac
| _ => try (unify (typeof X) E; T X Y)
end).

Tactic Notation "exec" tactic(T) "on" "couples" "in" "_" "*" constr(E) :=
map_couples_ ltac:(fun X Y=>try (unify (typeof Y) E; T X Y)).

Tactic Notation "exec" tactic(T) "on" "true" "couples" "in" "_" "*"
constr(E) :=
map_couples_ ltac:(fun X Y=>match X with
| Y => idtac
| _ => try (unify (typeof Y) E; T X Y)
end).

(* Additional
tools ------------------------------------------------------------------------------*)

Tactic Notation "remove" "duplicates" :=
exec (fun X Y=>try (unify (typeof X) (typeof Y); first [clear Y | clear
X])) on pairs.
(* In a context with "Hi:T Hj:T", try to clear "Hj", then if unsuccessful
"Hi" *)

Ltac rem_occ_ n T :=
match n with
| 0 => exec (fun X=>try (clear X)) on hyps in (typeof T)
| S ?n' => exec (fun X=>try (rem_occ_ n' (T X))) on hyps
end.

Tactic Notation "remove" "instances" constr(n) "of" constr(E) := try
(rem_occ_ n E).
(* Remove n-instances of E, that is hypotheses of the form "E x1 x2 ... xn"
*)

Tactic Notation "remove" "all" "instances" "of" constr(E) :=
try (rem_occ_ 5 E); try (rem_occ_ 4 E); try (rem_occ_ 3 E); try (rem_occ_ 2
E);
try (rem_occ_ 1 E); try (rem_occ_ 0 E).
(* Remove all instances of E, that is hypotheses of the form "E", "E x", "E
x1 x2", etc. *)

Tactic Notation "new" constr(E) "as" ident(I) :=
match goal with [ _:?T|-_ ] => unify T (typeof E) | _ => generalize E;
intro I end.
(* Creates an hypothesis "I:E" provided no other hypothesis of type "E"
exists *)

Ltac symm_sat_ H := exec (fun X=>try (let H' := fresh X in new (@H _ _ X) as
H')) on hyps.
Tactic Notation "close" "by" "symmetry" constr(E) := symm_sat_ E.
(* Generate new results from hypotheses and symmetry "H:forall x y, R x y->R
y x" *)

Ltac trans_sat_ H :=
repeat (exec (fun X Y=>try (let H' := fresh X Y in new (@H _ _ _ X Y) as
H')) on couples).
Tactic Notation "close" "by" "transitivity" constr(E) := trans_sat_ E.
(* Generate new results from hypotheses and transitive "H:forall x y z, R x
y->R y z->R x z" *)

Ltac asym_sat_ H :=
repeat (exec (fun X Y=>try (let H' := fresh X Y in new (@H _ _ X Y) as H'))
on couples).
Tactic Notation "close" "by" "antisymmetry" constr(E) := asym_sat_ E.
(* Generate new results from hypotheses and antisymmetry "H:forall x y z, R
x y->R y x->_" *)

(*================================================================================================*)