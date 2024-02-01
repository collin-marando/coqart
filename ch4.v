
Require Import Arith.
Require Import ZArith.
Require Import FunctionalExtensionality.

Open Scope nat_scope.

(* Exercise 4.1 *)
(* Show that the following types are well-formed in the
  Calculus of Constructions. For each of them, cite an
  example of a concept that could be represented by terms
  of this type. *)

(* 1. (nat -> nat) -> Prop *)
(* Var: nat : Set *)
(* Prod-Set: nat -> nat : Set *)
(* Prod-dep: (nat -> nat) -> Prop : Type *)

Definition type1 := (nat -> nat) -> Prop.
Definition involutive : type1 :=
  fun f => forall n, f (f n) = n.

Check involutive.

Example ident_involutive : involutive (fun n => n).
Proof. unfold involutive; auto. Qed.

(* 2. (nat -> nat) -> (nat -> nat) -> Prop *)
(* Var: nat : Set *)
(* Prod-Set: nat -> nat : Set *)
(* Prod-dep: (nat -> nat) -> Prop : Type *)
(* Prod-dep: (nat -> nat) -> (nat -> nat) -> Prop : Type *)

Definition type2 := (nat -> nat) -> (nat -> nat) -> Prop.
Definition twice n := n + n.
Definition doubl n := 2 * n.

Definition same_func : type2 := fun f g => f = g.

Check same_func.

Goal same_func twice doubl.
Proof.
  unfold same_func, twice, doubl.
  extensionality n.
  unfold mult; auto.
Qed.

(* nat -> nat -> Set *)
(* Var: nat : Set *)
(* Prod-dep : nat -> Set : Type *)
(* Prod-dep : nat -> nat -> Set : Type *)

Definition type3 := nat -> nat -> Set.

Inductive matrix_2d : type3 := 
  | mat_2d rows cols : matrix_2d rows cols.

Check matrix_2d.

(* Exercise 4.2 *)
(* What are the values of the implicit arguments for
  the uses of the thrice function in the example below? *)

Set Implicit Arguments.
Definition compose (A B C:Set) (f:A -> B) (g:B -> C) (a:A) := g (f a).
Definition thrice (A:Set) (f:A->A) := compose f (compose f f).
Unset Implicit Arguments.

Print Implicit compose.
Print Implicit thrice.

(* The implicit arguments are:
    A B C in compose
    A in thrice
*)

(* Example: A = nat is inferred *)
Compute (thrice S 3).

Eval cbv beta delta in (thrice (thrice (A:=nat)) S 0).

Check (thrice (thrice (A:=nat))).

(* In this evaluation, the inner thrice has its argument
  A expressed explicitly as having value _nat_.
  This means _thrice (A:= nat)_ has type _(nat->nat)->nat->nat_.
  The outer use of thrice takes this as its first explicit
  argument: f. f asks for a type _A->A_, and since
  _thrice (A:= nat)_ has type _(nat->nat)->nat->nat_,
  A is implicitly derived to be _nat->nat_.
    
  In chruch numerals, this depth of composistion is
  equivalent to exponentiation. _thrice S_ being 3, 
  _thrice thrice S_ would be 3^3 = 27.
*)

(* Exercise 4.3 *)
(* In the context of the following section, verify that
  the three theorems have well-formed statements and then
  construct terms that inhabit these types. *)
Section A_declared.
Variables (A:Set)(P Q:A->Prop)(R:A->A->Prop).

Theorem all_perm : (forall a b, R a b) -> forall a b, R b a.
Proof. exact (fun H a b => H b a). Qed.

Theorem all_imp_dist :
  (forall a, P a -> Q a) -> (forall a, P a) -> (forall a, Q a).
Proof. exact (fun HPQ HP a => (HPQ a) (HP a)). Qed.

Theorem all_delta : (forall a b, R a b) -> forall a, R a a.
Proof. exact (fun HR a => HR a a). Qed.

End A_declared.

Check all_perm.
Definition eq_sym := all_perm nat eq.
Locate "_ < _".
Definition neqz_impl_gtz := all_imp_dist nat (fun n => not (eq 0 n)) (lt 0).
Print neqz_impl_gtz.

(* Exercise 4.4 *)
(* For each of the following specifications, check that it is a
well-formed type of sort Type and build a function realizing this
specification. *)

(* Note: Playing around a bit with what's asked for this question
  to cement some ideas and show competency. Below, several approaches
  are used. Not all of these are what's asked for, but I show that
  they're all effectively equivalent approaches.
*)

(* Check spec is of type _Type_ *)
Definition id_type := forall A : Set, A->A.
Check id_type.
(* We can define a function on this type *)
Definition id : id_type := fun A a => a.
(* This can be expressed more cleanly by moving inputs to lhs *)
Definition id' (A:Set) (a:A) := a.

(* Alternatively, we can define the type and prove well-formed *)
Definition diag : forall A B : Set, (A -> A -> B) -> A -> B.
Proof. intros A B f a; exact (f a a). Qed.

(* We can absorb the intros into the construction of the solution *)
Definition permute : forall A B C : Set, (A->B->C)->B->A->C.
Proof. exact (fun A B C f b a => f a b). Qed.
  
(* And finally, we can drop the proof mode by assigning directly *)
Definition f_nat_Z : forall A : Set, (nat->A)->Z->A := 
  fun A f z => f (Z.to_nat z).

(* Which ultimately brings us back direct definition with inputs on rhs *)

(* Exercise 4.5 *)
(* For the following theorems, check that the statement is a
  well-formed proposition, perform the proof, and exhibit the
  proof term. *)

Definition all_perm' := forall (A : Type) (P : A -> A -> Prop),
  (forall x y:A, P x y) -> forall x y: A, P y x.
Check all_perm'.

Goal all_perm'.
Proof.
  intros A R H x y.
  apply H.
Qed.

Definition proof1 : all_perm' := fun A' R' H x y => H y x.

Definition resolution := forall (A : Type) (P Q R T : A -> Prop),
  (forall a:A, Q a -> R a -> T a) ->
  (forall b:A, P b -> Q b) -> (forall e:A, P e -> R e -> T e).
Check resolution.

Goal resolution.
Proof.
  intros A P Q R T HQRT HPQ.
  intros e Pe Re.
  apply (HQRT e).
  - apply (HPQ e), Pe.
  - apply Re.
Qed.

Goal resolution.
Proof.
  intros A P Q R T HQRT HPQ e Pe Re.
  apply (HQRT e).
  - exact (HPQ e Pe).
  - exact Re.
Qed.

Goal resolution.
Proof.
  intros A P Q R T HQRT HPQ e Pe Re.
  exact (HQRT e (HPQ e Pe) Re).
Qed.

Definition proof2 : resolution :=
  fun A P Q R T HQRT HPQ e Pe Re => HQRT e (HPQ e Pe) Re.