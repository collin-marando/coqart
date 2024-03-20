Require Import List.
Import ListNotations.

Set Implicit Arguments.

CoInductive LList (A:Set) : Set := 
  | LNil: LList A
  | LCons : A -> LList A -> LList A.

Arguments LNil {A}.

(* Exercise 13.1 *)
(* Define an injection mapping every list of type "listA"
  to a list of type "LList A" and prove that it is injective. *)

Fixpoint list_LList {A : Set} (l : list A) : LList A :=
  match l with
  | nil => LNil
  | a :: l' => LCons a (list_LList l')
  end.

Theorem list_LList_inj : forall (A : Set) (l l': list A),
  list_LList l = list_LList l' -> l = l'.
Proof.
  induction l; simpl; intros.
  - destruct l'; auto. discriminate.
  - destruct l'. discriminate.
    simpl in H. inversion H.
    f_equal. auto.
Qed.

(* Exercise 12 *)
(* Define predicates and access functions for the type of lazy binary trees:

  • is_LLeaf: to be a leaf,
  • L_root: the label of the tree root (when it exists),
  • L_left_son,
  • L_right_son,
  • L_subtree: yields the subtree given by a path from the root (when it exists),
  • Ltree_label: yields the label of the subtree given by a path from the root
    (when it exists).

The paths are described as lists of directions where a direction is defined as follows:
  Inductive direction: Set:= dO (* left *) | d1 (* right *)
*)

Inductive direction: Set := dO (* left *) | d1 (* right *).

CoInductive LTree (A:Set) : Set := 
  | LLeaf: LTree A
  | LBin : A -> LTree A -> LTree A -> LTree A.

Arguments LLeaf {A}.

Definition is_LLeaf {A : Set} (t : LTree A) : Prop :=
  match t with
  | LLeaf => True
  | _ => False
  end.

Definition L_root {A : Set} (t : LTree A) : option A :=
  match t with
  | LLeaf => None
  | LBin a _ _ => Some a 
  end.

Definition L_left_son {A : Set} (t : LTree A) : option (LTree A) :=
  match t with
  | LLeaf => None
  | LBin _ l  _ => Some l
  end.

Definition L_right_son {A : Set} (t : LTree A) : option (LTree A) :=
  match t with
  | LLeaf => None
  | LBin _ _ r => Some r
  end.

Fixpoint L_subtree {A : Set} (p: list direction) (t : LTree A) : option (LTree A) :=
  match p with
  | nil => Some t
  | dO :: p' =>
    match L_left_son t with
    | None => None
    | Some t' => L_subtree p' t'
    end
  | d1 :: p' =>
    match L_right_son t with
    | None => None
    | Some t' => L_subtree p' t'
    end
  end.

Definition Ltree_label {A : Set} (p: list direction) (t : LTree A) : option A :=
  match L_subtree p t with
  | Some (LBin a _ _) => Some a
  | _ => None
  end.

(* Exercise 13.3 *)
(* Build a binary tree containing all strictly positive integers. *)

Definition from_tree : nat -> LTree nat :=
  (cofix F (n : nat) :=
    LBin n (F (S n)) (F (S n))).

Definition Nats_Tree : LTree nat := from_tree 0.

Compute (Ltree_label [d1; d1; d1] Nats_Tree).

Fixpoint n_copies {A: Set} (n : nat) (v: A) : list A :=
  match n with O => nil | S n' => v :: n_copies n' v end.

Compute (Ltree_label (n_copies 123 d1) Nats_Tree).

(* Exercise 13.4 *)
(* Define a function graft on "LTree A" so that "graft t t'"
  is the result of replacing all leaves of t by t' *)

CoFixpoint graft {A : Set} (t t': LTree A) : LTree A :=
  match t with
  | LLeaf => t'
  | LBin a l r => LBin a (graft l t') (graft r t')
  end.

(* Exercise 13.5 *)
(* Define the functional with the following type
  LMap: forall A B:Set, (A->B) -> LList A -> LList B
such that "LMap f l" is the list of images by f of all elements of l.
Can you define the functional with the following type
  LMapcan: forall A B:Set, (A->(LList B)) -> LList A -> LList B
such that "LMap f l" is the concatenation using LAppend of the images by f of all elements of l? *)

Definition LMap {A B:Set} (f: A -> B) : LList A -> LList B :=
  cofix F (l: LList A) :=
    match l with
    | LNil => LNil
    | LCons a l' => LCons (f a) (F l')
    end.

CoFixpoint LAppend (A:Set) (u v:LList A) : LList A :=
  match u with
  | LNil => v
  | LCons a u' => LCons a (LAppend u' v)
  end.

(* 
  Definition LMapcan {A B:Set} (f: A -> (LList B)) : LList A -> LList B :=
    cofix F (l: LList A) :=
      match l with
      | LNil => LNil
      | LCons a l' => LAppend (f a) (F l')
      end.

  LMapcan cannot be defined because the call of LAppend is 
  unguarded, and thus can produce loops.

  For example, if the function f returned LNil for all elements
  of the inifinite input list l, then trying to get the first
  element of the output list would be a non-teminating evaluation.
*)


(* Exercise 13.6 *)
(* Follow the same approach for the type of potentially infinite binary trees. *)

Definition LTree_decompose {A: Set} (t:LTree A) : LTree A :=
  match t with
  | LLeaf => LLeaf
  | LBin a l r => LBin a l r
  end.

Theorem LTree_decompose_eq: forall A (t: LTree A), t = LTree_decompose t.
Proof.
  intros. destruct t; auto.
Qed.

(* End 13.6 *)

(* Exercise 13.7 *)
(* Define a function List_decomp_n with type
    forall A:Set, nat -> LList A -> LList A
  that iterates the function LList_decompose.
  Generalize the decomposition lemma to this function.
*)

Definition LList_decompose {A:Set} (l:LList A) : LList A :=
  match l with
  | LNil => LNil
  | LCons a l' => LCons a l'
  end.

Fixpoint LList_decomp_n {A:Set} (n: nat) (l:LList A) : LList A :=
  match n with
  | O => l
  | S n' =>
    match l with
    | LNil => LNil
    | LCons a l' => LCons a (LList_decomp_n n' l')
    end
  end.

Eval simpl in (LAppend (LCons 0 (LCons 1 LNil)) (LCons 2 (LCons 3 LNil))).
(* = LAppend (LCons 0 (LCons 1 LNil)) (LCons 2 (LCons 3 LNil)) : LList nat *)

Eval simpl in (LList_decomp_n 3 (LAppend (LCons 0 (LCons 1 LNil)) (LCons 2 (LCons 3 LNil)))).
(* = LCons 0 (LCons 1 (LCons 2 (LCons 3 LNil))) : LList nat *)

Lemma LList_decomp_n_eq : forall A n (l:LList A), l = LList_decomp_n n l.
Proof.
  induction n; simpl; intros; auto.
  destruct l; auto.
  rewrite <- IHn; auto.
Qed.

(* End 13.7 *)

Theorem LList_decompose_eq: forall (A:Set) (l:LList A), l = LList_decompose l.
Proof.
  intros A l; case l; trivial.
Qed.

Ltac LList_unfold term :=
  apply trans_equal with (1 := LList_decompose_eq term).

Theorem LAppend_LNil: forall (A:Set) (v:LList A), LAppend LNil v = v.
Proof.
  intros A v.
  LList_unfold (LAppend LNil v).
  case v; simpl; auto.
Qed.

Theorem LAppend_LCons : forall (A:Set) (a:A) (u v:LList A),
  LAppend (LCons a u) v = LCons a (LAppend u v). 
Proof.
  intros A a u v.
  LList_unfold (LAppend (LCons a u) v).
  case v; simpl; auto.
Qed.

Hint Rewrite LAppend_LNil LAppend_LCons: core.

(* Exercise 13.8 *)
(* Prove the unfolding lemmas for the example functions defined in this chapter:*)

CoFixpoint from (n:nat) : LList nat := LCons n (from (S n)).
CoFixpoint repeat (A:Set) (a:A) : LList A := LCons a (repeat a).

CoFixpoint general_omega (A:Set) (u v:LList A) : LList A :=
  match v with
  | LNil => u
  | LCons b v' =>
    match u with
    | LNil => LCons b (general_omega v' v)
    | LCons a u' => LCons a (general_omega u' v)
    end
  end.

Definition omega (A:Set) (u:LList A) : LList A := general_omega u u.

Lemma from_unfold : forall n:nat, from n = LCons n (from (S n)).
Proof.
  intros n.
  LList_unfold (from n).
  simpl; auto.
Qed.

Lemma repeat_unfold : forall (A:Set) (a: A), repeat a = LCons a (repeat a).
Proof.
  intros A a.
  LList_unfold (repeat a).
  simpl; auto.
Qed.

Lemma general_omega_LNil: forall A:Set, omega LNil = LNil (A := A).
Proof.
  intros.
  LList_unfold (omega LNil (A := A)).
  simpl; auto.
Qed.

Lemma general_omega_LCons : forall (A:Set) (a:A) (u v: LList A),
  general_omega (LCons a u) v = LCons a (general_omega u v).
Proof.
  intros.
  LList_unfold (general_omega (LCons a u) v); simpl.
  destruct v; auto.
  f_equal; symmetry.
  LList_unfold (general_omega u LNil); simpl.
  destruct u; auto.
Qed.
  
Lemma general_omega_LNil_LCons : forall (A:Set) (a:A) (u:LList A),
  general_omega LNil (LCons a u) = LCons a (general_omega u (LCons a u)).
Proof.
  intros.
  LList_unfold (general_omega LNil (LCons a u)).
  simpl; auto.
Qed.

(* Conclude with the following lemma: *)

Lemma general_omega_shoots_again : forall (A:Set) (v:LList A),
  general_omega LNil v = general_omega v v.
Proof.
  intros.
  destruct v; auto.
  symmetry.
  LList_unfold (general_omega (LCons a v) (LCons a v)); simpl.
  rewrite general_omega_LNil_LCons; auto.
Qed.

(* End 13.8 *)

(* Exercise 13.9 *)
(* Prove the unfolding lemmas for the function graft defined in Exercise 13.4. *)

Ltac LTree_unfold term :=
  apply trans_equal with (1 := LTree_decompose_eq term).

Lemma graft_LLeaf_unfold : forall (A:Set) (t':LTree A),
  graft LLeaf t' = t'.
Proof.
  intros.
  LTree_unfold (graft LLeaf t').
  simpl; destruct t'; auto.
Qed.

Lemma graft_LBin_unfold : forall (A:Set) (a:A) (t' l r:LTree A),
  graft (LBin a l r) t' = LBin a (graft l t') (graft r t').
Proof.
  intros.
  LTree_unfold (graft (LBin a l r) t').
  simpl; auto.
Qed.

(* End 13.9 *)

Inductive Finite (A:Set) : LList A -> Prop :=
  | Finite_LNil : Finite LNil
  | Finite_LCons : forall (a:A) (l:LList A),
    Finite l -> Finite (LCons a l).
    
Hint Resolve Finite_LNil Finite_LCons: core.

(* Exercise 13.10 *)
(* Prove the following lemma that expresses how the function omega
  iterates on its argument. Note that this theorem is restricted to
  finite streams. This is a partial solution to the problem
  described in Remark 13.1. *)

Lemma general_omega_of_Finite:
  forall (A:Set) (u:LList A), Finite u ->
    forall v:LList A, general_omega u v = LAppend u (general_omega v v).
Proof.
  induction 1; intros.
  - rewrite LAppend_LNil, general_omega_shoots_again; auto.
  - rewrite general_omega_LCons, LAppend_LCons.
    f_equal. auto.
Qed.

Theorem omega_of_Finite : forall (A: Set) (u: LList A),
  Finite u -> omega u = LAppend u (omega u).
Proof.
  induction 1.
  - rewrite LAppend_LNil; auto.
  - rewrite LAppend_LCons.
    LList_unfold (omega (LCons a l)).
    simpl. f_equal.
    rewrite general_omega_of_Finite; auto.
Qed.

(* End 13.10 *)

(* Exercise 13.11 *)
(* Define the predicate on "LTree A" which characterizes finite trees.
  Prove the equality
    graft t (LLeaf A) = t
  for every finite tree t. *)

Inductive Finite_T (A:Set) : LTree A -> Prop :=
  | Finite_LLeaf : Finite_T LLeaf
  | Finite_LBin : forall a l r,
      Finite_T l -> Finite_T r -> Finite_T (LBin a l r).

Goal forall A t, Finite_T t -> graft t (LLeaf (A := A)) = t.
Proof.
  induction 1.
  - rewrite graft_LLeaf_unfold; auto.
  - rewrite graft_LBin_unfold.
    f_equal; auto.
Qed.

(* End 13.11 *)

CoInductive Infinite (A:Set) : LList A -> Prop :=
  Infinite_LCons: forall (a:A) (l:LList A),
    Infinite l -> Infinite (LCons a l).

Hint Resolve Infinite_LCons : core.

(* Exercise 13.12 *)
(* Prove the following lemmas, using the cofix tactic: *)

Lemma repeat_infinite: forall (A:Set) (a:A), Infinite (repeat a).
Proof.
  intros.
  cofix H.
  rewrite (repeat_unfold).
  auto.
Qed.

Lemma general_omega_infinite: forall (A:Set) (a:A) (u v:LList A),
  Infinite (general_omega v (LCons a u)).
Proof.
  intros A a.
  cofix H.
  intros.
  destruct v.
  1: rewrite general_omega_shoots_again.
  all: rewrite general_omega_LCons; auto.
Qed.

(* Conclude with the following theorem: *)

Theorem omega_infinite: forall (A: Set) (a:A) (l:LList A),
  Infinite (omega (LCons a l)).
Proof.
  intros.
  unfold omega.
  apply general_omega_infinite.
Qed.

(* Exercise 13.13 A distracted student confuses keywords and gives
  an inductive definition of being infinite: *)

Inductive BugInfinite (A:Set) : LList A -> Prop :=
  BugInfinite_intro: forall (a:A) (l: LList A),
    BugInfinite l -> BugInfinite (LCons a l).
  
(* Show that this predicate can never be satisfied. *)

Goal forall A l, ~ BugInfinite l (A := A).
Proof.
  intros; intro.
  induction H.
  assumption.
Qed.

(* Exercise 13.14 *)
(* Define the predicates "to have at least one infinite branch" and
  "to have all branches infinite" for potentially infinite binary trees
  (see Sect. 13.1.5). Consider similar predicates for finite branches.
  Construct a term that satisfies each of these predicates and prove it.
  Study the relationships between these predicates; beware that the
  proposition statement:
  "If a tree has no finite branch, then it contains an infinite branch"
  can only be proved using classical logic, in other words with the following
  added axiom: *)

  Axiom double_neg : forall P: Prop, ~~P -> P.

CoInductive HasInfinite (A:Set) : LTree A -> Prop :=
  | HInf_left: forall a l r, HasInfinite l -> HasInfinite (LBin a l r)
  | HInf_right: forall a l r, HasInfinite r -> HasInfinite (LBin a l r).

CoInductive AllInfinite (A:Set) : LTree A -> Prop :=
  | AInf: forall a l r,
    AllInfinite l -> AllInfinite r -> AllInfinite (LBin a l r).

(* The predicates for Finite can be Inductive rather than CoInductive, yielding induction priciples *)

Inductive HasFinite (A:Set) : LTree A -> Prop :=
  | HFin_LLeaf: HasFinite LLeaf
  | HFin_left: forall a l r, HasFinite l -> HasFinite (LBin a l r)
  | HFin_right: forall a l r, HasFinite r -> HasFinite (LBin a l r).

Inductive AllFinite (A:Set) : LTree A -> Prop :=
  | AFin_LLeaf: AllFinite LLeaf
  | AFin: forall a l r, AllFinite l -> AllFinite r -> AllFinite (LBin a l r).

Hint Constructors HasInfinite AllInfinite HasFinite AllFinite : core.

(* We can still use a CoInductive predicate for finite recursions,
  but the Inductive definitions are more useful for the upcoming
  exercises. Note that the relation between these two definitions
  is a one-way implication and not a bijection.
*)

CoInductive CoAllFinite (A:Set) : LTree A -> Prop :=
  | CoAFin_LLeaf: CoAllFinite LLeaf
  | CoAFin: forall a l r, CoAllFinite l -> CoAllFinite r -> CoAllFinite (LBin a l r).

Lemma AllFinite_CoAllFinite : forall A t, AllFinite t -> CoAllFinite t (A := A).
Proof.
  intros A.
  cofix H; intros t HAF.
  destruct HAF;
  constructor; auto.
Qed.

(* Instance of HasInfinite: Nats_Tree (Exercise 13.3) *)

Lemma from_tree_unfold : forall n,
  from_tree n = LBin n (from_tree (S n)) (from_tree (S n)).
Proof.
  intros.
  LTree_unfold (from_tree n).
  simpl; auto.
Qed.

Lemma HasInf_from_tree : forall n, HasInfinite (from_tree n).
Proof.
  cofix H.
  intros n.
  rewrite from_tree_unfold.
  auto.
Qed.
  
Goal HasInfinite Nats_Tree.
Proof HasInf_from_tree 0.

(* Instance of AllInfinite: Nats_Tree (Exercise 13.3) *)

Lemma AllInf_from_tree : forall n, AllInfinite (from_tree n).
Proof.
  cofix H.
  intros n.
  rewrite from_tree_unfold.
  auto.
Qed.

Goal AllInfinite Nats_Tree.
Proof AllInf_from_tree 0.

(* Instances of HasFinite and AllFinite *)

Goal HasFinite (LBin 0 LLeaf Nats_Tree).
Proof. auto. Qed.

Goal AllFinite (LBin 0 LLeaf (LBin 1 LLeaf LLeaf)).
Proof. auto. Qed.

(* Relationships between the predicates *)
(* 
  The relationships are as follows:
    All Inf -> Has Inf
    All Fin -> Has Fin
    All Inf <-> ~ Has Fin
    All Fin <-> ~ Has Inf
  
  For the latter two, there is also the inverse and contrapositive.
  For each, we can show either the forward implication or the contrapositive.
  Similiraily, we can show either the converse implication or the inverse.
  
  These ones are chosen to show the various types of proofs that occur
  between inductive and coinductive types and their negations.

  With a few logical lemmas, some using the extra axiom,
  we have the freedom to choose which implications to prove.
*)

Lemma demorgan_nand : forall P Q: Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros.
  apply double_neg.
  contradict H.
  split; apply double_neg; contradict H; auto.
Qed.

Lemma contrapositive : forall P Q: Prop, (P -> Q) -> (~ Q -> ~ P).
Proof. intros P Q HImp H; contradict H; auto. Qed.

Lemma contrapositive_inv : forall P Q: Prop, (~ Q -> ~ P) -> (P -> Q).
Proof.
  intros.
  apply double_neg.
  intro HNQ.
  apply H; auto.
Qed.

Lemma neg_converse_inverse : forall P Q: Prop, (~ P -> Q) -> (~ Q -> P).
Proof.
  intros.
  apply double_neg.
  intro; auto.
Qed.

Lemma negation_converse : forall P Q: Prop, (P -> ~ Q) -> (Q -> ~ P).
Proof. auto. Qed.

(* Properties of predicates *)

Lemma Not_AllFinite_LBin : forall A a l r,
  ~ AllFinite (LBin a l r) -> ~ AllFinite l \/ ~ AllFinite r (A := A).
Proof.
  intros.
  apply demorgan_nand.
  contradict H.
  constructor; intuition.
Qed.

Lemma Not_HasFinite_LBin : forall A a l r,
  ~ HasFinite (LBin a l r) -> ~ HasFinite l /\ ~ HasFinite r (A := A).
Proof.
  intros.
  split; auto.
Qed.

(* Proofs of relationships *)

Theorem AllInfinite_HasInfinite : forall A t,
  AllInfinite t -> HasInfinite t (A := A).
Proof.
  intros A.
  cofix HRel.
  intros t H.
  inversion H.
  constructor; auto.
Qed.

Theorem AllFinite_HasFinite : forall A t,
  AllFinite t -> HasFinite t (A := A).
Proof.
  intros A t H.
  induction H; auto.
Qed.

Theorem AllInfinite_Not_HasFinite : forall A t,
  AllInfinite t -> ~ HasFinite t (A := A).
Proof.
  intros A t.
  apply negation_converse.
  intros.
  induction H; intro HF;
  inversion HF; contradiction.
Qed.

Theorem Not_AllInfinite_HasFinite : forall A t,
  ~ AllInfinite t -> HasFinite t (A := A).
Proof.
  intros A t.
  apply neg_converse_inverse.
  revert t.
  cofix HRel.
  intros t H.
  destruct t.
  - contradict H; auto.
  - apply Not_HasFinite_LBin in H as [Hl Hr];
    constructor; auto.
Qed.

Theorem AllInfinite_NoFinite_equiv :forall A t,
  AllInfinite t <-> ~ HasFinite t (A := A).
Proof.
  split.
  - apply AllInfinite_Not_HasFinite.
  - apply neg_converse_inverse, Not_AllInfinite_HasFinite.
Qed.

Theorem AllFinite_Not_HasInfinite : forall A t,
  AllFinite t -> ~ HasInfinite t (A := A).
Proof.
  intros A t AF.
  induction AF; intro.
  - inversion H.
  - inversion H; contradiction.
Qed.

Theorem Not_AllFinite_HasInfinite : forall A t,
  ~ AllFinite t -> HasInfinite t (A := A).
Proof.
  intros A.
  cofix HRel.
  intros t H.
  destruct t.
  - contradict H; auto.
  - apply Not_AllFinite_LBin in H as [Hl | Hr]; auto.
Qed.

Theorem AllInfinite_NoInfinite_equiv :forall A t,
  AllFinite t <-> ~ HasInfinite t (A := A).
Proof.
  split.
  - apply AllFinite_Not_HasInfinite.
  - apply neg_converse_inverse, Not_AllFinite_HasInfinite.
Qed.

(* Exercise 13.15 *)
(* Prove the following statements: *)

Theorem Infinite_of_LCons: forall (A: Set) (a:A) (u:LList A), Infinite (LCons a u) -> Infinite u.
Proof.
  intros. inversion H; auto.
Qed.

Lemma LAppend_of_Infinite: forall (A: Set) (u: LList A), Infinite u -> forall v:LList A, Infinite (LAppend u v).
Proof.
  cofix HRel.
  intros A u H v.
  destruct u; inversion H.
  rewrite LAppend_LCons; auto.
Qed.

Lemma Finite_not_Infinite: forall (A:Set) (l:LList A), Finite l -> ~ Infinite l.
Proof.
  intros A l HF.
  induction HF; intro; inversion H.
  contradiction.
Qed.

Lemma Infinite_not_Finite: forall (A: Set) (l :LList A), Infinite l -> ~ Finite l.
Proof.
  intros.
  contradict H; revert H.
  apply Finite_not_Infinite.
Qed.

Lemma Not_Finite_Infinite: forall (A: Set) (l: LList A), ~ Finite l -> Infinite l.
Proof.
  cofix HRel.
  intros A l H.
  destruct l.
  - contradict H; auto.
  - constructor; auto.
Qed.

(* Exercise 13.16 *)
(* Prove the following two statement in the framework of classical logic. To do these proofs,
load the Classical module from the Coq library. *)

Require Import Classical.

Lemma Not_Infinite_Finite: forall (A: Set) (l: LList A), ~ Infinite l -> Finite l.
Proof.
  intros A l.
  apply neg_converse_inverse.
  apply Not_Finite_Infinite.
Qed.
  
Lemma Finite_or_Infinite: forall (A:Set) (l:LList A), Finite l \/ Infinite l.
Proof.
  intros.
  destruct (classic (Finite l)); auto.
  right. apply Not_Finite_Infinite; auto.
Qed.

(* Exercise 13.17 *)
(* The following definitions are valid in the Coq system: *)
Definition Infinite_ok (A:Set) (X:LList A -> Prop) := 
  forall l:LList A, X l ->
    exists a:A, (exists l':LList A, l = LCons a l' /\ X l').

Definition Infinite1 (A:Set) (l:LList A) :=
  exists X: LList A -> Prop, Infinite_ok X /\ X l.

(* Prove that the predicates Infinite and Infinitel are logically equivalent. *)

Lemma Not_Infinite1_LNil : forall A, ~ Infinite1 LNil (A := A).
Proof.
  intros; intro H.
  inversion H as [X [Hok HX]].
  unfold Infinite_ok in Hok.
  apply Hok in HX as [a [l' [Heq HX']]].
  discriminate.
Qed.

Lemma ok_LCons :
  forall (A : Set) (X:LList A -> Prop) (a:A) (l:LList A),
   Infinite_ok X -> X (LCons a l) -> X l.
Proof.
  unfold Infinite_ok.
  intros A X a l H H0.
  case (H (LCons a l (A := A))); auto.
  simple destruct 1; intros x0 H2; case H2; injection 1.
  simple destruct 1; auto.
Qed.

Lemma Infinite1_LCons : forall A a l, Infinite1 (LCons a l) -> Infinite1 l (A := A).
Proof.
  intros A a l [X [Hok HX]].
  exists (fun u => exists b, X (LCons b u)); split.
  - unfold Infinite_ok in *.
    intros l' [b HX'].
    apply ok_LCons in HX'; eauto.
    destruct (Hok l' HX') as [x [u [Heq HXu]]].
    exists x, u.
    split; auto.
    exists x; rewrite <- Heq; auto.
  - exists a; auto.
Qed.

Goal forall A l, Infinite l <-> Infinite1 l (A := A).
Proof.
  split; intros.
  - exists (Infinite (A := A)).
    split; auto.
    unfold Infinite_ok.
    intros l' H'.
    inversion H'.
    repeat eexists; auto.
  - revert l H.
    cofix HInf.
    intros l H.
    destruct l.
    + contradict H. apply Not_Infinite1_LNil.
    + inversion H.
      apply Infinite1_LCons in H.
      constructor; auto.
Qed.

(* End 13.17 *)

(* Exerpt from the textbook, leading into Exercise 13.18: *)

(* [...] consider the proof that concatenating any infinite stream
  to any other stream yields the first stream. Here is a first attempt
  to perform this proof: *)

Lemma Lappend_of_Infinite_o: forall (A: Set) (u: LList A),
  Infinite u -> forall v: LList A, u = LAppend u v.

(* The only tool at our disposal is a case analysis on the variable u.
  If we decompose u into "LCons a u'," we obtain a goal that is similar
  to the initial goal:
    
    H1 : Infinite u'
    v: LList A
    =======================
    u' = LAppend u'v

  We see that a finite numbers of these steps wil not make it possible to
  conclude. However, we can restrict our attention to a relation on streams
  that is weaker than equality but supports co-inductive reasoning. *)

(* Exercise 13.18 *)
(* Write the proof steps that lead ot this situation. *)
Proof.
  intros A u HInf v.
  inversion HInf as [a u' H1].
  clear dependent u.
  rewrite LAppend_LCons.
  f_equal.
Abort.

(* Exercise 13.19 *)
(* After loading the module Relations from the Coq library,
  show that bisimilar is an equivalence relation. Among other
  results, reflexivity shows that the bisimilar relation accepts
  more pairs of streams than equality. *)

CoInductive bisimilar {A:Set} : LList A -> LList A -> Prop :=
  | bisimO : bisimilar LNil LNil
  | bisim1 : forall (a:A) (l l':LList A),
    bisimilar l l' -> bisimilar (LCons a l) (LCons a l').

Hint Constructors bisimilar : core.

Require Import Relations.
Require Import Relation_Definitions.

Theorem bisim_refl : forall A, reflexive (LList A) bisimilar.
Proof.
  unfold reflexive.
  cofix H.
  destruct x; constructor; auto.
Qed.

Theorem bisim_sym : forall A, symmetric (LList A) bisimilar.
Proof.
  unfold symmetric.
  cofix HInd.
  intros A x y H.
  inversion H; constructor; auto.
Qed.

Theorem bisim_trans : forall A, transitive (LList A) bisimilar.
Proof.
  unfold transitive.
  cofix H.
  intros A x y z H1 H2.
  inversion H1; inversion H2; subst;
  try discriminate; auto.
  inversion H6; subst; eauto.
Qed.

Theorem bisimilar_equivalence : forall A:Set, equivalence (LList A) (bisimilar).
Proof.
  constructor.
  - apply bisim_refl.
  - apply bisim_trans.
  - apply bisim_sym.
Qed.

(* Exercise 13.20 *)
(* For a better understanding of the bisimilar relation, we can use
  the function LNth defined in Fig. 13.1. Show the following two
  theorems, which establish a relation between bisimilar and LNth: *)

Fixpoint LNth (A:Set) (n:nat) (l: LList A) : option A :=
  match l with
  | LNil => None
  | LCons a l' =>
    match n with
      | O => Some a
      | S n' => LNth n' l'
    end
  end.

Lemma bisimilar_LNth : forall (A: Set) (n:nat) (u v:LList A),
  bisimilar u v -> LNth n u = LNth n v.
Proof.
  induction n; intros;
  inversion H; simpl; auto.
Qed.

Lemma LNth_bisimilar : forall (A:Set) (u v: LList A),
  (forall n:nat, LNth n u = LNth n v) -> bisimilar u v.
Proof.
  intros A.
  cofix HInd.
  intros.
  pose proof (H 0) as Heq.
  destruct u; destruct v; [constructor| | |];
  inversion Heq.
  constructor.
  apply HInd.
  intros n; specialize H with (S n).
  auto.
Qed.

(* Exercise 13.21 *)
(* Prove the following two theorems (the proof techniques are
  interestingly different): *)

Theorem bisimilar_of_Finite_is_Finite: forall (A: Set) (l:LList A),
  Finite l -> forall l':LList A, bisimilar l l' -> Finite l'.
Proof.
  induction 1; intros l' Hbisim;
  inversion Hbisim; subst; auto.
Qed.

Theorem bisimilar_of_Infinite_is_Infinite: forall (A: Set) (l: LList A),
  Infinite l -> forall l':LList A, bisimilar l l' -> Infinite l'.
Proof.
  cofix HInd.
  intros A l H l' Hbisim.
  inversion H; subst.
  inversion Hbisim; subst.
  constructor.
  eapply HInd; eauto.
Qed.

(* Exercise 13.22 *)
(* Prove that restricting bisimilar to finite lists gives regular
  equality, in other words: *)

Theorem bisimilar_of_Finite_is_eq: forall (A:Set) (l:LList A),
  Finite l -> forall l':LList A, bisimilar l l' -> l = l'.
Proof.
  induction 1; intros l' Hbisim;
  inversion Hbisim; subst; auto.
  f_equal; auto.
Qed.

(* Exercise 13.23 *)
(* Redo the previous exercises for lazy binary trees (see Sect. 13.1.5).
  Define the relationship LTree_bisimilar and establish its relation with
  a function accessing the nodes of a tree, in a similar manner as to what
  is done in Exercise 13.20. *)

(* Note: Presumably, by "previous exercises", author means all the exercises
  of this section (13.7 Bisimilarity) thus far. This means from 13.19 to 13.22, 
  since 13.18 is a reflection on a specific exerpt *)

(* 13.19: Show bisimilarT is an equivalence relation *)

CoInductive bisimilarT {A:Set} : LTree A -> LTree A -> Prop :=
  | bisimTO : bisimilarT LLeaf LLeaf
  | bisimT1 : forall (a:A) (l l' r r':LTree A),
    bisimilarT l l' -> bisimilarT r r' 
      -> bisimilarT (LBin a l r) (LBin a l' r').

Hint Resolve bisimTO bisimT1 : core.

Theorem bisimT_refl : forall A, reflexive (LTree A) bisimilarT.
Proof.
  unfold reflexive.
  cofix H.
  destruct x; constructor; auto.
Qed.

Theorem bisimT_sym : forall A, symmetric (LTree A) bisimilarT.
Proof.
  unfold symmetric.
  cofix HInd.
  intros A x y H.
  inversion H; constructor; auto.
Qed.

Theorem bisimT_trans : forall A, transitive (LTree A) bisimilarT.
Proof.
  unfold transitive.
  cofix H.
  intros A x y z H1 H2.
  inversion H1; inversion H2; subst;
  try discriminate; auto.
  inversion H8; subst; eauto.
Qed.

Theorem bisimilarT_equivalence : forall A:Set, equivalence (LTree A) (bisimilarT).
Proof.
  constructor.
  - apply bisimT_refl.
  - apply bisimT_trans.
  - apply bisimT_sym.
Qed.

(* Two lemmas used by autorewrite in the proof to follow *)

Lemma Ltree_label_dO_LBin : forall (A:Set) (a:A) p l r,
  Ltree_label (dO :: p) (LBin a l r) = Ltree_label p l.
Proof. auto. Qed.

Lemma Ltree_label_d1_LBin : forall (A:Set) (a:A) p l r,
  Ltree_label (d1 :: p) (LBin a l r) = Ltree_label p r.
Proof. auto. Qed.

Hint Rewrite 
  Ltree_label_dO_LBin Ltree_label_d1_LBin : core.

(* 13.20: Relation between bisimilarT and Ltree_label *)

Lemma bisimilarT_Ltree_label : forall (A: Set) (p: list direction) (u v:LTree A),
  bisimilarT u v -> Ltree_label p u = Ltree_label p v.
Proof.
  induction p; intros;
  inversion H as [|x l l' r r' HB1 HB2]; simpl; auto.
  clear dependent u; clear dependent v.
  destruct a; autorewrite with core; auto.
Qed.

Lemma Ltree_label_bisimilarT : forall (A:Set) (u v: LTree A),
  (forall p: list direction, Ltree_label p u = Ltree_label p v) -> bisimilarT u v.
Proof.
  intros A.
  cofix HInd.
  intros.
  pose proof (H []) as Heq.
  destruct u; destruct v; [constructor| | |];
  try discriminate.
  inversion Heq; subst.
  constructor.
  - apply HInd.
    intros.
    pose proof (H (dO::p)) as H.
    auto.
  - apply HInd.
    intros.
    pose proof (H (d1::p)) as H.
    auto.
Qed.

(* 13.21: Theorems for bisimilarity on finite and infinite trees *)

Theorem bisimilarT_of_AllFinite_is_AllFinite: forall (A: Set) (u:LTree A),
  AllFinite u -> forall v:LTree A, bisimilarT u v -> AllFinite v.
Proof.
  induction 1; intros l' Hbisim;
  inversion Hbisim; subst; constructor; auto.
Qed.

Theorem bisimilarT_of_HasFinite_HasFinite: forall (A: Set) (u:LTree A),
  HasFinite u -> forall v:LTree A, bisimilarT u v -> HasFinite v.
Proof.
  induction 1; intros l' Hbisim;
  inversion Hbisim; subst; auto.
Qed.

Theorem bisimilarT_of_AllInfinite_is_AllInfinite: forall (A: Set) (t: LTree A),
  AllInfinite t -> forall t':LTree A, bisimilarT t t' -> AllInfinite t'.
Proof.
  cofix HInd.
  intros A l H l' Hbisim.
  inversion H; subst.
  inversion Hbisim; subst.
  constructor.
  all: eapply HInd; [|eauto]; auto.
Qed.

Theorem bisimilarT_of_HasInfinite_HasInfinite: forall (A: Set) (t: LTree A),
  HasInfinite t -> forall t':LTree A, bisimilarT t t' -> HasInfinite t'.
Proof.
  cofix HInd.
  intros A l H l' Hbisim.
  inversion H; subst;
  inversion Hbisim; subst.
  - apply HInf_left.
    eapply HInd; [|eauto]; auto.
  - apply HInf_right.
    eapply HInd; [|eauto]; auto.
Qed.

(* 13.22: Bisimilarity of finite trees implies equality *)

Theorem bisimilar_of_AllFinite_is_eq: forall (A:Set) (t:LTree A),
  AllFinite t -> forall t':LTree A, bisimilarT t t' -> t = t'.
Proof.
  induction 1; intros l' Hbisim;
  inversion Hbisim; subst; auto.
  f_equal; auto.
Qed.

(* Exercise 13.24 *)
(* Prove that every infinite sequence is left-absorbing for concatenation: *)

Lemma LAppend_of_Infinite_bisim: forall (A:Set) (u:LList A),
  Infinite u -> forall v: LList A, bisimilar u (LAppend u v).
Proof.
  intros A.
  cofix HInd; intros.
  inversion H.
  rewrite LAppend_LCons.
  constructor; auto.
Qed.
  
(* Exercise 13.25 *)
(* Prove that the sequence "omega u" is a fixpoint for concatenation
  (with respect to bisimilarity.) 
  Hint: first prove a lemma about general_omega. *)

Lemma general_omega_lappend: forall (A: Set) (u v: LList A),
  bisimilar (general_omega u v) (LAppend u (general_omega v v)).
Proof.
  intro A.
  cofix HInd.
  intros.
  destruct u.
  - rewrite general_omega_shoots_again, LAppend_LNil.
    apply bisim_refl.
  - rewrite LAppend_LCons, general_omega_LCons.
    constructor; auto.
Qed.

Lemma omega_lappend: forall (A: Set) (u: LList A),
  bisimilar (omega u) (LAppend u (omega u)).
Proof.
  intros; apply general_omega_lappend.
Qed.

(* Exercise 13.26 *)
(* As a continuation of Exercise 13.23, show that a tree where all
  branches are infinite is left-absorbing for the graft operation
  defined in Exercise 13.4. *)

Lemma graft_of_Infinite_bisimT: forall (A:Set) (u:LTree A),
  AllInfinite u -> forall v: LTree A, bisimilarT u (graft u v).
Proof.
  intros A.
  cofix HInd; intros.
  inversion H.
  rewrite graft_LBin_unfold.
  constructor; auto.
Qed.

(* End 13.24 *)

Definition bisimulation (A:Set) (R:LList A -> LList A -> Prop) :=
  forall l1 l2: LList A,
    R l1 l2 -> 
    match l1 with
    | LNil => l2 = LNil 
    | LCons a l'1 =>
      match l2 with
      | LNil => False
      | LCons b l'2 => a = b /\ R l'1 l'2
      end
    end.

(* Exercise 13.27 *)
(* Prove the following theorem (Park principle): *)

Theorem park_principle: forall (A: Set) (R:LList A -> LList A -> Prop),
  bisimulation R -> forall l1 l2:LList A, R l1 l2 -> bisimilar l1 l2.
Proof.
  intro A.
  cofix H.
  intros R Hbisim l1 l2 HR.
  destruct l1; destruct l2; auto;
  apply Hbisim in HR; inversion HR; subst.
  constructor; eauto.
Qed.

(* Exercise 13.28 *)
(* Use the Park principle to prove that the following two streams are bisimilar: *)

CoFixpoint alter : LList bool := LCons true (LCons false alter).
Definition alter2 : LList bool := omega (LCons true (LCons false LNil)).

(* Hint: consider the following binary relation and prove that it is a bisimulation: *)

Definition R (l1 l2:LList bool) : Prop :=
  l1 = alter /\ l2 = alter2 \/
  l1 = LCons false alter /\ l2 = LCons false alter2.

Lemma bisimulation_R : bisimulation R.
Proof.
  unfold bisimulation; intros.
  inversion H as [[HA1 HA2] | [HA1 HA2]]; subst.
  - unfold alter, alter2, omega.
    rewrite general_omega_LCons; split; auto.
    right; split; auto.
    rewrite general_omega_LCons; f_equal.
    rewrite general_omega_shoots_again; auto.
  - split; auto.
    left; auto.
Qed.

Lemma bisim_alters : bisimilar alter alter2.
Proof.
  eapply park_principle.
  - apply bisimulation_R.
  - left; auto.
Qed.

(* End 13.28 *)

Definition satisfies {A : Set} (l:LList A) (P:LList A -> Prop) : Prop := P l.
Hint Unfold satisfies : core.

Inductive Atomic {A : Set} (At:A -> Prop) : LList A -> Prop := 
  Atomic_intro : forall (a:A) (l:LList A), At a -> Atomic At (LCons a l).
  
Hint Resolve Atomic_intro : core.

Inductive Next {A : Set} (P:LList A -> Prop) : LList A -> Prop := 
  Next_intro : forall (a:A) (l:LList A), P l -> Next P (LCons a l).

Hint Resolve Next_intro : core.

Inductive Eventually {A : Set} (P:LList A -> Prop) : LList A -> Prop := 
  | Eventually_here :
    forall (a:A) (l: LList A), P (LCons a l) -> Eventually P (LCons a l)
  | Eventually_further:
    forall (a:A) (l:LList A), 
      Eventually P l -> Eventually P (LCons a l).

Hint Resolve Eventually_here Eventually_further : core.

(* Exercise 13.29 *)
(* Here is a lemma and its proof: *)
Theorem Eventually_of_LAppend :
  forall {A : Set} (P:LList A -> Prop) (u v:LList A), Finite u ->
    satisfies v (Eventually P) -> satisfies (LAppend u v) (Eventually P).
Proof.
  unfold satisfies; induction 1; intros;
  autorewrite with core; auto.
Qed.

(* What is the role of finiteness? Is it really necessary?
  If it is, build a counterexample. *)

Section counterexample.

  Let CoFixpoint inf_repeat {A : Set} (a : A) : LList A :=
    LCons a (inf_repeat a).

  Lemma inf_repeat_unfold : forall A a,
    inf_repeat a = LCons a (inf_repeat a) (A := A).
  Proof.
    intros.
    LList_unfold (inf_repeat a).
    simpl; auto.
  Qed.

  Let starts_with_true (l : LList bool) : Prop :=
    match l with
    | LCons true _ => True
    | _ => False
    end.

  Let u := inf_repeat false.
  Let v := LCons true LNil.

  Lemma bisim_c : bisimilar u (LAppend u v).
  Proof.
    apply LAppend_of_Infinite_bisim.
    unfold u.
    cofix H.
    rewrite inf_repeat_unfold.
    auto.
  Qed.

  Lemma LNth_c : forall n, LNth n (LAppend u v) = Some false.
  Proof.
    intro; symmetry.
    replace (Some false) with (LNth n u).
    - apply bisimilar_LNth, bisim_c.
    - induction n; simpl; auto.
  Qed.

  Lemma satisfies_EP_exists : forall l,
    satisfies l (Eventually starts_with_true) -> exists n, LNth n l = Some true.
  Proof.
    induction 1.
    - destruct a; inversion H.
      exists 0; auto.
    - destruct IHEventually as [n Hn].
      exists (S n); auto.
  Qed.

  Lemma not_satisfies_c : ~ satisfies (LAppend u v) (Eventually starts_with_true).
  Proof.
    intro H.
    apply satisfies_EP_exists in H as [n Hn].
    rewrite LNth_c in Hn.
    inversion Hn.
  Qed. 

End counterexample.
 
Definition Eventually_of_LAppend_general := 
  forall (B:Set) (P:LList B -> Prop) (u v:LList B),
    satisfies v (Eventually P) -> satisfies (LAppend u v) (Eventually P).

Goal ~ Eventually_of_LAppend_general.
Proof.
  unfold Eventually_of_LAppend_general.
  intro H.
  apply not_satisfies_c, H.
  left; auto.
Qed.

(* End 13.29 *)

(* Exercise 13.30 *)
(* Prove that every stream satisfying "Always P" is infinite. *)

CoInductive Always {A : Set} (P:LList A -> Prop) : LList A -> Prop := 
  Always_LCons : forall (a:A) (l: LList A),
    P (LCons a l) -> Always P l -> Always P (LCons a l).

Lemma Always_Infinite : forall A P l, Always P l -> Infinite l (A := A).
Proof.
  cofix HInd.
  intros.
  inversion H.
  constructor; eauto.
Qed.

(* Exercise 13.31 *)
(* Prove that every suffix of the stream "repeat a" starts with a: *)
Lemma always_a : forall A a, satisfies (repeat a) (Always (Atomic (eq a))) (A := A).
Proof.
  unfold satisfies.
  cofix H.
  intros.
  rewrite repeat_unfold.
  constructor; auto.
Qed.

(* End 13.31 *)

Definition F_Infinite {A:Set} (P:LList A -> Prop) : LList A -> Prop :=
  Always (Eventually P).

(* Exercise 13.32 *)
(* Show that the infinite sequence w where a and b alternate contains
  an infinity of occurrences of a. *)

(* Note: Given that I've opted to remove the LTL section and make
  this portion read more generally, a and b don't exist here. An
  equivalent proof can be done using any two values of the chosen type A. *)

CoFixpoint alt_inf {A : Set} (a b: A) : LList A :=
  LCons a (LCons b (alt_inf a b)).

Lemma alt_inf_unfold : forall A a b,
  alt_inf a b = LCons a (LCons b (alt_inf a b)) (A := A).
Proof.
  intros.
  LList_unfold (alt_inf a b);
  simpl; auto.
Qed.

Lemma Inf_alternate_F_Infinite : forall A a b,
  satisfies (alt_inf a b) (F_Infinite (Atomic (eq a))) (A := A).
Proof.
  unfold satisfies, F_Infinite.
  cofix H.
  intros.
  rewrite alt_inf_unfold.
  constructor.
  - left; auto.
  - constructor; auto.
    right. rewrite alt_inf_unfold.
    left; auto.
Qed.

(* End 13.32 *)

Definition G_Infinite {A : Set} (P:LList A -> Prop) : LList A -> Prop :=
  Eventually (Always P).

(* Exercise 13.33 *)
(* Show the following theorems: *)

Lemma LAppend_G_Infinite: forall A (P:LList A -> Prop) (u v: LList A),
  Finite u -> satisfies v (G_Infinite P)
    -> satisfies (LAppend u v) (G_Infinite P).
Proof.
  induction 1; intro Hs;
  autorewrite with core; auto.
  unfold satisfies, G_Infinite in IHFinite.
  right; auto.
Qed.

Lemma Always_G_Inf : forall A P l,
  Always P l -> G_Infinite P l (A := A).
Proof.
  intros.
  inversion H.
  constructor.
  constructor; auto.
Qed.

Lemma LAppend_G_Infinite_R : forall {A : Set} (P:LList A -> Prop) (u v: LList A),
  Finite u -> satisfies (LAppend u v) (G_Infinite P)
    -> satisfies v (G_Infinite P).
Proof.
  unfold satisfies.
  induction 1 as [|a l HF IH];
  autorewrite with core; intros H; auto.
  inversion H; auto; subst.
  inversion H1; subst.
  apply IH, Always_G_Inf; auto.
Qed.

(* End 13.33 *)

Record automaton : Type := 
  mk_auto {
    states : Set; actions : Set;
    initial : states;
    transitions: states -> actions -> list states
  }.

Definition deadlock (A: automaton) (q:states A) :=
  forall a:actions A, @transitions A q a = nil.

Unset Implicit Arguments.

CoInductive Trace (A: automaton) : states A -> LList (actions A) -> Prop :=
  | empty_trace: forall q:states A, deadlock A q -> Trace A q LNil
  | lcons_trace: forall (q q': states A) (a:actions A) (l:LList (actions A)),
    In q' (transitions A q a) -> Trace A q' l -> Trace A q (LCons a l).

Set Implicit Arguments.

(* Exercise 13.34 *** We consider the following automaton: *)

(* states *)
Inductive st : Set := q0 | q1 | q2.
(* actions *)
Inductive acts : Set := a | b.
(* transitions *)
Definition trans (q:st)(x:acts) : list st :=
  match q, x with
  | q0, a => cons q1 nil
  | q0, b => cons q1 nil
  | q1, a => cons q2 nil
  | q2, b => cons q2 (cons q1 nil)
  | _ , _ => nil (A := _)
  end.

Definition A1 := mk_auto q0 trans.

(* Draw this automaton, then show that every trace for A, contains an
  infinite number of b actions: *)

(* A drawing of the automaton reveals that q2 is reachable from any state
  in a finite number of actions, and its only action is a b action.
  We can also observe that from any state, passing through q2 eventually is
  guaranteed.

  Therefore, the proof will be centered around showing that:
    - There are no deadlocks
    - We MUST arrive at q2 eventually from any other state
    - Passing through state q2 results in a b action
*)

(* First, we must prove that the trace is infinite, i.e. no deadlocks *)

Lemma no_deadlocks : forall q, ~ deadlock A1 q.
Proof.
  unfold deadlock.
  intros q; intro H.
  destruct q.
  - specialize H with a; inversion H.
  - specialize H with a; inversion H.
  - specialize H with b; inversion H.
Qed.

(* Now we show that from q0 and q1, and for any trace t,
  we will arrive at q2 in a finite number of steps *)

(* Proving from_q1 first, as it can be used to to shorten the
  proof for from_q0, since the trace from q0 to q2 goes through q1 *)

Lemma from_q1 : forall t,
  Trace A1 q1 t -> exists t', Trace A1 q2 t' /\
    t = LCons a t'.
Proof.
  intros.
  inversion_clear H as [? Hdl|? q' x l HIn H'].
  - contradict Hdl; apply no_deadlocks.
  - destruct x; simpl in *;
    inversion_clear HIn; subst.
    + exists l; auto.
    + contradiction.
Qed.

Lemma from_q0 : forall t,
  Trace A1 q0 t -> exists t', Trace A1 q2 t' /\
    (t = LCons a (LCons a t') \/ t = LCons b (LCons a t')).
Proof.
  intros.
  inversion_clear H as [? Hdl|? q' x l HIn H'].
  - contradict Hdl; apply no_deadlocks.
  - destruct q'; destruct x; simpl in *;
    inversion_clear HIn.
    all: try discriminate; try contradiction; clear H.
    all: apply from_q1 in H' as [t' [H Heq]]; subst;
    exists t'; auto.
Qed.

(* Now we show that from q2, the follow action must be a b action *)

Lemma from_q2 : forall t,
  Trace A1 q2 t -> exists t', 
    (Trace A1 q1 t' \/ Trace A1 q2 t') /\ t = LCons b t'.
Proof.
  intros.
  inversion_clear H as [? Hdl|? q' x l HIn H'].
  - contradict Hdl; apply no_deadlocks.
  - destruct x; simpl in *; [contradiction|].
    destruct HIn as [|[|]]; subst; try contradiction.
    all: exists l; auto.
Qed.

(* Now we can prove the final statement *)

Theorem Infinite_bs : forall (q:st) (t:LList acts),
  Trace A1 q t -> satisfies t (F_Infinite (Atomic (eq b))).
Proof.
  unfold satisfies, F_Infinite.
  cofix HInd.
  intros q t HT.
  destruct q.
  - apply from_q0 in HT as [t' [HT [|]]]; subst.
    + apply from_q2 in HT as [t'' [[HT | HT] ?]]; subst.
      all: repeat (constructor; auto).
      all: eauto.
    + constructor; auto.
      constructor.
      * apply from_q2 in HT as [t'' [[HT | HT] ?]]; subst; auto.
      * eauto.
  - apply from_q1 in HT as [t' [HT ?]]; subst.
    constructor; eauto.
    apply from_q2 in HT as [t'' [[HT | HT] ?]]; subst; auto.
  - apply from_q2 in HT as [t'' [[HT | HT] ?]]; subst; auto.
    all: constructor; eauto.
Qed.