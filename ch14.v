Require Import ZArith.

(* Exercise 14.1 *)
(* Describe natural number addition using nat_rec instead of the
  command Fixpoint. *)

Definition nat_plus :=
  nat_rec (fun (n:nat) => nat -> nat) (fun n => n) (fun n f p => S (f p)).

Compute nat_plus 3 4.

Goal forall n m:nat, n + m = nat_plus n m.
Proof. induction n; simpl; auto. Qed.

(* Exercise 14.2 *) 
(* Redefine the induction principle Z_btree_ind using the fix construct. *)

Inductive Z_btree : Set :=
  Z_bleaf : Z_btree | Z_bnode : Z->Z_btree->Z_btree->Z_btree.

Print Z_btree_ind.

Definition Z_btree_ind' := 
  fun (P : Z_btree -> Prop) (f : P Z_bleaf)
    (f0 : forall (z : Z) (z0 : Z_btree), 
      P z0 -> forall z1 : Z_btree, P z1 -> P (Z_bnode z z0 z1)) => 
  fix F (z : Z_btree) : P z :=
    match z as z0 return (P z0) with
    | Z_bleaf => f
    | Z_bnode z0 z1 z2 => f0 z0 z1 (F z1) z2 (F z2)
    end.

(* Exercise 14.3 *)
(* Manually build the induction principle for the sorted predicate from Sect. 8.1. *)

Require Import List.

Inductive sorted (A: Set) (R: A->A->Prop): list A -> Prop :=
  | sorted0: sorted A R nil
  | sorted1: forall x:A, sorted A R (cons x nil)
  | sorted2: forall (x y:A) (l:list A), 
    R x y -> sorted A R (cons y l) -> sorted A R (cons x (cons y l)).

(* If a given property P holds for all the possible inductive cases
  of a sorted list, then it holds for all sorted lists. If we replace
  "sorted A R l" by "P l" in each of the inductive constructors final types,
  these then represent all the prerequisites for the inductive principle. *)

Definition sorted_ind' : forall (A : Set) (R: A->A->Prop) (P : list A -> Prop),
  P nil -> (forall x:A, P (x :: nil)) ->
  (forall x y l, R x y -> sorted A R (y :: l) -> P (y :: l) -> P (x :: y :: l)) ->
  forall l, sorted A R l -> P l.
Proof.
  intros A R P Hnil Hone Htwo l Hsorted.
  refine (
    (fix F l (h: sorted A R l) : P l :=
    match h with
    | sorted0 _ _ => Hnil
    | sorted1 _ _ x => Hone x
    | sorted2 _ _ x y l' HR HS => Htwo x y l' HR HS (F (y :: l') HS)
    end) l Hsorted  
  ).
Defined.

(* Exercise 14.4 *)
(* Redo the proof of the theorem le_2_n_pred from Sect. 9.2.4 using the maximal induction principle for le. *)

Scheme le_ind_max := Induction for le Sort Prop.

Definition pred_partial : forall n:nat, n <> 0 -> nat.
  intros n; case n.
  intros h; elim h; reflexivity.
  intros p h'; exact p.
Defined.

Theorem le_2_n_not_zero: forall n:nat, le 2 n -> n <> 0.
Proof.
intros n Hle; elim Hle; intros; discriminate. Qed.

Theorem le_2_n_pred: forall (n:nat) (h:le 2 n),
  pred_partial n (le_2_n_not_zero n h) <> 0.
Proof.
  intros.
  induction h using le_ind_max; simpl.
  - discriminate.
  - intro; subst.
    inversion h.
Qed.

(* Exercise 14.5 *)
(* We consider the inductive property on polymorphic lists "u is a prefix of v": *)

Require Import List.
Import ListNotations.

Inductive lfactor {A:Set} : list A -> list A -> Prop :=
  | f1 : forall u:list A, lfactor nil u
  | f2 : forall (a:A) (u v:list A),
    lfactor u v -> lfactor (a :: u) (a :: v).

(* Build a function realizing the following specification: *)

Definition rfactor : forall (A: Set) (u v:list A),
  lfactor u v -> {w: list A | v = u ++ w}.
Proof.
  induction u; simpl; intros.
  - exists v; reflexivity.
  - destruct v as [|x v'].
    + exists nil; inversion H.
    + elim (IHu v').
      intros r Heq; subst.
      exists r.
      all: inversion H; trivial.
Defined.

(* End 14.5 *)

Section update_def.
  Variables (A : Set) (A_eq_dec : forall x y:A, {x = y}+{x <> y}).
  Variables (B : A->Set) (a : A) (v : B a) (f : forall x:A, B x).
  
  Definition update (x:A) : B x :=
    match A_eq_dec a x with
    | left h => eq_rec a B v x h
    | right h' => f x
    end.
End update_def.

(* Exercise 14.6 *)
(* Show that the update function satisfies the following proposition: *)
Require Import Eqdep.

Definition update_eq: forall (A:Set) (eq_dec: forall x y:A, {x = y} + {x <> y})
  (B:A->Set) (a:A) (v:B a) (f:forall x:A, B x), update A eq_dec B a v f a = v.
Proof.
  intros; unfold update.
  destruct (eq_dec a a); [|contradiction].
  erewrite eq_rec_eq; eauto.
Qed.
  
(* End 14.6 *)

Inductive ltree (A:Set) : Set :=
  | lnode : A -> list (ltree A) -> ltree A.

Section correct_ltree_ind.
  Variables
    (A : Set)(P : ltree A -> Prop)(Q : list(ltree A) -> Prop).
  Hypotheses
    (H : forall (a:A) (l:list (ltree A)), Q l -> P (lnode A a l))
    (H0 : Q nil)
    (H1 : forall t:ltree A, P t -> forall l:list (ltree A), Q l -> Q (t :: l)).

  Fixpoint ltree_ind2 (t:ltree A) : P t :=
    match t as x return P x with
    | lnode _ a l => 
        H a l
          (((fix l_ind (l':list (ltree A)) : Q l' :=
            match l' as x return Q x with
            | nil => H0
            | cons t1 tl => H1 t1 (ltree_ind2 t1) tl (l_ind tl)
            end)) l)
    end.

End correct_ltree_ind.

(* Exercise 14.7 *)
(* Build the induction principle list_ltree_ind2 that is suitable to reason by induction over lists of trees. *)

(* Given the induction principle for ltrees, the inductive principle on lists of ltrees can make use of it. 
  To make use of it, the function should have all the same context as the above section *)

Section correct_list_ltree_ind.
  Variables
    (A : Set)(P : ltree A -> Prop)(Q : list(ltree A) -> Prop).
  Hypotheses
    (H : forall (a:A) (l:list (ltree A)), Q l -> P (lnode A a l))
    (H0 : Q nil)
    (H1 : forall t:ltree A, P t -> forall l:list (ltree A), Q l -> Q (t :: l)).

  (* Given that this is an induction hypothesis on a list, it should be of type Q l, where l is the input *)
  (* 
    The cases for a list are nil and not nil. Nil is easy, we have a proof for Q nil, namely H0.
    
    For a non nil list a :: l', we need a proof of Q (a :: l). The final type of H1 fits this signature.
    We just need to satisfy the head types. With t := a and l := l', we're left with two other arguments needed:
    a proof of P a, and a proof of Q l'.
    
    The proof of Q l' naturally lends to the structural recursion of l within
    list_ltree_ind2, and so we can use (list_ltree_ind2 l').
    
    For P a, we can use the induction principle on
    ltrees: ltree_ind2, passing in all the same context, as mentioned previously.
  *)

  Fixpoint list_ltree_ind2 (l: list (ltree A)) : Q l :=
    match l as x return Q x with
    | nil => H0
    | a :: l' => H1 a (ltree_ind2 A P Q H H0 H1 a) l' (list_ltree_ind2 l')
    end.

End correct_list_ltree_ind.

(* Note these two induction principles could simply exist in a single section, which would simplify
  the arguments required in the nested calls. But the separation makes the passthrough of context clearer. *)

(* Exercise 14.8 *)
(* Define the function lcount: forall A:Set, ltree A -> nat that counts the number of nodes in a tree of type ltree. *)

Fixpoint lcount {A : Set} (t : ltree A) {struct t} : nat :=
  match t with
  | lnode _ a l => 
      1 + 
        ((fix lcount_list (l : list (ltree A)) : nat := 
          match l with
          | nil => 0
          | t :: l' => lcount t + lcount_list l'
          end) l)
  end.

Definition ltree_ex : ltree nat := 
  let lnat := lnode nat in
    lnat 0 ((lnat 1 nil) :: (lnat 2 ((lnat 3 nil) :: nil)) :: (lnat 4 nil) :: nil).

Compute lcount ltree_ex.

(* End 14.8 *)

Inductive ntree (A:Set) : Set := 
  | nnode : A -> nforest A -> ntree A
with nforest (A:Set) : Set :=
  | nnil : nforest A | ncons : ntree A -> nforest A -> nforest A.

Scheme ntree_ind2 :=
  Induction for ntree Sort Prop
with nforest_ind2 :=
  Induction for nforest Sort Prop.

(* Exercise 14.9 *)
(* Define the functions ltree_to_ntree and ntree_to_ltree that translate trees from one type to the other
  and respects the structure, and prove that these functions are inverses of each other. *)

Fixpoint ltree_to_ntree {A : Set} (t : ltree A) : ntree A :=
  match t with
  | lnode _ a l =>
      nnode A a 
        ((fix list_to_nforest (l : list (ltree A)) : nforest A :=
          match l with
          | nil => nnil A
          | t :: l' => ncons A (ltree_to_ntree t) (list_to_nforest l')
          end) l)
  end.

Fixpoint ntree_to_ltree {A : Set} (t : ntree A) : ltree A :=
  match t with
  | nnode _ a f => lnode A a (nforest_to_list f)
  end
with nforest_to_list {A : Set} (f : nforest A) : list (ltree A) :=
  match f with
  | nnil _ => nil
  | ncons _ t f' => (ntree_to_ltree t) :: (nforest_to_list f')
  end.


(* In the following proofs, the internal fixpoint list_to_nforest used in the properties
  Q and P0: conversion between lists and nforests is invertible (both ways), is copied
  from the definition of ltree_to_ntree. *)

Theorem ltree_to_ntree_to_ltree_correct : forall A (t : ltree A),
  ntree_to_ltree (ltree_to_ntree t) = t.
Proof.
  intros A t.
  induction t using ltree_ind2 with
    (Q := (fun l =>
      nforest_to_list
        ((fix list_to_nforest (l : list (ltree A)) : nforest A :=
          match l with
          | nil => nnil A
          | t :: l' => ncons A (ltree_to_ntree t) (list_to_nforest l')
          end) l) = l)).
  all: simpl; auto.
  all: f_equal; assumption.
Qed.

Theorem ntree_to_ltree_to_ntree_correct : forall A (t : ntree A),
  ltree_to_ntree (ntree_to_ltree t) = t.
Proof.
  intros A t.
  induction t using ntree_ind2 with
    (P0 := (fun f => 
      (fix list_to_nforest (l : list (ltree A)) : nforest A :=
        match l with
        | nil => nnil A
        | t :: l' => ncons A (ltree_to_ntree t) (list_to_nforest l')
        end) (nforest_to_list f) = f)).
  all: simpl; auto.
  all: f_equal; assumption.
Qed.
