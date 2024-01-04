Require Import List.
Require Import JMeq.
Import ListNotations.

(* Exercise 8.1 *)
(* Define the inductive property "last A a l" that is
  satisfied if and only if l is a list of values of 
  type A and a is the last element of l. Define a
  function last_fun: (list A)->(option A) that returns
  the last element when it exists. Give a statement
  that describes the consistency between these two 
  definitions and prove it. Compare the difference in 
  conciseness and programming style for the two definitions. *)

Inductive last (A : Type) (a : A) : list A -> Prop :=
  | last_one : last A a [a]
  | last_more : forall b l, last A a l -> last A a (b :: l).

Fixpoint last_fun (A : Type) (l : list A) : option A :=
  match l with
  | nil => None
  | [x] => Some x
  | _ :: l' => last_fun A l'
  end.

Theorem last_sound : forall A a l, 
  last A a l -> last_fun A l = Some a.
Proof.
  intros.
  induction H; simpl; auto.
  destruct l.
  - discriminate.
  - assumption.
Qed.

Theorem last_complete : forall A a l,
  last_fun A l = Some a -> last A a l.
Proof.
  induction l.
  - discriminate.
  - intros H.
    destruct l.
    + inversion H. constructor.
    + constructor. apply IHl. assumption.
Qed.
    
Theorem last_correct : forall A a l,
  last A a l <-> last_fun A l = Some a.
Proof.
  split.
  - apply last_sound.
  - apply last_complete.
Qed.

(* Exercise 8.2 *)
(* Use inductive definitions to describe the property "to be a palindrome."
  An auxiliary inductive definition, akin to last, but also describing a list
  without its last element, may be necessary. *)

Inductive palindrome {A : Type} : list A -> Prop :=
  | p_nil : palindrome nil
  | p_one : forall a, palindrome [a]
  | p_more : forall a l, palindrome l -> palindrome (a :: l ++ [a]).

(* Exercise 8.3 *)
(* Define the reflexive and transitive closure of a binary relation
 (using an inductive definition). The Rstar module of the Coq standard
 library provides an impredicative definition of this closure (constant Rstar).
 Prove that the two definitions are equivalent. *)

(* Note: Rstar was moved out of the standard library in 2008, 
  and the version of the textbook being referenced predeces this date.
  The following is the presumed definition from the old version: *)

Section Rstar.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Definition Rstar (x y:A) :=
    forall P: A -> A -> Prop,
      (forall u:A, P u u) -> (forall u v w:A, R u v -> P v w -> P u w) -> P x y.

  Theorem Rstar_refl : forall x:A, Rstar x x.
  Proof.
    unfold Rstar; intros; auto.
  Qed.

  Theorem Rstar_R : forall x y z:A, R x y -> Rstar y z -> Rstar x z.
  Proof.
    intros x y z HR H.
    unfold Rstar; intros P Href Htrans.
    apply (Htrans x y z).
    - assumption.
    - apply H; assumption.
  Qed.

  Theorem Rstar_trans : forall x y z, Rstar x y -> Rstar y z -> Rstar x z.
  Proof.
    intros x y z Hxy.
    apply Hxy.
    - intros; assumption.
    - intros u v w HR H1 H2.
      eapply Rstar_R.
      + apply HR.
      + apply H1, H2.
  Qed.

End Rstar.

Inductive R_rt {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | R_orig : forall x y, R x y -> R_rt R x y
  | R_refl : forall x, R_rt R x x
  | R_trans : forall x y z, R_rt R x y -> R_rt R y z -> R_rt R x z.

Theorem Rstar_equiv : forall A R x y, Rstar A R x y <-> R_rt R x y.
Proof.
  split; intros.
  - apply H.
    + apply R_refl.
    + intros.
      apply (R_trans R u v w).
      * apply R_orig; assumption.
      * assumption.
  - induction H.
    + unfold Rstar; intros P Hrefl Htrans.
      apply (Htrans x y y).
      * assumption.
      * apply Hrefl.
    + apply Rstar_refl.
    + apply (Rstar_trans A R x y z); auto.
Qed.

(* Exercise 8.4 *)
(* Define inductively the following binary relations on "list A":
  - the list l' is obtained from l by transposing two consecutive elements,
  - the list l' is obtained from l by applying the above operation a finite 
    number of times. Here we say that l' is a permutation of l.
  Show that the second relation is an equivalence relation. *)

Inductive list_trans {A : Type} : list A -> list A -> Prop :=
  | lt_swap x y l : list_trans (x :: y :: l) (y :: x :: l)
  | lt_skip x l l': list_trans l l' -> list_trans (x :: l) (x :: l').

Goal list_trans [1;2;3;4;5] [1;3;2;4;5].
Proof. apply lt_skip, lt_swap. Qed.

Inductive list_perm {A : Type} : list A -> list A -> Prop :=
  | lp_nil : list_perm [] []
  | lp_skip x l l': list_perm l l' -> list_perm (x :: l) (x :: l')
  | lp_swap x y l : list_perm (x :: y :: l) (y :: x :: l)
  | lp_trans l l' l'': list_perm l l' -> list_perm l' l'' -> list_perm l l''.

Goal list_perm [1;2;3;5;4] [1;3;2;4;5].
Proof.
  apply lp_skip.
  apply lp_trans with [3;2;5;4]; constructor.
  apply lp_skip.
  apply lp_trans with [4;5]; constructor.
  apply lp_skip.
  apply lp_nil.
Qed.

Theorem perm_refl : forall A l, @list_perm A l l.
Proof.
  induction l.
  - apply lp_nil.
  - apply lp_skip, IHl.
Qed.

Theorem perm_sym : forall A l l', @list_perm A l l' -> @list_perm A l' l.
Proof.
  intros A l l' H.
  induction H.
  - apply lp_nil.
  - apply lp_skip, IHlist_perm.
  - apply lp_swap.
  - apply lp_trans with l'; auto.
Qed.

Theorem perm_trans : forall A l l' l'',
  @list_perm A l l' -> @list_perm A l' l'' -> @list_perm A l l''.
Proof.
  intros A l l' l''.
  apply lp_trans.
Qed.

(* Exercise 8.5 *)
(* This exercise starts a long series ofexercises on parenthesized expressions.
  This series will finish with the construction of a parser for well-parenthesized
  expressions; in other words, a program that constructs a piece of data that
  represents the structure of an expression (see Exercises 8.19 and 8.24,
  pages 231, 238. 
  
  We consider the following type of characters: *)
    Inductive par : Set := open | close.
(* We represent character strings using the type "list par".
  
  An expression is well-parenthesized when:
  1. it is the empty list,
  2. it is a well-parenthesized expression between parentheses,
  3. it is the concatenation of two well-parenthesized expressions.
  
  Define the inductive property "wp:list par -> Prop" that corresponds to this
  informal definition. You can use the function app given in the module List to
  concatenate two lists. Prove the following two properties:
*)

Inductive wp : list par -> Prop :=
  | wp_nil : wp []
  | wp_nest a : wp a -> wp (open :: a ++ [close])
  | wp_concat a b : wp a -> wp b -> wp (a ++ b).

Theorem w_oc : wp (cons open (cons close nil)).
Proof. apply wp_nest with (a := nil). apply wp_nil. Qed.

Theorem wp_o_head_c: forall l1 l2: list par,
  wp l1 -> wp l2 -> wp (cons open (app l1 (cons close l2))).
Proof.
  intros.
  change (wp (open :: l1 ++ [close] ++ l2)).
  rewrite app_assoc.
  apply (wp_concat (open :: l1 ++ [close])).
  - apply wp_nest, H.
  - assumption.
Qed.

Theorem w_o_tail_c: forall l1 l2: list par,
  wp l1 -> wp l2 -> wp (app l1 (cons open (app l2 (cons close nil)))).
Proof.
  intros l1 l2 H1 H2.
  apply (wp_concat l1).
  - assumption.
  - apply wp_nest, H2.
Qed.

(* Exercise 8.6 *)
(* This exercise continues Exercise 8.5. We consider a tupe of binary trees
  without labels and a function that maps any tree to a list of characters.
  Show that this function always builds a well-parenthesized expression: *)

Inductive bin : Set := L:bin | N:bin->bin->bin.

Fixpoint bin_to_string (t:bin) : list par :=
  match t with
  | L => nil
  | N u v => cons open (app (bin_to_string u) (cons close (bin_to_string v)))
  end.

Theorem bin_to_string_wp : forall b, wp (bin_to_string b).
Proof.
  intros.
  induction b; simpl.
  - apply wp_nil.
  - apply wp_o_head_c; assumption.
Qed.

(* Exercise 8.7 *)
(* This exercise continues Exercise 8.6. Prove that the following 
  function also returns a well-parenthesized expression: *)

Fixpoint bin_to_string' (t:bin) : list par :=
  match t with
  | L => nil
  | N u v => 
    app (bin_to_string' u) (cons open (app (bin_to_string' v) (cons close nil)))
  end.

Theorem bin_to_string_wp' : forall b, wp (bin_to_string' b).
Proof.
  intros.
  induction b; simpl.
  - apply wp_nil.
  - apply w_o_tail_c; assumption.
Qed.

(* Exercise 8.8 *)
(* Prove the following statement, without using the eq predicate: *)

Goal forall x y z:nat, JMeq (x+(y+z)) ((x+y)+z).
Proof.
  induction x; simpl.
  - auto.
  - intros; rewrite IHx. auto.
Qed.

