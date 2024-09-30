Require Import List.
Require Import JMeq.
Require Import ZArith.
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

Lemma list_trans_sym : forall A l l', @list_trans A l l' -> @list_trans A l' l.
Proof.
  induction 1; constructor; assumption.
Qed.

Inductive list_perm {A : Type} : list A -> list A -> Prop :=
  | lp_refl l : list_perm l l
  | lp_trans l l' l'': list_perm l l' -> list_trans l' l'' -> list_perm l l''.

Theorem perm_refl : forall A l, @list_perm A l l.
Proof.
  intros; apply lp_refl.
Qed.

Lemma perm_intro_r :
 forall A l l', @list_perm A l l' -> 
    forall l'', list_trans l'' l ->  list_perm l'' l'.
Proof.
  intros A l l' H; induction H.
  - intros l'' H.
    econstructor.
    + apply lp_refl.
    + assumption.
  - intros.
    apply lp_trans with l'; auto.
Qed.

Theorem perm_trans : forall A l l' l'',
  @list_perm A l l' -> @list_perm A l' l'' -> @list_perm A l l''.
Proof.
  intros A l l' l'' H; revert l''.
  induction H; simpl; auto.
  intros;
  apply IHlist_perm.
  eapply perm_intro_r; eauto.
Qed.

Theorem perm_sym : forall A l l', @list_perm A l l' -> @list_perm A l' l.
Proof.
  intros A l l' H.
  induction H.
  - apply lp_refl.
  - eapply perm_intro_r.
    apply IHlist_perm.
    apply list_trans_sym.
    assumption.
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

Theorem bin_to_string'_wp : forall b, wp (bin_to_string' b).
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

(* Exercise 8.9 *)
(* Prove that an even number is the double of another number. *)

Inductive even : nat -> Prop :=
  | O_even : even O
  | p2_even : forall n, even n -> even (S (S n)).

Goal forall n, even n -> exists x, 2*x = n.
Proof.
  intros.
  induction H.
  - exists 0; auto.
  - destruct IHeven as [x Hdouble].
    exists (1 + x).
    rewrite PeanoNat.Nat.mul_add_distr_l.
    rewrite Hdouble; auto.
Qed.
    
(* Exercise 8.10 *)
(* Prove that the double of a number is always even. This proof requires an induction
  with the usual induction principle. Then show that the square of an even number is
  always even, this time with an induction on the even predicate.*)

Theorem double_even : forall n, even (n+n).
Proof.
  induction n; simpl.
  - constructor.
  - rewrite PeanoNat.Nat.add_succ_r.
    apply p2_even, IHn.
Qed.

Lemma add_even : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m H.
  induction H; simpl; intros.
  - auto.
  - apply p2_even, IHeven; auto.
Qed.

Goal forall n, even n -> even (n*n).
Proof.
  intros.
  induction H; simpl.
  - constructor.
  - apply p2_even.
    rewrite 2 PeanoNat.Nat.add_succ_r.
    apply p2_even.
    rewrite PeanoNat.Nat.add_assoc.
    apply add_even.
    + apply double_even.
    + repeat rewrite PeanoNat.Nat.mul_succ_r.
      rewrite <- PeanoNat.Nat.add_assoc.
      apply add_even; auto.
      apply double_even.
Qed.

(* Exercise 8.11 *)
(* Redo the following proof, using the tactic apply instead of elim: *)

Theorem lt_le: forall n p: nat, n < p -> n <= p.
Proof.
  intros n p H; elim H; repeat constructor; assumption.
Qed.

Goal forall n p: nat, n < p -> n <= p.
Proof.
  intros n p H; apply le_S_n; constructor; assumption.
Qed.

(* Exercise 8.12 *)
(* Prove by induction on le that the inductive definition 
  implies the impredicative version given in Sect. 5.5.4.1: *)
Definition my_le (n p : nat) :=
  forall P : nat -> Prop, P n -> (forall q, P q -> P (S q)) -> P p.

Theorem le_my_le: forall n p: nat, n <= p -> my_le n p.
Proof.
  intros n p H.
  induction H; intros P HP HS.
  - assumption.
  - apply HS, IHle.
    + apply HP.
    + apply HS.
Qed.

(* Exercise 8.13 *)
(* Use induction to prove that le is transitive
  (this proof is already in the Coq libraries, do not use it). *)

Theorem le_trans': forall n p q: nat, n < p -> p < q -> n < q.
Proof.
  intros n p q H.
  induction H; intros.
  - apply PeanoNat.Nat.lt_succ_l; auto.
  - apply IHle, PeanoNat.Nat.lt_succ_l; auto.
Qed.

(* Compare this proof with the proof of transitivity for my_le
  (without using the equivalence between le and my_le). *)

Theorem my_le_trans: forall n p q: nat, my_le n p -> my_le p q -> my_le n q.
Proof.
  intros n p q Hnp Hpq P HP H.
  apply Hpq.
  - apply Hnp.
    + apply HP.
    + apply H.
  - apply H.
Qed. 

(* Exercise 8.14 (proposed by J.F. Monin) *)
(* Here is another definition of <:
    n < m iff exists x:nat, x+n = m
  This can be written as an inductive definition in the following manner: *)

  Inductive le_diff (n m : nat) : Prop := 
    le_d: forall x: nat, x+n = m -> le_diff n m.

(* The variable x can be interpreted as the height of a proof tree for n <= m. 
  Prove the equivalence between le and le_diff. *)

Theorem le_le_diff_equiv: forall n m, n <= m <-> le_diff n m.
Proof.
  split; intros.
  - induction H.
    + apply (le_d _ _ 0). auto.
    + inversion IHle as [x Hx].
      apply (le_d _ _ (S x)).
      simpl; auto.
  - destruct H; subst.
    induction x; simpl.
    + constructor.
    + constructor; assumption.
Qed.

(* Exercise 8.15 *)
(* An alternative description of the order < on nat is the following one: *)

  Inductive le': nat -> nat -> Prop :=
  | le'_O_p : forall p: nat, le' 0 p
  | le'_Sn_Sp : forall n p: nat, le' n p -> le' (S n) (S p).

(* Prove that le and le' are equivalent. *)

Theorem le_le'_equiv: forall n m, n <= m <-> le' n m.
Proof.
  split.
  - revert m; induction n; intros.
    + constructor.
    + destruct m.
      * inversion H.
      * constructor.
        apply IHn, le_S_n.
        assumption.
  - intros H; induction H.
    + induction p.
      * constructor.
      * constructor; assumption.
    + apply le_n_S.
      assumption.
Qed.

(* Exercise 8.16 *)
(* An alternative description of sorted lists is the following one: *)
  Definition sorted' (A: Set) (R: A->A->Prop) (l: list A) := 
    forall (l1 l2: list A) (n1 n2: A),
      l = app l1 (cons n1 (cons n2 l2)) -> R n1 n2. 
(* Prove that sorted and sorted' are equivalent. *)

Inductive sorted (A: Set) (R: A->A->Prop): list A -> Prop :=
  | sorted0: sorted A R nil
  | sorted1: forall x:A, sorted A R (cons x nil)
  | sorted2: forall (x y:A) (l:list A), R x y -> sorted A R (cons y l) -> sorted A R (cons x (cons y l)).


Lemma trim_sorted': forall A R a l, sorted' A R (a :: l) -> sorted' A R l.
Proof.
  intros A R a l.
  induction l; intros;
  unfold sorted'; intros l1 l2 n1 n2 Heq.
  - destruct l1; inversion Heq.
  - apply (H (a :: l1) l2); simpl.
    rewrite Heq. auto.
Qed.

Theorem sorted_sorted'_equiv: forall A R l, sorted A R l <-> sorted' A R l.
Proof.
  split; intros.
  - induction H; intros l1 l2 n1 n2 ?H.
    + destruct l1; inversion H.
    + destruct l1; inversion H.
      destruct l1; inversion H2.
    + unfold sorted' in IHsorted.
      destruct l1; simpl in H1.
      * inversion H1; subst. assumption.
      * inversion H1.
        apply (IHsorted l1 l2). assumption.
  - induction l; [constructor|].
    destruct l; constructor.
    + apply (H [] l); auto.
    + apply trim_sorted' in H; auto.
Qed.

(* Exercise 8.17 *)
(* What is the systematic way to translate an inductive definition
  into an impredicative definition? Propose a method and test it on the
  examples given in Sect. 5.5. For each case, prove the equivalence
  between the inductive definition and the impredicative dernition. *)

(* From the inductive defintion, take the generated induction principle.
  Remove all instances of the inductive predicate from implications in
  the inductive principle, and instead imply the consequent directly. 
  Also, strictly for readability, move all dependant products except
  the last (forall P: Prop) into the header as arguments. This will
  match its header signature with the inductive definition.
*)

Check True_ind. (* forall P : Prop, P -> True -> P *)
Check False_ind. (* forall P : Prop, False -> P *)
Check and_ind. (* forall A B P : Prop, (A -> B -> P) -> A /\ B -> P *)
Check or_ind. (* forall A B P : Prop, (A -> P) -> (B -> P) -> A \/ B -> P *)
Check ex_ind. (* forall (A : Type) (P : A -> Prop) (P0 : Prop), (forall x : A, P x -> P0) -> (exists y, P y) -> P0 *)
Check le_ind. (* forall (n : nat) (P : nat -> Prop), P n -> (forall m : nat, n <= m -> P m -> P (S m)) -> forall n0 : nat, n <= n0 -> P n0 *)

Definition my_True := forall P: Prop, P -> P.
Definition my_False := forall P: Prop, P.
Definition my_and (P Q:Prop) := forall R: Prop, (P->Q->R) -> R.
Definition my_or (P Q:Prop) := forall R: Prop, (P->R)->(Q->R) -> R.
Definition my_ex (A:Set) (P:A->Prop) := forall R: Prop, (forall x:A, P x -> R) -> R.
(* Definition my_le (n p : nat) :=
  forall P : nat -> Prop, P n -> (forall q, P q -> P (S q)) -> P p. *)

Goal True <-> my_True.
Proof. split; auto. intros T P; auto. Qed.

Goal False <-> my_False.
Proof. split; intros H; [elim H | apply H]. Qed.

Goal forall P Q, and P Q <-> my_and P Q.
Proof.
  split; intros.
  - unfold my_and; elim H; auto.
  - split; apply H; intros; auto.
Qed.

Goal forall P Q, or P Q <-> my_or P Q.
Proof.
  split; intros.
  - unfold my_or; elim H; auto.
  - apply H; auto.
Qed.

Goal forall A P, ex P <-> my_ex A P.
Proof.
  split; intros.
  - unfold my_ex; elim H; intros x HP R Hex.
    apply (Hex x), HP.
  - apply H; intros x HP.
    exists x; auto.
Qed.

Goal forall n m, le n m <-> my_le n m.
Proof.
  split; [apply le_my_le|].
  unfold my_le; intros.
  apply H.
  - constructor.
  - intros q Hle.
    constructor; auto.
Qed.

(* Exercise 8.18 (proposed by H. Südbrock) *)
(* Carry on with the following development: *)
(* We advise the reader to prove a few lemmas before attacking
  the main theorem. Actually, this exercise is interesting mainly for 
  the choice of lemmas. *)

Section weird_induc_proof.
  Variable P : nat->Prop. 
  Variable f : nat->nat.

  Hypothesis f_strict_mono: forall n p:nat, 
    lt n p -> lt (f n) (f p).
  Hypothesis f_0 : lt 0 (f 0).

  Hypothesis PO: P 0.
  Hypothesis P_Sn_n: forall n:nat, P (S n) -> P n.
  Hypothesis f_P: forall n:nat, P n -> P (f n).

  (* Using P_Sn_n we can show (P n) also covers all cases less than n *)
  Lemma P_le: forall n m, n <= m -> P m -> P n.
  Proof. intros n m Hle HP. induction Hle; auto. Qed.

  (* Then using f_P we can show that for any n, there exists a number 
    greater than or equal to n that is the result of repeated
    applications of f on 0, and that that number is also covered *)
  Fixpoint iter (i n:nat) : nat :=
  match i with
  | O => n
  | S i' => f (iter i' n)
  end.

  Lemma iter_incr : forall i, iter i 0 < iter (S i) 0.
  Proof. induction i; simpl; auto. Qed.
  
  Lemma i_iter_lt: forall i:nat, i <= iter i 0.
  Proof.
    induction i; auto.
    pose proof (iter_incr i).
    eapply PeanoNat.Nat.le_lt_trans.
    - apply IHi.
    - auto.
  Qed.

  Lemma P_iter: forall i, P (iter i 0).
  Proof. induction i; simpl; auto. Qed.

  (* Therefore given any n, there exists a number m s.t. n <= m \/ P m 
    and since P m -> for all n <= m, P n, we have a proof for any P n *)
  Theorem weird_induc: forall n:nat, P n.
  Proof.
    intros. 
    eapply P_le.
    - apply i_iter_lt.
    - apply P_iter.
  Qed.

End weird_induc_proof.

(* Exercise 8.19 *)
(* This exercise continues Exercise 8.5, page 216. Here is a
  second definition of well-parenthesized expressions. Prove that
  it is equivalent to the previous one: *)
Inductive wp': list par -> Prop :=
| wp'_nil: wp' nil
| wp'_cons: forall l1 l2: list par, wp' l1 -> wp' l2 ->
    wp' (cons open (app l1 (cons close l2))).

Theorem wp'_wp: forall l, wp' l -> wp l.
Proof.
  intros l H; induction H.
  - constructor.
  - change (wp ([open] ++ l1 ++ [close] ++ l2)).
    rewrite 2 app_assoc.
    apply wp_concat; simpl.
    + constructor; auto.
    + auto.
Qed.

Theorem wp_wp': forall l, wp l -> wp' l.
Proof.
  intros; induction H.
  - constructor.
  - constructor; [auto|constructor].
  - induction IHwp1; simpl; auto.
    rewrite <- app_assoc; simpl.
    constructor; auto.
    apply IHIHwp1_2, wp'_wp; auto.
Qed.

Theorem wp_wp'_equiv: forall l, wp l <-> wp' l.
Proof.
  split.
  - apply wp_wp'.
  - apply wp'_wp.
Qed.

(* Exercise 8.20 *)
(* This exercise continues Exercise 8.19. Here is a
  third deftnition. Prove that it is equivalent to the previous ones: *)
Inductive wp'': list par -> Prop :=
  | wp''_nil: wp'' nil
  | wp''_cons: forall l1 l2: list par, wp'' l1 -> wp'' l2
    -> wp'' (app l1 (cons open (app l2 (cons close nil)))).
  
Theorem wp''_wp: forall l, wp'' l -> wp l.
Proof.
  intros l H; induction H.
  - constructor.
  - apply wp_concat.
    + auto.
    + constructor; auto.
Qed.

Theorem wp_wp'': forall l, wp l -> wp'' l.
Proof.
  intros; induction H.
  - constructor.
  - apply (wp''_cons nil); [constructor|auto].
  - induction IHwp2; simpl.
    + rewrite app_nil_r; auto.
    + rewrite app_assoc; simpl.
      constructor; auto.
      apply IHIHwp2_1, wp''_wp; auto.
Qed.

Theorem wp_wp''_equiv: forall l, wp l <-> wp'' l.
Proof.
  split.
  - apply wp_wp''.
  - apply wp''_wp.
Qed.

(* Exercise 8.21 *)
(* This exercise continues Exercise 8.20. Here is a function that
 recognizes well-parenthesized expressions by counting the opening
 parentheses that are not yet closed: *)

  Fixpoint recognize (n:nat) (l:list par): bool :=
    match l with
    | nil => match n with 0 => true | _ => false end
    | cons open l' => recognize (S n) l'
    | cons close l' =>
      match n with 0 => false | S n' => recognize n' l' end 
    end.

(* Prove the following theorem: *)

Theorem recognize_complete_aux: forall l: list par,
  wp l -> forall (n:nat) (l':list par),
    recognize n (app l l' ) = recognize n l'.
Proof.
  intros l H.
  rewrite wp_wp'_equiv in H.
  induction H; intros; simpl; auto.
  rewrite <- app_assoc; simpl.
  rewrite IHwp'1; simpl.
  apply IHwp'2.
Qed.

(* Conclude with the following main theorem: *)

Theorem recognize_complete: forall l:list par,
  wp l -> recognize 0 l = true.
Proof.
  intros l H.
  induction H; simpl; [auto| |];
  rewrite recognize_complete_aux; auto.
Qed.

(* Exercise 8.22 *)
(* This exercise is rather hard and continues Exercise 8.21.
  Prove that the recognize function only accepts well-parenthesized
  expressions, More precisely: *)

Fixpoint opens (n : nat): list par :=
  match n with
  | O => nil
  | S n' => open :: opens n'
  end.

Lemma opens_app: forall n, opens (S n) = opens n ++ [open].
Proof.
  induction n; simpl; [|rewrite <- IHn]; auto.
Qed.

Lemma wp_pair: wp [open; close].
Proof.
  change (wp (open :: nil ++ [close])).
  apply wp_nest. apply wp_nil.
Qed.

Theorem app_decompose :
 forall (A:Type) (l1 l2 l3 l4:list A),
   l1 ++ l2 = l3 ++ l4 ->
   (exists l1' : list A, l1 = l3 ++ l1' /\ l4 = l1' ++ l2) \/
   (exists a : A,
      exists l2' : list A, l3 = l1 ++ a :: l2' /\ l2 = (a :: l2') ++ l4).
Proof.
  simple induction l1.
  - intros l2 l3; case l3.
    + intros l4 H; left; exists (nil (A:=A)); auto.
    + intros a l3' Heq; right; exists a; exists l3'; auto.
  - clear l1; intros a l1 Hrec l2 l3; case l3.
    + intros l4 H; left; exists (a :: l1); auto.
    + simpl ; intros a' l3' l4 Heq; injection Heq; intros Heq' Heq''.
      elim Hrec with (1 := Heq').
      intros [l1' [Heq3 Heq4]]; left; exists l1'; split; auto.
      rewrite Heq''; rewrite Heq3; auto.
      intros [a'' [l2' [Heq3 Heq4]]]; right; exists a'', l2'; split; auto.
      rewrite Heq''; rewrite Heq3; auto.
Qed.

Local Hint Resolve wp_pair : core.
Theorem wp_remove_oc_aux :
forall l:list par,
  wp l ->
  forall l1 l2:list par, l1 ++ l2 = l -> wp (l1 ++ open :: close :: l2).
Proof.
  intros l H; elim H.
  - intros l1 l2 Heq.
    destruct (app_eq_nil _ _ Heq).
    subst; auto.
  - clear l H; intros l Hl IHl l1 l2 Heq.
    rewrite app_comm_cons in Heq.
    elim (app_decompose _ _ _ _ _ Heq).
    + intros [l1' [Heq1 Heq2]].
      destruct l1'; simpl in *; subst.
      * simpl; rewrite app_nil_r.
        change (wp (open :: l ++ [open; close] ++ [close])).
        rewrite app_assoc.
        apply wp_nest, wp_concat; auto.
      * inversion Heq2.
        symmetry in H1; destruct (app_eq_nil _ _ H1).
        subst. apply wp_concat; [apply wp_nest|]; auto.
    + intros [a [l2' [Heq1 Heq2]]].
      destruct l1; simpl in *.
      * change (wp ([open;close] ++ l2)).
        apply wp_concat; auto.
        subst; apply wp_nest; auto.
      * subst; inversion Heq1.
        change (wp ([open] ++ l1 ++ open :: close :: a :: l2' ++ [close])).
        repeat rewrite app_comm_cons.
        rewrite (app_assoc l1).
        apply wp_nest, IHl; auto.
  - intros l1 l2 Hp1 Hr1 Hp2 Hr2 l3 l4 Heq.
    elim (app_decompose _ _ _ _ _ Heq).
    intros [l1' [Heq1 Heq2]]; rewrite Heq1, <- app_assoc;
    apply wp_concat; auto.
    intros [a' [l2' [Heq1 Heq2]]].
    rewrite Heq2, !app_comm_cons, app_assoc.
    apply wp_concat; auto.
Qed.

Lemma recognize_sound_aux: forall n l,
  recognize n l = true -> wp ((opens n) ++ l).
Proof.
  intros n l; revert n.
  induction l; simpl; intros.
  - destruct n; [|discriminate].
    simpl; constructor.
  - destruct a.
    + change (wp (opens n ++ [open] ++ l)).
      rewrite app_assoc, <- opens_app. auto.
    + destruct n; [discriminate|].
      rewrite opens_app, <- app_assoc.
      change (wp (opens n ++ open :: close :: l)).
      apply (wp_remove_oc_aux (opens n ++ l)); auto.
Qed.

Theorem recognize_sound: forall l: list par, recognize 0 l = true -> wp l.
Proof.
  intros l H; apply (recognize_sound_aux _ _ H).
Qed.

(* Exercise 8.23 *)
(* This exercise continues Exercises 8.7 and 8.20. 
  We consider the following parsing function: *)

Fixpoint parse (s:list bin) (t:bin) (l:list par): option bin :=
  match l with
  | nil => match s with nil => Some t | _ => None end
  | cons open l' => parse (cons t s) L l'
  | cons close l' =>
    match s with
    | cons t' s' => parse s' (N t' t) l'
    | _ => None
    end
  end.

(* Prove that this parser is correct and complete: *)

Theorem parse_reject_indep_t :
  forall (l:list par) (s:list bin) (t:bin),
    parse s t l = None ->
    forall (s':list bin) (t':bin),
      length s' = length s -> parse s' t' l = None.
Proof.
  induction l; simpl;
  intros s t Heq s' t' Hlen.
  - destruct s; simpl in *.
    + inversion Heq.
    + destruct s'.
      * discriminate.
      * auto.
  - destruct a; simpl.
    + apply (IHl _ _ Heq); simpl; auto.
    + destruct s; destruct s';
      simpl in *; auto.
      * discriminate.
      * apply (IHl _ _ Heq); auto.
Qed.

Theorem parse_complete_aux: forall l: list par,
  wp' l -> 
  forall s t l', 
    parse s t (l ++ l') = None ->
    forall s' t',
      length s' = length s -> parse s' t' l' = None.
Proof.
  simple induction 1; simpl.
  - intros; eapply parse_reject_indep_t; eauto.
  - intros l1 l2 Hl1 IHl1 Hl2 IHl2 s t l' Heq s' t' Hlen.
    change (close :: l2) with ([close] ++ l2) in Heq.
    rewrite <- app_assoc in Heq.
    eapply IHl1 with (s':=t::s) (t':= L) in Heq; auto.
    rewrite <- app_assoc in Heq; simpl in Heq.
    eapply IHl2; eauto.
Qed.

Theorem parse_complete: forall l: list par,
  wp l -> parse nil L l <> None.
Proof.
  intros l H.
  replace l with (l ++ nil) by apply app_nil_r.
  intro HF.
  eapply parse_complete_aux with (s':= nil) (t':=L) in HF.
  - simpl in HF. discriminate.
  - apply wp_wp'; auto.
  - auto.
Qed.

Fixpoint unparse_stack (s:list bin): list par :=
  match s with
  | nil => nil
  | t :: s' => unparse_stack s' ++ bin_to_string' t ++ [open]
  end.
 
Theorem parse_invert_aux: forall (l:list par) (s:list bin) (t t':bin),
  parse s t l = Some t' ->
  bin_to_string' t' = unparse_stack s ++ bin_to_string' t ++ l.
Proof.
  induction l; simpl; intros.
  - rewrite app_nil_r.
    destruct s; simpl.
    + inversion H; subst; auto.
    + discriminate.
  - destruct a.
    + apply IHl in H; simpl in H.
      repeat rewrite <- app_assoc in H.
      auto.
    + destruct s; [discriminate|]; simpl.
      apply IHl in H; rewrite H; simpl.
      repeat (rewrite <- app_assoc; simpl).
      repeat apply f_equal; auto.
Qed.

Theorem parse_invert: forall (l:list par) (t:bin),
  parse nil L l = Some t -> bin_to_string' t = l.
Proof.
  intros l t H; apply parse_invert_aux in H; simpl in H; auto.
Qed.

Theorem parse_sound: forall (l:list par) (t:bin),
  parse nil L l = Some t -> wp l.
Proof.
  intros l t H; apply parse_invert in H.
  subst. apply bin_to_string'_wp.
Qed.

(* Exercise 8.24 *)
(* This exercise continues Exercise 8.7 page 217. The following
  inductive definition gives the description of a parsing function for 
  well parenthesized expressions. Intuitively, "parse_rel l1 l2 t" reads
  as "parsing the string l1 leaves l2 as suffix and builds the tree t". *)

Inductive parse_rel: list par -> list par -> bin -> Prop :=
  | parse_node: 
    forall (l1 l2 l3:list par) (t1 t2:bin),
      parse_rel l1 (cons close l2) t1 -> parse_rel l2 l3 t2 -> 
      parse_rel (cons open l1) l3 (N t1 t2)
  | parse_leaf_nil: parse_rel nil nil L
  | parse_leaf_close:
    forall l : list par, parse_rel (cons close l) (cons close l) L.

(* Prove the following lemmas: *)

Lemma parse_rel_sound_aux: forall (l l': list par) (t:bin),
  parse_rel l l' t -> l = app (bin_to_string t) l'.
Proof.
  simple induction 1; simpl; auto.
  intros l1 l2 l3 t1 t2 Hl1 Heq1 Hl2 Heq2.
  subst l1; rewrite <- app_assoc, <- app_comm_cons.
  repeat apply f_equal; auto.
Qed.

Lemma parse_rel_sound:
  forall l:list par, (exists t:bin, parse_rel l nil t) -> wp l.
Proof.
  intros l [t H].
  assert (l = bin_to_string t) as Heq.
  - rewrite <- app_nil_r. apply parse_rel_sound_aux. auto.
  - subst. apply bin_to_string_wp.
Qed.

Section little_semantics.

Variables Var aExp bExp : Set.
Inductive inst : Set :=
  | Skip : inst
  | Assign : Var->aExp->inst
  | Sequence : inst->inst->inst
  | WhileDo : bExp->inst->inst.

Variables
  (state : Set)
  (update: state->Var->Z -> option state)
  (evalA: state->aExp -> option Z)
  (evalB: state->bExp -> option bool).

Inductive exec: state->inst->state->Prop :=
  | execSkip: forall s:state, exec s Skip s
  | execAssign: forall (s s1:state) (v: Var) (n:Z) (a: aExp),
      evalA s a = Some n -> update s v n = Some s1 ->
      exec s (Assign v a) s1
  | execSequence: forall (s s1 s2:state) (i1 i2:inst),
      exec s i1 s1 -> exec s1 i2 s2 ->
      exec s (Sequence i1 i2) s2
  | execWhileFalse: forall (s:state) (i:inst) (e:bExp),
      evalB s e = Some false -> exec s (WhileDo e i) s
  | execWhileTrue: forall (s s1 s2:state) (i:inst) (e:bExp),
      evalB s e = Some true -> exec s i s1 ->
      exec s1 (WhileDo e i) s2 ->
      exec s (WhileDo e i) s2.

Theorem HoareWhileRule: 
  forall (P:state->Prop) (b:bExp) (i: inst) (s s':state),
    (forall s1 s2:state, 
      P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2) ->
      P s -> exec s (WhileDo b i) s' ->
      P s' /\ evalB s' b = Some false.
Proof.
  intros P b i s s' H Hp Hexec.
  remember (WhileDo b i) as i'.
  induction Hexec; intros;
  inversion Heqi'; subst; auto.
  apply IHHexec2; auto.
  apply (H s s1); auto.
Qed.

(* Exercise 8.25 *)
(* Find a method that avoids using an equality, just by
  making "WhileDo b i" occur in the goal. Prove the theorem
  again using this method. *)

Definition whileProjB (d:bExp) (i:inst): bExp :=
  match i with
  | WhileDo b _ => b
  | _ => d
  end.

Definition whileProjI (i: inst): inst :=
  match i with
  | WhileDo _ i' => i'
  | _ => i
  end.

Definition isWhile (i: inst): Prop :=
  match i with
  | WhileDo _ _ => True
  | _ => False
  end.

Theorem HoareWhileRule_aux: 
  forall (P:state->Prop) (b:bExp) (i: inst) (s s':state),
    (forall s1 s2:state, 
      P s1 -> evalB s1 (whileProjB b (WhileDo b i)) = Some true ->
      exec s1 (whileProjI (WhileDo b i) ) s2 -> P s2) ->
      P s -> exec s (WhileDo b i) s' ->
      P s' /\ evalB s' (whileProjB b (WhileDo b i)) = Some false.
Proof.
  intros P b i s s' Hinvar HP Hexec.
  generalize (I: isWhile (WhileDo b i)).
  revert HP Hinvar; elim Hexec; 
  try contradiction; auto.
  simpl in *.
  intros s1 s2 s3 i' e Heval Hexec1 IH1 Hexec2 IH2 HP IHinvar _.
  apply IH2; auto.
  apply (IHinvar s1); auto.
Qed.

Theorem HoareWhileRule':
  forall (P:state->Prop) (b:bExp) (i: inst) (s s':state),
    (forall s1 s2:state, 
      P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2) ->
      P s -> exec s (WhileDo b i) s' ->
      P s' /\ evalB s' b = Some false.
Proof.
  intros; eapply HoareWhileRule_aux; eauto.
Qed.

(* Exercise 8.26 *)
(* Prove that if b evaluates to true in the state s and the
  loop body is the Skip instruction, then execution never terminates.
  Here is the statement: *)

Lemma skip_loop_aux: forall (s s': state) (i:inst),
  exec s i s' ->
  forall b, i = WhileDo b Skip -> evalB s b = Some true -> False.
Proof.
  intros s s' i H.
  elim H; try discriminate.
  - intros s1 i' bf Heval1 bt Heq Heval2.
    inversion Heq; subst.
    rewrite Heval1 in Heval2.
    discriminate.
  - intros s0 s1 s2 i0 bt Heval1 Hexec1 IH1 Hexec2 IH2 bt' Heq Heval2.
    inversion Heq; subst.
    inversion Hexec1; subst.
    eapply IH2; eauto.
Qed.

Theorem skip_loop: forall (s s':state) (b:bExp),
  exec s (WhileDo b Skip) s' -> evalB s b = Some true -> False.
Proof.
  intros s s' b H Heval.
  eapply skip_loop_aux; eauto.
Qed.

(* Exercise 8.27 *)
(* Prove the Hoare logic rule for sequences. *)
Theorem HoareSequenceRule :
 forall (P1 P2 P3:state->Prop)(i1 i2:inst)(s s':state),
  (forall s1 s2, exec s1 i1 s2 -> P1 s1 -> P2 s2)->
  (forall s1 s2, exec s1 i2 s2 -> P2 s1 -> P3 s2)->
  exec s (Sequence i1 i2) s' -> P1 s -> P3 s'.
Proof.
  intros P1 P2 P3 i1 i2 s s' H1 H2 Hexec HP1.
  inversion Hexec; subst.
  eapply H2; eauto.
Qed.

End little_semantics.

(* Exercise 8.28 *)
(* Prove that the list 1;3;2 is not sorted (the definition
  of sorted is given in Sect. 8.1.1): *)

Goal ~sorted nat le (1::3::2::nil).
Proof.
  intro.
  inversion H; subst.
  inversion H4; subst.
  inversion H3.
  inversion H1.
  inversion H7.
Qed.

(* Exercise 8.29 (Proposed by L. Théry) *)
(* Prove that using stamps of 5 cents and stamps of 3 cents, one can pay all amounts greater than 
  or equal to 8 cents. This is the Frobenius problem, instantiated for 3 and 5. *)

Import Lia.

Theorem frobenius: forall n, 8 <= n -> exists p q, n = 3*p + 5*q.
Proof.
  intros.
  induction H as [| m Hm IHm].
  - exists 1, 1; auto.
  - destruct IHm as [a [b Heq]].
    assert (3 <= a \/ 1 <= b) as [Ha | Hb].
    { destruct b; try lia. }
    + exists (a - 3), (b + 2); lia.
    + exists (a + 2), (b - 1); lia.
Qed.
