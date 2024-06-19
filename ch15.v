Require Import Arith.
Require Import Lia.

Fixpoint bdiv_aux (b m n:nat) {struct b} : nat*nat :=
  match b with
  | 0 => (0, 0)
  | S b' =>
    match le_gt_dec n m with
    | left H =>
      match bdiv_aux b' (m-n) n with
      | pair q r => (S q, r)
      end
    | right H => (0, m)
    end
  end.

(* Exercise 15.1 *)
(* Prove the hypothesis bdiv_aux_correct2. *)

Theorem bdiv_aux_correct2 :
  forall b m n:nat, m <= b -> 0 < n -> snd (bdiv_aux b m n) < n.
Proof.
  induction b; intros m n Hle Hnz; simpl; auto.
  destruct (le_gt_dec n m); simpl; auto.
  pose proof (IHb (m - n) n).
  destruct (bdiv_aux b (m - n) n) eqn:E.
  simpl in *; apply H; auto.
  lia.
Qed.

(* Exercise 15.2 *)
(* Build a well-specified variant of the function bdiv_aux. *)

(* For the specification of bdiv_aux, we can borrow the conclusions
  of the theorems bdiv_aux_correct1 and bdiv_aux_correct2 *)

Definition bdiv_aux_ws : forall b m n: nat, m <= b -> 0 < n ->
  {p : nat * nat | m = fst p * n + snd p  /\ snd p < n}.
Proof.
  induction b; intros m n Hleb Hnz; simpl.
  - exists (0, 0); inversion Hleb; auto.
  - destruct (le_gt_dec n m) as [Hle|Hgt].
    + pose proof (IHb (m - n) n) as Hrec.
      destruct Hrec as [[q r] [H1 H2]]; [lia|trivial|].
      exists (S q, r); simpl in *.
      split; [lia|trivial].
    + exists (0, m); auto.
Qed.

(* Exercise 15.3 *)
(* An algorithm to merge two sorted lists is an important auxiliary algorithm
  to a sorting algorithm. Its structure can be summarized by the following equalities,
  where we suppose a ≤ b:

  merge (cons a l) (cons b l') = cons a (merge l (cons b l'))
  merge (cons b l) (cons a l') = cons a (merge (cons b l) l')

  This algorithm is not structurally recursive with respect to either of its arguments,
  but the sum of the two lists' lengths decreases at each recursive call. Write a merge
  function with three arguments, where the first two have type "list A" and the third one
  is a natural number, working in the following context: *)

Require Import List.

Section merge_sort.
  Variables (A : Set) (Ale : A->A->Prop) (Ale_dec : forall x y:A, {Ale x y}+{Ale y x}).

  Fixpoint merge_aux (l1 l2 : list A) (n : nat) {struct n} : list A :=
    match n with
    | O => nil
    | S n' => 
        match l1, l2 with
        | nil, _ => l2
        | _, nil => l1
        | a :: l1', b :: l2' => 
            match Ale_dec a b with
            | left _ => a :: merge_aux l1' l2 n'
            | right _ => b :: merge_aux l1 l2' n'
            end
        end
    end.

  Definition merge (l1 l2 : list A) : list A := merge_aux l1 l2 (length l1 + length l2).

  Fixpoint merge_pairs_of_lists (L : list (list A)) : list (list A) :=
    match L with
    | l1 :: l2 :: L' => merge l1 l2 :: merge_pairs_of_lists L'
    | _ => L
    end.

  Fixpoint explode_list (l : list A) : list (list A) :=
    match l with
    | nil => nil
    | a :: l' => (a :: nil) :: explode_list l'
    end.

  Fixpoint merge_repeat (L : list (list A)) (n : nat) : list A :=
    match n with
    | O => nil
    | S n' =>
      match L with
      | nil => nil
      | l :: nil => l
      | _ => merge_repeat (merge_pairs_of_lists L) n'
      end
    end.

  Definition merge_sort (l : list A) : list A := merge_repeat (explode_list l) (length l).  

End merge_sort.

Definition nat_merge_sort := merge_sort nat le le_ge_dec.

Compute nat_merge_sort (1 :: 7 :: 5 :: 2 :: 4 :: 6 :: 8 :: 4 :: nil).


(* Exercise 15.4 *)
(* Note: a similar algo was made in Exercise 9.16. The following is the copied content
  using nat -> nat instead of positive -> Z. Many simplifications can be made using what
  we've learnt about bounded recursion. *)

(* Conversion of the sqrt function requires a way to express nats as quotient and remainder
  pairs when divided by 4 *)

Fixpoint div4 (n : nat) : nat * nat :=
  match n with
  | S (S (S (S n'))) => let (s, r) := div4 n' in (S s, r)
  | r => (0, r)
  end.

(* We need a rewrite rule for div4 later, and for that we borrow the 4 step
  induction rule from chapter 9 *)

Definition nat_4_ind:
  forall P: nat->Prop, P 0 -> P 1 -> P 2 -> P 3 ->
    (forall n, P n -> P (S (S (S (S n))))) ->
    forall n, P n.
Proof.
  intros P P0 P1 P2 P3 Hrec n.
  cut (P n /\ P (S n) /\ P (S (S n)) /\ P (S (S (S n)))).
  tauto.
  elim n; auto. 
  intros a [H1 [H2 [H3 H4]]].
  auto.
Defined.

Lemma div4_eq : forall n s r,
  div4 n = (s, r) -> n = 4*s + r.
Proof.
  induction n using nat_4_ind;
  intros s r;
  try solve [intros H; inversion H; lia].
  unfold div4; fold div4.
  destruct (div4 n) as [s' r'].
  assert (Heq: n = 4 * s' + r') by auto.
  intros H; inversion H; subst. lia.
Qed.

(* We also need a bound for the remainder in order to establish the bound for the sqaure root *)

Lemma div4_rem : forall n s r,
  div4 n = (s, r) -> r < 4.
Proof.
  induction n using nat_4_ind;
  intros s r;
  try solve [intros H; inversion H; lia].
  unfold div4; fold div4.
  destruct (div4 n) as [s' r'].
  intros H; inversion H; subst.
  eapply IHn. auto.
Qed.

(* As expected from exercises in this chapter, the only way to fix this algorithm
  is to come up with a bound on which to recurse, since the recursive call to sqrt
  is not structurally recursive *)

Fixpoint sqrt (a n: nat): nat * nat :=
  match a with
  | 0 => (0, 0)
  | S a' =>
    match (div4 n) with
    | (0, 0) => (0, 0)
    | (0, S x) => (1, x)
    | (q, x) => 
      let (s, r) := sqrt a' q in
      match (le_gt_dec (4*s+1) (4*r+x)) with
      | left Hle => (2*s+1, 4*r+x-(4*s+1))
      | right Hgt => (2*s, 4*r+x)
      end
    end
  end.

(* Now we can prove the two properties before defining the well-specified version. *)

Theorem sqrt_correct : forall a n s r,
  n <= a -> sqrt a n = (s, r) -> n = s*s + r.
Proof.
  induction a; intros n s r Hle Heq.
  - inversion Heq; lia.
  - unfold sqrt in *; fold sqrt in *.
    destruct (div4 n) as [q x] eqn:E.
    apply div4_eq in E.
    destruct q.
    + destruct x; intros;
      inversion Heq; lia.
    + destruct (sqrt a (S q)) as (s', r') eqn:Hsqrt.
      apply IHa in Hsqrt; [|lia].
      destruct (le_gt_dec (4 * s' + 1) (4 * r' + x)).
      all: inversion Heq; lia.
Qed.

Theorem sqrt_bound : forall a n s r,
  n <= a -> sqrt a n = (s, r) -> n < (s+1)*(s+1).
Proof.
  induction a; intros n s r Hle Heq.
  - inversion Hle; lia.
  - pose proof sqrt_correct _ _ _ _ Hle Heq as Heqn. 
    unfold sqrt in *; fold sqrt in *.
    destruct (div4 n) as [q x] eqn:E.
    pose proof div4_rem n q x E as Hltx.
    apply div4_eq in E.
    destruct q.
    + destruct x; intros;
      inversion Heq; lia.
    + destruct (sqrt a (S q)) as (s', r') eqn:Hsqrt.
      apply IHa in Hsqrt; [|lia].
      destruct (le_gt_dec (4 * s' + 1) (4 * r' + x)).
      all: inversion Heq; lia.
Qed.

Definition root_spec: forall n: nat,
  {s: nat & {r: nat | n = s*s + r /\ n < (s+1)*(s+1)}}.
Proof.
  intros n.
  destruct (sqrt n n) as [s r] eqn:E.
  exists s, r.
  split.
  - apply (sqrt_correct n); auto.
  - eapply (sqrt_bound n); eauto.
Qed.

(* Exercise 15.5 *)
(* Consider a type of polymorphic binary trees and the relation defined by "t is the left or right
  direct subterm of t'." Show that this relation is well-founded. *)

Inductive tree {A : Set} : Type :=
  | leaf
  | node (a : A) (l r: tree).

Inductive R_subtree {A : Set} (t : @tree A) : tree -> Prop :=
  | R_left : forall r a, R_subtree t (node a t r)
  | R_right : forall l a, R_subtree t (node a l t).

Theorem well_founded_R_subtree : forall A, well_founded (@R_subtree A).
Proof.
  unfold well_founded.
  induction a; constructor;
  intros y HR;
  inversion HR; auto.
Qed.

(* Exercise 15.6 *)
(* Prove the following theorem (the predicate inclusion is defined in the module Relations): *)

Require Import Relations.

Lemma wf_inclusion : forall (A: Set) (R S:A->A->Prop),
  inclusion A R S -> well_founded S -> well_founded R.
Proof.
  unfold inclusion, well_founded.
  intros A R S HRS HAcc a.
  induction (HAcc a) as [x _ HIndR].
  constructor.
  intros y HR.
  apply HIndR, HRS, HR.
Qed.

(* Exercise 15.7 *)
(* Show that if a relation R on A is well-founded, then there is no infinite R-decreasing chain in A: *)

Theorem not_decreasing : forall (A: Set) (R: A->A->Prop),
  well_founded R -> ~ (exists seq:nat->A, (forall i:nat, R (seq (S i)) (seq i))).
Proof.
  intros A R Hwf; intro H.
  destruct H as [seq HR].
  (* We state that any term belonging to the sequence is not accessible *)
  assert (H : forall a:A, (exists i, a = (seq i)) -> ~ Acc R a).
  (* We need to perform well founded induction on this proposition, so we use
    well_founded_ind, which has a final type of P a where P is of type A -> Prop.
    We can achieve this in our goal by changing the proposition to a function
    on a general element a, using pattern. *)
  - intro a; pattern a.
    apply (well_founded_ind Hwf).
    intros x Hx [i Heq]; subst.
    intro Hacc.
    apply (Hx (seq (S i)) (HR i)).
    + exists (S i); auto.
    + apply Hacc, HR.
  (* Now we have the above statement, but also that R is well-founded. These cannot both be true,
    and thus we can meet our goal of False. *)
  - eapply H.
    + exists 123; auto.
    + apply Hwf.
Qed.

(* Conclude that le:nat->nat->Prop and Zlt:Z->Z->Prop are not well-founded. *)

Lemma le_not_wf : ~ well_founded le.
Proof.
  intro Hwf.
  apply (not_decreasing _ _ Hwf).
  exists (fun i => 0).
  auto.
Qed.

Require Import ZArith.
Open Scope Z_scope.

Lemma Zlt_not_wf : ~ well_founded Z.lt.
Proof.
  intro Hwf.
  apply (not_decreasing _ _ Hwf).
  exists (fun i : nat => - (Z.of_nat i)).
  intros.
  apply -> Z.opp_lt_mono.
  apply inj_lt; auto.
Qed.

Close Scope Z_scope.

(* What about the reciprocal theorem to not_decreasing? Does classical logic play a role?
  (You can experiment with the module Classical.) *)

(* Here, I assume reciprocal means the converse and not the contrapositive since that'd be too obvious *)

Require Import Classical.
Require Import Logic.ClassicalChoice.

Section not_wf_converse.

Variable A : Set.
Variable R : A->A->Prop.

Theorem not_decreasing_conv_fail :
  ~ (exists seq:nat->A, (forall i:nat, R (seq (S i)) (seq i))) -> well_founded R.
Proof.
  intros.
  apply NNPP.
  contradict H.
  (* After using NNPP from Classical, we turn the converse into the inverse, and here we
    find a goal which can be solved using the axiom of choice, a part of classical logic. *)
  Check choice.

  (* 
    forall (A B : Type) (R : A -> B -> Prop), 
      (forall x : A, exists y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x)
  
  We see that we require a proof of (forall x : A, exists y : B, R x y). This clearly follows 
  from the fact that under the current context, R is not well-founded, and therefore we 
  should be able to produce an infinite R-descending sequence. Note that the relation's
  infinite chain in this axiom ascends rather than descends, so we'll have to map between
  two different relations. *)

  Abort.

Section not_wf_impl.

  Hypothesis Nwf : ~ well_founded R.

  Theorem not_acc_exists : exists x, ~ Acc R x.
  Proof. intros; apply not_all_ex_not in Nwf; auto. Qed.

  Theorem not_acc_impl : forall x, ~ Acc R x -> exists y, R y x /\ ~ Acc R y (A := A).
  Proof.
    intros x H.
    apply not_all_not_ex.
    contradict H.
    constructor.
    intros y HR.
    specialize (H y).
    apply not_and_or in H as [NR | NNAcc].
    - contradiction.
    - apply NNPP; assumption.
  Qed.

  (* From the above two theorems, we see that we can produce an infinite chain provided the first element
    in the chain is not accessible. So, we define a set which holds this property in the specification.*)

  Definition X : Type := {x : A | ~ Acc R x}.

  (* We also need a relation that swap the argument order, so we can define an infinite ascending
    chain for the axiom of choice. *)
 
  Search (sig _ -> ?x).

  Definition RX (x y : X) : Prop := R (proj1_sig y) (proj1_sig x).

  (* Now we need to show that there exists a mapping (F : nat -> X) that produces an infinite RX-ascending chain
    of values. First, we show that for any element of x, the next value exists. *)

  Lemma exists_next_X : forall x : X, exists y, RX x y.
  Proof.
    intros. destruct x as [a Nacc].
    pose proof (not_acc_impl a Nacc) as [b [HR H]].
    (* b is an element of A and is not accesible, so we can make an X element using the exist constructor *)
    exists (exist _ b H); auto.
  Qed.

  Lemma ascending_chain_X : exists F: nat -> X, forall i, RX (F i) (F (S i)).
  Proof.
    destruct not_acc_exists as [a Nacc].
    pose proof (choice RX exists_next_X) as [fx H].
    pose proof (exist (fun a => ~ Acc R a) a Nacc) as x.
    exists (fix f i := 
      match i with 0 => x | S i' => fx (f i') end).
    induction i; auto.
  Qed.

  Lemma descending_chain_A : exists f: nat -> A, forall i, R (f (S i)) (f i).
  Proof.
    destruct ascending_chain_X as [F HR].
    unfold RX in HR.
    exists (fun i => proj1_sig (F i)).
    auto.
  Qed.
    
End not_wf_impl.

Theorem not_decreasing_conv_fail :
  ~ (exists seq:nat->A, (forall i:nat, R (seq (S i)) (seq i))) -> well_founded R.
Proof.
  intros.
  apply NNPP.
  contradict H.
  apply descending_chain_A, H.
Qed.

End not_wf_converse.

(* Exercise 15.8 *)
(* This function continues the series of exercises on the Fibonacci
  sequence started with Exercise 9.8 page 270. *)

From CA Require Import ch9.

(* We need a sumbool describing how to divide x in half, be it even or odd *)
(* Thus, we also need a 2-step recursor on sets *)

Theorem nat_2_rec: forall P : nat -> Set,
  P 0 -> P 1 -> (forall n : nat, P n -> P (S (S n))) -> forall n : nat, P n.
Proof.
  intros P P0 P1 Hrec.
  refine (fix F n : P n := 
    match n with
    | 0 => P0
    | 1 => P1
    | S (S n') => Hrec n' (F n')
    end   
  ).
Qed.

(* Now for any x, we can break it up into its half and remainder (0 or 1) *)

Definition factor_2_dec: forall x, {y | x = 2*y} + {y | x = S(2*y)}.
  induction x using nat_2_rec.
  - left; exists 0; auto.
  - right; exists 0; auto.
  - destruct IHx as [[y H]|[y H]].
    + left; exists (S y); lia.
    + right; exists (S y); lia.
Defined.

(* We use well-founded recursion, with relation lt, since for any x > 0, div2 x < x
  Thus dividing by 2 as shown above should yield a finite descending chain.
  Note that this means x=0 is a seperate base case. *)

Definition fib_spec: forall x:nat, {u:nat & {v:nat | u = fib x /\ v = fib (S x)}}.
  apply well_founded_induction with lt.
  - apply lt_wf.
  - intros.
    (* Need to cover base case x=0 manually *)
    destruct x.
    exists 1, 1; auto.
    (* Rest can be done through recursion on half of x *)
    destruct (factor_2_dec (S x)) as [[y Heq]|[y Heq]].
    all : specialize (H y).
    all : destruct H as [a [b [Ha Hb]]]; [lia|].
    + pose proof (fib_2n y).
      pose proof (fib_2n1 y).
      rewrite <- Ha, <- Hb, <- Heq in *.
      exists (a * a + (b - a) * (b - a)), (2 * b * a - a * a); auto.
    + pose proof (fib_2n1 y).
      pose proof (fib_2n2 y).
      replace (2 * S y) with (S (S (2 * y))) in * by lia.
      rewrite <- Ha, <- Hb, <- Heq in *.
      exists (2 * b * a - a * a), (b * b + a * a); auto.
Defined.

(* Exercise 15.9 *)
(* Using the function two-power such that "two-power n" is 2^n (see Exercise 6.18),
  define the discrete logarithm function with the following specification: *)

Fixpoint two_power (n : nat) : nat :=
  match n with
  | O   => 1
  | S n => 2 * (two_power n)
  end.

Definition log2: forall n:nat, n <> 0 ->
  {p:nat | two_power p <= n /\ n < two_power (p + 1)}.
  intros n; pattern n.
  apply well_founded_induction with lt.
  - apply lt_wf.
  - clear n; intros x H Hneq.
     (* case: x = 0, impossible given x <> 0 *)
    destruct x; [contradiction|].
     (* case: x = 1, after which y <> 0 *)
    destruct x; [exists 0; auto|].
    destruct (factor_2_dec (S (S x))) as [[y Heq]|[y Heq]].
    all : specialize (H y).
    all : destruct H as [p [Hge Hlt]]; try lia.
    all : exists (S p); simpl; lia.
Qed.

(* Exercise 15.10 *)
(* What are the existing well-founded orders provided for inte-
gers (type Z) in the Coq library? Use them to define a function
that coincides with the factorial function on positive integers
and returns zero for other integers. *)

Require Import ZArith.Zwf.

Open Scope Z_scope.

Search "wf" Z.

Definition factZ : Z -> Z.
  apply well_founded_induction with (fun a b => Zwf 0 a b).
  - apply Zwf_well_founded.
  - intros x H.
    destruct (Z_dec x 0) as [[Hlt | Hgt] | Heq].
    + exact 0.
    + specialize (H (x - 1)).
      assert (Hwf : Zwf 0 (x - 1) x).
      * unfold Zwf. lia.
      * apply H in Hwf as y.
        exact (x * y).
    + exact 1.
Defined.

Close Scope Z_scope.

(* Note: I have no idea if this actually works since the proof Zwf_well_founded uses components
  which do not collapse under computation. I've done significant digging to find a clear answer,
  but haven't found enough. I've decided it's beyond the scope of the question. *)

(* Exercise 15.11 *)
(* Build a function that uses the algorithm described in Exercise 15.4,
  this time using well-founded recursion. This function must have the folowing type: *)

Definition div4_nat_spec : forall n, {s: nat & {r: nat | n = 4*s + r /\ r < 4}}.
  intros.
  destruct (div4 n) as [a b] eqn:E.
  exists a, b.
  split.
  - apply div4_eq; auto.
  - eapply div4_rem; eauto.
Defined.

Definition sqrt_nat_spec: forall n: nat, {s: nat & {r: nat | n = s*s + r /\ n < (s+1)*(s+1)}}.
  apply well_founded_induction with lt.
  - apply lt_wf.
  - intros n H.
    destruct (div4_nat_spec n) as [q [x [Heq Hrem]]].
    destruct q.
    + destruct x.
      * exists 0, 0; lia.
      * exists 1, x; lia.
    + specialize (H (S q)).
      destruct H as [s [r [Heq' Hrem']]]; [lia|].
      destruct (le_gt_dec (4 * s + 1) (4 * r + x)).
      * exists (2 * s + 1), (4 * r + x - (4 * s + 1)); lia.
      * exists (2 * s), (4 * r + x); lia.
Defined.

Definition sqrt_nat (n: nat) :=
  match (sqrt_nat_spec n) with
    existT _ s (exist _ r _) => (s, r) end.

Compute (sqrt_nat 3).

(* Any input past 3 doesn't compute into a pair,
  This issue is solved in a contributed solution in the online answers,
    https://github.com/coq-community/coq-art/blob/master/ch15_general_recursion/SRC/sqrt_by_GhaS_See.v
  but I can't understand how their methods solve this problem.
*)

(* Nonetheless, specific cases can be shown to produce correct results
  by contradicting requirements from the specification until only one
  output is possible: the correct one *)
Goal (sqrt_nat 4) = (2, 0).
Proof.
  unfold sqrt_nat.
  destruct (sqrt_nat_spec 4) as [s [r [Heq Hbound]]].
  assert (s <> 1) by lia.
  assert (s = 2) by lia.
  assert (r = 0) by lia.
  auto.
Qed.

(* Exercise 15.12 *)
(* In the same spirit as in Exercise 15.11, define a cubic root function. *)

(* Rather than take the approach taken in 15.4, we can use what we've learnt
  to define a well specified div8 algorithm in one go.*)

Definition div8_spec : forall n: nat, {s: nat & {r: nat | n = 8*s + r /\ r < 8}}.
  (* First we destruct n into cases 0-7, and the recursive case *)
  refine (fix div8 n : {s: nat & {r: nat | n = 8*s + r /\ r < 8}} :=
    match n with
    | S (S (S (S (S (S (S (S n'))))))) =>
      match div8 n' with _ => _ end
    | _ => _
    end).
  - exists 0, 0; lia.
  - exists 0, 1; lia.
  - exists 0, 2; lia.
  - exists 0, 3; lia.
  - exists 0, 4; lia.
  - exists 0, 5; lia.
  - exists 0, 6; lia.
  - exists 0, 7; lia.
  - pose proof s as [a [b [Heq Hrem]]]; clear s.
    exists (S a), b; lia.
Qed.

(* I have no clue what the general cubic algorithm is, and I'm certain it's quite tedious *)
Definition cubic: forall n: nat, {s: nat & {r: nat | n = s*s*s + r /\ n < (s+1)*(s+1)*(s+1)}}.
  apply well_founded_induction with lt.
  - apply lt_wf.
  - intros n H.
    destruct (div8_spec n) as [q [x [Heq Hrem]]].
    destruct q.
    + destruct x.
      * exists 0, 0; lia.
      * exists 1, x; lia.
    + specialize (H (S q)).
      destruct H as [s [r [Heq' Hrem']]]; [lia|].
      (* Right here is where we need to know more about general cubic root, to do case analysis *)
      (* Having looked online, I've decided to skip this exercise, as I don't think it helps
        provide any insight into Coq beyond what the previous exercise has. *)
Admitted.

(* Exercise 15.13 *)
(* Prove the facts f_lemma and double_div2_le. *)

Theorem double_div2_le : forall x:nat, div2 x + div2 x <= x.
Proof.
  induction x using nat_2_ind; auto.
  simpl; lia.
Qed.

Theorem f_lemma: forall x v:nat, v <= div2 x -> div2 x + v <= x.
Proof.
  intros. pose proof (double_div2_le x). lia.
Qed.

(* Exercise 15.14 *)
(* Define the function f given by the following equations:
  f (0) = 0
  f (1) = 0
  f (x+1) = 1 + f(1 + f(x)) (x <> 0) *)

(* This function produces the sequence 0, 0, 1, 2, 3, 4, ... *)
(* So it will be strictly increasing for x > 0 *)

(* Following the pattern shown in the section content *)
Definition nested_F:
  forall x:nat, (forall y:nat, y < x -> {v:nat | v = 0 \/ v < y}) -> {v:nat | v = 0 \/ v < x}.
  refine (fun x => 
    match x with 
    | S (S x') => fun Hrec =>
      match Hrec (S x') _ with exist _ y Hley =>
        match Hrec (S y) _ with exist _ z Hlez => 
          exist _ (S z) _
        end
      end
    | _ => fun Hrec => exist _ 0 _
    end); clear x; auto.
    all: try lia.
Defined.

Definition nested_f :=
  well_founded_induction
    lt_wf (fun x => {v:nat | v = 0 \/ v < x}) nested_F.

Definition f1 (x : nat) : nat := extract (nested_f x).

Compute (f1 4).

(* Exercise 15.15 *)
(* This exercise continues the sequence of exercises on well-parenthesized expressions
  and needs the results from Exercise 8.24 page 238. Define a parsing function that satisfies
  the following specification: *)


(* This keeps ch8 definitions out of the core namespace after the section *)
From CA Require ch8.
Section parse_rel.
Import ch8.

Print parse_rel.
(*
  Inductive parse_rel: list par -> list par -> bin -> Prop :=
  | parse_node: 
    forall (l1 l2 l3:list par) (t1 t2:bin),
      parse_rel l1 (cons close l2) t1 -> parse_rel l2 l3 t2 -> 
      parse_rel (cons open l1) l3 (N t1 t2)
  | parse_leaf_nil: parse_rel nil nil L
  | parse_leaf_close:
    forall l : list par, parse_rel (cons close l) (cons close l) L. *)

(* We know that as a parenthesized expression is parsed through parse_rel, parse_rel l l' t,
  that l' is a subsequence of l, and thus will be of equal or shorter length. *)

Lemma rem_length_le : forall l l' t, parse_rel l l' t -> length l' <= length l.
Proof.
  intros.
  induction H;
  simpl in *; lia.
Qed.

(* Looking then at the constructors, we can see that the only recursive case
  will yield a strictly shorter string for the first argument, the input string.
  Thus, parsing of a parenthesized expression should eventually terminate,
  and we can use the length of the input string as our metric for 
  well-founded induction. *)

Definition length_lt := fun (l l' : list par) => length l < length l'.

Lemma llt_wf' : forall (n : nat) l, length l < n -> Acc length_lt l.
Proof.
  unfold length_lt.
  induction n.
  - intros l H; inversion H.
  - destruct l; simpl; intros Hlt.
    all: constructor; simpl.
    + intros y H; inversion H.
    + intros y H.
      apply IHn.
      lia.
Qed.  

Theorem llt_wf : well_founded length_lt.
Proof.
  unfold length_lt, well_founded.
  constructor; simpl.
  apply llt_wf'.
Qed.

(* In the various lemmas to follow, we find ourselves in situations where the context claims that
  two different remainders result from the parsing of an expression. In these cases, we would like
  to show that the parsing of a string is deterministic, and thus these remainders are equal. *)

Theorem parse_rel_same_rem :
 forall l l1 t1,
   parse_rel l l1 t1 -> forall l2 t2, parse_rel l l2 t2 -> l1 = l2.
Proof.
  intros l l1 t1 H1; elim H1.
  - intros l2 l3 l4 t2 t3 Hl2 Hl2eq Hl3 Hl3eq l5 t4 H.
    inversion H; subst.
    apply Hl2eq in H2; inversion H2; subst.
    apply Hl3eq in H3; inversion H3; subst.
    auto.
  - intros l2 t2 H. inversion H; auto.
  - intros l2 l3 t2 H. inversion H; auto.
Qed.

(* Through pursuing the main goal using well-founded induction, we find ourselves with various
  cases where our hypotheses lead to a definitive choice for the sumbool. These each merit a
  seperate lemma for legibility. *)

(* For an expression (open :: x) to be even partially resolved, which is to say it would leave
  a remainder l' such that "parse_rel (open :: x) l' t" for some t, the prerequisites described
  by the constructor must be satisfied. We should then be able to disprove existence of a solution
  if these prerequisites are not met. *)

(* If x is a well-parenthesized expression, then (open :: x) will leave its leading open unresolved *)
Lemma L1 : forall x t, parse_rel x nil t -> forall l' t', ~ parse_rel (open :: x) l' t'.
Proof.
  intros.
  intro HF.
  inversion HF; subst.
  pose proof (parse_rel_same_rem _ _ _ H _ _ H1).
  discriminate.
Qed.

(* If x leaves a leading open in the remainder, then (open :: x) will leave its leading open unresolved *)
Lemma L2 : forall x y t, parse_rel x (open :: y) t -> forall l' t', ~ parse_rel (open :: x) l' t'.
Proof.
  intros.
  intro HF.
  inversion HF; subst.
  pose proof (parse_rel_same_rem _ _ _ H _ _ H1).
  discriminate.
Qed.

(* If x leaves (close :: y) remaining, but y has no partial resolution, then neither does (open :: x) *)
Lemma L3 : forall x y z t t',
  parse_rel x (close :: y) t -> (forall l s, ~ parse_rel y l s) -> ~ parse_rel (open :: x) z t'.
Proof.
  intros x y z t t' Hrel HF.
  intro H; inversion H; subst.
  pose proof (parse_rel_same_rem _ _ _ Hrel _ _ H1) as Heq.
  inversion Heq; subst.
  eapply HF; eauto.
Qed.

Definition parse_rel_dec : forall l:list par,
  {l':list par & {t:bin | parse_rel l l' t}} + {forall l' t', ~parse_rel l l' t'}.
  apply (well_founded_induction llt_wf); unfold length_lt.
  intros x H.
  destruct x; [left; exists nil, L; constructor|].
  destruct p; [| left; exists (close :: x), L; constructor].
  destruct (H x) as [[y [t Hrel]] | HF]; auto.
  - destruct y as [|[] y].
    + right; apply (L1 _ _ Hrel).
    + right; apply (L2 _ _ _ Hrel).
    + destruct (H y) as [[l' [t' Hy]]|HF].
      * apply rem_length_le in Hrel.
        simpl in *; auto.
      * left; exists l', (N t t').
        econstructor; eauto.
      * right; intros l' t'.
        apply (L3 _ _ _ _ _ Hrel HF).
  - right; intros l t.
    intro H1. inversion H1; subst.
    eapply HF; eauto.
Qed. 

End parse_rel.

(* End 15.15 *)

Definition div_it_F (f:nat->nat->nat*nat) (m n:nat) :=
  match le_gt_dec n m with
  | left _ => let (q, r) := f (m-n) n in (S q, r)
  | right _ => (0, m)
  end.

Fixpoint iter {A:Set} (n:nat) (F:A->A) (g:A) {struct n} : A :=
  match n with 0 => g | S p => F (iter p F g) end.

Definition div_it_terminates:
  forall n m : nat, 0 < m ->
    {v:nat*nat| exists p:nat,
      (forall k:nat, p < k -> forall g:nat->nat->nat*nat,
        iter k div_it_F g n m = v)}.

  intros n; elim n using (well_founded_induction lt_wf).
  intros n' Hrec m Hlt.
  case (le_gt_dec m n') as [H|H] eqn:Heq_test.
  - case Hrec with (y := n'-m) (2 := Hlt); auto with arith.
    intros [q r] Hex; exists (S q, r).
    destruct Hex as [p Heq].
    exists (S p).
    intros k; case k.
    + intros; elim (Nat.nlt_0_r (S p)); auto.
    + intros k' Hplt g; simpl; unfold div_it_F at 1.
      rewrite Heq; auto with arith.
      rewrite Heq_test; auto.
  - exists (0, n'); exists 0; intros k; case k.
    intros; elim (Nat.lt_irrefl 0); auto.
    intros k' Hltp g; simpl; unfold div_it_F at 1.
    rewrite Heq_test; auto.
Defined.

Definition div_it (n m:nat) (H:0 < m) : nat*nat := let (v, _) := div_it_terminates n m H in v.

Theorem div_it_fix_eqn : forall (n m: nat) (h: (0 < m)), 
  div_it n m h =
    match le_gt_dec m n with
    | left H => let (q,r) := div_it (n-m) m h in (S q, r)
    | right H => (0, n)
    end.
Proof.
  intros; unfold div_it.
  destruct (div_it_terminates n m h) as [v [p H1]].
  destruct (div_it_terminates (n - m) m h) as [v' [p' H2]].
  rewrite <- H1 with (k := S(S(max p p')))(g := fun x y:nat => v).
  erewrite <- H2. reflexivity.
  all: lia.
Qed.

(* Exercise 15.16 *)
(* Prove the following companion theorem to the function div_lt: *)

Theorem div_reduce : forall (m n:nat) (h:0 < n), snd (div_it m n h) < n.
Proof.
  induction m using (well_founded_ind lt_wf).
  intros.
  rewrite div_it_fix_eqn.
  destruct (le_gt_dec n m); [|auto].
  destruct (div_it (m - n) n h) as [a b] eqn:E.
  assert (Hlt: snd (div_it (m - n) n h) < n).
  apply H; lia.
  rewrite E in Hlt; auto.
Qed.

(* Exercise 15.17 *)
(* Define the factorial function on integers (with the value zero
  for negative arguments) by using this method and the well-founded
  relation Zwf. *)

Require ZArith.
Section Z_fact.

Open Scope Z_scope.

Definition fact_it_F (f: Z -> Z) (z : Z) : Z :=
  match z with
  | Zpos _ => z * f (z - 1)  
  | _ => 0
  end.

Close Scope Z_scope.

Definition fact_it_terminates :
  forall z : Z,
    {v : Z | exists l : nat, forall k : nat,
      forall g: Z -> Z, (l < k)%nat -> iter k fact_it_F g z = v}.
apply well_founded_induction with (fun a => Zwf 0 a).
- apply Zwf_well_founded.
- intros z Hrec.
  destruct z eqn:E.
  + exists 0%Z, 0.
    intros k g H.
    destruct k; [lia|].
    simpl; auto.
  + specialize (Hrec (z-1)%Z) as [y Hex]; [unfold Zwf; lia|].
    exists (z * y)%Z; auto.
    destruct Hex as [l H].
    exists (S l); intros k g Hlt.
    assert (Heq: iter (k - 1) fact_it_F g (z - 1)%Z = y).
    apply H; lia.
    inversion Hlt; subst; auto.
    simpl. rewrite Nat.sub_0_r. auto.
  + exists 0%Z, 0.
    intros k g H.
    destruct k; [lia|].
    simpl; auto.
Defined.

Definition fact_it (z : Z) : Z :=
  let (v, _) := fact_it_terminates z in v.

End Z_fact.

(* Exercise 15.18 *)
(* Define the log2 function and prove that it satisfies the 
  following property: 
  forall n: nat, n > 0 -> 2^(log2 n) <= n < 2*2^(log2 n) *)

Definition log2_it_F (f: nat -> nat) (n: nat) : nat :=
  match n with
  | S (S q) => S (f (div2 n))
  | _ => 0
  end.

Lemma div2_lt : forall n, div2 (S (S n)) < S (S n).
Proof.
  induction n using nat_2_ind; simpl in *; lia.
Qed.

Definition log2_it_terminates :
  forall n : nat,
    {v : nat | exists l : nat, forall k : nat,
      forall g: nat -> nat, (l < k)%nat -> iter k log2_it_F g n = v}.
apply (well_founded_induction lt_wf).
intros n Hrec.
destruct n.
- exists 0, 0; intros.
  destruct k; [lia|].
  simpl; auto.
- destruct n.
  + exists 0, 0; intros.
    destruct k; [lia|].
    simpl; auto.
  + specialize (Hrec (div2 (S (S n)))) as [v Hex].
    apply div2_lt.
    simpl in *.
    exists (S v).
    destruct Hex as [l H].
    exists (S l); intros k g Hlt.
    destruct k; [lia|].
    simpl; rewrite H; lia.
Defined.

Definition log2_it (n : nat) : nat :=
  let (v, _) := log2_it_terminates n in v.

Theorem log2_fix_eqn : forall n,
  log2_it n =
    match n with
    | S (S q) => S (log2_it (div2 n))
    | _ => 0
    end.
Proof.
  destruct n; auto.
  destruct n; auto.
  unfold log2_it.
  destruct (log2_it_terminates (S (S n))) as [x [l1 Heq1]].
  destruct (log2_it_terminates (div2 (S (S n)))) as [y [l2 Heq2]].
  rewrite <- (Heq1 (S (S (l1 + l2))) log2_it); [|lia].
  rewrite <- (Heq2 (S (l1 + l2)) log2_it); [|lia].
  simpl; auto.
Qed.

Lemma div2_eq : forall n,
  2 * div2 n = n \/ 2 * div2 n + 1 = n.
Proof.
  induction n using nat_2_ind; auto.
  destruct IHn; simpl; lia.
Qed.

Theorem log2_valid : forall n: nat,
  n > 0 -> 2^(log2_it n) <= n < 2*2^(log2_it n).
Proof.
  intros n; pattern n.
  apply (well_founded_induction lt_wf); clear n.
  destruct x; auto.
  destruct x; auto.
  intros Hrec Hgt.
  destruct (Hrec (div2 (S (S x)))) as [Hle Hlt].
  - apply div2_lt.
  - simpl; lia.
  - rewrite log2_fix_eqn.
    unfold Nat.pow; fold Nat.pow.
    split.
    + apply Nat.le_trans with (2 * div2 (S (S x))).
      * lia.
      * destruct (div2_eq (S (S x))); lia.
    + apply Nat.le_lt_trans with (2 * div2 (S (S x)) + 1).
      * destruct (div2_eq (S (S x))); lia.
      * lia.
Qed.

(* End 15.18 *)

Inductive log_domain : nat -> Prop :=
  | log_domain_1: log_domain 1
  | log_domain_2 :
    forall p:nat, log_domain (S (div2 p)) -> log_domain (S (S p)).

Theorem log_domain_non_0 : forall x:nat, log_domain x -> x <> 0.
Proof. intros x H; case H; intros; discriminate. Qed.

Theorem log_domain_inv:
  forall x p:nat, log_domain x -> x = S (S p) -> log_domain (S (div2 p)).
Proof.
  intros x p H; case H; try (intros H'; discriminate H').
  intros p' H1 H2; injection H2; intros H3;
  rewrite <- H3; assumption.
Defined.

(* Exercise 15.19 *)
(* Define a structurally recursive function over log_domain with
  the following specification:
  forall x : nat, { y : nat | two_power y <= x /\ x < two_power (S y)}. *)

Definition log_spec : forall (x : nat) (h : log_domain x),
  { y : nat | two_power y <= x /\ x < two_power (S y)}.
refine (fix log_spec (x : nat) (h:log_domain x) {struct h} :
  {y : nat |  two_power y <= x < 2 * two_power y } :=
    match x as y
    return x = y -> {y : nat |  two_power y <= x < 2 * two_power y } with
    | 0 => fun h' => False_rec _ (log_domain_non_0 x h h')
    | S 0 => fun h' => _
    | S (S p) => fun h' => _
    end (refl_equal x)).
- exists 0; simpl; lia.
- specialize (log_spec _ (log_domain_inv x p h h')) as [y Hex].
  exists (S y); subst.
  unfold two_power; fold two_power.
  destruct (div2_eq (S (S p))) as [H | H];
  rewrite <- H; simpl; lia.
Defined.

(* End 15.19 *)

(* Exercise 15.20 *)
(* This exercise reuses the toy programming language defined in
  Sect. 8.4.2. The inductive property forLoops characterizes
  programs in which one can recognize that all loops have an
  associated expression whose value decreases while staying positive
  at each iteration. Executing such programs is guaranteed to
  terminate. The goal of this exercise is to describe a function
  that executes these programs when it is possible without execution
  error. Being able to write such a function is quite remarkable because
  the semantics of the language makes it a Turing-complete language. *)

Require Import Wellfounded.Inverse_Image.

Section for_loops.

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

(* Assume execution is deterministic *)
Parameter exec_deterministic : forall i s s1 s2,
  exec s i s1 -> exec s i s2 -> s1 = s2.

Definition extract_option {A:Set} (x:option A) (def:A) : A :=
  match x with
  | None => def
  | Some v => v
  end.

Open Scope Z_scope.

Inductive forLoops : inst -> Prop :=
  | aForLoop:
      forall (e: bExp) (i: inst) (variant:aExp),
        (forall s s':state, evalB s e = Some true -> exec s i s' ->
        Zwf 0 (extract_option (evalA s' variant) 0)
          (extract_option (evalA s variant) 0)) ->
        forLoops i -> forLoops (WhileDo e i)
  | assignFor : forall (v:Var) (e:aExp), forLoops (Assign v e)
  | skipFor : forLoops Skip
  | sequenceFor:
      forall i1 i2: inst,
        forLoops i1 -> forLoops i2 -> forLoops (Sequence i1 i2).

Definition next_state (i : inst) (b : bExp) (s1 s2 : state) :=
  evalB s2 b = Some true /\ exec s2 i s1.

Theorem next_state_while_wf : forall i b,
  forLoops (WhileDo b i) -> well_founded (next_state i b).
Proof.
  intros i b H.
  inversion H; subst.
  eapply wf_inclusion; unfold inclusion.
  intros s1 s2 [Heq Hexec].
  apply (H2 s2 s1 Heq Hexec).
  apply wf_inverse_image.
  apply Zwf_well_founded.
Qed.

Definition exec_dec s i := {s':state | exec s i s'} + {forall s':state, ~exec s i s'}.

(* Tactic for eliminating option equalities and duplicates *)
Ltac invert_cleanup :=
  match goal with
  | [ H1: ?H, H2: ?H |- _] => clear H2; invert_cleanup
  | [ H1: (?x = Some ?n1), H2: (?x = Some ?n2) |- _] => 
    rewrite H1 in H2; inversion H2; subst; clear H2; invert_cleanup
  | [ H1: (?x = Some ?n1), H2: (?x = None) |- _] =>
    rewrite H1 in H2; discriminate
  | _ => idtac
  end.

(* Tactic for inverting an exec lemma and its subsequent results *)
Ltac invert_exec H := 
  match type of H with
  | (exec _ _ _) => inversion H; clear H; subst; invert_cleanup
  | _ => fail "expected lemma in the form: exec ?s ?i ?s'"
  end.

(* Tactic for handling the case when the goal is decidedly not executable *)
Ltac not_executable :=
  let HF := fresh "HF" in
  let ns := fresh "ns" in
    right; intros ns; intro HF; invert_exec HF.

(* Separate lemma for while loop for cleanliness:
  If the while loop is a "for-loop" and its body is decidedly executable for any state,
  then the loop itself is decidedly executable. *)
Lemma exec_while_aux :
  forall i b s,
    forLoops (WhileDo b i) ->
    (forall s':state, exec_dec s' i) -> exec_dec s (WhileDo b i).
Proof.
  intros i b s Hfor Hbody; revert s.
  apply well_founded_induction with (next_state i b).
  apply next_state_while_wf, Hfor.
  intros s Hnext.
  destruct (evalB s b) as [[]|] eqn:Heval.
  - destruct (Hbody s) as [[s' Hexec]|Hexec].
    + assert (H: exec_dec s' (WhileDo b i)).
      apply Hnext; split; auto.
      destruct H as [[sf Hs']| Hs'].
      * left; exists sf.
        apply (execWhileTrue _ s'); auto.
      * not_executable.
        assert (s' = s1); [|subst].
        eapply exec_deterministic; eauto.
        eapply Hs'; eauto.
    + not_executable.
      eapply Hexec; eauto.
  - left; exists s.
    apply execWhileFalse; auto.
  - not_executable.
Qed.

Definition exec_for_spec :
  forall (s:state) (i:inst), forLoops i -> exec_dec s i.
refine (fix espec s i h := 
  match i as j return i = j -> _ with
  | WhileDo e i' => fun h' => _
  | Assign v e => fun h' => _
  | Skip => fun h' => _
  | Sequence i1 i2 => fun h' => _
  end (refl_equal i)
).
- left; eexists; constructor.
- refine (match (evalA s e) as E return _ = E -> _ with
  | Some n => fun Heval =>
      (match (update s v n) as U return _ = U -> _ with
      | Some s' => fun Hupdate => _
      | None => fun Hupdate => _
      end (refl_equal (update s v n)))
  | None => fun Heval => _
  end (refl_equal (evalA s e))).
  + left; exists s'.
    eapply execAssign; eauto.
  + not_executable.
  + not_executable.
- assert (forLoops i1 /\ forLoops i2) as [F1 F2].
  subst; inversion h; auto.
  eapply espec in F1 as [[s1 F1] | F1].
  eapply espec in F2 as [[s2 F2] | F2].
  * left; exists s2.
    eapply execSequence; eauto.
  * not_executable.
    assert (s1 = s2); [|subst].
    eapply exec_deterministic; eauto.
    eapply F2; eauto.
  * not_executable.
    eapply F1; eauto.
- subst i.
  apply exec_while_aux. auto.
  intros; apply espec.
  inversion h; auto.
Defined.