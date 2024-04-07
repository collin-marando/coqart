Require Import ZArith.
Require Import Arith.
Require Import List.
Require Import Lia.
Import ListNotations.

(* Exercise 9.1 *)
(* Build a function extract with the following type: 
  forall (A: Set) (P: A -> Prop), sig P -> A *)

Definition extract {A: Set} {P: A -> Prop}: sig P -> A :=
  fun (X: sig P) => match X with
  | exist _ x _ => x
  end.

(* and prove the following property: *)

Theorem P_extract: forall (A: Set) (P: A -> Prop) (X: {x: A | P x}),
  P (extract X).
Proof.
  intros. destruct X; simpl. auto.
Qed.

(* Exercise 9.2 *)
(* With the help of the extract function given in Exercise 9.1, 
  define a well-specified function that has the same input arguments
  as the function div_pair', but has a strongly specified output. *)

Open Scope Z_scope.

Parameter div_pair:
  forall a b:Z,
    0 < b ->
    {p : Z * Z | a = fst p * b + snd p  /\ 0 <= snd p < b}.

Definition div_pair' (a b:Z) (h: 0 < b) :=
  extract (div_pair a b h).

Theorem div_pair''_ok:
 forall (a b: Z) (h: 0 < b),
    let p := div_pair' a b h in
    a = fst p * b + snd p /\ 0 <= snd p < b.
Proof.
 intros a b h.
 unfold div_pair'.
 pattern (extract (div_pair a b h)).
 apply P_extract.
Qed.

Close Scope Z_scope.

(* Exercise 9.3 *)
(* Build a function sig_rec_simple that has the following type: 
  forall (A:Set)(P:A->Prop)(B:Set), (forall x:A, P x -> B) -> sig P -> B *)

(* Using a proof to help visualize the functional construction *)
Theorem sig_rec_proof: forall (A:Set)(P:A->Prop)(B:Set),
  (forall x:A, P x -> B) -> sig P -> B.
Proof.
  intros A P B H X.
  destruct X as [x Px].
  apply (H x Px).
Qed.

Definition sig_rec_simple: forall (A:Set)(P:A->Prop)(B:Set),
  (forall x:A, P x -> B) -> sig P -> B :=
    fun A P B H X => let (x, Px) := X in (H x Px).

(* Exercise 9.4 *)
(* Prove that equality on the type nat is decidable
  (in other words, construct a term of type "eq_dec nat") *)
 
Definition eq_dec (A:Type) := forall x y:A, {x = y} + {x <> y}.

Definition eq_dec_nat : eq_dec nat.
  unfold eq_dec.
  intros x y.
  destruct (x =? y) eqn:E.
  - left. apply Nat.eqb_eq, E.
  - right. apply Nat.eqb_neq, E.
Defined.

Goal forall x y:nat, x = y \/ x <> y.
Proof.
  intros x y; destruct (eq_dec_nat x y); auto.
Qed.

(* Exercise 9.5 *)
(* This exercise continues Exercise 8.4 from page 216. Use the function
  required in Exercise 9.4 to construct a function that takes a list of
  natural numbers l and a natural number n and returns the number of
  occurrences of n in l. *)

Fixpoint num_occur (l: list nat) (n: nat) : nat :=
  match l with
  | nil => 0
  | a :: l' => 
    match (eq_dec_nat a n) with
    | left _ => 1 + num_occur l' n
    | right _ => num_occur l' n
    end
  end.

Goal num_occur [2;3;4;5;2;3;4;2] 2 = 3.
Proof. auto. Qed.

(* Exercise 9.6 *)
(* Define a function div3 that computes the result of dividing by 3.
  Prove a theorem similar to div2_le that expresses that the result
  is always smaller than the argument. *)

Fixpoint div3 (n:nat) : nat :=
  match n with
  | S (S (S p)) => S (div3 p)
  | _ => 0
  end.

Theorem div3_le: forall n: nat, div3 n <= n.
Proof.
  intros.
  cut (div3 n <= n /\ div3 (S n) <= S n /\ div3 (S (S n)) <= S (S n)).
  { tauto. }
  elim n; auto.
  intros a [H1 [H2 H3]].
  repeat split;
  simpl; auto with arith.
Qed.

(* Exercise 9.7 *)
(* Define a function mod that computes the remainder of
  the division by 2. Prove the following theorem: *)

Fixpoint div2 (n: nat): nat :=
  match n with S (S p) => S (div2 p) | _ => 0 end.

Fixpoint mod2 (n: nat): nat :=
  match n with S (S p) => mod2 p | x => x end.

Goal forall n: nat, n = 2*(div2 n) + (mod2 n).
Proof.
  intros.
  cut (n = 2 * div2 n + mod2 n /\ S n = 2 * div2 (S n) + mod2 (S n)).
  tauto.
  elim n; auto.
  intros a [H1 H2].
  split; auto.
  simpl; f_equal.
  rewrite Nat.add_succ_r.
  simpl; f_equal.
  auto.
Qed.

(* Exercise 9.8 *)
(* Define the Fibonacci sequence as a recursive function with a
  two-step recursive structure. The Fibonacci sequence is given by
  the following equations: 
    U0 = 1
    U1 = 1 
    U(n+2) = Un + U(n+1). *)

  Fixpoint fib (n: nat): nat :=
    match n with
    | S (S p as q) => fib p + fib q
    | _ => 1
    end.

(* Then define a function that simultaneously computes Un and U(n+1). *)

  Fixpoint fib2 (n: nat): nat*nat :=
    match n with
    | 0 => (1, 1)
    | S p => let (p, q) := fib2 p in (q, p + q)
    end. 
  
(* Prove that the two functions return consistent values.*)

Theorem fib_equiv: forall n, fib2 n = (fib n, fib (S n)).
Proof.
  intros.
  induction n; simpl; auto.
  rewrite IHn; auto.
Qed.

(* Exercise 9.9 *)
(* Prove a three-step and a four-step induction principle. *)

Theorem nat_2_ind:
  forall P: nat->Prop, P 0 -> P 1 ->
    (forall n, P n -> P (S (S n))) ->
    forall n, P n.
Proof.
  intros P P0 P1 Hrec n.
  cut (P n /\ P (S n)).
  tauto.
  elim n; auto.
  intros a [H1 H2].
  auto.
Qed.

Theorem nat_3_ind:
  forall P: nat->Prop, P 0 -> P 1 -> P 2 ->
    (forall n, P n -> P (S (S (S n)))) ->
    forall n, P n.
Proof.
  intros P P0 P1 P2 Hrec n.
  cut (P n /\ P (S n) /\ P (S (S n))).
  tauto.
  elim n; auto.
  intros a [H1 [H2 H3]].
  auto.
Qed.

Theorem nat_4_ind:
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
Qed.

(* Exercise 9.10 *)
(* The two-step induction principle nat_2_ ind is not adapted to
 reason about the Fibonacci function (see Exercise 9.8 page 270).
 Build and prove the induction principle for that function. Use it to 
 prove the following statement:
  
  forall n, U(n+p+2) = U(n+1)*U(p+1) + Un*Up *)

Lemma fib_ind:
  forall P: nat->Prop, P 0 -> P 1 ->
    (forall n, P n -> P (S n) -> P (S (S n))) ->
    forall n, P n.
Proof.
  intros P P0 P1 Hrec n.
  cut (P n /\ P (S n)).
  tauto.
  elim n; auto.
  intros a [H1 H2].
  auto.
Qed.

Lemma fib_SSn: forall n, fib (S (S n)) = fib n + fib (S n).
Proof.
  induction n using fib_ind; simpl; auto.
Qed.

Theorem fib_rel: forall n p,
  fib (S (S p) + n) = fib (S n) * fib (S p) + fib n * fib p.
Proof.
  induction n as [| | n IHn IHSn] using fib_ind; intros.
  - simpl; rewrite !Nat.add_0_r, Nat.add_comm; auto.
  - rewrite Nat.add_succ_r, !Nat.add_0_r. 
    rewrite !fib_SSn; simpl. ring.
  - rewrite !Nat.add_succ_r.
    rewrite fib_SSn, IHn.
    rewrite <- Nat.add_succ_r, IHSn.
    simpl; ring.
Qed.

(* Exercise 9.11 *)
(* Redo Exercises 9.6 to 9.8 from the previous section using the
  corresponding induction principles. *)

Goal forall n: nat, div3 n <= n.
Proof.
  intros n; elim n using nat_3_ind; auto.
  intros p H; simpl. auto with arith.
Qed.

Goal forall n: nat, n = 2*(div2 n) + (mod2 n).
Proof.
  intros n; elim n using nat_2_ind; auto.
  intros p H; simpl in *.
  rewrite Nat.add_succ_r; simpl.
  repeat apply f_equal. auto.
Qed.

Goal forall n, fib2 n = (fib n, fib (S n)).
Proof.
  intros n; elim n using nat_2_ind; auto.
  intros p H; simpl in *.
  rewrite H. auto.
Qed.

(* Exercise 9.12 *)
(* Define a simple-step recursive function for the following specification: *)

Fixpoint mult2 (n:nat): nat :=
  match n with
  | 0 => 0
  | S p => S (S (mult2 p))
  end.

Definition nlt1: forall n, n <= 1 -> {n = 0} + {n = 1}.
Proof.
  destruct n; auto.
  destruct n; auto with arith.
Defined.

Definition div2_mod2: forall n:nat,
  {q:nat & {r:nat | n = (mult2 q) + r /\ r <= 1}}.
Proof.
  induction n as [|n [a [b [Heq Hlt]]]].
  - exists 0, 0; auto.
  - destruct (nlt1 _ Hlt); subst.
    + exists a, 1; split; auto.
    + exists (S a), 0; split; simpl; auto.
Defined.

(* Exercise 9.13 *)
(* Prove that plus' is associative, without using the equivalence with plus. *)

Fixpoint plus' (n m:nat){struct m} : nat :=
  match m with 0 => n | S p => S (plus' n p) end.

Theorem plus'_assoc: forall a b c,
  plus' (plus' a b) c = plus' a (plus' b c).
Proof.
  intros; revert a b.
  induction c; simpl; auto.
Qed.

(* Exercise 9.14 *)
(* Prove that plus'' is associative. *)

Fixpoint plus'' (n m:nat) {struct m} : nat :=
  match m with 0 => n | S p => plus'' (S n) p end.

Lemma plus''_Sn_m: forall n m:nat, S (plus'' n m) = plus'' (S n) m.
Proof.
  intros; revert n.
  induction m; intros; simpl; auto.
Qed.

Theorem plus''_assoc: forall a b c,
  plus'' (plus'' a b) c = plus'' a (plus'' b c).
Proof.
  intros; revert a b.
  induction c; intros; simpl; auto.
  repeat rewrite <- plus''_Sn_m.
  simpl; rewrite <- plus''_Sn_m.
  auto.
Qed.

(* Exercise 9.15 *)
(* Define a tail-recursive function that computes the terms of the
  Fibonacci sequence. Show that this function is equivalent to the 
  function defined in Exercise 9.8 page 270. *)

Fixpoint fib_gen (a b n: nat) {struct n} :=
  match n with
  | 0 => a
  | S p => fib_gen b (a + b) p
  end.

Lemma fib_gen_Sn: forall a b n: nat,
  fib_gen a b (S n) = fib_gen b (a + b) n.
Proof. induction n; auto. Qed.

Lemma fib_gen_rel: forall a b n: nat,
  fib_gen a b (S (S n))= fib_gen a b n + fib_gen a b (S n).
Proof.
  intros; revert a b.
  induction n; intros; auto.
  rewrite fib_gen_Sn, IHn.
  rewrite !fib_gen_Sn. auto.
Qed.

Definition fib_tail (n: nat) := fib_gen 1 1 n.

Theorem fib_tail_equiv: forall n:nat, fib_tail n = fib n.
Proof.
  intros n; elim n using fib_ind; simpl; auto.
  intros p IHn IHSn.
  unfold fib_tail in *.
  rewrite <- IHSn, <- IHn.
  apply fib_gen_rel.
Qed.

(* Exercise 9.16 *)
(* Square root computation can also be described by a structural
  recursive algorithm on the positive type. If n' is a quarter of n,
  s is the square root of n' (rounded by default), and r is the remainder
  such that r = n' - s*s, then the square root of s is 2s' or 2s'+1.
  Find the test that should be done to decide which of the two valves
  is right, then build a function realizing the following specification: *)

Open Scope Z_scope.

(* The specification demands the following inequality be satisfied
    n = s*s + r /\ s*s <= n < (s+1) *(s+1)
  or equivalently:
  <->  n = s*s + r /\ s*s <= s*s + r < s*s + 2*s + 1
  <->  n = s*s + r /\ 0 <= r < 2*s + 1
  <->  n = s*s + r /\ 0 <= r <= 2*s

Cases:
  n = 1 -> (1, 0)
  n = 2 -> (1, 1)
  n = 3 -> (1, 2)
  n = 4n'+x, x={0,1,2,3}, n' > 0 -> ?(p, q)
    Let (s, r) = sqrt(n') s.t. 
      n' = s*s + r, s*s <= n' < (s+1)*(s+1)
      n' = s*s + r, 0 <= r <= 2*s
      4n' = 4*s*s + 4*r, 0 <= 4*r <= 4*(2*s)
      n-x = 4*s*s + 4*r, 0 <= 4*r <= 4*(2*s)
      n = (2*s)^2 + 4*r+x, 0 <= 4*r <= 4*(2*s)

    ?({p = 2s} + {p = 2s+1})
    Find threshold for case p = 2s+1
      (2*s+1)^2 = 4*s^2 + _4*s+1_
    Thus, p = (2*s+1) if 4*r+x >= 4*s+1
      
    if 4*r+x >= 4*s+1:
      -> n = (2*s+1)^2 + (4*r+x-(4*s+1)), 
      Check that this satisfies the spec for sqrt
        { 4*r <= 4*(2*s) }
        -> 4*s+1 <= 4*r+x <= 4*(2*s)+x
        -> 0 <= 4*r+x-(4*s+1) <= 4*(2*s) - (4*s+1) + x = 4*s-1+x
        { x <= 3 }
        -> 0 <= 4*r-(4*s+1)+x <= 4*s-1+x <= 4*s+2
        -> 0 <= 4*r+x-(4*s+1) <= 2*(2s+1)
      -> sqrt(n) = (2*s+1, 4*r+x-(4*s+1))

      else 4*r+x < 4*s + 1
        -> n = (2*s)^2 + 4*r+x, 0 <= 4*r+x < 4*s+1
        -> n = (2*s)^2 + 4*r+x, 0 <= 4*r+x <= 2*(2*s)
        -> sqrt(n) = (2*s, 4*r+x)
*)

Definition sqrt_aux (sr: Z*Z) (x: Z): Z*Z :=
  let s := fst sr in
  let r := snd sr in
  match (Z_lt_ge_dec (4*r+x) (4*s+1)) with
  | left Hlt => (2*s, 4*r+x)
  | right Hge => (2*s+1, 4*r+x-(4*s+1))
  end.

Fixpoint sqrt (n: positive): Z*Z :=
  match n with
  | 1%positive => (1, 0)
  | 2%positive => (1, 1)
  | 3%positive => (1, 2)
  | xO (xO n') => sqrt_aux (sqrt n') 0
  | xI (xO n') => sqrt_aux (sqrt n') 1
  | xO (xI n') => sqrt_aux (sqrt n') 2
  | xI (xI n') => sqrt_aux (sqrt n') 3
  end.

Inductive sqrt_data (n: positive) (s r: Z): Prop :=
  sqrt_data_def:
    Zpos n = s*s+r -> s*s <= Zpos n < (s+1)*(s+1) -> sqrt_data n s r.

Lemma sqrt_1: sqrt_data 1 1 0.
Proof. apply (sqrt_data_def 1 1 0); lia. Qed.

Lemma sqrt_2: sqrt_data 2 1 1.
Proof. apply (sqrt_data_def 2 1 1); lia. Qed.

Lemma sqrt_3: sqrt_data 3 1 2.
Proof. apply (sqrt_data_def 3 1 2); lia. Qed.

Lemma sqrt_4n_lt: forall n' s r, 
  sqrt_data n' s r ->
  4*r < 4*s+1 ->
  sqrt_data n'~0~0 (2*s) (4*r).
Proof.
  intros n' s r Hn' Hlt.
  inversion Hn'; constructor; lia.
Qed.

Lemma sqrt_4n_ge: forall n' s r, 
  sqrt_data n' s r ->
  4*r >= 4*s+1 ->
  sqrt_data n'~0~0 (2*s+1) (4*r-(4*s+1)).
Proof.
  intros n' s r Hn' Hlt.
  inversion Hn'; constructor; lia.
Qed.

Lemma sqrt_4n_1_lt: forall n' s r, 
  sqrt_data n' s r ->
  4*r+1 < 4*s+1 ->
  sqrt_data n'~0~1 (2*s) (4*r+1).
Proof.
  intros n' s r Hn' Hlt.
  inversion Hn'; constructor; lia.
Qed.

Lemma sqrt_4n_1_ge: forall n' s r, 
  sqrt_data n' s r ->
  4*r+1 >= 4*s+1 ->
  sqrt_data n'~0~1 (2*s+1) (4*r+1-(4*s+1)).
Proof.
  intros n' s r Hn' Hlt.
  inversion Hn'; constructor; lia.
Qed.

Lemma sqrt_4n_2_lt: forall n' s r, 
  sqrt_data n' s r ->
  4*r+2 < 4*s+1 ->
  sqrt_data n'~1~0 (2*s) (4*r+2).
Proof.
  intros n' s r Hn' Hlt.
  inversion Hn'; constructor; lia.
Qed.

Lemma sqrt_4n_2_ge: forall n' s r, 
  sqrt_data n' s r ->
  4*r+2 >= 4*s+1 ->
  sqrt_data n'~1~0 (2*s+1) (4*r+2-(4*s+1)).
Proof.
  intros n' s r Hn' Hlt.
  inversion Hn'; constructor; lia.
Qed.

Lemma sqrt_4n_3_lt: forall n' s r, 
  sqrt_data n' s r ->
  4*r+3 < 4*s+1 ->
  sqrt_data n'~1~1 (2*s) (4*r+3).
Proof.
  intros n' s r Hn' Hlt.
  inversion Hn'; constructor; lia.
Qed.

Lemma sqrt_4n_3_ge: forall n' s r, 
  sqrt_data n' s r ->
  4*r+3 >= 4*s+1 ->
  sqrt_data n'~1~1 (2*s+1) (4*r+3-(4*s+1)).
Proof.
  intros n' s r Hn' Hlt.
  inversion Hn'; constructor; lia.
Qed.

Hint Resolve
  sqrt_1 sqrt_2 sqrt_3 sqrt_4n_1_lt
  sqrt_4n_lt sqrt_4n_ge
  sqrt_4n_1_lt sqrt_4n_1_ge
  sqrt_4n_2_lt sqrt_4n_2_ge
  sqrt_4n_3_lt sqrt_4n_3_ge: core.

Ltac case_all :=
  match goal with
  | |- context [if ?X then _ else _] => destruct X
  end.

Require Import FunInd.
Functional Scheme sqrt_ind := Induction for sqrt Sort Prop.

Check sqrt_ind.

Lemma sqrt_correct: forall n, let (s, r) := sqrt n in sqrt_data n s r.
Proof.
  intros n.
  functional induction (sqrt n); auto;
  unfold sqrt_aux;
  destruct (sqrt n') as [s r] eqn:E;
  cbn [fst snd]; case_all; auto;
  rewrite Z.add_0_r in *; auto.
Qed.

Definition root_spec: forall n:positive,
  {s: Z & {r: Z | Zpos n = s*s + r /\ s*s <= Zpos n < (s+1)*(s+1)}}.
Proof.
  intros.
  pose proof (sqrt_correct n) as H.
  destruct (sqrt n) as [s r].
  exists s, r.
  inversion H; auto.
Qed.

Close Scope Z_scope.

(* Exercise 9.17 *)
(* Using the result of Exercise 9.8, find a relation between (U_2n, U_2n+1)
and (U_n, U_n+1), where Un is the nth element in the Fibonacci sequence.
Deduce a function that implements the following specification using a
recursive algorithm on numbers of type positive: 
  forall n:nat, {u:nat & {u':nat | u = fib n /\ u' = fib (n+1)}} *)

Lemma double: forall n, 2*n = n+n. Proof. lia. Qed.

(* This is the relation between (U_n, U_n+1) and U_2n+2 *)
Theorem fib_2n2: forall n,
  fib(2*(S n)) = fib(S n) * fib(S n) + fib n * fib n.
Proof.
  intros. destruct n; auto.
  rewrite double, fib_rel, !fib_SSn. lia.
Qed.

(* The same relation will be true for (U_n-1, U_n) and U_2n 
  We need U_n-1 in terms of U_n and U_n+1. By rearranging the basic
  fib relation: U_n-1 = U_n+1 - U_n *)

Lemma fib_n_sub: forall n, fib n = fib (S (S n)) - fib (S n).
Proof. intros; rewrite fib_SSn; lia. Qed.

Theorem fib_2n: forall n,
  fib(2*n) = fib n * fib n + (fib (S n) - fib n) * (fib (S n) - fib n).
Proof.
  intros.
  destruct n; auto.
  rewrite <- fib_n_sub.
  apply fib_2n2.
Qed.

(* Now with formulae for both U_2n and U_2n+2 in terms of U_n and U_n+1
  We can easily come up with an expression for U_2n+1 using the basic
  relation. For brevity, let a = U_n, b = U_n+1:
  
    U_2n+1 = U_2n+2 - U_2n
    U_2n+1 = b*b + a*a - a*a - (b - a)*(b - a)
    U_2n+1 = b*b - (b*b - 2*a*b + a*a)
    U_2n+1 = 2*a*b - a*a

  Note: The first step differs from the equation fib_sub in that
    the middle term is isolated rather than the least term.
*)

Lemma fib_Sn_sub: forall n, fib (S n) = fib (S (S n)) - fib n.
Proof. intros; rewrite fib_SSn; lia. Qed.

Lemma fib_mono: forall n, fib n <= fib (S n).
Proof.
  destruct n; auto.
  rewrite fib_SSn. lia.
Qed.

Lemma fib_mono_strong: forall n m, n <= m -> fib n <= fib m.
Proof.
  intros.
  induction H; auto.
  eapply Nat.le_trans.
  - apply IHle.
  - apply fib_mono.
Qed.

Theorem fib_2n1: forall n,
  fib(S(2*n)) = 2 * fib (S n) * fib n - fib n * fib n.
Proof.
  intros. rewrite fib_Sn_sub.
  replace (S (S (2*n))) with (2*(S n)) by lia.
  (* Eliminate subtractions *)
  symmetry; apply Nat.add_sub_eq_l.
  rewrite Nat.add_sub_assoc; [| apply fib_mono_strong; lia].
  apply Nat.add_sub_eq_l.
  (* Develop 2n and 2n2 terms *)
  rewrite fib_2n, fib_2n2.
  (* Use identity to replace subtraction *)
  destruct n; auto.
  rewrite <- fib_n_sub.
  (* Explode fib SSn and solve *)
  rewrite fib_SSn; lia.
Qed.

(* Now we can create the fib function on positive type *)

Fixpoint fib2_pos (p:positive): nat*nat :=
  match p with
  | xH => (1, 2)
  | xO p => let (a, b) := fib2_pos p in (a*a + (b-a)*(b-a), 2*b*a - a*a)
  | xI p => let (a, b) := fib2_pos p in (2*b*a - a*a, b*b + a*a)
  end.

Inductive fib_data (n a b: nat) :=
  fib_data_def: a = fib n /\ b = fib (S n) -> fib_data n a b.

Lemma fib_pos_2n: forall p a b,
  fib_data (Pos.to_nat p) a b ->
  fib_data (Pos.to_nat (xO p)) (a*a + (b-a)*(b-a)) (2*b*a - a*a).
Proof.
  intros p a b H.
  destruct H as [[H1 H2]].
  replace (Pos.to_nat (p~0)) with (2 * Pos.to_nat p) by lia.
  constructor.
  rewrite fib_2n, fib_2n1; auto.
Qed.

Lemma fib_pos_2n1: forall p a b,
  fib_data (Pos.to_nat p) a b ->
  fib_data (Pos.to_nat (xI p)) (2*b*a - a*a) (b*b + a*a).
Proof.
  intros p a b H.
  destruct H as [[H1 H2]].
  replace (Pos.to_nat (p~1)) with (S (2 * Pos.to_nat p)) by lia.
  constructor.
  replace (S (S (2 * Pos.to_nat p))) with (2 * (S (Pos.to_nat p))) by lia.
  rewrite fib_2n1, fib_2n2; auto.
Qed.

Theorem fib_correct: forall (p:positive) (a b: nat),
  fib2_pos p = (a, b) -> fib_data (Pos.to_nat p) a b.
Proof.
  induction p; [| | constructor; inversion H; auto];
  intros; inversion H as [Heq];
  destruct (fib2_pos p) as [u v];
  inversion Heq; subst;
  replace ((v + (v + 0)) * u) with (2*v*u) by lia.
  - apply fib_pos_2n1; auto.
  - apply fib_pos_2n; auto.
Qed. 

Definition nat_0_dec: forall n, {n = 0} + {n <> 0}.
Proof. destruct n; auto. Defined.

(* Now we prove that the function implements the specification *)
Definition fib_spec: forall n:nat, 
  {u:nat & {v:nat | u = fib n /\ v = fib (n+1)}}.
Proof.
  intros.
  destruct (nat_0_dec n) as [Hz|Hnz].
  - exists 1, 1; subst; auto.
  - destruct (fib2_pos (Pos.of_nat n)) as [a b] eqn: Heq.
    pose proof (fib_correct (Pos.of_nat n) a b Heq) as H.
    rewrite (Nat2Pos.id n Hnz) in H.
    exists a, b.
    replace (n+1) with (S n) by lia.
    apply H.
Qed.