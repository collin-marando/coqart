Require Import Arith.
Require Import ZArith.

(* Exercise 7.1 *)
(* Prove the hypotheses of the primes section. *)

Section primes.
Definition divides (n m:nat) := exists p:nat, p*n = m.

Theorem divides_O : forall n:nat, divides n 0.
Proof.
  unfold divides; intros.
  exists 0; auto.
Qed.

Theorem divides_plus : forall n m:nat, divides n m -> divides n (n+m).
Proof.
  unfold divides.
  intros n m [k H].
  exists (1 + k).
  simpl; auto.
Qed.

Theorem not_divides_plus : forall n m:nat, ~divides n m -> ~divides n (n+m).
Proof.
  unfold divides.
  intros n m H.
  contradict H.
  destruct H as [k H].
  revert n m H.
  destruct k.
  - exists 0; simpl in *.
    destruct n; auto; discriminate.
  - simpl. intros. exists k.
    rewrite <- (Nat.add_cancel_l _ _ n).
    assumption.
Qed.

Theorem not_divides_lt : forall n m:nat, 0<m -> m<n -> ~divides n m.
Proof.
  unfold divides.
  intros n m Hnz Hlt [k H].
  destruct k; simpl in H.
  - destruct Hnz; discriminate.
  - clear Hnz; subst m.
    contradict Hlt.
    rewrite Nat.nlt_ge.
    apply Nat.le_add_r.
Qed.

Theorem not_lt_2_divides: forall n m:nat, n<>1 -> n<2 -> 0<m -> ~divides n m.
Proof.
  intros.
  destruct n.
  - unfold divides.
    intros [k F].
    rewrite Nat.mul_comm in F.
    simpl in F; subst m.
    contradict H1.
    apply Nat.lt_irrefl.
  - destruct n.
    + contradiction.
    + repeat apply Arith_prebase.lt_S_n in H0.
      contradict H0.
      apply Nat.nlt_0_r.
Qed.

Theorem le_plus_minus : forall n m:nat, le n m -> m = n+(m-n).
Proof.
  intros.
  rewrite Nat.add_comm.
  symmetry.
  apply (Nat.sub_add _  _ H).
Qed.

Theorem lt_lt_or_neg: forall n m:nat, n < S m -> n<m \/ n=m.
Proof.
  intros.
  rewrite Nat.lt_succ_r in H.
  apply (Lt.le_lt_or_eq_stt _ _ H).
Qed.

Ltac le_S_star := apply le_n || (apply le_S; le_S_star).

Ltac check_not_divides := 
  match goal with
  | [ |- (~divides ?X1 ?X2) ] =>
    cut (X1<=X2); [ idtac | le_S_star ]; intros Hle;
    rewrite (le_plus_minus _ _ Hle); apply not_divides_plus;
    simpl; clear Hle; check_not_divides
  | [ |- _ ] => apply not_divides_lt; unfold lt; le_S_star
  end.

Goal ~divides 5 16.
Proof.
  check_not_divides.
Qed.

(* Exercise 7.2 *)
(* The ZArith library provides the following two theorems:

  Check Zpos_xI.
    Zpos_xI : forall p : positive, Zpos (xI p) = (2 * Zpos p + 1)%Z
  Check Zpos_xO.
    Zpos_xO : forall p : positive, Zpos (xO p) = (2 * Zpos p)%Z

  The number 2%Z actually the number "pos (x0 xH)."
  Write a tactic that rewrites as many times as possible 
  with these two theorems without entering a loop. *)

Open Scope Z_scope.

Ltac positive_to_mult_simpl :=
  match goal with
  | [ |- context [(xI ?p)]] => 
    rewrite (Zpos_xI p); positive_to_mult_simpl
  | [ |- context [(xO ?p)]] => 
    match p with
    | xH => fail 1
    | _ => rewrite (Zpos_xO p); positive_to_mult_simpl
    end
  | [ |- _] => idtac
  end.

Goal 25 = 5*5.
Proof.
  positive_to_mult_simpl.
  auto.
Qed.