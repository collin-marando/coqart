Require Export Zdiv.
Require Import ZArith.
Require Import Lia.
Require Import Arith.

(* Exercise 16.1 *)
(* Prove the lemmas verif_divide, divisor_smaller, check_range_correct, and check_correct. *)
Theorem verif_divide: forall m p: nat,
  0 < m -> 0 < p -> (exists q:nat, m = q*p) ->
    (Z_of_nat m mod Z_of_nat p = 0)%Z.
Proof.
  intros m p Hposm Hposp [q Heq]; subst.
  rewrite <- Nat2Z.inj_mod, Nat.Div0.mod_mul.
  auto.
Qed.

Theorem divisor_smaller: forall m p: nat,
  0 < m -> forall q:nat, m = q*p -> q <= m.
Proof.
  intros m p Hpos q.
  generalize dependent m.
  generalize dependent q.
  induction p; simpl; intros q m Hpos Heq.
  - lia.
  - rewrite Nat.mul_comm, Nat.mul_succ_l in Heq.
    lia.
Qed.

Fixpoint check_range (v:Z)(r:nat)(sr:Z) : bool :=
  match r with
  | O => true
  | S r' =>
    match (v mod sr)%Z with
    | Z0 => false
    | _ => check_range v r' (Z.pred sr)
    end
  end.

Definition check_primality (n:nat) :=
  check_range (Z_of_nat n) (pred (pred n)) (Z_of_nat (pred n)).

Lemma Z_abs_zero: forall z, Z.abs_nat z = 0 -> z = 0%Z.
Proof.
  induction z; simpl; intros; auto.
  all: pose proof (Pos2Nat.is_pos p); lia.
Qed.

Lemma Z_abs_nat_to_Z: 
  forall x:Z, (0 <= x)%Z -> (Z.of_nat (Z.abs_nat x)) = x.
Proof.
  intros.
  rewrite Nat2Z.inj_abs_nat.
  apply Z.abs_eq_iff; auto.
Qed.

Theorem check_range_correct: forall (v:Z)(r:nat)(rz:Z),
  (0 < v)%Z -> Z_of_nat (S r) = rz -> check_range v r rz = true ->
  ~(exists k:nat, k <= S r /\ k <> 1 /\ (exists q:nat, Z.abs_nat v = q*k)).
Proof.
  intros v r; induction r;
  intros rz Hpos Heq Hcheck H;
  destruct H as [k [Hle [Hn1 [q Hfact]]]].
  - assert (k = 0) by lia; subst.
    rewrite <- mult_n_O in Hfact.
    apply Z_abs_zero in Hfact; lia.
  - destruct k.
    + rewrite Nat.mul_comm in Hfact; simpl in Hfact.
      apply Z_abs_zero in Hfact; subst.
      lia.
    + unfold check_range in Hcheck; fold check_range in Hcheck.
      (* Convert Hcheck into an expression matching verif_divide *)
      rewrite <- (Z_abs_nat_to_Z v), <- Heq in Hcheck by lia.
      (* Then apply verif_divide *)
      rewrite verif_divide in Hcheck; try lia.
      (* and revert expression *)
      rewrite Z_abs_nat_to_Z, Heq in Hcheck by lia.
      inversion Hle.
      * subst; exists q; auto.   
      * case_eq ((v mod rz)%Z). intros Heqmod.
        rewrite Heqmod in Hcheck; discriminate.
        all: intros p Heqmod; rewrite Heqmod in Hcheck.
        all: destruct (IHr (Z.pred rz)); try lia; auto.
        all: exists (S k); repeat split; auto.
        all: exists q; auto.
Qed.

Theorem check_correct: forall p:nat,
  0 < p -> check_primality p = true ->
  ~(exists k:nat, k <> 1 /\ k <> p /\ (exists q:nat, p = q*k)).
Proof.
  unfold check_primality.
  intros p Hpos Hprime; intro Hdiv.
  destruct Hdiv as [k [Hneq1 [Hneq2 Heq]]].
  destruct p; [lia|].
  destruct p.
  - destruct Heq as [q Heq].
    symmetry in Heq.
    apply Nat.eq_mul_1 in Heq.
    lia.
  - simpl Init.Nat.pred in Hprime. 
    assert (HposZ: (0 < Z_of_nat (S (S p)))%Z) by lia.
    eapply (check_range_correct _ _ _ HposZ _ Hprime).
    rewrite Zabs2Nat.id.
    exists k; repeat split; auto; simpl.
    assert (k <= (S (S p))).
    destruct Heq as [q Heq].
    apply (divisor_smaller (S (S p)) q); auto; lia.
    lia.
  Unshelve. auto.
Qed.

(* Exercise 16.2 *)
(* Show that when a number n is the product of two numbers p and a,
  then one of these numbers is smaller than the square root of n. 
  Use this lemma to justify a method by reflection that only verifies 
  odd divisors smaller than the square root. *)

(* Note: Exercise says "smaller than" but it should be "smaller or equal to", 
  for when n is a perfect square *)

Open Scope Z_scope.

Lemma factor_le_sqrt: forall n p q, 0 < p < n -> 
  n = p * q -> p <= Z.sqrt n \/ q <= Z.sqrt n.
Proof.
  intros n p q Hlt Heq.
  destruct (Z_lt_le_dec (Z.sqrt n) p) as [H1|]; auto.
  destruct (Z_lt_le_dec (Z.sqrt n) q) as [H2|]; auto.
  assert (Hle1: (Z.sqrt n) + 1 <= p) by lia.
  assert (Hle2: (Z.sqrt n) + 1 <= q) by lia.
  elim (Z.lt_irrefl n).
  apply Z.lt_le_trans with (((Z.sqrt n)+1)*((Z.sqrt n)+1)).
  - rewrite Z.mul_add_distr_r, Z.mul_add_distr_l.
    pose proof (Z.sqrt_spec_alt n) as H.
    destruct H as [r [Heqn Hboundr]]; lia.
  - rewrite Heq at 3.
    assert (H: 0 < n) by lia.
    apply Z.sqrt_pos in H.
    apply Zmult_le_compat; auto; lia.
Qed.

(* Because we know that one of the factors must be less than or equal to
  the the square root, we need only check up to the square root when verifying
  factors. Also, other than 2, we need only check odd factors. *)

Definition divides p n := 
  match (n mod p) with
  | 0 => true
  | _ => false
  end.

(* First need a function that determines the number of odd numbers there are
  below or equal to a certain number. This will be used to decide the number
  of recursive steps for check_factors. We also need to know which odd number
  to start checking at. With these two pieces of info combined, we effectively
  give the checker a description of which odds factors to check.
  
  Note that we only care about positive number inputs *)

Definition which_odds' (z : Z) : Z * Z :=
  match z with
  | Zpos (xI z') => (Zpos z', z)
  | Zpos (xO z') => (Zpos z' - 1, z - 1)
  | Zpos xH => (0, 0)
  | _ => (0, 0)
  end. 

Compute (which_odds' 4).
Compute (which_odds' 5).

(* While this is efficient, note that in the case that z is even, we subtract from
  Zpos z' and from z, both of which will require the unraveling of z'
  to compute the value. Obviously, this would make the proof of correctness much
  more complicated, and for very little compute cost benefit. Alternatively, we can
  try to make it so that the two output numbers are related by a fixed property.
  Then when we prove correctness, it suffices to only check validility under 
  those conditions.
*)

(* For the even case, we change z'-1 to z' and z-1 to z+1. This means that
  we will be checking an extra case that is larger than the input value.
  While this is clearly redundant, doing so solves our problem, and we
  can expect the proof to be much more convenient *)

Definition which_odds (z : Z) : Z * Z :=
  match z with
  | Zpos (xI z') => (Zpos z', z)
  | Zpos (xO z') => (Zpos z', z + 1)
  | Zpos xH => (0, 1)
  | _ => (0, 1)
  end.

Lemma which_odds_i_pos: forall z p i,
  which_odds z = (i, p) -> 0 <= i.
Proof.
  intros z p i H.
  destruct z; simpl in *.
  - inversion H; lia.
  - destruct p0; inversion H; lia.
  - inversion H; lia.
Qed.

Lemma which_odds_consistent: forall z p i,
  0 < z -> which_odds z = (i, p) -> 2*i+1 = p.
Proof.
  destruct z; try discriminate.
  intros q i _; revert q i.
  induction p; simpl; intros q i Heq.
  all: inversion Heq; auto.
Qed.

(* Then, we design a function that, for some number n, checks only
  for divisibilty by 2 and odd factors less than or equal to some odd p.
  Given that this function is recursive but reasons about integers, which
  are harder to reason about through induction, we need use independent
  nat parameter to terminate the computation after a certain number of steps. *)

Fixpoint check_factors (i: nat) (p n: Z) :=
  match i with
  | O => divides 2 n
  | S i' => if divides p n then true else check_factors i' (p - 2) n
  end.

(* Before creating the prime checking function, we can verify the validity
  of this function under more general conditions. *)

Lemma check_factors_correct_2: forall (i n: nat) (p: Z),
  (1 < n)%nat ->
  check_factors i p (Z.of_nat n) = false ->
    ~(exists y, n = y*2)%nat.
Proof.
  intros i n p Hgt; revert p.
  induction i; simpl (check_factors _ _ _);
  intros p Hcheck; intro Heq; destruct Heq as [y Heq].
  - subst n. unfold divides in Hcheck.
    rewrite Nat2Z.inj_mul, Z_mod_mult in Hcheck.
    discriminate.
  - destruct (divides p (Z.of_nat n)); try discriminate.
    apply (IHi (p-2) Hcheck).
    exists y; assumption.
Qed.

(* For divisibility by odds, we need only check on inputs which have the
  conditions shared by the outputs of the which_odds function: 2*i+1 = p. *)

Lemma check_factors_correct: forall (i n: nat) (p: Z),
  (1 < n)%nat ->
  2*(Z.of_nat i)+1 = p ->
  check_factors i p (Z.of_nat n) = false ->
    forall x:nat, (1 < x <= 2*i+1)%nat -> ~(exists y, n = y*x)%nat.
Proof.
  intros i n p Hgt; revert p.
  induction i;
  intros p Heq Hcheck x Hlte; [lia|].
  intro H; destruct H as [y H].
  simpl in Hcheck.
  destruct (divides p (Z.of_nat n)) eqn:Hdiv; try discriminate.
  destruct (le_lt_eq_dec x (2 * S i + 1)) as [Hlt1 | Hxeq]; [lia| | ].
  destruct (le_lt_eq_dec x (2 * S i)) as [Hlt | Hxeq]; [lia| | ]; clear Hlt1.
  - eapply (IHi (p-2) _ Hcheck x). Unshelve.
    + lia.
    + exists y; assumption.
    + lia.
  - apply (check_factors_correct_2 _ _ _ Hgt Hcheck).
    exists (y * S i)%nat; lia.
  - unfold divides in Hdiv.
    destruct (Z.eq_dec (Z.of_nat n mod p) 0) as [HF | Hneq].
    + rewrite HF in Hdiv; discriminate.
    + contradict Hneq.
      subst n x.
      rewrite Nat2Z.inj_mul.
      replace (Z.of_nat (2 * S i + 1)) with p by lia.
      apply Z_mod_mult.
Qed.

Lemma Z_to_nat_to_Z: forall z : Z, 0 <= z -> Z.of_nat (Z.to_nat z) = z.
Proof.
  intros. destruct z; try lia.
Qed.

(* Now we can use the factor checking function to define a primality test *)

Definition is_prime (n : nat) :=
  let sz := (Z.sqrt (Z.of_nat n)) in 
  let (i, p) := which_odds sz in
  match n with
  | S (S n') => negb (check_factors (Z.to_nat i) p (Z.of_nat n))
  | _ => false
  end.

Theorem is_prime_correct: forall n,
  is_prime n = true ->
    ~(exists x:nat, x <> 1 /\ x <> n /\ (exists y:nat, n = y*x))%nat.
Proof.
  destruct n; try discriminate.
  destruct n as [|n']; try discriminate.
  remember (S (S n')) as n.
  unfold is_prime.
  destruct (which_odds (Z.sqrt (Z.of_nat n))) as [i p] eqn:Hwhich.

  assert (Hip: 2 * i + 1 = p).
  {
    apply (which_odds_consistent (Z.sqrt (Z.of_nat n))); auto.
    subst; simpl. lia.
  }

  assert (Hipos: 0 <= i).
  {
    eapply (which_odds_i_pos (Z.sqrt (Z.of_nat n))).
    eauto. 
  }

  rewrite Heqn, Bool.negb_true_iff.
  intros Hcheck.

  case_eq (Z.sqrt (Z.of_nat n)).
  all: try solve [ destruct n; discriminate].

  - intros p0 H.
    rewrite H in Hwhich; simpl in Hwhich.
    intros [x [Hneq1 [Hneqn [y Heqnyx]]]]; rewrite <- Heqn in *.

    assert (Hex: exists k:nat, (1 < (Z_of_nat k) <= (Z.sqrt (Z_of_nat n))) /\
               (exists q:nat, n=(k*q)%nat)).
    
    {
      destruct (factor_le_sqrt (Z_of_nat n) (Z_of_nat y) (Z_of_nat x)).
      - split.
        + lia.
        + assert (Hle: (y <= n)%nat).
          eapply divisor_smaller; eauto; lia.
          destruct (le_lt_eq_dec y n Hle).
          * lia.
          * subst y.
            assert (x = 1)%nat.
            destruct x; lia.
            contradiction.
      - lia.
      - exists y.
        repeat split.
        + destruct y; lia.
        + auto.
        + exists x; auto.
      - exists x.
        repeat split.
        + lia.
        + auto.
        + exists y; lia. 
    }

  destruct Hex as [k [[Hklower Hkupper] [q Heqnkq]]].
  destruct p0; inversion Hwhich.
  + eapply (check_factors_correct (Z.to_nat i) n).
    * lia.
    * rewrite Z_to_nat_to_Z; eauto.
    Unshelve.
    apply k.
    * auto.
    * lia.
    * exists q. lia.
  + eapply (check_factors_correct (Z.to_nat i) n).
    * lia.
    * rewrite Z_to_nat_to_Z; eauto.
    Unshelve.
    apply k.
    * auto.
    * lia.
    * exists q. lia.
  + elim (Zle_not_lt 0 (Z.sqrt (Z_of_nat n))).
    lia.
    lia.
Qed.