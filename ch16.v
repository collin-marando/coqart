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
    unshelve eapply (check_range_correct _ _ _ HposZ _ Hprime); auto.
    rewrite Zabs2Nat.id.
    exists k; repeat split; auto; simpl.
    assert (k <= (S (S p))).
    destruct Heq as [q Heq].
    apply (divisor_smaller (S (S p)) q); auto; lia.
    lia.
Qed.

(* Exercise 16.2 *)
(* Show that when a number n is the product of two numbers p and a,
  then one of these numbers is "smaller than" the square root of n. 
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
  - unshelve eapply (IHi (p-2) _ Hcheck x); try lia.
    exists y; assumption.
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

(* Now we can use the factor checking function to define a primality test *)

Definition is_prime (n : nat) :=
  let sz := (Z.sqrt (Z.of_nat n)) in 
  let (i, p) := which_odds sz in
  match n with
  | S (S n') => negb (check_factors (Z.abs_nat i) p (Z.of_nat n))
  | _ => false
  end.

Theorem is_prime_correct: forall n,
  is_prime n = true ->
    ~(exists x:nat, x <> 1 /\ x <> n /\ (exists y:nat, n = y*x))%nat.
Proof.
  (* 1 < n *)
  destruct n; try discriminate;
  destruct n as [|n']; try discriminate.
  remember (S (S n')) as n.
  
  unfold is_prime.
  destruct (which_odds (Z.sqrt (Z.of_nat n))) as [i p] eqn:Hwhich.
  rewrite Heqn, Bool.negb_true_iff, <- Heqn.
  intros Hcheck.

  (* sqrt n is a positive number *)
  case_eq (Z.sqrt (Z.of_nat n)).
  all: try solve [ destruct n; discriminate].
  
  intros p0 H [x [Hneq1 [Hneqn [y Heqnyx]]]].
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
      repeat split; auto.
      + destruct y; lia.
      + exists x; auto.
    - exists x.
      repeat split; auto.
      + lia.
      + exists y; lia. 
  }

  destruct Hex as [k [[Hklower Hkupper] [q Heqnkq]]].

  rewrite H in Hwhich; simpl in Hwhich.
  destruct p0; inversion Hwhich;
  unshelve eapply (check_factors_correct (Z.abs_nat i) n p _ _ _ k).
  all: try lia.
  all: try assumption.
  all: exists q; lia.
Qed.

Close Scope Z_scope.

(* End 16.2 *)

Module assoc.

Inductive bin: Set := node : bin -> bin -> bin | leaf: nat -> bin.

Fixpoint flatten_aux (t fin:bin) {struct t} : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
  end.

Fixpoint flatten (t:bin) : bin := 
  match t with
  | node t1 t2 => flatten_aux t1 (flatten t2)
  | x => x
  end.

Fixpoint bin_nat (t:bin) : nat :=
  match t with
  | node t1 t2 => bin_nat t1 + bin_nat t2
  | leaf n => n
  end.

(* Exercise 16.3 *)
(* Prove the theorems flatten aux_valid, flatten_valid, and flatten_valid_2. *)

Theorem flatten_aux_valid: forall t t':bin,
  bin_nat t + bin_nat t' = bin_nat (flatten_aux t t').
Proof.
  induction t; intros t'; simpl; auto.
  rewrite <- Nat.add_assoc.
  rewrite IHt2.
  rewrite IHt1.
  reflexivity.
Qed.

Theorem flatten_valid: forall t:bin,
  bin_nat t = bin_nat (flatten t).
Proof.
  induction t; simpl; auto.
  rewrite <- flatten_aux_valid.
  auto.
Qed.

Theorem flatten_valid_2: forall t t':bin,
  bin_nat (flatten t) = bin_nat (flatten t') -> bin_nat t = bin_nat t'.
Proof.
  intros; rewrite (flatten_valid t); rewrite (flatten_valid t'); auto.
Qed.

(* End 16.3 *)

Section assoc_eq.

Import List.

Variables (A : Set) (f : A->A->A)
  (assoc: forall x y z:A, f x (f y z) = f (f x y) z).

Fixpoint bin_A (l:list A) (def:A) (t:bin) {struct t} : A :=
  match t with
  | node t1 t2 => f (bin_A l def t1) (bin_A l def t2)
  | leaf n => nth n l def
  end.

(* Exercise 16.4 *)
(* Using the hypothesis f_assoc, prove the three theorems flatten_aux_valid_A,
  flatten_valid_A, and flatten_valid_A_2. *)

Theorem flatten_aux_valid_A: forall (l:list A) (def:A) (t t':bin),
  f (bin_A l def t) (bin_A l def t') = bin_A l def (flatten_aux t t').
Proof.
  induction t; simpl; intros; auto.
  rewrite <- assoc.
  rewrite IHt2.
  rewrite IHt1.
  auto.
Qed.

Theorem flatten_valid_A: forall (l:list A) (def:A) (t:bin),
  bin_A l def t = bin_A l def (flatten t).
Proof.
  induction t; simpl; auto.
  rewrite <- flatten_aux_valid_A, IHt2.
  auto.
Qed.

Theorem flatten_valid_A_2: forall (t t':bin) (l:list A) (def:A),
  bin_A l def (flatten t) = bin_A l def (flatten t') -> bin_A l def t = bin_A l def t'.
Proof.
  intros.
  rewrite (flatten_valid_A _ _ t).
  rewrite (flatten_valid_A _ _ t').
  auto.
Qed.

End assoc_eq.

(* End 16.4 *)

Section tactic.

  Ltac term_list f l v := 
    match v with
    | f ?X1 ?X2 => 
      let l1 := term_list f l X2 in
        term_list f l1 X1
    | ?X1 => constr:(cons X1 l) 
    end.

  Ltac compute_rank l n v := match l with
    | cons ?X1 ?X2 =>
      let tl := constr:(X2) in
        match constr:(X1 = v) with
        | ?X1 = ?X1 => n
        | _ => compute_rank tl (S n) v
        end
    end.
  
  Ltac model_aux l f v := match v with
    | f ?X1 ?X2 => 
      let r1 := model_aux l f X1 with r2 := model_aux l f X2 in
        constr:(node r1 r2)
    | ?X1 => let n := compute_rank l 0 X1 in
        constr:(leaf n)
    end.
  
  Ltac model_A A f def v := 
    let l := term_list f (nil (A:=A)) v in
    let t := model_aux l f v in
    constr:(bin_A A f l def t).
  
  (* At the end of the tactic, we also remove the zero. *)
  Ltac assoc_eq A f assoc_thm :=
    match goal with
    | |- @eq A ?X1 ?X2 =>
      let term1 := model_A A f X1 X1 with
        term2 := model_A A f X1 X2 in
        (change (term1 = term2));
        apply flatten_valid_A_2 with ( 1 := assoc_thm ); 
        auto
    end.
  
  Theorem reflection_test3:
  forall (x y z t u : Z),  (x * (((y * z) )* (t * u)) = (x * ( y)) * (z * (t * u)))%Z.
  Proof.
    intros; assoc_eq Z Zmult Zmult_assoc.
  Qed.

End tactic.

End assoc.

(* Exercise 16.5 *)
(* Adapt the tactic to the case where the binary operation has a neutral element,
  like zero for addition. It should be able to prove equalities of the form
  "(x+0)+(y+(z+0)) = x+(y+(z+0))" *)

Module neutral_element.

Inductive bin: Set :=
  | node: bin -> bin -> bin 
  | leaf: nat -> bin
  | neutral: bin.

Fixpoint flatten_aux (t fin:bin) {struct t} : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
  end.

Fixpoint flatten (t:bin) : bin := 
  match t with
  | node t1 t2 => flatten_aux t1 (flatten t2)
  | x => x
  end.

Fixpoint remove_neutral1 (t : bin) : bin :=
 match t with
   leaf n => leaf n
  | neutral => neutral
  | node neutral t' => remove_neutral1 t'
  | node t t' => node t (remove_neutral1 t')
 end.
 
Fixpoint remove_neutral2 (t : bin) : bin :=
 match t with
   leaf n => leaf n
  | neutral => neutral
  | node t neutral => t
  | node t1 t2 => node t1 (remove_neutral2 t2)
 end.

Definition remove_neutral (t : bin) := remove_neutral2 (remove_neutral1 t).

Section assoc_eq.

Import List.

Variables (A : Set) (f : A->A->A) (zero_A : A)
  (assoc: forall x y z:A, f x (f y z) = f (f x y) z)
  (zero_left: forall (x : A), f zero_A x = x)
  (zero_right: forall (x : A), f x zero_A = x).

Fixpoint bin_A (l:list A) (t:bin) {struct t} : A :=
  match t with
  | node t1 t2 => f (bin_A l t1) (bin_A l t2)
  | leaf n => nth n l zero_A
  | neutral => zero_A
  end.

Theorem flatten_aux_valid_A: forall (l:list A) (t t':bin),
  f (bin_A l t) (bin_A l t') = bin_A l (flatten_aux t t').
Proof.
  induction t; simpl; intros; auto.
  rewrite <- assoc.
  rewrite IHt2.
  rewrite IHt1.
  auto.
Qed.

Theorem flatten_valid_A: forall (l:list A) (t:bin),
  bin_A l t = bin_A l (flatten t).
Proof.
  induction t; simpl; auto.
  rewrite <- flatten_aux_valid_A, IHt2.
  auto.
Qed.

Theorem flatten_valid_A_2: forall (t t':bin) (l:list A),
  bin_A l (flatten t) = bin_A l (flatten t') -> bin_A l t = bin_A l t'.
Proof.
  intros.
  rewrite (flatten_valid_A _ t).
  rewrite (flatten_valid_A _ t').
  auto.
Qed.

Theorem remove_neutral1_valid_A:
 forall (l : list A) (t : bin), bin_A l (remove_neutral1 t) = bin_A l t.
Proof.
intros l t; elim t; auto.
intros t1; case t1; simpl.
- intros t1' t1'' IHt1 t2 IHt2; rewrite IHt2; trivial.
- intros n IHt1 t2 IHt2; rewrite IHt2; trivial.
- intros IHt1 t2 IHt2; rewrite zero_left; trivial.
Qed.
 
Theorem remove_neutral2_valid_A:
 forall (l : list A) (t : bin),  bin_A l (remove_neutral2 t) = bin_A l t.
Proof.
  intros l t; elim t; auto.
  intros t1 IHt1 t2; case t2; simpl.
  - intros t2' t2'' IHt2; rewrite IHt2; trivial.
  - auto.
  - intros IHt2; rewrite zero_right; trivial.
Qed. 
 
Theorem remove_neutral_equal: forall (t t' : bin) (l : list A),
  bin_A l (remove_neutral t) = bin_A l (remove_neutral t') -> bin_A l t = bin_A l t'.
Proof.
  unfold remove_neutral; intros t t' l.
  repeat rewrite remove_neutral2_valid_A.
  repeat rewrite remove_neutral1_valid_A.
  trivial.
Qed.

End assoc_eq.

Ltac term_list f zero l v := 
  match v with
  | f ?X1 ?X2 => 
    let l1 := term_list f zero l X2 in
      term_list f zero l1 X1
  | zero => l
  | ?X1 => constr:(cons X1 l) 
  end.

Ltac compute_rank l n v := 
  match l with
  | cons ?X1 ?X2 =>
    let tl := X2 in
      match constr:(X1 = v) with
      | ?X1 = ?X1 => n
      | _ => compute_rank tl (S n) v
      end
  end.

Ltac model_aux l f zero v := 
  match v with
  | f ?X1 ?X2 => 
    let r1 := model_aux l f zero X1 with r2 := model_aux l f zero X2 in
      constr:(node r1 r2)
  | zero => neutral
  | ?X1 => let n := compute_rank l 0 X1 in
      constr:(leaf n)
  end.

Ltac model_A A f zero v := 
  let l := term_list f zero (nil (A:=A)) v in
  let t := model_aux l f zero v in
  constr:(bin_A A f zero l t).

Ltac assoc_eq A f zero assoc_thm neutral_left_thm neutral_right_thm :=
  match goal with
  | |- @eq A ?X1 ?X2 =>
    let term1 := model_A A f zero X1 with
      term2 := model_A A f zero X2 in
      (change (term1 = term2); 
      apply flatten_valid_A_2 with ( 1 := assoc_thm );
      apply remove_neutral_equal
        with ( 1 := neutral_left_thm ) ( 2 := neutral_right_thm ); auto)
  end.

Theorem reflection_test_neutral: forall (x y z t u : Z),
  ((x + 0) + (y + (z + 0)) = x + (y + (z + 0)))%Z.
Proof.
  intros; assoc_eq Z Z.add 0%Z Z.add_assoc Z.add_0_l Z.add_0_r.
Qed.

(* End 16.5 *)

Fixpoint nat_le_bool (n m:nat) {struct m} : bool :=
  match n, m with
  | 0, _ => true
  | S n, 0 => false
  | S n, S m => nat_le_bool n m
  end.

Fixpoint insert_bin (n:nat) (t:bin) {struct t} : bin :=
  match t with
  | leaf m => 
    match nat_le_bool n m with
    | true => node (leaf n) (leaf m)
    | false => node (leaf m) (leaf n)
    end
  | node (leaf m) t' =>
    match nat_le_bool n m with
    | true => node (leaf n) t
    | false => node (leaf m) (insert_bin n t')
    end
  | t => node (leaf n) t
  end.

Fixpoint sort_bin (t:bin) : bin := 
  match t with
  | node (leaf n) t' => insert_bin n (sort_bin t')
  | t => t
  end.

Section commut_eq.
Variables (A : Set) (f : A -> A -> A) (zero_A : A)
  (zero_left: forall (x : A), f zero_A x = x)
  (zero_right: forall (x : A), f x zero_A = x).
Hypothesis comm : forall x y:A, f x y = f y x.
Hypothesis assoc : forall x y z:A, f x (f y z) = f (f x y) z.

Definition bin_A' := bin_A A f zero_A.

Import List.

Theorem insert_is_f: forall (l:list A) (n:nat) (t:bin),
  bin_A' l (insert_bin n t) = f (nth n l zero_A) (bin_A' l t).
Proof.
  induction t; simpl; intros.
  - destruct t1; auto.
    destruct (nat_le_bool n n0) eqn:E; auto.
    simpl; auto.
    rewrite IHt2.
    repeat rewrite assoc; rewrite (comm (nth n l zero_A)); auto.
  - destruct (nat_le_bool n n0) eqn:E; auto.
  - auto.
Qed.

Theorem sort_eq : forall (l:list A) (t:bin),
  bin_A' l (sort_bin t) = bin_A' l t.
Proof.
  induction t; simpl; auto.
  destruct t1; auto.
  rewrite insert_is_f; rewrite IHt2.
  reflexivity.
Qed.

Theorem sort_eq_2 : forall (l:list A) (t1 t2:bin),
  bin_A' l (sort_bin t1) = bin_A' l (sort_bin t2) -> bin_A' l t1 = bin_A' l t2.
Proof.
  intros.
  rewrite <- (sort_eq _ t1).
  rewrite <- (sort_eq _ t2).
  assumption.
Qed.

End commut_eq.

Ltac comm_eq A f zero_A assoc_thm comm_thm neutral_left_thm neutral_right_thm := 
  match goal with
  | [|- (?X1 = ?X2) ] => 
    let l := term_list f zero_A (nil (A:=A)) X1 in
    let term1 := model_aux l f zero_A X1
    with term2 := model_aux l f zero_A X2 in
    (change (bin_A A f zero_A l term1 = bin_A A f zero_A l term2);
    apply flatten_valid_A_2 with (1 := assoc_thm);
    apply remove_neutral_equal
        with ( 1 := neutral_left_thm ) ( 2 := neutral_right_thm );
    apply sort_eq_2 with (1 := comm_thm) (2 := assoc_thm); auto)
  end.

Theorem reflection_test4 : forall x y z:Z, (x + (y + z) = (z + x) + y)%Z.
Proof.
  intros x y z; comm_eq Z Zplus 0%Z Zplus_assoc Z.add_comm Z.add_0_l Z.add_0_r.
Qed.

Theorem reflection_test5 : forall x y z:Z, (x + (y + z) + 0 = 0 + (z + x) + y)%Z.
Proof.
  intros x y z; comm_eq Z Zplus 0%Z Zplus_assoc Z.add_comm Z.add_0_l Z.add_0_r.
Qed.

End neutral_element.

(* End 16.6 *)

(* Exercise 16.7 *)
(* Using the notion of permutations defined in Exercise 8.4 page 216 and the
  counting function defined in Exercise 9.5 page 256, show that if a list is
  a permutation of another list, then any natural number occurs as many times
  in both lists. *)

(* From Exercise 8.5 *)
Require Import List.
Import ListNotations.

Inductive list_trans {A : Type} : list A -> list A -> Prop :=
  | lt_swap x y l : list_trans (x :: y :: l) (y :: x :: l)
  | lt_skip x l l': list_trans l l' -> list_trans (x :: l) (x :: l').

Inductive list_perm {A : Type} : list A -> list A -> Prop :=
  | lp_refl l : list_perm l l
  | lp_trans l l' l'': list_perm l l' -> list_trans l' l'' -> list_perm l l''.

Section count.
Variables (A : Set).
Hypothesis eq_dec: forall x y:A, {x = y} + {x <> y}.

(* From 9.5, made generic *)
Fixpoint num_occur (l: list A) (n: A) : nat :=
  match l with
  | nil => 0
  | a :: l' => 
    match (eq_dec a n) with
    | left _ => 1 + num_occur l' n
    | right _ => num_occur l' n
    end
  end.

Theorem trans_occur: forall l l':list A,
  list_trans l l' -> forall x, num_occur l x = num_occur l' x.
Proof.
  induction 1; simpl; intros z.
  - destruct (eq_dec _ _); destruct (eq_dec _ _); auto.
  - destruct (eq_dec _ _); auto.
Qed.

Theorem perm_occur: forall l l':list A,
  list_perm l l' -> forall x, num_occur l x = num_occur l' x.
Proof.
  induction 1; auto.
  intros x.
  rewrite IHlist_perm.
  apply trans_occur; auto.
Qed.

(* Build a specialized reflection tactic "NoPerm" that solves goals of the
  form "~ perm l l'" by finding an element of the first list that does not occur the
  same number of times in both lists. *)

Theorem no_perm: forall l l':list A, 
  (exists x, num_occur l x <> num_occur l' x) -> ~ list_perm l l'.
Proof.
  intros l l' [x H]; contradict H.
  apply perm_occur; auto.
Qed.

Fixpoint check_counts (l l' lt : list A) : bool :=
  match lt with
  | nil => true
  | t :: lt' => 
    let c1 := num_occur l t in
    let c2 := num_occur l' t in
    match Nat.eq_dec (num_occur l t) (num_occur l' t) with
    | left _ => check_counts l l' lt'
    | right _ => false
    end
  end.

Theorem counts_in_perms: forall l l' lt,
  check_counts l l' lt = false -> ~ list_perm l l'.
Proof.
  induction lt; simpl; try discriminate.
  destruct (Nat.eq_dec (num_occur l a) (num_occur l' a)); auto.
  intros _; apply no_perm; eexists; eauto.
Qed.

End count.

Ltac NoPerm A eq_dec :=
  match goal with
  | [ |- (~ list_perm ?l ?l')] =>
    apply (counts_in_perms A eq_dec) with (lt := app l l'); auto
  end.

Goal ~(list_perm [1;2;3] [1;3;2;4]).
Proof.
  NoPerm nat Nat.eq_dec.
Qed.

(* End 16.7 *)

(* See more/perm_tacs for a reflexion tactic that solves both goals of the form
  "perm l l'" and of the form "~ perm l l'" *)