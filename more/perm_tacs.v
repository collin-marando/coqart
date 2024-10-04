Require Import Arith.
Require Import List.
Import ListNotations.

(* The following is a continuation of Exercise 16.7. 
  In this file, we expand the NoPerm tactic to "Perm", a reflexion tactic
  that solves both goals of the form "perm l l'" and of the form "~ perm l l'"
  using the method suggested by the exercise. *)

(* Note that rather than use "num_occur" from 9.5 as in the exercise, we opt 
  to use "count_occ" from the standard library. This function is trivially
  equivalent, but has the added convenience of established properties, which
  are used at the end of "count_all". We show a proof of this equivalence before
  continuing. *)

Section trivial.
Variables (A : Set).
Hypothesis eq_dec: forall x y:A, {x = y} + {x <> y}.

Fixpoint num_occur (l: list A) (n: A) : nat :=
  match l with
  | nil => 0
  | a :: l' => 
    match (eq_dec a n) with
    | left _ => 1 + num_occur l' n
    | right _ => num_occur l' n
    end
  end.

Goal forall a l, num_occur l a = count_occ eq_dec l a.
Proof. auto. Qed.

End trivial.

(* The remainder is the construction of the "Perm" tactic *)

Inductive list_trans {A : Type} : list A -> list A -> Prop :=
  | lt_swap x y l : list_trans (x :: y :: l) (y :: x :: l)
  | lt_skip x l l': list_trans l l' -> list_trans (x :: l) (x :: l').

Lemma lt_sym {A : Type}: forall l l':list A,
  list_trans l l' -> list_trans l' l.
Proof.
  induction 1; constructor; auto.
Qed.

Inductive perm {A : Type} : list A -> list A -> Prop :=
  | lp_refl l : perm l l
  | lp_trans l l' l'': perm l l' -> list_trans l' l'' -> perm l l''.

Hint Resolve lp_refl : core.

Lemma perm_skip {A : Type}: forall (a : A) l l',
  perm l l' -> perm (a :: l) (a :: l').
Proof.
  induction 1; auto.
  econstructor.
  apply IHperm.
  apply lt_skip; auto.
Qed.

Lemma perm_cut {A : Type}: forall l l' l'':list A,
  perm l' l'' -> perm (l ++ l') (l ++ l'').
Proof.
  induction l; simpl; auto; intros.
  apply perm_skip; auto.
Qed.

Lemma perm_intro_r {A : Type}:
  forall l l': list A, perm l l' -> 
    forall l'', list_trans l'' l ->  perm l'' l'.
Proof.
  induction 1; intros.
  - econstructor; auto.
  - apply lp_trans with l'; auto.
Qed.

Lemma perm_trans {A : Type}: forall l l' l'':list A,
  perm l l' -> perm l' l'' -> perm l l''.
Proof.
  induction 1; auto.
  intros H'.
  apply IHperm.
  eapply perm_intro_r; eauto.
Qed.

Lemma perm_sym {A : Type}: forall l l':list A,
  perm l l' -> perm l' l.
Proof.
  induction 1; auto.
  apply perm_trans with l'; auto.
  eapply perm_intro_r; auto.
  apply lt_sym; auto.
Qed.

Lemma perm_rotate {A : Type}: forall (a:A) l,
  perm (a :: l) (l ++ [a]).
Proof.
  induction l; simpl; auto.
  eapply perm_trans with (a0 :: a :: l).
  - eapply lp_trans; auto.
    apply lt_swap.
  - eapply perm_skip.
    assumption.
Qed.

Lemma perm_app_swap {A : Type}: forall l l':list A,
  perm (l ++ l') (l' ++ l).
Proof.
  induction l; simpl; intros.
  - rewrite app_nil_r; auto.
  - eapply perm_trans.
    + apply perm_rotate.
    + change (l' ++ a :: l) with (l' ++ [a] ++ l).
      rewrite app_assoc, <- app_assoc.
      apply IHl.
Qed.

Lemma perm_middle {A : Type}: forall l1 (a : A) l l2, 
  perm l (l1 ++ l2) -> perm (a :: l) (l1 ++ a :: l2).
Proof.
  intros.
  eapply perm_trans.
  - apply perm_skip, H.
  - eapply perm_trans.
    apply perm_rotate.
    rewrite <- app_assoc.
    apply perm_cut.
    apply perm_sym.
    apply perm_rotate.
Qed.

Section count.
Variables (A : Set).
Hypothesis eq_dec: forall x y:A, {x = y} + {x <> y}.

Ltac simpldec :=
  match goal with
  | |- context [eq_dec ?x ?x]  =>
    destruct (eq_dec x x) as [Heq|F];
    try discriminate; try contradiction; auto; clear Heq
  | H : context [eq_dec ?x ?x] |- _ =>
    destruct (eq_dec x x) as [Heq|F];
    try discriminate; try contradiction; auto; clear Heq
  | _ => idtac
  end.

Definition occ := count_occ eq_dec.

Theorem trans_occur: forall l l':list A,
  list_trans l l' -> forall x, occ l x = occ l' x.
Proof.
  induction 1; simpl; intros z.
  - destruct (eq_dec _ _); destruct (eq_dec _ _); auto.
  - destruct (eq_dec _ _); auto.
Qed.

Theorem perm_occur: forall l l':list A,
  perm l l' -> forall x, occ l x = occ l' x.
Proof.
  induction 1; auto.
  intros x.
  rewrite IHperm.
  apply trans_occur; auto.
Qed.

Theorem no_perm: forall l l':list A, 
  (exists x, occ l x <> occ l' x) -> ~ perm l l'.
Proof.
  intros l l' [x H]; contradict H.
  apply perm_occur; auto.
Qed.

Fixpoint check_counts (l l' lt : list A) : bool :=
  match lt with
  | nil => true
  | t :: lt' => 
    let c1 := occ l t in
    let c2 := occ l' t in
    match Nat.eq_dec (occ l t) (occ l' t) with
    | left _ => check_counts l l' lt'
    | right _ => false
    end
  end.

(* This theorem allows us to build a reflection tactic for goal of the form "~ perm l l'" *)

Theorem counts_diff_not_perm: forall l l' lt,
  check_counts l l' lt = false -> ~ perm l l'.
Proof.
  induction lt; simpl; try discriminate.
  destruct (Nat.eq_dec (occ l a) (occ l' a)); auto.
  intros _; apply no_perm; eexists; eauto.
Qed.

(* Next we prove the inverse: check_counts l l' lt = true -> perm l l'. *)

Lemma occ_S: forall l (a : A) n,
  S n = occ l a -> exists l1 l2, l = l1 ++ a :: l2.
Proof.
  induction l; simpl; intros; [discriminate|].
  intros.
  destruct (eq_dec a a0); subst.
  - exists nil, l. auto.
  - apply IHl in H as [u [v H]].
    exists (a :: u), v. subst; auto.
Qed.

Lemma count_all: forall l l':list A,
  (forall a, occ l a = occ l' a) -> perm l l'.
Proof.
  unfold occ.
  induction l; simpl; intros.
  - destruct l'; auto.
    specialize H with a; simpl in H.
    simpldec.
  - destruct l' as [|a' l'].
    specialize H with a; simpl in H; simpldec.
    destruct (eq_dec a a'); subst.
    + apply perm_skip.
      simpl in *.
      apply IHl; intros.
      specialize H with a.
      destruct (eq_dec a' a); subst; auto.
    + pose proof (H a) as Ha.
      simpl in *; simpldec.
      destruct (eq_dec a' a) eqn:Eaa'; subst; simpldec.
      apply occ_S in Ha as [x [y Hl']].
      subst.
      change (a' :: x ++ a :: y) with ((a' :: x) ++ a :: y).
      apply perm_middle; simpl.
      apply IHl.
      intros b. specialize H with b. simpl.
      destruct (eq_dec a b); destruct (eq_dec a' b); subst; simpldec.
      rewrite count_occ_elt_eq in H; auto.
      all: rewrite count_occ_elt_neq in H; auto.
Qed.

Lemma not_in_app: forall (a : A) l l',
  ~ In a (l ++ l') -> ~ In a l /\ ~ In a l'.
Proof.
  intros.
  apply Decidable.not_or.
  contradict H.
  apply in_or_app; auto.
Qed.

Lemma not_in_count: forall a l,
  ~ In a l -> occ l a = 0.
Proof.
  induction l; simpl; auto.
  intros.
  destruct (eq_dec a0 a); subst; auto.
  contradict H; auto.
Qed.

Theorem check_counts_all: forall L l l',
  check_counts l l' L = true -> forall a, In a L -> occ l a = occ l' a.
Proof.
  induction L; intros; try contradiction.
  simpl in *.
  destruct (Nat.eq_dec (occ l a) (occ l' a)); try discriminate.
  destruct H0; subst; auto.
Qed.

Theorem check_all: forall l l',
  check_counts l l' (l ++ l') = true -> (forall a, occ l a = occ l' a).
Proof.
  intros.
  destruct (In_dec eq_dec a (l ++ l')).
  - eapply check_counts_all; eauto.
  - apply not_in_app in n.
    destruct n.
    rewrite !not_in_count; auto.
Qed.

Theorem counts_same_perm: forall l l',
  check_counts l l' (l ++ l') = true -> perm l l'.
Proof.
  intros.
  apply count_all.
  apply check_all.
  assumption.
Qed.

End count.

(* In the case where the two lists are equal and the goal is to prove they are
  permutations, Perm solves directly rather than converting to computable terms.
  This is both more efficient computationally, and more general as demonstrated below *)

Ltac Perm A eq_dec :=
  try solve [
    match goal with
    | [ |- (~ perm ?l ?l')] =>
      apply (counts_diff_not_perm A eq_dec) with (lt := app l l')
    | [ |- (perm ?l ?l)] => 
      apply lp_refl
    | [ |- (perm ?l ?l')] => 
      apply (counts_same_perm A eq_dec)
    end; auto]. 

Goal ~(perm [1;2;3] [1;3;2;4]).
  Perm nat Nat.eq_dec.
Qed.

Goal perm [1; 3; 5] [5; 3; 1].
  Perm nat Nat.eq_dec.
Qed.

Goal forall l, @perm nat l l.
  intros; Perm nat Nat.eq_dec.
Qed.

(* Note that this tactic cannot solve more abstract goals like the following: *)

Goal forall l l', @perm nat (l ++ l') (l' ++ l).
Proof.
  intros; Perm nat Nat.eq_dec.
Admitted.

(* See more/perm_tacs2 for a tactic which can solve this goal *)