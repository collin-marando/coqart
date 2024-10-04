Require Import Arith.
Require Import List.
Import ListNotations.

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

Lemma perm_cut_l {A : Type}: forall l l' l'':list A,
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

Lemma perm_cut_r {A : Type}: forall l l' l'':list A,
  perm l' l'' -> perm (l' ++ l) (l'' ++ l).
Proof.
  induction l; simpl; auto; intros.
  - rewrite !app_nil_r; auto.
  - eapply perm_trans, perm_app_swap.
    apply perm_sym.
    eapply perm_trans, perm_app_swap.
    apply perm_cut_l.
    apply perm_sym; auto.
Qed.

(* Unused *)
Lemma perm_middle {A : Type}: forall l1 (a : A) l l2, 
  perm l (l1 ++ l2) -> perm (a :: l) (l1 ++ a :: l2).
Proof.
  intros.
  eapply perm_trans.
  - apply perm_skip, H.
  - eapply perm_trans.
    apply perm_rotate.
    rewrite <- app_assoc.
    apply perm_cut_l.
    apply perm_sym.
    apply perm_rotate.
Qed.

Module test.

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

Section full_perm.

Variables (A : Set).

Fixpoint bin_l (l: list (list A)) (t:bin) {struct t} : list A :=
  match t with
  | node t1 t2 => bin_l l t1 ++ bin_l l t2
  | leaf n => nth n l []
  | neutral => []
  end.

Theorem flatten_aux_valid: forall (t t':bin) L,
  perm (bin_l L t ++ bin_l L t') (bin_l L (flatten_aux t t')).
Proof.
  induction t; intros t' L; simpl; auto.
  rewrite <- app_assoc.
  apply perm_trans with (bin_l L t1 ++ bin_l L (flatten_aux t2 t')); auto.
  apply perm_cut_l; auto.
Qed.

Theorem flatten_valid: forall (t:bin) L,
  perm (bin_l L t) (bin_l L (flatten t)).
Proof.
  induction t; simpl; auto; intros.
  apply perm_trans with (bin_l L t1 ++ bin_l L (flatten t2)).
  - apply perm_cut_l; auto.
  - apply flatten_aux_valid.
Qed.

Theorem flatten_valid_2: forall (t t':bin) L,
  perm (bin_l L (flatten t)) (bin_l L (flatten t')) -> perm (bin_l L t) (bin_l L t').
Proof.
  intros.
  eapply perm_trans. apply flatten_valid.
  apply perm_sym.
  eapply perm_trans. apply flatten_valid.
  apply perm_sym; auto.
Qed.

Theorem remove_neutral1_valid_A:
 forall l (t : bin), bin_l l (remove_neutral1 t) = bin_l l t.
Proof.
intros l t; elim t; auto.
intros t1; case t1; simpl.
- intros t1' t1'' IHt1 t2 IHt2; rewrite IHt2; trivial.
- intros n IHt1 t2 IHt2; rewrite IHt2; trivial.
- intros IHt1 t2 IHt2; auto.
Qed.
 
Theorem remove_neutral2_valid_A:
 forall l (t : bin), bin_l l (remove_neutral2 t) = bin_l l t.
Proof.
  intros l t; elim t; auto.
  intros t1 IHt1 t2; case t2; simpl.
  - intros t2' t2'' IHt2; rewrite IHt2; trivial.
  - auto.
  - rewrite app_nil_r; auto.
Qed. 
 
Theorem remove_neutral_perm: forall (t t' : bin) l,
  perm (bin_l l (remove_neutral t)) (bin_l l (remove_neutral t')) -> perm (bin_l l t) (bin_l l t').
Proof.
  unfold remove_neutral; intros t t' l.
  repeat rewrite remove_neutral2_valid_A.
  repeat rewrite remove_neutral1_valid_A.
  trivial.
Qed.

Theorem insert_is_f: forall (l:list (list A)) (n:nat) (t:bin),
  perm (bin_l l (insert_bin n t)) ((nth n l []) ++ (bin_l l t)).
Proof.
  induction t; simpl; intros.
  - destruct t1; auto.
    destruct (nat_le_bool n n0) eqn:E; auto.
    simpl; auto.
    eapply perm_trans.
    apply perm_cut_l, IHt2.
    repeat rewrite app_assoc.
    apply perm_cut_r.
    apply perm_app_swap.
  - destruct (nat_le_bool n n0); simpl; auto.
    apply perm_app_swap.
  - rewrite app_nil_r; auto.
Qed.

Theorem sort_perm : forall l (t:bin),
  perm (bin_l l (sort_bin t)) (bin_l l t).
Proof.
  induction t; simpl; auto.
  destruct t1; auto.
  eapply perm_trans. apply insert_is_f.
  eapply perm_trans. apply perm_cut_l, IHt2.
  auto.
Qed.

Theorem sort_perm_2 : forall l (t1 t2:bin),
  perm (bin_l l (sort_bin t1)) (bin_l l (sort_bin t2)) -> perm (bin_l l t1) (bin_l l t2).
Proof.
  intros.
  eapply perm_trans, sort_perm.
  apply perm_sym.
  eapply perm_trans, sort_perm.
  apply perm_sym; auto.
Qed.

End full_perm.

Ltac term_list l v := 
  match v with
  | ?X1 ++ ?X2 => 
    let l1 := term_list l X2 in
      term_list l1 X1
  | [] => l
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

Ltac model_aux l v := 
  match v with
  | ?X1 ++ ?X2 => 
    let r1 := model_aux l X1 with r2 := model_aux l X2 in
      constr:(node r1 r2)
  | [] => neutral
  | ?X1 => let n := compute_rank l 0 X1 in
      constr:(leaf n)
  end.

Ltac comm_perm A := 
  try solve [
  match goal with
  | [|- perm ?X1 ?X2 ] => 
    let l := term_list (nil (A:=(list A))) X1 in
    let term1 := model_aux l X1
    with term2 := model_aux l X2 in
    (change (perm (bin_l A l term1) (bin_l A l term2));
    apply flatten_valid_2;
    apply remove_neutral_perm;
    apply sort_perm_2; simpl; auto)
  end].

Goal forall l l' x, @perm nat (l ++ l' ++ [x]) ([x] ++ l' ++ l).
  intros; comm_perm nat.
Qed.

(* TODO: Handle cons in tactic also *)

Goal forall l l' x, @perm nat (3 :: l ++ l' ++ [x]) (3 :: x :: l' ++ l).
  intros. 
  change (perm ([3] ++ l ++ l' ++ [x]) ([3] ++ [x] ++ l' ++ l)).
  intros; comm_perm nat.
Qed.