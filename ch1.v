(* 1.5 - A Sorting Example *)
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

Locate "_ <= _ ".
Open Scope Z_scope.

Inductive sorted : list Z -> Prop :=
  | sorted0: sorted nil
  | sorted1 x: sorted x
  | sorted2 x y l: sorted (y :: l) -> x <= y -> sorted (x :: y :: l).

Fixpoint nb_occur (z: Z) (l : list Z) : nat :=
  match l with
  | nil => 0
  | x :: l' => (if x =? z then 1 else 0) + nb_occur z l'
  end.

Definition perm (l l': list Z) : Prop :=
  forall z : Z, nb_occur z l = nb_occur z l'.

Lemma perm_refl: forall l, perm l l.
Proof. unfold perm. reflexivity. Qed.

Lemma perm_sym: forall l l', perm l l' -> perm l' l.
Proof. unfold perm. symmetry. auto. Qed.

Lemma perm_trans: forall l l' l'', perm l l' -> perm l' l'' -> perm l l''.
Proof. unfold perm. intros. rewrite H. auto. Qed.

Lemma perm_cons: forall z l l', perm l l' -> perm (z::l) (z::l').
Proof.
  unfold perm. intros.
  simpl. rewrite H. auto.
Qed.

Lemma perm_swap: forall x y l, perm (x::y::l) (y::x::l).
Proof.
  unfold perm. intros.
  simpl. rewrite !Nat.add_assoc.
  f_equal. rewrite Nat.add_comm. auto.
Qed.

Fixpoint sort_aux z l :=
  match l with
  | nil => [z]
  | x :: l' => if z <=? x then z :: l else x :: (sort_aux z l')
  end.

Lemma aux_perm : forall z l, perm (z::l) (sort_aux z l).
Proof.
  intros. induction l; simpl.
  - apply perm_refl.
  - destruct (z <=? a).
    + apply perm_refl.
    + eapply perm_trans.
      * apply perm_swap.
      * apply perm_cons, IHl.
Qed.

Lemma aux_sorted : forall z l, sorted l -> sorted (sort_aux z l).
Proof.
  intros. induction l; simpl.
  - constructor.
  - destruct (z <=? a) eqn:Hle.
    + constructor.
    + constructor.
Qed.

Fixpoint sort l :=
  match l with
  | nil => nil
  | z :: l => sort_aux z (sort l)
  end.
  
Definition is_sorter f := forall l, sorted (f l) /\ perm l (f l).

Theorem sort_sorted : forall l, sorted (sort l).
Proof.
  intros. induction l; simpl.
  - constructor.
  - constructor.
Qed. 

Theorem sort_perm : forall l, perm l (sort l).
Proof.
  intros. induction l; simpl.
  - constructor.
  - eapply perm_trans.
    + apply perm_cons, IHl.
    + apply aux_perm.
Qed. 

Theorem sort_spec : is_sorter sort.
Proof.
  unfold is_sorter.
  intros. split.
  - apply sort_sorted.
  - apply sort_perm.
Qed.