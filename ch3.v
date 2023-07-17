Section Minimal_propositional_logic.
Variables P Q R T : Prop.

(* Exercise 3.1 *)
(* Reconstitute the sequence of typing judgements that
  corresponds to the type computation done by the 
  Coq system for the following command *)

Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof. intros H1 H2 p. exact (H2 (H1 p)). Qed.
(* (P -> Q) -> ((Q -> R) -> (P -> R)) *)
(* P : Prop, R : Prop => P -> R : Prop
   Q : Prop, R : Prop => Q -> R : Prop
    => (Q -> R) -> (P -> R) : Prop
   P : Prop, Q : Prop => P -> Q : Prop
    => (P -> Q) -> (Q -> R) -> P -> R : Prop *)

(* Exercise 3.2 *) 
(* Using the basic tactics assumption, intros,
  and apply, prove the following lemmas: *)

Lemma id_P : P -> P.
Proof. intros. assumption. Qed.

Lemma id_PP : (P -> P) -> (P -> P).
Proof. intros. assumption. Qed.

Lemma imp_trans' : (P -> Q) -> (Q -> R) -> P -> R.
Proof. intros H1 H2 p. apply H2, H1, p. Qed.

Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
Proof. intros H q p. apply H; assumption. Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof. intros H p q. apply H. assumption. Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof. intros H p. apply H; assumption. Qed.

Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
Proof. intros H p _. apply H. assumption. Qed.
  
Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros H1 H2 H3 p.
  apply H3; [apply H1| apply H2]; assumption.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros H. apply H.
  intros H'. apply H'.
  intros p. apply H.
  intros _. assumption.
Qed.

(* Ex: Proof without tactics, using the section mechanism *)
Section proof_of_triple_impl.
  Hypothesis H : ((P -> Q) -> Q) -> Q.
  Hypothesis p : P.

  Lemma Rem : (P -> Q) -> Q.
  Proof (fun H0 : P -> Q => H0 p ).
  
  Theorem triple_impl : Q.
  Proof (H Rem).
End proof_of_triple_impl.

Print triple_impl.

(* Exercise 3.3 *)
(* Redo Exercise 3.2, using as many tacticals as needed 
  to perform each proof in only one complex step. *)

Section tacticals.

  Lemma id_P' : P -> P.
  Proof. intros; assumption. Qed.

  Lemma id_PP' : (P -> P) -> (P -> P).
  Proof. intros; assumption. Qed.

  Lemma imp_trans'' : (P -> Q) -> (Q -> R) -> P -> R.
  Proof. intros H1 H2 p; exact (H2 (H1 p)). Qed.
  
  Lemma imp_perm' : (P -> Q -> R) -> (Q -> P -> R).
  Proof. intros H q p; exact (H p q). Qed.
  
  Lemma ignore_Q' : (P -> R) -> P -> Q -> R.
  Proof. intros H p _; exact (H p). Qed.
  
  Lemma delta_imp' : (P -> P -> Q) -> P -> Q.
  Proof. intros H p; exact (H p p). Qed.
  
  Lemma delta_impR' : (P -> Q) -> (P -> P -> Q).
  Proof. intros H p _; exact (H p). Qed.
    
  Lemma diamond' : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
  Proof.
    intros H1 H2 H3 p.
    apply H3; [apply H1| apply H2]; assumption.
  Qed.
  
  Lemma weak_peirce' : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intros H; apply H;
    intros H'; apply H';
    intros p; apply H;
    intros _; assumption.
  Qed.

End tacticals.

(* Exercise 3.4 *)
(* Show that if there exists a term t such that the judgment [below],
  holds according to the typing rules presented in this chapter,
  then a goal with P as its statement can be solved in the 
  environment E and the context r, only by using the tactics
  apply, intra, and assumption. *)

Section existence_of_proof.

Variable S : Prop.
Variable s : S.

Lemma proof_exists_for_S : S. apply s. Qed.

Definition existence_of_proof : forall (S' : Prop), (exists (t : S'), True) -> S'.
Proof. intros S' H. apply H. Qed.

End existence_of_proof.

Section section_for_cut_example.

Hypotheses  (H : P -> Q)
            (H0 : Q -> R)
            (H1 : (P -> R) -> T -> Q) (H2 : (P -> R) -> T).

Theorem cut_example : Q.
Proof.
  cut (P -> R).
  intro H3.
  apply H1; [assumption | apply H2; assumption].
  intro; apply H0; apply H; assumption.
Qed.

Print cut_example.

(* Exercise 3.5 *)
(* Perform the same proof without using cut and compare both
  approaches and both proof terms. *)

Theorem cutless_example : Q.
Proof.
  apply H1; [idtac | apply H2];
  intro p; exact (H0 (H p)).
Qed.

End section_for_cut_example.

(* Exercise 3.6 *)
(* Design a goal of minimal propositional logic that can be solved
  by auto 6 but not by auto (in other words, not by auto 5). Find 
  a general pattern for depth n.*)

Goal ((((((((((P->Q)->Q)->Q)->Q)->Q)->Q)->Q)->Q)->Q)->P->Q). 
  auto 6.
Qed.

(* General pattern *)
(* INCOMPLETE *)
Fixpoint depth_n_aux (n : nat) :=
  match n with
  | 0 => (P -> Q)
  | S n' => ((depth_n_aux n' -> Q) -> Q)
  end.

Definition depth_n (n : nat) :=
  match n with
  | 0 => True
  | S n' => (depth_n_aux n') -> P -> Q
  end.

Goal depth_n 1. unfold depth_n, depth_n_aux. auto 1. Qed.
Goal depth_n 2. unfold depth_n, depth_n_aux. auto 3. Qed.

(* 1 -> 1, 2 -> 3, ...etc, no solution for x -> 2 *)

End Minimal_propositional_logic.