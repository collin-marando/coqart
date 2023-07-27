(* Exercise 5.1 *)
(* Redo Exercise 3.2, given on page 58, but with closed
  statements, in other words, statements where the 
  propositional variables are not the pre-declared
  variables P, Q, R, but universally quantified variables. *)

  Lemma id_P : forall P : Prop, P -> P.
  Proof (fun P HP => HP).

  Lemma id_PP : forall P : Prop, (P -> P) -> (P -> P).
  Proof (fun P HPP => HPP).

  Lemma imp_trans : forall P Q R : Prop,
    (P -> Q) -> (Q -> R) -> P -> R.
  Proof (fun P Q R HPQ HQR HP => HQR (HPQ HP)).

  Lemma imp_perm : forall P Q R : Prop,
    (P -> Q -> R) -> (Q -> P -> R).
  Proof (fun P Q R HPQR HQ HP => HPQR HP HQ).
  
  Lemma ignore_Q : forall P Q R: Prop,
    (P -> R) -> P -> Q -> R.
  Proof (fun P _ R HPR HP _ => HPR HP).

  Lemma delta_imp : forall P Q : Prop,
    (P -> P -> Q) -> P -> Q.
  Proof (fun P Q HPPQ HP => HPPQ HP HP).

  Lemma delta_impR : forall P Q : Prop,
    (P -> Q) -> (P -> P -> Q).
  Proof (fun P Q HPQ HP => HPQ).

  Lemma diamond : forall P Q R T : Prop,
    (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
  Proof
    (fun P Q R T HPQ HPR HQRT HP => HQRT (HPQ HP) (HPR HP)).
  
  Lemma weak_peirce : forall P Q : Prop,
    ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof
    (fun P Q HPQPPQ => HPQPPQ (
      fun HPQP => HPQP (
        fun HP => HPQPPQ (
          fun _ => HP)))).

(* Exercise 5.2 *)
(* Using tactics, redo the proofs of Exercise 4.5. *)

Theorem all_perm : forall (A : Type) (P : A -> A -> Prop),
  (forall x y:A, P x y) -> forall x y: A, P y x.
Proof.
  intros A R H x y.
  apply H.
Qed.

Definition resolution : forall (A : Type) (P Q R T : A -> Prop),
  (forall a:A, Q a -> R a -> T a) ->
  (forall b:A, P b -> Q b) -> (forall e:A, P e -> R e -> T e).
Proof.
  intros A P Q R T HQRT HPQ e Pe Re.
  apply (HQRT e).
  - apply (HPQ e Pe).
  - apply Re.
Qed.

(* Exercise 5.3 *)
(* Prove the following statements: 
• ~ False
• forall P : Prop, ~~~P->~P
• forall P Q : Prop, ~~~P->P->Q
• forall P Q : Prop, (P->Q)->(~Q->~P)
• forall P Q R : Prop, (P->Q)->(P->~Q)->P->R

  Find the proofs that can be done without False_ind.
  Show how the corresponding theorems can be seen as
  simple applications of more general theorems from 
  minimal propositional logic.
*)

Section min_prop.

Goal ~False.
Proof. intro H. apply H. Qed.

Theorem triple_neg_inv : forall P : Prop, ~~~P -> ~P.
Proof.
  intros P HNNNP.
  intro HP.
  apply HNNNP.
  intro HNP.
  apply HNP, HP.
Qed.

Theorem absurd : forall P Q : Prop, ~~~P->P->Q.
Proof.
  intros P Q HNNNP.
  apply (triple_neg_inv) in HNNNP.
  apply imp_trans with False.
  - apply HNNNP.
  - apply False_ind.  (* False_ind must be used for this proof *)
Qed.

Goal forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HNQ.
  intro HP.
  apply HNQ, HPQ, HP.
Qed.

Goal forall P Q R : Prop, (P -> Q) -> (P -> ~Q) -> P -> R.
Proof.
  intros P Q R HPQ HPNQ HP.
  apply absurd with Q.
  - intro H. apply H, HPNQ, HP.
  - apply HPQ, HP.
Qed.

End min_prop.

(* Exercise 5.4 *)
(* Usual reasoning errors rely on pseudo inference rules that
  can lead to contradictions. These rules are often the result
  of some sort of dyslexia. Here are two examples: implication
  dyslexia (confusion between P~Q and Q~ P) and dyslexic 
  contraposition:
*)

Definition dyslexic_imp := forall P Q : Prop, (P -> Q) -> (Q -> P).
Definition dyslexic_contrap := forall P Q : Prop, (P -> Q) -> (~P -> ~Q).

(* Show that, if one of these types were inhabited,
  one could build a proof of False, hence a proof of any proposition. *)

Goal dyslexic_imp -> False.
Proof.
  unfold dyslexic_imp.
  intros H.
  apply (H False True); auto.
Qed.

Goal dyslexic_contrap -> False.
Proof.
  unfold dyslexic_contrap, not.
  intros H.
  apply (H False True); auto.
Qed.

(* Exercise 5.5 *)
(* Prove the following theorem. *) 

Goal forall (A : Set) (a b c d : A), a = c \/ b = c \/ c = c \/ d = c.
Proof.
  intros.
  right.
  right.
  left.
  auto.
Qed.

(* Exercise 5.6 *)
(* Prove the following theorems. *)
Goal forall A B C : Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C HABC; elim HABC.
  intros HA HBC; elim HBC.
  intros HB HC.
  apply conj.
  apply conj.
  all : assumption.
Qed.

Goal forall A B C D : Prop, (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D. 
Proof.
  intros A B C D H.
  elim H; clear H; intros HAB H.
  elim H; clear H; intros HCD H.
  elim H; clear H; intros HA HC.
  apply conj; auto.
Qed.

Goal forall A : Prop, ~(A /\ ~A).
Proof.
  intros A.
  intro H.
  elim H; clear H; intros HA HNA.
  apply HNA, HA.
Qed.

Goal forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H.
  elim H; clear H; intro HA.
  left; left; assumption.
  elim HA; clear HA; intro HB.
  left; right; assumption.
  right; assumption.
Qed.
  
Goal forall A : Prop, ~~(A \/ ~A).
Proof.
  intros A.
  intro HNOR; apply HNOR.
  right. intro.
  apply HNOR.
  left. apply H.
Qed.

Goal forall A B : Prop, (A \/ B) /\ ~ A -> B.
Proof.
  intros A B H.
  elim H; intros HOR HNA.
  elim HOR; [|intro; assumption].
  intro HA.
  elim HNA.
  apply HA.
Qed.

(* Exercise 5.7 *) 
(* Here are five statements that are often considered as
  characterizations of classical logic. Prove that these
  five propositions are equivalent. *)

Definition peirce := forall P Q : Prop, ((P->Q)->P)->P.
Definition classic := forall P : Prop, ~~P -> P.
Definition excluded_middle := forall P : Prop, P\/~P.
Definition de_morgan_not_and_not := forall P Q : Prop, ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q : Prop, (P->Q)->(~P\/Q).

Goal peirce -> classic.
Proof.
  unfold peirce, classic.
  intros peirce P HNNP.
  apply (peirce P False).
  intros HNP.
  elim HNNP.
  unfold not. assumption.
Qed.

Goal classic -> excluded_middle.
Proof.
  unfold classic, excluded_middle.
  intros classic P.
  apply classic.
  intro H; apply H.
  right. intro HP.
  apply H.
  left. apply HP.
Qed.

Goal excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle, de_morgan_not_and_not.
  intros excluded_middle P Q H.
  pose proof excluded_middle P as Pdec.
  pose proof excluded_middle Q as Qdec.
  elim Pdec; auto.
  elim Qdec; auto.
  intros HNQ HNP.
  elim H; split; assumption.
Qed.

Goal de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not, implies_to_or.
  intros de_morgan P Q HPQ.
  apply de_morgan.
  intro H; apply H.
  elim H; intros HNNP HNQ.
  elim HNNP; intro HP.
  apply HNQ, HPQ, HP.
Qed.

Goal implies_to_or -> peirce.
Proof.
  unfold implies_to_or, peirce.
  intros implies_to_or P Q H.
  specialize (implies_to_or P P (fun P => P)).
  elim implies_to_or; auto; intro HNP.
  apply H; intro HP.
  elim HNP. apply HP.
Qed.

(* Exercise 5.8 *)
(* What do the tactics repeat idtac and repeat fail do? *)

(* _repeat idtac_ does nothing to the proof space,
  and therefore never fails: it would loop forever, eating up RAM
  
  _repeat fail_ would catch a failure on the first use.
  It does nothing, and terminates thereafter.
*)

(* Exercise 5.9 *)
(* In a context where A: Set and P, Q: A -> Prop are declared,
  prove the following statements: *)
Section existential.

Variable A : Set.
Variables P Q : A -> Prop.

Goal (exists x : A, P x \/ Q x) -> (ex P) \/ (ex Q).
Proof.
  intros.
  elim H; clear H; intros a H.
  elim H; clear H; intros H.
  - left. exists a. apply H.
  - right. exists a. apply H.
Qed.

Goal (ex P) \/ (ex Q) -> exists x : A, P x \/ Q x.
Proof.
  intros.
  elim H; clear H; intros H;
  elim H; clear H; intros x H;
  exists x; [left | right]; auto.
Qed.

Goal (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
Proof.
  intros.
  elim H; clear; intros a H.
  specialize H with (fun _ => 2 = 3).
  simpl in H; apply H.
Qed.

Goal (forall x : A, P x) -> ~(exists y : A, ~ P y).
Proof.
  intros H.
  intro Hex.
  elim Hex; intros x HNP.
  apply HNP, H.
Qed.

End existential.

(* Exercise 5.10 *)
(* Prove the following statement: *)
Require Import Arith.
Theorem p1us_permute2 : forall n m p : nat, n+m+p = n+p+m.
Proof.
  intros.
  rewrite <- Nat.add_assoc.
  (* This trick using pattern allows me to isolate the rewrite target
    by abstracting away the variable that isn't involved. *)
  (* This is similar to using revert but does so
    via a function rather than a universal quantifier. *)
  (* revert n. rewrite Nat.add_comm. *)
  pattern n. rewrite Nat.add_comm. 
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

(* Exercise 5.11 *)
(* Prove the following theorem, first by a direct use of eq_ind,
then with the rewrite tactic: *)
Theorem eq_trans : forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros A x y z Hxy Hyz.
  apply (eq_ind y).
  - apply Hxy.
  - apply Hyz.
Qed.

Reset eq_trans.
Theorem eq_trans : forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros A x y z Hxy Hyz.
  rewrite Hxy. apply Hyz.
Qed.

(* Exercise 5.12 *)
(* Construct manually the proof terms that are used as values
  of the constants my_I and my_False_ind *)
Definition my_True := forall P : Prop, P -> P.
Definition my_I : my_True := (fun P HP => HP).

Definition my_False := forall P : Prop, P.
Definition my_False_ind : forall P : Prop, my_False -> P :=
  (fun P F => F P).

(* Exercise 5.13 *)
(* It is possible to define negation on top of our notion of falsehood:
  Definition my_not (P:Prop) : Prop := P -> my_False.
Redo Exercise 5.3 using my_False and my_not instead of False and not. *)

Definition my_not (P:Prop) : Prop := P -> my_False.

Goal my_not my_False.
Proof. intro H. apply H. Qed.

Theorem triple_neg_inv' : 
  forall P : Prop, my_not (my_not (my_not P)) -> my_not P.
Proof.
  intros P HNNNP.
  intro HP.
  apply HNNNP.
  intro HNP.
  apply HNP, HP.
Qed.

Theorem absurd' :
  forall P Q : Prop, my_not (my_not (my_not P)) -> P -> Q.
Proof.
  intros P Q HNNNP.
  apply (triple_neg_inv') in HNNNP.
  apply imp_trans with my_False.
  - apply HNNNP.
  - apply my_False_ind.
Qed.

Goal forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HNQ.
  intro HP.
  apply HNQ, HPQ, HP.
Qed.

Goal forall P Q R : Prop, (P -> Q) -> (P -> my_not Q) -> P -> R.
Proof.
  intros P Q R HPQ HPNQ HP.
  apply absurd' with Q.
  - intro H. apply H, HPNQ, HP.
  - apply HPQ, HP.
Qed.

(* The point of this exercise is clearly that under the new
  defintions of False and not, the proof structure remains the same. *)

Section leibniz.
Set Implicit Arguments.
Unset Strict Implicit.

Variable A : Set.
Definition leibniz (a b:A) : Prop := forall P : A -> Prop, P a -> P b.

Require Import Relations.
Theorem leibniz_sym : symmetric A leibniz.
Proof.
  unfold symmetric.
  unfold leibniz; intros x y H Q.
  apply H; trivial.
Qed.

(* Exercise 5.14 *)
(* Prove the following statements: *)
Theorem leibniz_refl : reflexive A leibniz.
Proof.
  unfold reflexive, leibniz.
  intros x P HPx. assumption.
Qed.

Theorem leibniz_trans : transitive A leibniz.
Proof. 
  unfold transitive, leibniz.
  intros x y z Hxy Hyz P HPx.
  apply Hyz, Hxy, HPx.
Qed.

Theorem leibniz_equiv : equiv A leibniz.
Proof.
  unfold equiv, leibniz.
  repeat split.
  - apply leibniz_refl.
  - apply leibniz_trans.
  - apply leibniz_sym.
Qed.

Theorem leibniz_least_reflexive :
  forall R : relation A, reflexive A R -> inclusion A leibniz R.
Proof.
  unfold inclusion.
  intros R Hrefl x y Heq.
  apply Heq, Hrefl.
Qed.
  
Theorem leibniz_eq :
  forall a b : A, leibniz a b -> a = b.
Proof.
  intros a b Heq.
  apply Heq. reflexivity.
Qed.    
    
Theorem eq_leibniz : forall a b : A, a = b -> leibniz a b.
Proof.
  intros a b Heq.
  rewrite Heq. apply leibniz_refl.
Qed.

Theorem leibniz_ind :
  forall (x : A) (P : A -> Prop), P x -> forall y : A, leibniz x y -> P y.
Proof.
  intros x P HPx y Heq.
  apply Heq, HPx.
Qed.

Unset Implicit Arguments.
End leibniz.

(* Exercise 5.15 *)
(* In order to feel at home with the preceding encodings,
  prove the following statements (use the definition of 
  negation from Exercise 5.13): *)

Definition my_and (P Q : Prop) :=
  forall R : Prop, (P->Q->R)->R.
Definition my_or (P Q : Prop) :=
  forall R : Prop, (P->R)->(Q->R)->R.
Definition my_ex (A : Set) (P : A->Prop) :=
  forall R : Prop, (forall x:A, P x -> R) -> R.

Theorem my_and_l : forall A B : Prop, my_and A B -> A.
Proof.
  intros. apply H.
  intros. assumption.
Qed.

Theorem my_and_r : forall A B : Prop, my_and A B -> B.
Proof.
  intros. apply H.
  intros. assumption.
Qed.

Goal forall P Q R : Prop, (P -> Q -> R) -> my_and P Q -> R.
Proof.
  intros P Q R HPQR HPQ.
  apply HPQR.
  - eapply my_and_l, HPQ.
  - eapply my_and_r, HPQ.
Qed.

Goal forall P Q : Prop, P -> my_or P Q.
Proof.
  intros P Q HP.
  unfold my_or.
  intros R HPR HQR.
  apply HPR, HP.
Qed.

Goal forall P Q : Prop, Q -> my_or P Q.
Proof.
  intros P Q HP.
  unfold my_or.
  intros R HPR HQR.
  apply HQR, HP.
Qed.

Goal forall P Q R : Prop, (P->R) -> (Q->R) -> my_or P Q -> R.
Proof.
  intros P Q R HPR HQR HPQ.
  apply HPQ; assumption.
Qed.

Goal forall P : Prop, my_or P False -> P.
Proof.
  intros P Hor.
  apply Hor.
  - trivial.
  - apply False_ind.
Qed.

Goal forall P Q : Prop, my_or P Q -> my_or Q P.
Proof.
  intros P Q Hor.
  unfold my_or.
  intros R HQR HPR.
  apply Hor; assumption.
Qed.

Theorem my_ex_intro : forall (A : Set) (P : A -> Prop) (a : A), P a -> my_ex A P.
Proof.
  intros A P a HPa.
  intros R Hf.
  apply (Hf a), HPa.
Qed.

Goal forall (A : Set) (P : A -> Prop), my_not (my_ex A P) ->
  forall (a : A), my_not (P a).
Proof.
  intros A P Hex a.
  intro HPa.
  apply Hex.
  apply my_ex_intro with a.
  apply HPa.
Qed.

Definition my_le (n p : nat) :=
  forall P : nat -> Prop, P n -> (forall q, P q -> P (S q)) -> P p.

(* Exercise 5.16 *)
(* Prove the following lemmas: *)
Lemma my_le_n : forall n:nat, my_le n n.
Proof.
  intros n P HPn _.
  apply HPn.
Qed.

Lemma my_le_S : forall n p, my_le n p -> my_le n (S p).
Proof.
  intros n p Hle.
  intros P HPn Hsucc.
  apply Hsucc.
  apply Hle; assumption.
Qed.

Lemma my_le_le : forall n p, my_le n p -> n <= p.
Proof.
  intros n p Hle.
  apply Hle; auto.
Qed. 