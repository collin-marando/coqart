Require Import Relations.
Require Import List.
Require Import Recdef.
Import ListNotations.

Module Type DEC_ORDER.
  Parameter A : Set.
  Parameter le : A->A->Prop.
  Parameter lt : A->A->Prop.
  Axiom ordered : order A le.
  Axiom lt_le_weak : forall a b:A, lt a b -> le a b.
  Axiom lt_diff : forall a b:A, lt a b -> a <> b.
  Axiom le_lt_or_eq: forall a b:A, le a b -> lt a b \/ a = b.
  Parameter lt_eq_lt_dec :
    forall a b:A, {lt a b} + {a = b} + {lt b a}.

  (* Tactic for reducing when lt_eq_lt_dec is applied
    on the same argument twice within the goal *)
  Ltac simpldec :=
    match goal with
    | |- context [lt_eq_lt_dec ?k ?k] => 
      destruct (lt_eq_lt_dec k k) as [[|_]|];
      try solve [exfalso; eapply lt_diff; eauto]
    | _ => idtac
    end.

End DEC_ORDER.

Module Type MORE_DEC_ORDERS.
  Parameter A : Set.
  Parameter le : A->A->Prop.
  Parameter lt : A->A->Prop.

  Axiom le_trans: transitive A le.
  Axiom le_refl : reflexive A le.
  Axiom le_antisym: antisymmetric A le.
  Axiom lt_irreflexive : forall a:A, ~lt a a.
  Axiom lt_trans : transitive A lt.
  Axiom lt_not_le: forall a b:A, lt a b -> ~le b a.
  Axiom le_not_lt: forall a b:A, le a b -> ~lt b a.
  Axiom lt_intro: forall a b:A, le a b -> a <> b -> lt a b.
  Parameter le_lt_dec : forall a b:A, {le a b} + {lt b a}.
  Parameter le_lt_eq_dec : forall a b:A, le a b -> {lt a b} + {a = b}.
End MORE_DEC_ORDERS.

Module More_Dec_Orders (P: DEC_ORDER) : 
  MORE_DEC_ORDERS 
    with Definition A := P.A 
    with Definition le := P.le
    with Definition lt := P.lt.

  Definition A := P.A.
  Definition le := P.le.
  Definition lt := P.lt.

  Theorem le_trans: transitive A le.
  Proof. apply P.ordered. Qed.

  Theorem le_refl : reflexive A le.
  Proof. apply P.ordered. Qed.

  Theorem le_antisym: antisymmetric A le.
  Proof. apply P.ordered. Qed.

  Theorem lt_irreflexive : forall a:A, ~lt a a.
  Proof.
    intros; unfold lt.
    intro. eapply P.lt_diff; eauto.
  Qed.

  Theorem lt_trans : transitive A lt.
  Proof.
    unfold transitive.
    intros x y z Hxy Hyz.
    assert (le x z).
    - eapply le_trans; eapply P.lt_le_weak; eauto.
    - destruct (P.le_lt_or_eq _ _ H); auto.
      subst.
      absurd (y = z).
      + intro; subst. eapply lt_irreflexive; eauto.
      + apply le_antisym; eapply P.lt_le_weak; auto.
  Qed.

  Theorem lt_not_le: forall a b:A, lt a b -> ~le b a.
  Proof.
    intros a b Hlt; intro Hle.
    absurd (a = b).
    + intro; subst. eapply lt_irreflexive; eauto.
    + apply le_antisym; auto; eapply P.lt_le_weak; auto.
  Qed.

  Theorem le_not_lt: forall a b:A, le a b -> ~lt b a.
  Proof.
    intros a b Hle; intro Hlt.
    absurd (a = b).
    + intro; subst. eapply lt_irreflexive; eauto.
    + apply le_antisym; auto; eapply P.lt_le_weak; auto.
  Qed.

  Theorem lt_intro: forall a b:A, le a b -> a <> b -> lt a b.
  Proof.
    intros a b Hle Hneq.
    destruct (P.le_lt_or_eq _ _ Hle); auto.
    contradiction.
  Qed.

  Definition le_lt_dec : forall a b:A, {le a b} + {lt b a}.
  Proof.
    intros.
    destruct (P.lt_eq_lt_dec a b) as [[Hlt|Heq]|Hlt]; auto;
    left.
    - apply P.lt_le_weak; auto.
    - subst. apply le_refl.
  Defined.

  Definition le_lt_eq_dec : forall a b:A, le a b -> {lt a b} + {a = b}.
  Proof.
    intros a b Hle.
    destruct (P.lt_eq_lt_dec a b) as [[Hlt|Heq]|Hlt]; auto.
    apply le_not_lt in Hle; contradiction.
  Defined.
    
End More_Dec_Orders.

(* Exercise 12.1 *)
(* Following the example of Lexico complete the following development: *)

Module List_Order (D: DEC_ORDER) <:
  DEC_ORDER with Definition A := list D.A.

  Module M := More_Dec_Orders D.

  Definition A := list D.A.

  Fixpoint le (x y : A) := 
    match x, y with
    | nil, _ => True
    | _::_, nil => False 
    | a::x', b::y' => D.lt a b \/ a = b /\ le x' y'
    end.
  
  Fixpoint lt (x y : A) := 
    match x, y with
    | _, nil => False 
    | nil, _::_ => True
    | a::x', b::y' => D.lt a b \/ a = b /\ lt x' y'
    end.

  Theorem ordered : order A le.
  Proof.
    split; unfold A, le, reflexive, transitive, antisymmetric.
    - induction x; auto.
    - induction x; auto.
      intros y z Hxy Hyz.
      destruct y as [|b]; [contradiction|].
      destruct z as [|c]; [contradiction|].
      fold le in *.
      destruct Hxy as [Hlt1|[Heq1 Hle1]];
      destruct Hyz as [Hlt2|[Heq2 Hle2]];
      subst; auto.
      + left. eapply M.lt_trans; eauto.
      + right. intuition. eapply IHx; eauto.
    - induction x;
      destruct y as [|b]; try contradiction; auto.
      fold le in *.
      intros [Hlt1|[Heq1 Hle1]] [Hlt2|[Heq2 Hle2]]; subst.
      + contradict Hlt1.
        apply M.le_not_lt, D.lt_le_weak; auto.
      + exfalso; eapply M.lt_irreflexive; eauto.
      + exfalso; eapply M.lt_irreflexive; eauto.
      + apply f_equal, IHx; auto.
  Qed.

  Theorem lt_le_weak : forall x y:A, lt x y -> le x y.
  Proof.
    unfold le.
    induction x; auto.
    destruct y as [|b]; [contradiction|].
    fold le in *.
    intros [|[]]; auto.
  Qed.

  Theorem lt_diff : forall x y:A, lt x y -> x <> y.
  Proof.
    intros x y Hlt.
    intro; subst.
    induction y; [contradiction|].
    destruct Hlt as [Hlt|[]]; auto.
    apply (M.lt_irreflexive _ Hlt).
  Qed.

  Theorem le_lt_or_eq: forall x y:A, le x y -> lt x y \/ x = y.
  Proof.
    induction x; intros;
    destruct y as [|b]; try contradiction; auto.
    destruct H as [Hlt|[Heq Hle]]; subst;
    unfold lt; auto.
    destruct (IHx _ Hle); subst; auto.
  Qed.

  Definition lt_eq_lt_dec :
    forall x y:A, {lt x y} + {x = y} + {lt y x}.
  Proof.
    induction x; destruct y as [|b];
    unfold lt; auto; fold lt.
    destruct (D.lt_eq_lt_dec a b) as [[]|];
    destruct (IHx y) as [[]|]; subst; auto.
  Defined.

  (* Extra theorems for list specific properties *)
  Theorem lt_hd : forall a b x y, D.lt a b -> lt (a :: x) (b :: y).
  Proof. unfold lt; auto. Qed.

  Theorem lt_app : forall u x y, lt x y -> lt (u ++ x) (u ++ y).
  Proof. induction u; simpl; auto. Qed.

  Theorem le_app : forall u x y, le x y -> le (u ++ x) (u ++ y).
  Proof. induction u; simpl; auto. Qed.

End List_Order.

(* then experiment with lists of natural numbers *)

Require Import Arith.
Module Nat_Order :
  DEC_ORDER
    with Definition A := nat
    with Definition le := Peano.le
    with Definition lt := Peano.lt.

  Definition A := nat.
  Definition le := Peano.le.
  Definition lt := Peano.lt.

  Theorem ordered : order A le.
  Proof.
    split; unfold A, le, reflexive, transitive, antisymmetric;
    eauto with arith.
  Qed.

  Theorem lt_le_weak : forall a b:A, lt a b -> le a b.
  Proof. exact Nat.lt_le_incl. Qed.

  Theorem lt_diff : forall a b:A, lt a b -> a <> b.
  Proof.
    unfold A, lt.
    intros; intro; subst.
    apply (Nat.lt_irrefl _ H).
  Qed.

  Theorem le_lt_or_eq: forall a b:A, le a b -> lt a b \/ a = b.
  Proof.
    apply Nat.lt_eq_cases.
  Qed.

  Definition lt_eq_lt_dec :
    forall a b:A, {lt a b} + {a = b} + {lt b a}.
  Proof.
    apply Compare_dec.lt_eq_lt_dec.
  Defined.

End Nat_Order.

Module Nat_List_Order := List_Order Nat_Order.

Goal (Nat_List_Order.le [2;3;7;5] [4;5;6;4;3;2]).
Proof. unfold Nat_List_Order.le, Nat_Order.lt. auto. Qed.

(* DICT *)

Module Type DICT.
  Parameter key data dict : Set.
  Parameter empty : dict.
  Parameter add : key -> data -> dict -> dict.
  Parameter find : key -> dict -> option data.
  Axiom success :
    forall d k v, find k (add k v d) = Some v.
  Axiom diff_key : 
    forall d k k' v, k <> k' -> find k (add k' v d) = find k d.
End DICT.

Module Type KEY.
  Parameter A : Set.
  Parameter eq_dec : forall x y:A, {x = y} + {x <> y}.
End KEY.

Module Type DATA.
  Parameter data : Set.
End DATA.

(* Exercise 12.2 *)
(* Propose a less naive implementation of DICT, using association lists;
  in other words, lists of pairs (key,value) *)

Module Dict (K: KEY) (D: DATA) : DICT
  with Definition key := K.A
  with Definition data := D.data.

  Definition key := K.A.
  Definition data := D.data.
  Definition dict := list (key * data).

  Definition empty := @nil (key * data).

  Definition add (k:key) (v:data) (d:dict) : dict := (k,v) :: d.

  Fixpoint find (k:key) (d:dict) : option data :=
    match d with
    | nil => None
    | (k', v) :: d' => 
      match K.eq_dec k k' with
      | left _ => Some v
      | right _ => find k d'
      end
    end.

  Theorem success : forall d k v, find k (add k v d) = Some v.
  Proof.
    induction d; simpl; intros;
    destruct (K.eq_dec k k); auto;
    contradiction.
  Qed.

  Theorem diff_key :
    forall d k k' v, k <> k' -> find k (add k' v d) = find k d.
  Proof.
    induction d; simpl; intros;
    destruct (K.eq_dec k k'); auto;
    contradiction.
  Qed.

End Dict.

(* Exercise 12.3 *)
(* In the same spirit as for TDict, propose an implementation
  of dictionaries that relies on an ordered association list
  (the keys must be ordered in the list). *)

(* Note: This implementation chooses to overwrite obsolete entries
  on add, whereas the implementation in the previous question simply
  makes them unreachable *)

Module LDict (K: DEC_ORDER) (D: DATA) : DICT
  with Definition key := K.A
  with Definition data := D.data.

  Definition key := K.A.
  Definition data := D.data.

  Definition dict := list (key * data).

  Definition empty := @nil (key * data).

  Fixpoint add (k:key) (v:data) (d:dict) : dict :=
    match d with
    | nil => (k, v) :: nil
    | (k', v') :: d' =>
      match K.lt_eq_lt_dec k k' with
      | inleft (left Hlt) => (k, v) :: d
      | inleft (right Heq) => (k, v) :: d'
      | inright Hgt => (k', v') :: (add k v d')
      end
    end.

  Fixpoint find (k:key) (d:dict) : option data :=
    match d with
    | nil => None
    | (k', v) :: d' => 
      match K.lt_eq_lt_dec k k' with
      | inleft (right Heq) => Some v
      | _ => find k d'
      end
    end.

  Theorem success :
    forall d k v, find k (add k v d) = Some v.
  Proof.
    induction d; simpl; intros.
    - K.simpldec; auto.
    - destruct a as [k' v'];
      destruct (K.lt_eq_lt_dec k k') as [[|]|] eqn: E; simpl;
      K.simpldec; auto.
      rewrite E; auto.
  Qed.

  Ltac destructall :=
    match goal with
    | |- context [K.lt_eq_lt_dec ?a ?b] => 
        destruct (K.lt_eq_lt_dec a b) as [[|]|]; subst; simpl;
        destructall
    | _ => idtac
    end.

  Theorem diff_key :
    forall d k k' v, k <> k' -> find k (add k' v d) = find k d.
  Proof.
    induction d; simpl; intros.
    - destruct (K.lt_eq_lt_dec k k') as [[|]|]; auto.
      contradiction.
    - destruct a as [x y].
      destructall; auto; contradiction.
  Qed.

End LDict.

(* Exercise 12.4 *)
(* Consider removing an entry from a dictionary (module types and functors for the implementation).
  Be careful to be precise about the behavior after multiple adds for the same key. *)

Module Type DICT_R.
  Parameter key data dict : Set.
  Parameter empty : dict.
  Parameter add : key -> data -> dict -> dict.
  Parameter find : key -> dict -> option data.
  Parameter remove : key -> dict -> dict.

  Axiom add_success :
    forall d k v, find k (add k v d) = Some v.
  Axiom add_diff : 
    forall d k k' v, k <> k' -> find k (add k' v d) = find k d.
  Axiom remove_success:
    forall d k, find k (remove k d) = None.
  Axiom remove_diff :
    forall d k k', k <> k' -> find k (remove k' d) = find k d.
End DICT_R.

(* In order to guarantee the property remove_success, no entries should be
  present for a given key after removal. Two potential implementations are:
  
  - add simply appends entries, and remove deletes all entries with the chosen key
  - add overwrites entries if the key exists, and remove need only delete the single entry

  The first is how _Dict_ is implemented in Exercise 12.2
  The second is how _LDict is implemented in Exercise 12.3

  An implementation that would fail the remove_success requirement would be
  an appending add and single entry removal. With this implementation,
  removing only the first found entry would result in the next entry
  becoming the new value. This behaviour could be desirable for other
  implementations where each key refers to a stack of entries, making
  the described removal behaviour akin to a pop function for that key.
*)

(* The following uses the Dict implementation from Exercise 12.2 *)
Module DictR (K: KEY) (D: DATA) : DICT_R
  with Definition key := K.A
  with Definition data := D.data.

  Definition key := K.A.
  Definition data := D.data.

  Definition dict := list (key * data).

  Definition empty := @nil (key * data).

  Definition add (k:key) (v:data) (d:dict) : dict := (k,v) :: d.

  Fixpoint find (k:key) (d:dict) : option data :=
    match d with
    | nil => None
    | (k', v) :: d' => 
      match K.eq_dec k k' with
      | left _ => Some v
      | right _ => find k d'
      end
    end.

  Fixpoint remove (k:key) (d:dict) : dict :=
    match d with
    | nil => nil
    | (k', v') :: d' => 
      match (K.eq_dec k k') with
      | left Heq => remove k d'
      | right Hneq => (k', v') :: (remove k d')
      end
    end.

  Theorem add_success : forall d k v, find k (add k v d) = Some v.
  Proof.
    induction d; simpl; intros;
    destruct (K.eq_dec k k); auto;
    contradiction.
  Qed.

  Theorem add_diff :
    forall d k k' v, k <> k' -> find k (add k' v d) = find k d.
  Proof.
    induction d; simpl; intros;
    destruct (K.eq_dec k k'); auto;
    contradiction.
  Qed.

  Theorem remove_success:
    forall d k, find k (remove k d) = None.
  Proof.
    induction d; simpl; auto.
    intros.
    destruct a as [k' v'];
    destruct (K.eq_dec k k') eqn:E; auto.
    simpl; rewrite E; auto.
  Qed.

  Theorem remove_diff :
    forall d k k', k <> k' -> find k (remove k' d) = find k d.
  Proof.
    induction d; simpl; auto.
    intros.
    destruct a as [x y].
    destruct (K.eq_dec k' x) eqn:E; simpl;
    destruct (K.eq_dec k x); auto.
    subst. contradiction.
  Qed.

End DictR.

(* Exercise 12.5 *)
(* Write a signature for a sorting module, where lists containing elements
  belonging to an decidable total order should be sorted; two implementations
  should be given, one using quicksort and the other one using insertion sort. *)

Module Sort_Defs (D:DEC_ORDER).

  Inductive sorted : list D.A -> Prop :=
    | sorted_nil : sorted nil
    | sorted_one : forall a, sorted [a]
    | sorted_more : forall a b l,
      D.le a b -> sorted (b :: l) -> sorted (a :: b :: l).

  Inductive perm: list D.A -> list D.A -> Prop :=
  | perm_nil: perm [] []
  | perm_skip x l l' : perm l l' -> perm (x::l) (x::l')
  | perm_swap x y l : perm (y::x::l) (x::y::l)
  | perm_trans l l' l'' :
    perm l l' -> perm l' l'' -> perm l l''.

  Hint Constructors sorted perm : core.

  Lemma perm_refl: forall l, perm l l.
  Proof. induction l; auto. Qed.

  Hint Resolve perm_refl : core.

End Sort_Defs.

Module Type SORT.

  Declare Module Order : DEC_ORDER.
  Include Sort_Defs Order.

  Parameter sort : list Order.A -> list Order.A.

  Axiom sort_sorted : forall l, sorted (sort l).
  Axiom sort_perm : forall l, perm l (sort l).

End SORT.

Module InsertionSort (D:DEC_ORDER) : SORT
  with Module Order := D.

  Module Order := D.
  Module M := More_Dec_Orders D.
  Include Sort_Defs Order.

  Definition A := M.A.
  Definition le_lt_dec := M.le_lt_dec. 

  Fixpoint insert (a:A) (l: list M.A) :=
    match l with
    | nil => [a]
    | b :: l' =>
      match le_lt_dec a b with
      | left Hle => a :: l
      | right Hgt => b :: insert a l'
      end
    end.

  Fixpoint sort (l:list M.A) :=
    match l with
    | nil => nil
    | a :: l' => insert a (sort l')
    end.

  Lemma insert_sorted : forall a l, sorted l -> sorted (insert a l).
  Proof.
    simple induction 1; simpl; auto; intros.
    - destruct (le_lt_dec a a0); constructor; auto.
      apply Order.lt_le_weak; auto.
    - destruct (le_lt_dec a a0);
      destruct (le_lt_dec a b);
      try repeat constructor; auto.
      apply Order.lt_le_weak; auto.
  Qed.

  Theorem sort_sorted : forall l, sorted (sort l).
  Proof.
    induction l as [|a l']; simpl; auto.
    apply insert_sorted; auto.
  Qed.

  Lemma insert_perm : forall a l, perm (a :: l) (insert a l).
  Proof.
    induction l; simpl; auto.
    destruct (le_lt_dec a a0); auto.
    eapply perm_trans.
    - apply perm_swap.
    - auto.
  Qed.

  Theorem sort_perm : forall l, perm l (sort l).
  Proof.
    induction l; auto.
    eapply perm_trans.
    - apply perm_skip, IHl.
    - apply insert_perm.
  Qed.

End InsertionSort.

Module Quicksort (D:DEC_ORDER) : SORT
  with Module Order := D.

  Module Order := D.
  Module M := More_Dec_Orders Order.
  Include Sort_Defs Order.

  Definition A := M.A.
  Definition le_lt_dec := M.le_lt_dec.

  Fixpoint filter (f : M.A -> bool) (l: list M.A) : list M.A :=
    match l with
    | nil => nil
    | a :: l' => if (f a) then a :: filter f l' else filter f l'
    end.

  Definition le_bool (p: M.A) : M.A -> bool :=
    fun a =>
    match le_lt_dec a p with
    | left Hle => true
    | right Hgt => false
    end.

  Definition gt_bool (p: M.A) : M.A -> bool :=
    fun a => 
    match le_lt_dec a p with
    | left Hle => false
    | right Hgt => true
    end.

  Definition filter_le (p : M.A) (l: list M.A) : list M.A := filter (le_bool p) l.
  Definition filter_gt (p : M.A) (l: list M.A) : list M.A := filter (gt_bool p) l.

  Lemma gtb_not_leb : forall a b, gt_bool a b = negb (le_bool a b).
  Proof.
    unfold le_bool, gt_bool; intros;
    destruct (le_lt_dec b a); auto.
  Qed.

  Lemma length_filter : forall l P, length (filter P l) <= length l.
  Proof.
    induction l; auto; simpl; intros.
    destruct (P a); simpl; auto.
    apply le_n_S; auto.
  Qed.

  (* Since quicksort's pricipal argument l isn't clearly decreasing
    between recursive calls, we need another mechanism to show that
    the argument is decreasing overall and thus the function will
    eventually terminate. We use _measure_ to say that the length
    of the pricipal argument l is decreasing between calls.
    Also we use Function (Recdef) instead of Fixpoint. *)

  Function sort (l: list M.A) {measure length l} :=
    match l with
      | nil => nil
      | a :: l' =>
        (sort (filter_le a l')) ++ a :: (sort (filter_gt a l')) 
    end.
  Proof.
    all: intros; simpl; unfold filter_le, filter_gt;
    apply Nat.lt_succ_r, length_filter.
  Defined.

  (* Using Defined instead of Qed gives us an induction priciple for sort (sort_ind) *)

  (* Next, we define an equivalent definition of a sorted list that lends to quicksort's recursion *)
  Inductive sorted' : list D.A -> Prop :=
    | sorted'_nil : sorted' nil
    | sorted'_app : forall a x y,
      sorted' x -> sorted' y ->
      (forall v, In v x -> M.le v a) ->
      (forall v, In v y -> M.le a v) ->
      sorted' (x ++ a :: y).

  Hint Constructors sorted' : core.

  Lemma sorted'_one : forall a, sorted' [a].
  Proof.
    intros; change ([a]) with ([] ++ a :: []).
    constructor; auto; intros v H; inversion H.
  Qed.

  Hint Resolve sorted'_one : core.

  Lemma sorted_app (x y: list M.A) (a : M.A):
    sorted x -> sorted y
    -> (forall v, In v x -> M.le v a)
    -> (forall v, In v y -> M.le a v)
    -> sorted (x ++ a :: y).
  Proof.
    elim x; auto.
    - intros; simpl.
      destruct y; auto.
      constructor; auto.
      apply H2; left; auto.
    - intros v x' IH1 Hsx Hsy Hinx Hiny.
      inversion Hsx; subst; auto.
      + constructor; auto.
        apply Hinx; left; auto.
        apply IH1; auto.
        contradiction.
      + simpl; constructor; auto.
        apply IH1; auto.
        intros c Hinc.
        apply Hinx. right; auto.
  Qed.

  (* We only need one direction of the bijection between these definitions *)
  Theorem sorted'_sorted : forall l, sorted' l -> sorted l.
  Proof.
    intros l H.
    induction H; auto.
    apply sorted_app; auto.
  Qed.

  (* To show quicksort returns a sorted list, a few inclusion lemmas are needed *)

  Lemma forall_filter : forall l v P, In v (filter P l) -> P v = true.
  Proof.
    induction l; auto; simpl; intros.
    destruct (P a) eqn:E; auto.
    inversion H; subst; auto.
  Qed.
  
  Lemma in_filter : forall l v P, In v (filter P l) -> In v l.
  Proof.
    induction l; simpl; auto.
    intros.
    destruct (P a).
    - inversion H; auto.
      right. eapply IHl; eauto.
    - right. eapply IHl; eauto.
  Qed. 

  Lemma in_sort : forall l v, In v (sort l) -> In v l.
  Proof.
    intros l.
    apply sort_ind; auto; simpl; clear l.
    intros l a l' Heq Hle Hgt v Hin.
    apply in_elt_inv in Hin as [|Hin]; auto.
    right.
    apply in_app_or in Hin as [];
    eapply in_filter; eauto.
  Qed.

  Theorem sort_sorted : forall l, sorted (sort l).
  Proof.
    intros; apply sorted'_sorted.
    apply sort_ind; auto; clear l.
    intros l a l' Heq Hle Hgt.
    constructor; auto; intros v Hin;
    apply in_sort, forall_filter in Hin;
    unfold le_bool, gt_bool in *;
    destruct le_lt_dec; auto;
    try discriminate.
    apply D.lt_le_weak; auto.
  Qed.

  (* To show the permutation property, we first prove that if two lists
    have the same number of occurences for every element, then they are
    permutations of eachother. *)

  (* For counting occurences, case analyis on equal or not equal is
    easier and more concise than splitting on lt_eq_lt_dec. *)
  Definition eq_or_neq : forall a b : M.A, {a = b} + {a <> b}.
  Proof.
    intros. destruct (D.lt_eq_lt_dec a b) as [[]|]; auto;
    right; contradict l; subst; apply M.lt_irreflexive.
  Defined.

  (* This tactic breaks down any instances of eq_or_neq where the two arguments are the same *)
  Ltac simpldec := match goal with
    | |- context [eq_or_neq ?k ?k] => 
      destruct (eq_or_neq k k) as [Heq|F];
      try discriminate; try contradiction; auto; clear Heq
    | H : context [eq_or_neq ?k ?k] |- _ => 
      destruct (eq_or_neq k k) as [Heq|F];
      try discriminate; try contradiction; auto; clear Heq
    | _ => idtac
    end.

  Fixpoint count (a : M.A) (l : list M.A) : nat :=
    match l with
    | nil => 0
    | x :: l' =>
      match eq_or_neq a x with
      | left Heq => S (count a l')
      | right Hne => count a l'
      end
    end.

  Lemma count_S : forall l a n, count a l = S n -> exists x y, l = x ++ a :: y.
  Proof.
    induction l; simpl; intros; [discriminate|].
    intros.
    destruct (eq_or_neq a0 a); subst.
    - exists nil, l. auto.
    - apply IHl in H as [u [v H]].
      exists (a :: u), v. subst; auto.
  Qed.

  Lemma count_middle : forall x y a, count a (x ++ a :: y) = S (count a (x ++ y)).
  Proof.
    induction x; simpl; intros.
    - simpldec.
    - destruct (eq_or_neq a0 a); subst; auto.
  Qed.

  Lemma skip_middle : forall x y a b, a <> b -> count a (x ++ b :: y) = count a (x ++ y).
  Proof.
    induction x; simpl; intros.
    - destruct (eq_or_neq a b); auto; contradiction.
    - destruct (eq_or_neq a0 a); subst; auto.
  Qed.

  Lemma perm_rotate : forall x a, perm (a :: x) (x ++ [a]).
  Proof.
    induction x; auto.
    intros.
    eapply perm_trans.
    - apply perm_swap.
    - simpl; constructor.
      apply IHx.
  Qed.

  Lemma perm_app_swap : forall x y, perm (x ++ y) (y ++ x).
  Proof.
    induction x; simpl; intros.
    - rewrite app_nil_r; auto.
    - eapply perm_trans.
      + apply perm_rotate.
      + change (y ++ a :: x) with (y ++ [a] ++ x).
        rewrite app_assoc, <- app_assoc.
        apply IHx.
  Qed.

  Lemma perm_sym : forall l l', perm l l' -> perm l' l.
  Proof.
    intros. induction H; auto.
    eapply perm_trans; eauto.
  Qed.

  (* Now we can prove the aforementioned implication *)
  Lemma count_all : forall l l',
    (forall a, count a l = count a l') -> perm l l'.
  Proof.
    induction l; simpl; intros.
    - destruct l'; auto.
      specialize H with a; simpl in H.
      simpldec.
    - destruct l' as [|a' l'].
      specialize H with a; simpl in H; simpldec.
      destruct (eq_or_neq a a') eqn:Eaa'; subst.
      + constructor.
        apply IHl. intros.
        specialize H with a.
        clear Eaa'; destruct (eq_or_neq a a') eqn:Eaa'; subst.
        * simpl in *; simpldec.
        * simpl in H; rewrite Eaa' in *; auto.
      + pose proof (H a) as Ha.
        simpl in *; simpldec.
        rewrite Eaa' in *.
        symmetry in Ha. apply count_S in Ha as [x [y Hl']].
        subst. apply perm_sym.
        change (a' :: x ++ a :: y) with ((a' :: x) ++ a :: y).
        eapply perm_trans; [apply perm_app_swap|simpl].
        constructor.
        eapply perm_trans; [apply perm_app_swap|simpl].
        apply perm_sym, IHl.
        intros b. specialize H with b.
        destruct (eq_or_neq b a); destruct (eq_or_neq b a') eqn:E; subst; simpl.
        * contradiction.
        * rewrite E; rewrite count_middle in H; auto.
        * rewrite E; rewrite skip_middle in H; auto.
        * rewrite E; rewrite skip_middle in H; auto.
  Qed.

  (* A couple supplementary lemmas are needed for the final proof *)
  Lemma count_app : forall x y a, count a (x ++ y) = count a x + count a y.
  Proof.
    induction x; simpl; auto.
    intros y a'.
    destruct (eq_or_neq a a') eqn:E1;
    destruct (eq_or_neq a' a) eqn:E2;
    subst; try contradiction; simpl; auto.
  Qed.

  Lemma count_le_gt : forall l a a',
    count a l = count a (filter_le a' l) + count a (filter_gt a' l).
  Proof.
    intros l a x; unfold filter_le, filter_gt.
    induction l as [|a' l]; simpl; auto.
    rewrite gtb_not_leb.
    destruct (le_bool x a'); simpl;
    destruct (eq_or_neq a a'); simpl; auto.
    subst. rewrite Nat.add_succ_r. auto.
  Qed.

  Theorem sort_perm : forall l, perm l (sort l).
  Proof.
    intros. apply count_all; intros.
    apply sort_ind; auto; clear l.
    intros l a' l' Heq Hle Hgt.
    destruct (eq_or_neq a a') as [|Hne] eqn:E; subst;
    [rewrite count_middle|rewrite skip_middle]; auto;
    rewrite count_app, <- Hle, <- Hgt, <- count_le_gt.
    - simpl; auto. simpldec. 
    - simpl. rewrite E. auto.
  Qed.

End Quicksort.