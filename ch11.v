Require Import ZArith.

(* Exercise 11.1 *)
(* The predicates min and maj could have been directly defined as 
  a recursive inductive predicate without using occ. Redo the whole 
  development (from the user contribution cited above) with such a 
  definition and compare the ease of development in the two approaches.
  Pay attention to minimizing the amount of modifications that are needed.
  This exercise shows that maintaining proofs is close to maintaining
  software. *)

Open Scope Z_scope.

Inductive Z_btree: Set := 
  | Z_leaf: Z_btree
  | Z_bnode: Z -> Z_btree -> Z_btree -> Z_btree.

Inductive min (n:Z): Z_btree -> Prop :=
  | min_leaf: min n Z_leaf
  | min_node: forall x t1 t2,
      min n t1 -> min n t2 -> n < x -> min n (Z_bnode x t1 t2).

Inductive maj (n:Z): Z_btree -> Prop :=
  | maj_leaf: maj n Z_leaf
  | maj_node: forall x t1 t2,
      maj n t1 -> maj n t2 -> n > x -> maj n (Z_bnode x t1 t2).
      
Inductive search_tree: Z_btree -> Prop :=
  | leaf_search_tree: search_tree Z_leaf
  | bnode_search_tree: forall (n:Z) (t1 t2:Z_btree),
    search_tree t1 -> search_tree t2 -> 
    maj n t1 -> min n t2 -> search_tree (Z_bnode n t1 t2).

(* Exercise 11.2 *)
(* How would the specification evolve if we were to use a type
  of "binary search trees" in the Set sort? *)

Section set_spec.

(* A type for binary trees in the Set sort can be defined using sig *)
Definition stree: Set := {x : Z_btree | search_tree x}.

Inductive occ (n:Z): Z_btree -> Prop :=
  | occ_root: forall t1 t2:Z_btree, occ n (Z_bnode n t1 t2)
  | occ_l: forall (p:Z) (t1 t2:Z_btree), occ n t1 -> occ n (Z_bnode p t1 t2)
  | occ_r: forall (p:Z) (t1 t2:Z_btree), occ n t2 -> occ n (Z_bnode p t1 t2).

(* The new occurence function is simply the original applied to an extracted value *)
Definition socc (n: Z) (s: stree) :=
  match s with exist _ t _ => occ n t end.

(* The sumbool for decidability is as expected *)
Definition socc_dec (n: Z) (s: stree) :=
  {socc n s} + {~socc n s}.

Inductive INSERT (n:Z) (t t': Z_btree): Prop :=
  insert_intro: 
    (forall p:Z, occ p t -> occ p t') -> occ n t' ->
    (forall p:Z, occ p t' -> occ p t \/ n = p) -> search_tree t' ->
    INSERT n t t'.

Definition insert_spec (n:Z) (t:Z_btree): Set :=
  search_tree t -> {t': Z_btree | INSERT n t t'}. 

(* In SINSERT, we no longer require "search_tree x" precondition,
  since the tree s' is already a well-specified search tree *)
Inductive SINSERT (n:Z) (s s': stree): Prop :=
  sinsert_intro:
    (forall p:Z, socc p s -> socc p s') -> socc n s' ->
    (forall p:Z, socc p s' -> socc p s \/ n = p) -> 
    SINSERT n s s'.

(* Similarily for the rest: precondition of "search_tree x" can be removed *)
Definition sinsert_spec (n:Z) (s:stree): Set :=
  {s': stree | SINSERT n s s'}. 

Inductive RM (n:Z) (t t': Z_btree): Prop :=
  rm_intro: ~occ n t' ->
    (forall p:Z, occ p t' -> occ p t) ->
    (forall p:Z, occ p t  -> occ p t' \/ n = p) ->
    search_tree t' -> RM n t t'.

Definition rm_spec (n:Z) (t:Z_btree): Set :=
  search_tree t -> {t': Z_btree | RM n t t'}.

Inductive SRM (n:Z) (s s': stree): Prop :=
  srm_intro: ~socc n s' ->
    (forall p:Z, socc p s' -> socc p s) ->
    (forall p:Z, socc p s  -> socc p s' \/ n = p) ->
    SRM n s s'.

Definition srm_spec (n:Z) (s:stree): Set :=
  {s': stree | SRM n s s'}.

(* Observation: by using the well specified stree, the proofs and definitions
 come closer to what the extracted terms would look like due to proof irrelevance. *)
