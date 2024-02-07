Require Extraction.

(* Exercise 10.1 *)
(* What is the extracted type for the type option and
  the extracted value for the function nth' given below? *)

Inductive option (A:Set) : Set :=
  Some : A -> option A | None : option A.

Arguments Some [A].
Arguments None {A}.

Check Some.

Fixpoint nth' (A:Set) (l:list A) (n:nat) {struct n}: option A :=
  match l, n with
  | nil, _ => None
  | cons a tl, 0 => Some a
  | cons a tl, S p => nth' A tl p
  end.

Extraction "nth.ml" nth'.

(*
  type 'a option =
  | Some of 'a
  | None

  let rec nth' l n =
    match l with
    | Nil -> None
    | Cons (a, tl) -> (match n with
                      | O -> Some a
                      | S p -> nth' tl p)
*)