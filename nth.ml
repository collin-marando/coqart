
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a option =
| Some of 'a
| None

(** val nth' : 'a1 list -> nat -> 'a1 option **)

let rec nth' l n =
  match l with
  | Nil -> None
  | Cons (a, tl) -> (match n with
                     | O -> Some a
                     | S p -> nth' tl p)
