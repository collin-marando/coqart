Require Import Arith.
Require Import ZArith.
Require Import Bool.

(* Exercise 2.1 *)
(* Reconstitute manually the type-checking operations on all these examples *)

Check (plus 3).
(*
  plus : nat -> nat -> nat, 3 : nat
  plus 3 : nat -> nat
*)

Check (Zmult (-5)).
(*
  Zmult : Z -> Z -> Z, -5 : Z
  Zmult (-5) : Z -> Z
*)

Check Z.abs_nat.
(*
  Z.abs_nat : Z -> nat
*)

Check (5 + Z.abs_nat (5-19)).
(*
  plus : nat -> nat -> nat, 5 : nat
  plus 5 : nat -> nat, Z.abs_nat : Z -> nat
  5 + Z.abs_nat : Z -> nat, Z.sub : Z -> Z -> Z
  5 + Z.abs_nat Z.sub : Z -> Z -> nat, 5 : Z
  5 + Z.abs_nat Z.sub 5 : Z -> nat, 19 : Z
  5 + Z.abs_nat (5-19) : nat
*)

(* Check (mult 3 (-45)%Z). *)
(*
  mult : nat -> nat -> nat, 3 : nat
  mult 3 : nat -> nat, (-45)%Z : Z
  mult 3 (-45)%Z : [Error]
*)

(* Exercise 2.2 *)
(* What is the type of the following expression *)

Definition exp1 := (fun a b c : Z => (b*b-4*a*c)%Z).

(* Z -> Z -> Z -> Z *)

Check exp1.

(* Exercise 2.3 *)

Definition exp2 := (fun (f g : nat -> nat) (n : nat) => g (f n)).

(* (nat -> nat) -> (nat -> nat) -> nat -> nat *)

Check exp2.

(* Exercise 2.4 *)
(* How many instances of the typing rules are needed to type this expression? *)

Definition exp3 :=
  fun n p : nat => 
    (let diff := n-p in
    let square := diff*diff in square * (square+n))%nat.

(*
  - Two instances of the _Lam_ rule for each parameter
  - Two instances of the _Let-in_ rule for each definition
  - Seven instances of the _Var_ rule for each parameter or local variable access
  [Operators would also have typing rules for multiple types (Z, nat)]
*)

Check exp3.

(* Exercise 2.5 *)
(* Write a function that takes five integer arguments and returns their sum *)
Definition sum5 (a b c d e: Z) : Z := a + b + c + d + e.

Compute (sum5 1 2 3 4 5).

(* Exercise 2.6 *)
(* Use the section mechanism to build a function that takes five arguments
  and returns their sum, without explicitly writing any abstractions. *)

Section Sum_5.
Variables a b c d e : Z.

Definition sumfive : Z := a + b + c + d + e.

Check sumfive.
End Sum_5.
Check sumfive.

(* Exercise 2.7 *)
(* Write the function that corresponds to the polynomial
  2 * x^2 + 3 * x + 3 on relative integers, using alpha-abstraction and
  the functions Zplus and Zmult provided in the ZArith library of Coq.
  Compute the value of this function on integers 2, 3, and 4 *)

Definition p1 (x : Z) : Z := 2 * x * x + 3 * x + 3.

Compute p1 2.
Compute p1 3.
Compute p1 4.