(* Some results about real numbers *)

From intuitionism Require Import lib set seq spr fan func choice bcp bar.

(*
To formalize some interesting results about real numbers this document defines
a distance judgement between binary sequences that is based on regarding real
numbers as sequences of nested rational intervals. A full formalization would
require a significant number of intermediary lemmas.

We describe the real numbers in [0, 1] as binary sequences. At each step the
interval [a, b] is split into [a, (a+2b)/3] and [(2a+b)/3, b]. A sequence
α ∈ Bin selects in which intervals a point is located. Note that splitting in
half would require exact knowledge about the upper/lower bound of some numbers,
which is a problem for some of the constructions.
*)

(* Compute left endpoint of the n-th interval of α with denominator 3^n. *)
Fixpoint lbound α n :=
  match n with
  | 0 => 0
  | S m => let l := lbound (del 1 α) m in if α 0 =? 0 then l else 3^m + l
  end.

(* Distance between m and n. *)
Definition distance m n := (m - n) + (m - n).

(* α and β are within distance 1/(2^δ) of each other. *)
Definition within (α β : dom Bin) (δ : nat) :=
  ∃n, 2^δ * distance (lbound α n) (lbound β n) < 3^n.

(* Pointwise continuity of f : [0,1] -> [0,1] at x0. *)
Definition point_continuous f x₀ ε :=
  ∃δ, ∀x, within x₀ x δ -> within (f x₀) (f x) ε.

(* Uniform continuity of f : [0,1] -> [0,1]. *)
Definition uniform_continuous f ε :=
  ∃δ, ∀x₀ x₁, within x₀ x₁ δ -> within (f x₀) (f x₁) ε.
