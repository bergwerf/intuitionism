(* Some results about real numbers *)

From intuitionism Require Import lib set seq spr fan func classic choice.
From intuitionism Require Import bcp bar.

(*
Describing intervals of real numbers as binary sequences
--------------------------------------------------------
We can describe the real numbers in [a_0, b_0] as binary sequences. At each step
the interval [a_n, b_n] is split into [a_n, (a_n+2b_h)/3], [(2a_n+b_n)/3, b_n].
A sequence α ∈ Bin selects in which intervals a point is located. Note that
splitting in half would require exact knowledge about the upper/lower bound of
some numbers, which is a problem for some constructions.
The next definitions use [a_0, b_0] = [0, 1].
*)

(* Compute left endpoint of the n-th interval of α with denominator 3^(n+1). *)
Fixpoint lbound α n :=
  (if α n =? 0 then 0 else 2^n) +
  match n with
  | 0 => 0
  | S m => 3 * lbound α m
  end.

(* Distance between m and n. *)
Definition distance m n := (m - n) + (m - n).

(* α and β are within distance 1/(2^δ) of each other. *)
Definition within (δ : nat) (α β : dom Bin) :=
  ∃n, 2^δ * distance (lbound α n) (lbound β n) < 3^n.

(* Continuity of f : [0,1] -> [0,1] at x. *)
Definition point_continuous f x ε :=
  ∃δ, ∀x', within δ x x' -> within ε (f x) (f x').

(* Pointwise continuity of f : [0,1] -> [0,1]. *)
Definition pointwise_continuous f :=
  ∀x ε, point_continuous f x ε.

(* Uniform continuity of f : [0,1] -> [0,1]. *)
Definition uniform_continuous f :=
  ∀ε, ∃δ, ∀x x', within δ x x' -> within ε (f x) (f x').

(* The intermediate value theorem. *)
Definition IntermediateValueTheorem :=
  ∀f, pointwise_continuous f /\ f (0^ω) = 0^ω /\ f (1^ω) = 1^ω ->
  ∀y, ∃x, f x = y.

(* Simple form of Brouwers fixed-point theorem. *)
Definition FixedPointTheorem :=
  ∀f, uniform_continuous f -> ∃x, f x = x.

(*
It would be nice if we can show that both the intermediate value theorem and
Brouwers fixed-point theorem imply LPO without resorting to a full definition
of real numbers. However it seems the binary sequences are not particularly
easy to reason about either, or do arithmetic with.
*)
