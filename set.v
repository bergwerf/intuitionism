(* Sets with constructive inequality *)

From intuitionism Require Import lib.

(*
The sets we use must provide a positive inequality predicate and a membership
predicate (like Ensembles). I decided to not use sigma types in this library
because projections cannot be automatically coerced. I do encourage using
extensionality axioms.

We need this intermediary definition such that we can later use one clean
definition of properties like injectivity. (I picked C as prefix for
*C*onstructive because I couldn't come up with anything better).
*)
Record cset := CSet {
  dom :> Type;
  member : dom -> Prop;
  apart : dom -> dom -> Prop;
  apart_neq : forall x y, apart x y -> x <> y;
  apart_sym : forall x y, apart x y -> apart y x;
}.

Definition full_set {T} (x : T) := True.

Arguments apart {_}.
Notation "α ':' X" := (member X α)(at level 50).
Notation "α '#' β" := (apart α β)(at level 50, format "α '#' β").

Definition neq_apart {T} (n m : T) := n <> m.

Lemma neq_apart_neq {T} (n m : T) : neq_apart n m -> n <> m.
Proof. auto. Qed.

Lemma neq_apart_sym {T} (n m : T) : neq_apart n m -> neq_apart m n.
Proof. unfold neq_apart; intros H P; apply H; auto. Qed.

(* The natural numbers *)
Section NaturalNumbers.

Definition nat_member (n : nat) := True.

Definition Nat := CSet nat nat_member neq_apart neq_apart_neq neq_apart_sym.

End NaturalNumbers.
