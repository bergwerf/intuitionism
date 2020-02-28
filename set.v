(* Sets with constructive inequality *)

From intuitionism Require Import lib.

(*
The sets we use must provide a positive inequality predicate and a membership
predicate (like Ensembles). I decided to not use sigma types in this library
because projections cannot be automatically coerced. I do encourage using
extensionality axioms. We need this intermediary definition such that we can
later use one definition of properties like injectivity.
*)
Record cset := CSet {
  dom :> Type;
  member : dom -> Prop;
  apart : dom -> dom -> Prop;
  apart_neq : forall x y, apart x y -> x <> y;
  apart_sym : forall x y, apart x y -> apart y x;
}.

Arguments apart {_}.
Notation "α ':' X" := (member X α)(at level 50).
Notation "α '#' β" := (apart α β)(at level 50, format "α '#' β").

(* The natural numbers *)
Section NaturalNumbers.

Definition nat_member (n : nat) := True.
Definition nat_apart (n m : nat) := n <> m.

Lemma nat_apart_neq n m : nat_apart n m -> n <> m.
Proof. auto. Qed.

Lemma nat_apart_sym n m : nat_apart n m -> nat_apart m n.
Proof. unfold nat_apart; omega. Qed.

Definition Nat := CSet nat nat_member nat_apart nat_apart_neq nat_apart_sym.

End NaturalNumbers.