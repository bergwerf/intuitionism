(* Sets with constructive inequality *)

From intuitionism Require Import lib.

(*
Sets with positive apartness

The sets we use must provide a positive inequality predicate and a membership
predicate (like Ensembles). I decided to not use sigma types in this library
because projections cannot be automatically coerced. I do encourage using
extensionality axioms.
*)
Record aset := ASet {
  dom : Type;
  member : dom -> Prop;
  apart : dom -> dom -> Prop;
  apart_spec : forall x y, ~apart x y <-> x = y;
  apart_neq : forall x y, apart x y -> x <> y;
  apart_sym : forall x y, apart x y -> apart y x;
}.

Arguments apart {_}.
Notation "α 'isin' X" := (member X α) (at level 50).
Notation "α '#' β" := (apart α β) (at level 50, format "α '#' β").

(* The second half of apart_neq is at least always not not true. *)
Theorem neq_nnapart S (x y : dom S) : x <> y -> ~~x#y.
Proof. intros H P; apply (apart_spec S) in P; auto. Qed.

Definition full_set {T} (x : T) := True.

(* Apartness for decidable equality *)
Section DecidableEquality.
Variable T : Type.
Variable dec : forall x y : T, {x = y} + {x <> y}.
Definition dec_apart (n m : T) := n <> m.

Lemma dec_apart_spec (x y : T) :
  ~dec_apart x y <-> x = y.
Proof.
unfold dec_apart; split; intros.
- destruct (dec x y); auto; exfalso; auto.
- intros P; auto.
Qed.

Lemma dec_apart_neq (x y : T) : dec_apart x y -> x <> y.
Proof. auto. Qed.

Lemma dec_apart_sym (n m : T) : dec_apart n m -> dec_apart m n.
Proof. unfold dec_apart; intros H P; apply H; auto. Qed.

End DecidableEquality.

Definition Nat := ASet nat full_set (dec_apart nat)
  (dec_apart_spec nat eq_dec) (dec_apart_neq nat)
  (dec_apart_sym nat).

Definition Bool := ASet bool full_set (dec_apart bool)
  (dec_apart_spec bool bool_dec) (dec_apart_neq bool)
  (dec_apart_sym bool).
