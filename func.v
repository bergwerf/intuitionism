(* Functions *)

From intuitionism Require Import lib set seq bcp spr fan.

(* Classic injective function. *)
Definition weak_injective A B (f : dom A -> dom B) :=
  forall a α, a isin A -> α isin A -> f a = f α -> a = α.

(* Strong injective function. *)
Definition injective A B (f : dom A -> dom B) :=
  forall a α, a isin A -> α isin A -> a#α -> f a # f α.

(* Surjective function. *)
Definition surjective A B (f : dom A -> dom B) :=
  forall β, β isin B -> exists α, α isin A /\ f α = β.

Definition bijective A B f := injective A B f /\ surjective A B f.

(* Strong injective implies weak injective. *)
Theorem injective_to_weak A B f :
  injective A B f -> weak_injective A B f.
Proof.
intros H a α Ha Hα Hf. apply apart_spec; intros P.
apply H in P; auto. apply apart_spec in P; auto.
Qed.

(* The set of all sequences is not denumerable. *)
Theorem seqs_uncountable :
  ~exists f, surjective Nat Seq f.
Proof.
intros H; destruct H as [f H].
pose(γ (n : nat) := f n n + 1).
assert(P: γ isin Seq). apply I.
apply H in P as [n [Hn Hf]].
apply equal_f with (x:=n) in Hf.
unfold γ in Hf. lia.
Qed.

(* The set of all finite sequences is denumerable. *)
Theorem fseq_eq_nat :
  exists f, bijective Nat FSeq f.
Proof.
(* The classic approach is to use prime factorization. *)
Admitted.

(*
There exists an injection from the Baire space (natural number sequences) to the
Cantor space (binary sequences). With the Fan Theorem we can later prove that a
bijection is not possible.
*)
Theorem cantor_eq_seq :
  exists f, injective Seq Cantor f.
Proof.
(* This function is trickier. *)
Admitted.
