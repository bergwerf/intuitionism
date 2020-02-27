(* Functions *)

From intuitionism Require Import lib seq bcp spr fan tau.

(* Strong definition of injective function on sequences. *)
Definition injective A B (f : seq -> seq) :=
  forall α β, α : A -> β : B -> α#β -> f α # f β.

(* Surjective function on sequences. *)
Definition surjective A B (f : seq -> seq) :=
  forall β, β : B -> exists α, α : A /\ f α = β.

(* Classical surjection is different from intuitionistic surjection. *)
Module ClassicalSurjection.

Definition f n :=
  match n with
  | 0 => 0..
  | S m => prepend m (0..) (1..)
  end.

Lemma f_image n :
  f n : τ1.
Proof.
apply intro_inspr; intros; apply intro_τP. unfold f; destruct n.
- intros n; unfold cseq; omega.
- intros i. split. split; apply prepend_prop; intros; unfold cseq; omega.
  unfold prepend, replace, fill, cseq.
  destruct (i <? n) eqn:E1; destruct (S i <? n) eqn:E2;
  repeat bool_to_Prop; omega.
Qed.

End ClassicalSurjection.
