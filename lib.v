(* All imports *)

Require Export Coq.Init.Nat.
Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Logic.ConstructiveEpsilon.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.micromega.Lia.
Require Export Coq.Unicode.Utf8.
Export PeanoNat.Nat.
Export ListNotations.

Arguments exist {_ _}.

(* Some first results in propositional logic. *)
Section PropositionalLogic.

Variable P : Prop.
Variable Q : Prop.

Lemma nnLEM : ~~(P \/ ~P).
Proof. unfold not; auto. Qed.

Lemma implyn_n : (P -> ~P) -> ~P.
Proof. auto. Qed.

Lemma contra : (P -> Q) -> ~Q -> ~P.
Proof. auto. Qed.

Lemma nn_imply_nn : (P -> Q) -> ~~P -> ~~Q.
Proof. auto. Qed.

Lemma nn_imply : ~~(P -> Q) -> (P -> ~~Q).
Proof. auto. Qed.

End PropositionalLogic.

(* Some first results in predicate logic. *)
Section PredicateLogic.

Variable T : Type.
Variable P : T -> Prop.

Lemma forall_nn : (~~∀x, P x) -> ∀x, ~~(P x).
Proof. unfold not; auto. Qed.

Lemma not_forall_not : (∃x, P x) -> ~∀x, ~P x.
Proof. intros [x Hx] H. eapply H; apply Hx. Qed.

Lemma forall_not : (~∃x, P x) -> ∀x, ~P x.
Proof. intros H1 n H2. apply H1; exists n; auto. Qed.

Lemma nn_exists (Q : T -> Prop) :
  ~~(∃x, P x) -> (∀x, P x -> Q x) -> ~~(∃x, Q x).
Proof.
intros nnEx PQ nH. apply nnEx; intros [x Px].
apply nH; exists x. now apply PQ.
Qed.

End PredicateLogic.

Ltac bool_to_Prop :=
  match goal with
  | [H : _ && _ = true |- _] =>
    let P := fresh H in (apply andb_prop in H as [P H])
  | [H : _ =? _ = true |- _]   => apply eqb_eq in H
  | [H : _ =? _ = false |- _]  => apply eqb_neq in H
  | [H : _ <=? _ = true |- _]  => apply leb_le in H
  | [H : _ <=? _ = false |- _] => apply leb_gt in H
  | [H : _ <? _ = true |- _]   => apply ltb_lt in H
  | [H : _ <? _ = false |- _]  => apply ltb_ge in H
  | |- (_ && _ = true)   => apply andb_true_intro; split
  | |- (_ =? _ = true)   => apply eqb_eq
  | |- (_ =? _ = false)  => apply eqb_neq
  | |- (_ <=? _ = true)  => apply leb_le
  | |- (_ <=? _ = false) => apply leb_gt
  | |- (_ <? _ = true)   => apply ltb_lt
  | |- (_ <? _ = false)  => apply ltb_ge
  | _ => idtac
  end.

Ltac bool_lia :=
  repeat bool_to_Prop;
  try (symmetry; repeat bool_to_Prop);
  lia.