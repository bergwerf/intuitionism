(* Contradictory results in classical logic. *)

From intuitionism Require Import lib set seq lpo spr fan tau func.

(*
Note that lpo.v cannot import any files that use the BCP axiom. Of course we
want to prove all classical facts in the absence of BCP.
*)

(* If weak injective is strong injective then we have Markov's Principle. *)
Theorem weak_injective_strong_markov :
  (forall A B f, weak_injective A B f -> injective A B f) -> markov_principle.
Proof.
intros WIS α Hα.
(* A weakly injective function s.t. strong injectivity proves the goal *)
pose (f (b : bool) := if b then α else (0..ω)).
assert(weak_inj: weak_injective Bool Seq f).
{ intros a b _ _ H. destruct a, b; auto; exfalso; apply Hα; intros.
  all: simpl in H; eapply equal_f in H; unfold cseq in H.
  apply H. symmetry; apply H. }
assert(apartness: @apart Bool true false).
{ simpl; unfold dec_apart. discriminate. }
apply WIS in weak_inj as inj.
apply inj in apartness; auto; apply I.
Qed.

(* A function which is probably non-surjective is surjective under LPO. *)
(* Note that the converse is not true because not every α : τ1. *)
Theorem lpo_f_surj :
  LPO -> surjective Nat τ2 Tau2.f.
Proof.
intros LPO; intros β Hβ; destruct (LPO β).
- pose (n := epsilon_smallest _ (neq0_dec β) H); destruct n as [n [Hn1 Hn2]].
  exists (S n); split. apply I. simpl; extensionality i.
  unfold prepend, replace, fill, cseq.
  destruct (i <? n) eqn:E; bool_to_Prop. apply Hn2 in E; omega.
  eapply τ_mono_ext with (n:=1)(j:=i) in Hβ. omega. apply E. omega.
- exists 0; split. apply I. simpl.
  extensionality n; auto.
Qed.
