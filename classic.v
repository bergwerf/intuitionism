(* Contradictory results in classical logic. *)

From intuitionism Require Import lib set seq lpo spr fan tau func.

(* A function which is probably non-surjective is surjective under LPO. *)
(* Note that the converse is not true because not every α : τ1. *)
Theorem lpo_f_surj :
  LPO -> surjective Nat τ1 NotSurj.f.
Proof.
intros LPO; intros β Hβ; destruct (LPO β).
- pose (n := epsilon_smallest _ (neq0_dec β) H); destruct n as [n [Hn1 Hn2]].
  exists (S n); split. apply I. simpl; extensionality i.
  unfold prepend, replace, fill, cseq.
  destruct (i <? n) eqn:E; bool_to_Prop. apply Hn2 in E; omega.
  eapply τ_mono in Hβ as Hmono; apply member_τP in Hβ.
  assert(P1: β n <= 1). apply Hβ. assert(P2: β i <= 1). apply Hβ.
  assert(P3: β n = 1). omega. assert(P4: β n <= β i). apply Hmono.
  omega. omega.
- exists 0; split. apply I. simpl.
  extensionality n; auto.
Qed.
