(* Functions *)

From intuitionism Require Import lib set seq bcp spr fan tau.

(* Strong definition of injective function on sequences. *)
Definition injective A B (f : dom A -> dom B) :=
  forall a α, a : A -> α : A -> a#α -> f a # f α.

(* Surjective function on sequences. *)
Definition surjective A B (f : dom A -> dom B) :=
  forall β, β : B -> exists α, α : A /\ f α = β.

(*
Classical surjection is different from intuitionistic surjection.
See classic.v for a proof that f is surjective under LPO.
*)
Module NotSurj.

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

(* f is injective. *)
Theorem f_inj :
  injective Nat τ1 f.
Proof.
intros n m _ _; simpl; unfold nat_apart; intros H.
assert(C: n < m \/ m < n). omega. destruct C, n, m; try omega; simpl.
- exists m. rewrite <-(add_0_r m) at 3; rewrite prepend_access_r.
  unfold cseq; omega.
- exists n. apply le_exists_sub in H0 as [k [Hk _]].
  assert(R: m = n + S k). omega. rewrite R, prepend_access_l.
  rewrite <-(add_0_r n) at 2; rewrite prepend_access_r. unfold cseq; omega.
- exists n. rewrite <-(add_0_r n) at 2; rewrite prepend_access_r.
  unfold cseq; omega.
- exists m. apply le_exists_sub in H0 as [k [Hk _]].
  assert(R: n = m + S k). omega. rewrite R, prepend_access_l.
  rewrite <-(add_0_r m) at 3; rewrite prepend_access_r. unfold cseq; omega.
Qed.

(* f is not surjective. *)
Theorem f_not_surj :
  ~surjective Nat τ1 f.
Proof.
assert(P0: 0.. : τ1). apply member_τP; intros n; unfold cseq; omega.
intros H; destruct (BCPext τ1 _ H (0..) P0) as [m [n Q]].
assert(P1: f (S (m + n)) : τ1). apply f_image. apply Q in P1 as [_ P1].
revert P1; destruct n; simpl; intros P1.
- apply equal_f with (x:=m) in P1; revert P1.
  rewrite add_0_r; rewrite prepend_access_r0.
  unfold cseq; intros; omega.
- apply equal_f with (x:=n) in P1; revert P1. rewrite prepend_access_r0.
  assert(R: m + S n = n + S m). omega. rewrite R; rewrite prepend_access_l.
  unfold cseq; intros; omega.
- intros i Hi; unfold f. unfold prepend, replace, fill.
  assert(R: i <? m + n = true). bool_to_Prop; omega. rewrite R.
  omega.
Qed.

End NotSurj.
