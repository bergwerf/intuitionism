(* Brouwer's Continuity Principle (BCP) and related notions. *)

From intuitionism Require Import lib set seq lpo.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Omega.
Import Nat.

(* Brouwers Continuity Principle *)
Axiom BCP :
  forall (R : seq -> nat -> Prop),
  (forall α, exists n, R α n) ->
  (forall α, exists m n, forall β, eqn m α β -> R β n).

(* We find that intuitionistic logic is *not* a subset of classical logic. *)
Theorem not_lpo :
  ~LPO.
Proof.
intros LPO.
assert(P: forall α : seq, exists i,
  (i = 0 /\ exists n, α n <> 0) \/
  (i > 0 /\ forall n, α n = 0)).
{ intros; destruct (LPO α). exists 0; left; auto. exists 1; right; auto. }
destruct (BCP _ P (0^ω)) as [m [n H]]. destruct (eq_dec n 0) as [n0|n1].
- assert(Hα : eqn m (0^ω) (0^ω)). apply eqn_refl.
  apply H in Hα as [[_ [i E]]|[n1 _]]; try omega.
  apply E; auto.
- pose(β := pre m (0^ω) (1^ω)).
  assert(Hβ: eqn m (0^ω) β). apply eqn_pre_n.
  apply H in Hβ as [[n0 _]|[_ A]]; try omega.
  assert(Hβ1: β (m + 1) <> 0). unfold β, cseq; rewrite pre_r; omega.
  auto.
Qed.

(* And indeed the law of excluded middle does not hold under BCP. *)
Corollary not_lem : ~LEM.
Proof. intros H; apply not_lpo; apply lem_lpo; auto. Qed.

(* Any function f : seq -> nat is computable. *)
Lemma f_computable (f : seq -> nat) :
  forall α, exists n, f α = n.
Proof. intros; exists (f α); auto. Qed.

(* Continuity of functions. *)
Theorem BCPf (f : seq -> nat) α :
  exists n, forall β, eqn n α β -> f α = f β.
Proof.
destruct (BCP _ (f_computable f) α) as [m [n H]]. exists m; intros.
rewrite H. symmetry; rewrite H; auto. apply eqn_refl.
Qed.

(* BCPf with a sigma type for the prefix length is inconsistent. *)
(* From: doc/bcp_sig.pdf *)
Section BCPsig.

Definition BCPfsig :=
  forall (f : seq -> nat) α,
  {n | forall β, eqn n α β -> f α = f β}.

(* Trying to prove BCPfsig from BCPf fails. *)
Theorem try_BCPfsig : BCPfsig.
Proof.
intros f α. assert(H := BCPf f α).
(* 'Case analysis on sort Set is not allowed for inductive definition ex.' *)
(* I am not familiar with the reasons for this. *)
Fail destruct H.
Abort.

(* And indeed, we do not want to add this as an axiom! *)
Theorem not_BCPfsig :
  BCPfsig -> 0 = 1.
Proof.
intros BCPfsig.
(* M : seq -> nat, gives us the prefix length of any f to compute its image. *)
pose(M f := proj1_sig (BCPfsig f (0^ω))).
assert(L1: forall f β, eqn (M f) (0^ω) β -> f (0^ω) = f β).
{ intros. apply (proj2_sig (BCPfsig f (0^ω))). auto. }
(* We now construct a function f that is not continuous. *)
pose(m := M (fun _ => 0)).
pose(f β := M (fun α => β (α m))).
assert(f0: f (0^ω) = m). { unfold f, cseq, m; auto. }
assert(L2a: forall β, eqn (M f) (0^ω) β -> f β = m).
{ intros. rewrite <-f0. symmetry; apply L1; auto. }
assert(L2b: forall β α, eqn (f β) (0^ω) α -> β 0 = β (α m)).
{ intros. unfold f in H. apply L1 in H. unfold cseq in H; auto. }
pose(β := pre (M f + 1) (0^ω) (1^ω)).
assert(Hβ: forall α, eqn m (0^ω) α -> β 0 = β (α m)).
{ intros. apply L2b. rewrite L2a; auto. apply eqn_pre. }
pose(α := pre m (0^ω) ((M f + 1)^ω)).
assert(H1α: α m = M f + 1). { unfold α. rewrite pre_r0; auto. }
assert(H2α: β 0 = β (α m)). { apply Hβ. apply eqn_pre_n. }
(* We are ready to show 0 = 1. *)
replace 1 with (β (M f + 1)). rewrite <-H1α, <-H2α. unfold β.
replace (M f + 1) with (0 + S (M f)) by omega. rewrite pre_l. auto.
unfold β. replace (M f + 1) with ((M f + 1) + 0) at 2 by omega.
rewrite pre_r; auto.
Qed.

End BCPsig.
