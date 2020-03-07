(* Brouwer's Continuity Principle (BCP) and related notions. *)

From intuitionism Require Import lib set seq spr classic.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Omega.
Import Nat.

(* Brouwers Continuity Principle *)
Axiom BCP :
  ∀ (R : seq -> nat -> Prop),
  (∀ α, ∃ n, R α n) ->
  (∀ α, ∃ m n, ∀ β, eqn m α β -> R β n).

(* We find that intuitionistic logic is *not* a subset of classical logic. *)
Theorem not_lpo :
  ~LPO.
Proof.
intros LPO.
assert(P: ∀ α : seq, ∃ i,
  (i = 0 /\ ∃ n, α n <> 0) \/
  (i > 0 /\ ∀ n, α n = 0)).
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

Lemma fully_defined {A B} (f : A -> B) :
  ∀ a, ∃ b, f a = b.
Proof. intros; now exists (f a). Qed.

Lemma fully_defined_aset_dom {A B} (f : dom A -> B) :
  ∀ α, α isin A -> ∃ b, f α = b.
Proof. intros; now exists (f α). Qed.

(* Continuity of functions. *)
Theorem BCPf (f : seq -> nat) α :
  ∃ n, ∀ β, eqn n α β -> f α = f β.
Proof.
destruct (BCP _ (fully_defined f) α) as [m [n H]]. exists m; intros.
rewrite H. symmetry; rewrite H; auto. apply eqn_refl.
Qed.

(* BCP generalizes to spreads *)
Theorem BCPext (X : spread) (R : seq -> nat -> Prop) :
  (∀ α, α isin X -> ∃ n, R α n) ->
  (∀ α, α isin X -> ∃ m n, ∀ β, β isin X -> eqn m α β -> R β n).
Proof.
intros Rall.
pose(rσ := (Retract.r X)).
pose(T := (λ α n, R (rσ α) n)).
assert(HT: ∀ α, ∃ n, T α n).
- intros; pose(Hα := Retract.r_image X α); apply Rall in Hα.
  destruct Hα as [n Hn]; exists n; auto.
- intros; destruct (BCP T HT α) as [m [n P]]. exists m, n; intros.
  apply P in H1; unfold T, rσ in H1; rewrite Retract.r_id in H1; auto.
Qed.

(* BCPf with a sigma type for the prefix length is inconsistent. *)
(* From: doc/bcp_sig.pdf *)
Section BCPsig.

Definition BCPfsig :=
  ∀ (f : seq -> nat) α,
  {n | ∀ β, eqn n α β -> f α = f β}.

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
assert(L1: ∀ f β, eqn (M f) (0^ω) β -> f (0^ω) = f β).
{ intros. apply (proj2_sig (BCPfsig f (0^ω))). auto. }
(* We now construct a function f that is not continuous. *)
pose(m := M (λ _, 0)).
pose(f β := M (λ α, β (α m))).
assert(f0: f (0^ω) = m). { unfold f, cseq, m; auto. }
assert(L2a: ∀ β, eqn (M f) (0^ω) β -> f β = m).
{ intros. rewrite <-f0. symmetry; apply L1; auto. }
assert(L2b: ∀ β α, eqn (f β) (0^ω) α -> β 0 = β (α m)).
{ intros. unfold f in H. apply L1 in H. unfold cseq in H; auto. }
pose(β := pre (M f + 1) (0^ω) (1^ω)).
assert(Hβ: ∀ α, eqn m (0^ω) α -> β 0 = β (α m)).
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
