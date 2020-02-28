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
  (forall α, exists m n, forall β, con m α β -> R β n).

(* We find that intuitionistic logic is *not* a subset of classical logic. *)
Theorem not_lpo :
  ~LPO.
Proof.
intros LPO.
assert(R: forall α : seq, exists i,
  (i = 0 /\ exists n, α n <> 0) \/
  (i > 0 /\ forall n, α n = 0)).
{ intros; destruct (LPO α). exists 0; left; auto. exists 1; right; auto. }
destruct (BCP _ R (0..)) as [m [n H]]. destruct (eq_dec n 0) as [n0|n1].
- assert(Hα : con m (0..) (0..)). apply con_id.
  apply H in Hα as [[_ [i E]]|[n1 _]]; try omega.
  apply E; auto.
- pose (β := (prepend m (0..) (1..))).
  assert(Hβ: con m (0..) β). apply con_prepend.
  apply H in Hβ as [[n0 _]|[_ A]]; try omega.
  assert(Hβ1: β (m + 1) <> 0). unfold β, cseq; rewrite prepend_access_r; omega.
  auto.
Qed.
