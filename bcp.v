(* Brouwer's Continuity Principle (BCP) and related notions. *)

From intuitionism Require Import seq.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Omega.
Import Nat.

(* Brouwers Continuity Principle *)
Definition BCP :=
  forall (R : seq -> nat -> Prop),
  (forall α, exists n, R α n) ->
  (forall α, exists m n, forall β, con m α β -> R β n).

Module Brouwer.
Axiom BCP : BCP.
End Brouwer.

(* Limited Principle of Omniscience *)
Definition LPO := forall (α : seq), (exists n, α n <> 0) \/ (forall n, α n = 0).

(* Lesser Limited Principle of Omniscience *)
Definition LLPO := forall (α : seq),
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Even k) \/
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Odd k).

Theorem lpo_llpo :
  LPO -> LLPO.
Proof.
assert(nltgt_eq: forall n m : nat, ~(n < m) /\ ~(n > m) -> n = m).
{ intros; omega. }
intros LPO α.
assert(neq0_dec: forall n, {α n <> 0} + {~(α n <> 0)}).
{ intros; destruct (eq_dec (α n) 0). right; omega. left; omega. }
destruct (LPO α).
- destruct (epsilon_smallest _ neq0_dec H) as [l [L1 L2]].
  destruct (even l) eqn:E.
  + apply even_spec in E; left; intros k [H1 H2].
    assert(Hk: k = l). apply nltgt_eq; split; intros P.
    * apply L2 in P; auto.
    * apply H1 in P; auto.
    * subst; auto.
  + assert(O: Odd l). apply odd_spec; unfold odd; rewrite E; auto.
    right; intros k [H1 H2].
    assert(Hk: k = l). apply nltgt_eq; split; intros P.
    * apply L2 in P; auto.
    * apply H1 in P; auto.
    * subst; auto.
- left; intros k [H1 H2]; exfalso; auto.
Qed.

Theorem bcp_nlpo :
  BCP -> ~LPO.
Proof.
intros BCP LPO.
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
  assert(Hβ1: β (m + 1) <> 0). unfold β, cseq; rewrite prepend_unshift; omega.
  auto.
Qed.
