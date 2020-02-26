(* Brouwer's Continuity Principle (BCP) and related notions. *)

From intuitionism Require Import seq.

Require Import Coq.Arith.PeanoNat.
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
Definition LPO := forall (α : seq), (forall n, α n = 0) \/ (exists n, α n <> 0).

(* Lesser Limited Principle of Omniscience *)
Definition LLPO := forall (α : seq),
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Even k) \/
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Odd k).

Lemma lpo_llpo :
  LPO -> LLPO.
Proof.
Admitted.

Lemma bcp_or_lpo :
  BCP -> ~LPO /\ LPO -> ~BCP.
Proof.
Admitted.

Lemma bcp_or_llpo :
  BCP -> ~LLPO /\ LLPO -> ~BCP.
Proof.
Admitted.