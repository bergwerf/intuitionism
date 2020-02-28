(* Some contradictory results in classical mathematics. *)

From intuitionism Require Import lib seq.

(* Limited Principle of Omniscience *)
Definition LPO := forall (α : seq), (exists n, α n <> 0) \/ (forall n, α n = 0).

(* Lesser Limited Principle of Omniscience *)
Definition LLPO := forall (α : seq),
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Even k) \/
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Odd k).

Lemma neq0_dec (α : seq) n : {α n <> 0} + {~(α n <> 0)}.
Proof. intros; destruct (eq_dec (α n) 0). right; omega. left; omega. Qed.

Theorem lpo_llpo :
  LPO -> LLPO.
Proof.
assert(nltgt_eq: forall n m : nat, ~(n < m) /\ ~(n > m) -> n = m).
{ intros; omega. } intros LPO α. destruct (LPO α).
- destruct (epsilon_smallest _ (neq0_dec α) H) as [l [L1 L2]].
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