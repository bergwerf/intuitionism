(* Some contradictory results in classical mathematics. *)

From intuitionism Require Import lib seq.

(* Principle of Omniscience, or the Law of the Excluded Middle *)
Definition LEM := forall P, P \/ ~P.

(* Limited Principle of Omniscience *)
Definition LPO := forall (α : seq), (exists n, α n <> 0) \/ (forall n, α n = 0).

(* Lesser Limited Principle of Omniscience *)
Definition LLPO := forall (α : seq),
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Even k) \/
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Odd k).

Lemma neq0_dec (α : seq) n : {α n <> 0} + {~(α n <> 0)}.
Proof. intros; destruct (eq_dec (α n) 0). right; lia. left; lia. Qed.

Lemma nat_nltgt_eq n m : ~(n < m) -> ~(n > m) -> n = m.
Proof. lia. Qed.

Lemma even_false_odd n : even n = false -> Odd n.
Proof. intros; apply odd_spec; unfold odd; rewrite H; auto. Qed.

(* LEM is as least as strong as LPO. *)
Theorem lem_lpo :
  LEM -> LPO.
Proof.
intros PO α; destruct (PO (exists n, α n <> 0)). left; auto.
right; intros n; destruct (eq_dec (α n) 0); auto.
exfalso; apply H; exists n; auto.
Qed.

(* LPO is as least as strong as LLPO. *)
Theorem lpo_llpo :
  LPO -> LLPO.
Proof.
intros LPO α. destruct (LPO α).
- destruct (epsilon_smallest _ (neq0_dec α) H) as [l [L1 L2]].
  destruct (even l) eqn:E.
  1: apply even_spec in E; left.
  2: apply even_false_odd in E; right.
  all: intros k [H1 H2]; replace k with l; auto.
  all: apply nat_nltgt_eq; intros P.
  all: try apply L2 in P; auto.
  all: try apply H1 in P; auto.
- left; intros k [H1 H2]; exfalso; auto.
Qed.

(* Some results using only constructive logic. *)
Section Logic.

Lemma nnLEM P : ~~(P \/ ~P).
Proof. unfold not; auto. Qed.

Lemma contra (P Q : Prop) : (P -> Q) -> ~Q -> ~P.
Proof. auto. Qed.

Lemma nn_imply_nn (P Q : Prop) : (P -> Q) -> ~~P -> ~~Q.
Proof. auto. Qed.

Lemma nn_imply (P Q : Prop) : ~~(P -> Q) -> (P -> ~~Q).
Proof. auto. Qed.

Section Quantification.

Variable T : Type.
Variable P : T -> Prop.

Lemma forall_nn : (~~forall x, P x) -> forall x, ~~(P x).
Proof. unfold not; auto. Qed.

Lemma not_forall_not : (exists x, P x) -> ~forall x, ~P x.
Proof. intros [x Hx] H. eapply H; apply Hx. Qed.

Lemma forall_not : (~exists x, P x) -> forall x, ~P x.
Proof. intros H1 n H2. apply H1; exists n; auto. Qed.

Lemma nn_exists (Q : T -> Prop) :
  ~~(exists x, P x) -> (forall x, P x -> Q x) -> ~~(exists x, Q x).
Proof.
intros nnEx PQ nH. apply nnEx; intros [x Px].
apply nH; exists x. now apply PQ.
Qed.

End Quantification.
End Logic.

(* Reckless statements *)
Section Recklessness.
(*
Some statements do not directly imply LPO or LLPO, yet as intuitionists we do
not want to consider them as true. In particular these are statements that can
prove properties about a number which is still unknown to mathematics and that
might not even exist at all. An example is the length of the first cycle in a
a Collatz sequence that does not contain 1, or the first position at which the
decimal expansion of π contains 99 consecutive nines.

Note that the key point here is that to an intuitionist 'A \/ B' means 'I can
give you a proof of either A or B'. A classical mathematician would be happy if
you can show that one of the two must hold, but you are still unsure which.
*)

(*
We say P is reckless if it can determine, for any function α (Collatz cycles,
extremely rare patterns in the decimal expansions of π, etc.) if the smallest
accepted number, if it exists, is even or odd, given that α does or does not
only map to 0. Note that this is just a weaker version of LLPO.
*)
Definition recklessness :=
  forall α, ~(forall n, α n = 0) ->
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Even k) \/
  (forall k, ((forall i, i < k -> α i = 0) /\ α k <> 0) -> Odd k).

(* A version of Markov's Principle that is stronger than recklessness. *)
Definition markov_principle :=
  forall α : seq, ~(forall n, α n = 0) -> exists n, α n <> 0.

(* Markov's Principle is reckless. *)
Theorem markov_reckless :
  markov_principle -> recklessness.
Proof.
intros SR α Hα. apply (SR α) in Hα.
assert(n0 := epsilon_smallest _ (neq0_dec α) Hα);
destruct n0 as [n0 [H1 H2]]; destruct (even n0) eqn:E.
1: apply even_spec in E; left.
2: apply even_false_odd in E; right.
all: intros n [Hn1 Hn2]; replace n with n0; auto.
all: apply nat_nltgt_eq; intros P.
all: try apply H2 in P; auto.
all: apply Hn1 in P; rewrite H1 in P; discriminate.
Qed.

(* LPO implies Markov's Principle. *)
Theorem lpo_markov :
  LPO -> markov_principle.
Proof.
intros LPO α H. destruct (LPO α).
- destruct H0 as [n Hn]; exists n; auto.
- exfalso; apply H; auto.
Qed.

End Recklessness.

(* Some results about the apartness relation for sequences. *)
Section Apartness.

(* Under LPO sequence apartness is equivalent to inequality. *)
Theorem lpo_neq_seq_apart α β :
  LPO -> α <> β -> seq_apart α β.
Proof.
(* Define a sequence which is non-zero where α anb β are not equal. *)
pose(γ n := if α n =? β n then 0 else 1).
assert(Hγ: forall n, γ n = 0 -> α n = β n).
{ unfold γ; intros n. destruct (α n =? β n) eqn:H; bool_lia. }
intros LPO H; destruct (LPO γ) as [[n Hn]|Hn].
- exists n; intros P; revert Hn; unfold γ.
  replace (α n =? β n) with true by bool_lia; auto.
- exfalso; apply H; extensionality n. apply Hγ; auto.
Qed.

(* If sequence inequality implies apartness, then we have Markov's Principle. *)
Theorem neq_seq_apart_markov :
  (forall α β, α <> β -> seq_apart α β) -> markov_principle.
Proof.
intros H α Hα. assert(αneq0: α <> (0^ω)).
{ intros P; apply Hα; rewrite P; auto. }
apply H in αneq0 as [n Hn].
exists n; auto.
Qed.

End Apartness.
