(* A peculiar sequence in Brouwers mind. *)

From intuitionism Require Import lib set seq lpo.

(*
In response to a letter from C. Griss about removing negation altogether,
Brouwer tries to agrue that without negation some interesting properties of
mathematics can not be stated ('Essentieel-negatieve eigenschappen'). The same
holds for denouncing LPO, but to the intuitionist this is already nonsense.
*)

Module Brouwer.
Section Truth.

Variable P : Prop.

(* α describes if P was proven on the n-th day of my life if this holds. *)
Definition proof_scan (α : seq) := forall n, α n <> 0 -> P.

(*
To Brouwer the meaning of truth is relative; there is no absolute truth which
exists regardless of the thoughts of the individual. Instead there is only
individual truth. If something is true, then there exists a day when he wrote
down a proof in his diary. The resulting two axioms can almost be proven (they
are both not not true under BCP). Note that the recall axiom in general states
there is an effective proof search technique. We could consider humanity as a
whole as the proof searching object.
*)

(* + Regardless of P, Brouwer can scan through his diary for a proof. *)
(* + Brouwer insists to only accept P as true if he ever wrote down a proof. *)
Definition intuition := exists π, proof_scan π /\ (P -> exists n, π n <> 0).

(* The Principle of Omniscience has immediate knowledge. *)
Theorem lem_intuition : LEM -> intuition.
Proof.
intros LEM; destruct (LEM P).
- exists (1^ω); split. intros _ _; auto.
  intros _; exists 0. unfold cseq; omega.
- exists (0^ω); split. unfold cseq; intros n Hn. omega.
  intros HP. exfalso; auto.
Qed.

(* + Regardless of P, Brouwer can scan through his diary for a proof. *)
(* + Brouwer insists to only accept P as true if he ever wrote down a proof. *)
Axiom have_intuition : intuition.

End Truth.

Section Sequence.

(* Take any proposition (such as one for which we do not yet know its truth). *)
Variable P : Prop.

(*
There now exists a sequence s.t. it impossible it is not apart from zero, but
for which apartness from zero is reckless.
*)
Theorem brouwers_sequence : exists β : seq,
  ~~(exists n, β n <> 0) /\ ((exists n, β n <> 0) -> P \/ ~P).
Proof.
destruct (have_intuition (P \/ ~P)) as [π [H1π H2π]].
exists π; split. apply (nn_imply_nn (P \/ ~P)). auto. apply nnLEM.
intros [n Hn]. apply (H1π n); auto.
Qed.

End Sequence.

(* Now Markov's Principle implies LPO. *)
Theorem markov_lpo :
  markov_principle -> LPO.
Proof.
unfold markov_principle; intros MP β.
destruct (brouwers_sequence (exists n, β n <> 0)) as [γ [H1γ H2γ]].
assert(MPH: ~forall n, γ n = 0). { intros H. apply H1γ; intros [n Hn]; auto. }
apply MP in MPH. apply H2γ in MPH as [H1|H2]. left; auto.
right; intros n. destruct (eq_nat_dec (β n) 0); auto.
exfalso; apply H2. exists n; auto.
Qed.

End Brouwer.

(* We can now contradict Markov's Principle under BCP. *)
From intuitionism Require Import bcp.

Corollary not_markov : ~markov_principle.
Proof. intros H; apply not_lpo. apply Brouwer.markov_lpo; auto. Qed.
