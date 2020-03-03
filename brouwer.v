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

(*
To Brouwer the meaning of truth is relative; there is no absolute truth which
exists regardless of the thoughts of the individual. Instead there is only truth
within the reference of the 'creating subject'. We could consider humanity as a
whole as the creating subject. Will we not only accept something as true if one
day someone comes up with a proof?
*)

(* α describes a proof search for P. If α is 1 then a proof of P is found. *)
Definition proof_search (α : seq) := forall n, α n <> 0 -> P.

(* Brouwer insists to only accept P as true if he ever wrote down a proof. *)
Definition creating_subject :=
  exists π, proof_search π /\ (P -> exists n, π n <> 0).

(* The Principle of Omniscience has immediate knowledge. *)
Theorem lem_intuition : LEM -> creating_subject.
Proof.
intros LEM; destruct (LEM P).
- exists (1^ω); split. intros _ _; auto.
  intros _; exists 0. unfold cseq; lia.
- exists (0^ω); split. unfold cseq; intros n Hn. lia.
  intros HP. exfalso; auto.
Qed.

(* We consider ourselves as the creating subject; we decide what is true. *)
Axiom internal_truth : creating_subject.

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
destruct (internal_truth (P \/ ~P)) as [π [H1π H2π]].
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
right; intros n. destruct (eq_dec (β n) 0); auto.
exfalso; apply H2. exists n; auto.
Qed.

End Brouwer.

(* We can now contradict Markov's Principle under BCP. *)
From intuitionism Require Import bcp.

Corollary not_markov : ~markov_principle.
Proof. intros H; apply not_lpo. apply Brouwer.markov_lpo; auto. Qed.
