(* A peculiar sequence in Brouwers mind. *)

From intuitionism Require Import lib set seq classic bcp.

(*
In response to a letter from C. Griss about removing negation altogether,
Brouwer tries to agrue that without negation some interesting properties of
mathematics can not be stated ('Essentieel-negatieve eigenschappen'). The same
holds for denouncing LPO, but to the intuitionist this is already nonsense.
*)
Section BrouwerAndNegation.

(*
To Brouwer the meaning of truth is relative; there is no absolute truth which
exists regardless of the thoughts of the individual. Instead there is only truth
within the reference of the 'creating subject'. We could consider humanity as a
whole as the creating subject. Will we not only accept something as true if one
day someone comes up with a proof?
*)
Section CreatingSubject.

Variable P : Prop.

(* α describes a proof search for P. If α is 1 then a proof of P is found. *)
Definition proof_search (α : seq) := ∀ n, α n <> 0 -> P.

(* Brouwer insists to only accept P as true if he ever wrote down a proof. *)
Definition creating_subject :=
  ∃ π, proof_search π /\ (P -> ∃ n, π n <> 0).

(* The Principle of Omniscience has immediate knowledge. *)
Theorem lem_creating_subject : LEM -> creating_subject.
Proof.
intros LEM; destruct (LEM P).
- exists (1^ω); split. intros _ _; auto.
  intros _; exists 0. unfold cseq; lia.
- exists (0^ω); split. unfold cseq; intros n Hn. lia.
  intros HP. exfalso; auto.
Qed.

(* We consider ourselves as the creating subject; we decide what is true. *)
Axiom internal_truth : creating_subject.

End CreatingSubject.

(*
There now exists a sequence s.t. it impossible it is not apart from zero, but
for which apartness from zero is reckless.
*)
Theorem brouwers_sequence P : ∃ β : seq,
  ~~(∃ n, β n <> 0) /\ ((∃ n, β n <> 0) -> P \/ ~P).
Proof.
destruct (internal_truth (P \/ ~P)) as [π [H1π H2π]].
exists π; split. apply (nn_imply_nn (P \/ ~P)). auto. apply nnLEM.
intros [n Hn]. apply (H1π n); auto.
Qed.

(* Now Markov's Principle implies LPO. *)
Theorem markov_lpo :
  MarkovsPrinciple -> LPO.
Proof.
unfold MarkovsPrinciple; intros MP β.
destruct (brouwers_sequence (∃ n, β n <> 0)) as [γ [H1γ H2γ]].
assert(MPH: ~∀ n, γ n = 0). { intros H. apply H1γ; intros [n Hn]; auto. }
apply MP in MPH. apply H2γ in MPH as [H1|H2]. left; auto.
right; intros n. destruct (eq_dec (β n) 0); auto.
exfalso; apply H2. exists n; auto.
Qed.

(* Hence we can contradict Markov's Principle under BCP. *)
Corollary not_markov : ~MarkovsPrinciple.
Proof. intros H; apply not_lpo. apply markov_lpo; auto. Qed.

End BrouwerAndNegation.
