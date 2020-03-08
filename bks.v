(* The Brouwer-Kripke scheme *)

From intuitionism Require Import lib set seq classic bcp choice.

(*
In response to a letter from C. Griss about removing negation altogether,
Brouwer tries to agrue that without negation some interesting properties of
mathematics can not be stated ('Essentieel-negatieve eigenschappen').
*)
Module BrouwerKripkeScheme.

(*
To Brouwer the meaning of truth is relative; there is no absolute truth which
exists regardless of the thoughts of the individual. Instead there is only truth
within the reference of the 'creating subject'. We could consider humanity as a
whole as the creating subject. In this axioms π symbolizes a proof conquest of
the creating subject:
-> := Brouwer insists to only accept P as true if he ever finds a proof.
<- := Brouwer trusts his own proof.
*)
Axiom BKS : ∀P, ∃π, P <-> ∃n : nat, π n <> 0.

(* AC_11 is false under BKS. *)
Corollary not_AC_11 : ~AC_11.
Proof. intros H. apply AC_11_controversy in H. apply H; intros. apply BKS. Qed.

(* We can use BKS to create a sequence with an 'essential negative property'. *)
Theorem brouwers_sequence P : ∃α : seq,
  ~~(∃n, α n <> 0) /\ ((∃n, α n <> 0) -> P \/ ~P).
Proof.
destruct (BKS (P \/ ~P)) as [π [H1π H2π]].
exists π; split; auto. apply (nn_imply_nn (P \/ ~P)). auto. apply nnLEM.
Qed.

(* Using this sequence Markov's Principle implies LPO. *)
Theorem markov_lpo :
  MarkovsPrinciple -> LPO.
Proof.
unfold MarkovsPrinciple; intros MP β.
destruct (brouwers_sequence (∃n, β n <> 0)) as [γ [H1γ H2γ]].
assert(MPH: ~∀n, γ n = 0). { intros H. apply H1γ; intros [n Hn]; auto. }
apply MP in MPH. apply H2γ in MPH as [H1|H2]. left; auto.
right; intros n. destruct (eq_dec (β n) 0); auto.
exfalso; apply H2. exists n; auto.
Qed.

(* Hence Markov's Principle is false under BCP and BKS. *)
Corollary not_markov : ~MarkovsPrinciple.
Proof. intros H; apply not_lpo. apply markov_lpo; auto. Qed.

End BrouwerKripkeScheme.
