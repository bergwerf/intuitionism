(* Kleene's alternative to the Fan Theorem *)

From intuitionism Require Import lib set seq spr fan func bar.

(*
If we assume every sequence α is given by a Turing program, then the Fan Theorem
fails. A proof for this was given by Kleene in 1954. Here I tried to replicate
his construction of a counter example (a bar which fails to be finite). For
simplicity I consider only deciders (binary sequences).
*)
Section Kleene.

(* Kleene's T-predicate: for program e and input n, z is a valid computation. *)
Variable T : nat -> nat -> nat -> Prop.

(* The T-predicate is decidable. *)
Variable T_dec : forall e n z, {T e n z} + {~T e n z}.

(* Retrieve the output of the computation tree encoded by z. *)
Variable U : nat -> bool.

(* Least valid computation tree *)
Definition μT e n z := (forall w, w < z -> ~T e n w) /\ T e n z.

(* Define the output of program e as a predicate. *)
Definition accept e n := exists z, μT e n z /\ U z = true.
Definition reject e n := exists z, μT e n z /\ U z = false.

(* A program is a decider if it is decidable on all inputs. *)
Definition decider e := forall n, accept e n \/ reject e n.

(* A program recognizes the set P if this holds. *)
Definition recognizer e P := forall n, P n <-> accept e n.

(* P is solvable if there exists a decidable recognizer. *)
Definition solvable (P : nat -> Prop) := exists e, decider e /\ recognizer e P.

(* A note about the halting problem. *)
Section HaltingProblem.

(* The Halting problem for program e with input e *)
Definition HALT e := exists z, T e e z.

(*
To prove the Halting problem is unsolvable we use diagonalization. Given the
index of the halting decider e and input n: if the n-th program halts on n, then
negate its output. Else reject.
*)
Definition HALTdiag e n := accept e n /\ reject n n.

(*
In general (for any e), HALTdiag has a Turing program (a recognizer).
If e is a decider for HALT, then HALTdiag is also solvable.
*)
Variable HALTdiag_solvable : forall e,
  decider e -> recognizer e HALT -> solvable (HALTdiag e).

Lemma μT_nlt e n z1 z2 : μT e n z1 -> μT e n z2 -> ~(z1 < z2).
Proof. intros H1 H2 H. eapply H2. apply H. apply H1. Qed.

Lemma μT_eq e n z1 z2 :
  μT e n z1 -> μT e n z2 -> z1 = z2.
Proof.
intros H1 H2. apply eq_dne; intros H.
apply not_eq in H as [H|H]; eapply μT_nlt.
apply H1. apply H2. auto. apply H2. apply H1. auto.
Qed.

Lemma T_μT e n :
  (exists z, T e n z) -> exists z, μT e n z.
Proof.
intros. destruct (epsilon_smallest _ (T_dec e n) H) as [z [H1z H2z]].
exists z; now split.
Qed.

Lemma reject_not_accept e n :
  reject e n -> ~accept e n.
Proof.
intros [az [μaz Uaz]] [rz [μrz Urz]].
rewrite (μT_eq _ _ _ _ μaz μrz) in Uaz.
rewrite Uaz in Urz; discriminate.
Qed.

(* The Halting problem is unsolvable. *)
Theorem HALT_unsolvable :
  ~solvable HALT.
Proof.
intros [e_halt [halt_dec halt_rec]].
destruct (HALTdiag_solvable e_halt) as [e_diag [diag_dec diag_rec]]; auto.
destruct (halt_dec e_diag) as [halt|halt].
- (* φ e e <-> ~φ e e *)
  destruct (diag_dec e_diag).
  + apply diag_rec in H as R. destruct R as [_ R].
    now apply reject_not_accept with (n:=e_diag)(e:=e_diag).
  + apply reject_not_accept in H as R; auto. apply R.
    apply diag_rec; now unfold HALTdiag.
- (* φ e e always halts. *)
  apply reject_not_accept in halt; auto. apply halt. apply halt_rec.
  destruct (diag_dec e_diag); destruct H as [z [[_ Hz] _]]; now exists z.
Qed.

End HaltingProblem.

(*
We are considering the Turing decidable subspace of the Cantor space. At first
it may seem that any finite prefix in Bin is also in Solv. However we cannot
claim both sets are equal due to the Halting problem.
*)
Definition Solv := Baire (fun α => α isin Bin /\ solvable (fun n => α n = 1)).

(*
We will construct a bar for which any finite bar fails. If we accept Bin_solv as
a fan, then this contradicts the Fan Theorem. If it is possible to enumerate
all solvable sets using a Turing program, then Solv would indeed be a fan.
However as we learned from the Halting problem, it is not possible for a Turing
program to exactly enumerate all possible decider programs.
*)

End Kleene.
