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
Variable T_dec : ∀ e n z, {T e n z} + {~T e n z}.

(* Retrieve the output of the computation tree encoded by z. *)
Variable U : nat -> bool.

(* Least valid computation tree *)
Definition μT e n z := (∀ w, w < z -> ~T e n w) /\ T e n z.

(* Define the output of program e as a predicate. *)
Definition accept e n := ∃ z, μT e n z /\ U z = true.
Definition reject e n := ∃ z, μT e n z /\ U z = false.

(* A program is a decider if it is decidable on all inputs. *)
Definition decider e := ∀ n, accept e n \/ reject e n.

(* A program recognizes the set P if this holds. *)
Definition recognizer e P := ∀ n, P n <-> accept e n.

(* P is solvable if there exists a decidable recognizer. *)
Definition solvable (P : nat -> Prop) := ∃ e, decider e /\ recognizer e P.

(* Some useful lemmas *)
Section Lemmas.

Variable e : nat.
Variable n : nat.

Lemma T_μT :
  (∃ z, T e n z) -> ∃ z, μT e n z.
Proof.
intros. destruct (epsilon_smallest _ (T_dec e n) H) as [z [H1z H2z]].
exists z; now split.
Qed.

Lemma μT_nlt z1 z2 : μT e n z1 -> μT e n z2 -> ~(z1 < z2).
Proof. intros H1 H2 H. eapply H2. apply H. apply H1. Qed.

Lemma μT_eq z1 z2 :
  μT e n z1 -> μT e n z2 -> z1 = z2.
Proof.
intros H1 H2. apply eq_dne; intros H.
apply not_eq in H as [H|H]; eapply μT_nlt.
apply H1. apply H2. auto. apply H2. apply H1. auto.
Qed.

Lemma reject_not_accept :
  reject e n -> ~accept e n.
Proof.
intros [az [μaz Uaz]] [rz [μrz Urz]].
rewrite (μT_eq _ _ μaz μrz) in Uaz.
rewrite Uaz in Urz; discriminate.
Qed.

Corollary accept_not_reject : accept e n -> ~reject e n.
Proof. intros A R; apply reject_not_accept in R; auto. Qed.

Variable dec : decider e.

Lemma not_reject_accept : ~reject e n -> accept e n.
Proof. intros; destruct (dec n); auto. now exfalso. Qed.

Lemma not_accept_reject : ~accept e n -> reject e n.
Proof. intros; destruct (dec n); auto. now exfalso. Qed.

End Lemmas.

(* A note about the halting problem. *)
Section HaltingProblem.

(* The Halting problem for program e with input e *)
Definition HALT e := ∃ z, T e e z.

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
Variable HALTdiag_solvable : ∀ e,
  decider e -> recognizer e HALT -> solvable (HALTdiag e).

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

(* Set corresponding to a binary mapping. *)
Definition bin_set (α : seq) := λ n, α n = 1.

(*
We are considering the Turing decidable subspace of the Cantor space. At first
it may seem that any finite prefix in Bin is also in Bin_solv. However we cannot
claim both sets are equal due to the Halting problem.
*)
Definition is_solvable α := α isin Bin /\ solvable (bin_set α).
Definition Bin_solv := Baire is_solvable.

(*
We will construct a bar for which any finite bar fails. If we accept Bin_solv as
a fan, then this contradicts the Fan Theorem. If it is possible to enumerate
all solvable sets using a Turing program, then Bin_solv would indeed be a fan.
However as we learned from the Halting problem, it is not possible for a Turing
program to exactly enumerate all possible decider programs.
*)

(* Compare the prefix of sequence α in Bin to Turing program e. *)
Section CheckPrefix.

Variable α : seq.
Variable e : nat.
Variable bin : α isin Bin.
Variable dec : decider e.
Variable rec : recognizer e (bin_set α).

(* s is a prefix of the Turing program e. Note that i must count down. *)
Fixpoint check_prefix s i :=
  match s with
  | [] => True
  | n :: s' => check_prefix s' (pred i) /\
    match n with
    | 0 => reject e i
    | 1 => accept e i
    | _ => False
    end
  end.

Lemma αn_01_dec n :
  match α n with
  | 0 => reject e n
  | 1 => accept e n
  | _ => False
  end.
Proof.
apply isin_pointspace with (n:=n) in bin.
destruct (α n) eqn:E; bool_to_Prop.
- apply not_accept_reject; auto; intros H. apply rec in H.
  unfold bin_set in H; now rewrite E in H.
- replace n0 with 0 by lia. apply rec. unfold bin_set. lia.
Qed.

Corollary check_prefix_pred n : check_prefix ⟨α;n⟩ (pred n).
Proof. induction n; simpl; split; auto. apply αn_01_dec. Qed.

Lemma check_prefix_unique_length s t i :
  check_prefix s i -> check_prefix t i -> length s = length t -> s = t.
Proof.
revert s i; induction t; simpl; intros. now apply length_zero_iff_nil.
destruct H0. destruct s; simpl in *. easy. destruct H. apply cons_split.
- destruct n, a; try destruct n; try destruct a; auto; try easy.
  all: exfalso; now apply reject_not_accept with (e:=e)(n:=i).
- eapply IHt. apply H. apply H0. now apply eq_add_S.
Qed.

End CheckPrefix.

(* We use these prefixes to define a bar. The bar name is somewhat random. *)
Definition good : bar := λ s,
  match s with
  | [] => False
  | _ :: t => let e := length t in check_prefix e s e
  end.

(* Each sequence in good has a unique length. *)
Lemma good_unique_length s t :
  good s -> good t -> length s = length t -> s = t.
Proof.
intros H1 H2 HL. destruct s, t; try easy. simpl in *.
apply eq_add_S in HL as HL2. rewrite <-HL2 in H2.
eapply check_prefix_unique_length; auto; simpl. apply H1. apply H2.
Qed.

(* Diagonalization of a finite bar. *)
Fixpoint good_diag (b : fbar) n :=
  match b with 
  | [] => 0
  | s :: t =>
    if length s =? n + 1
    then 1 - hd 0 s
    else good_diag t n
  end.

(* Given a finite bar, good_diag is fully decidable. *)
Variable good_diag_solvable : ∀ b, solvable (bin_set (good_diag b)).

(* Hence, good_diag is in Bin_solv. *)
Lemma good_diag_Bin_solv b :
  good_diag b isin Bin_solv.
Proof.
split. 2: apply good_diag_solvable.
intros n; induction n; simpl; repeat bool_to_Prop; auto. clear IHn.
induction b; simpl. lia. destruct (length a =? n + 1); auto.
destruct (hd 0 a); lia.
Qed.

(* For sequence (n :: s) in fbar b, good_diag b <> (n :: s) at (length s). *)
Lemma good_diag_neq b n s :
  Forall good b -> In (n :: s) b -> good_diag b (length s) <> n.
Proof.
induction b; simpl; auto. intros Hab [H|H].
- rewrite add_1_r. subst; simpl. rewrite eqb_refl. destruct n; lia.
- inversion_clear Hab. destruct (length a =? length s + 1) eqn:E; bool_to_Prop.
  + (* Again a = n :: s by the uniqueness of length in diag_bar. *)
    eapply Forall_forall in H1. 2: apply H.
    eapply good_unique_length in H1. 2: apply H0. subst.
    simpl; destruct n; lia. now rewrite E, add_1_r.
  + (* Use induction hypothesis. *)
    now apply IHb.
Qed.

(* good bars any solvable sequence in Bin_solv. *)
Theorem barred_Bin_solv_good :
  barred Bin_solv good.
Proof.
intros α [Cα [e [e_dec α_rec]]].
exists (S e). simpl; rewrite ?get_length; split.
now apply check_prefix_pred. now apply αn_01_dec.
Qed.

(* Any finite subset of good is insufficient. *)
Theorem no_good_fbar (b : fbar) :
  Forall good b -> not_barred_fbar Bin_solv b.
Proof.
intros H. exists (good_diag b); split. apply good_diag_Bin_solv.
apply Forall_forall; intros s Hs. destruct s.
- eapply Forall_forall in H. 2: apply Hs. easy.
- simpl. intros Heq; injection Heq; intros.
  eapply good_diag_neq. apply H. apply Hs. easy.
Qed.

End Kleene.
