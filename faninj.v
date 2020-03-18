(* Injective functions between finitary spreads. *)

From intuitionism Require Import lib set seq spr fan func bcp bar tau.

(*
In this file we explore when an injective function between two fans is
intuitionistically possible. This relation is denoted with ≼ and is introduced
in func.v.
*)

(* First we consider τ fans. *)
Section Tau.

(* Injection between similar bounds. *)
Theorem τ_preceq_translate k l m :
  τ k m ≼ τ l m.
Proof.
exists (λ α, λ i,  α i - k + l); split.
- intros α H. apply member_τP; intros i.
  tau_member H i; lia.
- intros α β Hα Hβ [i Hi]. exists i.
  tau_member Hα i; tau_member Hβ i; lia.
Qed.

(* Injection to a larger bound. *)
Theorem τ_preceq_id k l :
  k <= l -> τ 0 k ≼ τ 0 l.
Proof.
intros LE. exists (λ α, α); split.
- intros α H. apply member_τP; intros i. tau_member H i; lia.
- intros α β _ _ [i Hi]. now exists i.
Qed.

(* τ_prec inner induction step. *)
Lemma τ_prec_step k f z i :
  well_defined (τ 0 (S k + 1)) (τ 0 (S k)) f ->
  injective (τ 0 (S k + 1)) (τ 0 (S k)) f ->
  z <= 1 -> f (z^ω) i >= 1 -> ∃g,
    well_defined (τ 0 (k + 1)) (τ 0 k) g /\
    injective (τ 0 (k + 1)) (τ 0 k) g.
Proof.
intros f_wd f_inj z_le_1 fz_ge_1.
(* Find prefix length of z^ω such that the image is the same up to i. *)
destruct (BCPf_11 f (z^ω) (S i)) as [j Hj].
(* Prepend this prefix to α to create a new injective function. *)
pose(add1 (α : seq) n := S (α n)).
pose(sub1 (α : seq) n := pred (α n)).
pose(g α := sub1 (del i (f (pre j (z^ω) (add1 α))))).
assert(Hg: ∀α, α ∈ τ 0 (k + 1) -> pre j (z^ω) (add1 α) ∈ τ 0 (S k + 1)).
{ intros. apply τ_pre_cseq. unfold add1; lia.
  apply member_τP; intros n; unfold add1. tau_member H n; lia. }
exists g; split.
- (* Well defined *)
  intros α Hα. unfold g. remember (pre j (z^ω) (add1 α)) as γ.
  assert(Hγ: γ ∈ τ 0 (S k + 1)) by (rewrite Heqγ; now apply Hg).
  apply f_wd in Hγ. apply member_τP; intros n. unfold sub1, del.
  tau_member Hγ (i + n). rewrite add_succ_r; lia.
- (* Injective *)
  intros α β Hα Hβ [n Hn].
  assert(Hfα := Hg α Hα). assert(Hfβ := Hg β Hβ).
  assert(Hαβ: seq_apart (pre j (z^ω) (add1 α)) (pre j (z^ω) (add1 β))).
  { exists (j + n); rewrite ?pre_r. unfold add1; lia. }
  clear Hn n; apply f_inj in Hαβ as [n Hn]; auto.
  (* Apartness is after the shared prefix. *)
  eapply eqn_le_apart with (m:=S i) in Hn as Hi.
  2: apply eqn_trans with (β:=f (z^ω)). 2: apply eqn_sym.
  2,3: apply Hj, eqn_pre_n.
  (* Both images are >=1 at n. *)
  apply f_wd in Hfα; apply f_wd in Hfβ.
  apply τ_mono_lwb with (i:=i)(j:=n)(n:=1) in Hfα as [Hfα _].
  apply τ_mono_lwb with (i:=i)(j:=n)(n:=1) in Hfβ as [Hfβ _].
  exists (n - i). unfold g, del, sub1. replace (i + (n - i)) with n by lia.
  all: try lia. all: rewrite <-Hj. all: try lia. all: apply eqn_pre_n.
Qed.

(* Injection to a smaller bound is impossible. *)
Theorem τ_prec k l :
  k < l -> τ 0 k ≺ τ 0 l.
Proof.
intros LT. remember (l - S k) as d; assert(l = k + S d) by lia.
rewrite H; clear LT Heqd H l.
induction d; intros [f [f_wd f_inj]].
- (* Exhaust prefixes. *)
  induction k.
  + (* 0^ω # 1^ω, but f can only map to 0^ω. *)
    rewrite add_0_l in *.
    assert(H0: 0^ω ∈ τ 0 1) by (apply τ_cseq; lia).
    assert(H1: 1^ω ∈ τ 0 1) by (apply τ_cseq; lia).
    assert(H01: ∃n, 0^ω n <> 1^ω n) by (now exists 0).
    apply f_inj in H01 as [n H]; auto. apply H.
    apply f_wd in H0; apply f_wd in H1.
    tau_member H0 n; tau_member H1 n. lia.
  + (* If k is increased we can construct a failing injection. *)
    assert(Hk: ∃i, 0^ω i <> 1^ω i) by (exists 0; now unfold cseq).
    apply f_inj in Hk as [i H]. 2,3: apply τ_cseq; lia.
    (* At least one of these sequences is >=1 at i. *)
    assert(C: f (0^ω) i >= 1 \/ f (1^ω) i >= 1) by lia; destruct C as [C|C].
    * edestruct τ_prec_step with (f:=f) as [g [g_wd g_inj]].
      4: apply C. all: auto. now apply IHk with (f:=g).
    * edestruct τ_prec_step with (f:=f) as [g [g_wd g_inj]].
      4: apply C. all: auto. now apply IHk with (f:=g).
- (* Increasing k does not alter the base case proof. *)
  assert(R: k + S (S d) = (k + S d) + 1) by lia.
  apply IHd. exists f; split.
  + intros α H. apply f_wd. rewrite R; now apply τ_member_weaken.
  + intros α β Hα Hβ Hαβ. apply f_inj; auto;
    rewrite R; now apply τ_member_weaken.
Qed.

End Tau.

(*
Next we consider arbitrary fans. Note that it is possible to construct fans with
an undeterminable finite number of branching points (i.e. split at k99).
*)
Section Generalization.

Inductive degree := Degree (n : nat) | ωDegree.

Definition dle a b :=
  match a, b with
  | Degree n, Degree m => n <= m
  | ωDegree, Degree _ => False
  | _, ωDegree => True
  end.

Notation "a <=° b" := (dle a b) (at level 50).
Notation "a >° b" := (~dle a b) (at level 50).

(*
We define a function Δ from prefixes of the fan to ℕ ∪ {ω}.
If there is a finite number of members that start with s, then Δ s |-> 0.
If there is an infinite number of branching points along some path starting at s
such that at each point there is at least one sub-branch (not on the path) with
Δ = n, then Δ s |-> n + 1. If branching can continue infinitely, then Δ = ω.
*)
Section DegreeMapping.

Variable F : fan.
Variable Δ : fseq -> degree.

(* m and n are two distinct continuations of s. *)
Definition F_node m n s := m <> n /\ σ F (m :: s) = true /\ σ F (n :: s) = true.

(* N is a branching bound in F under s. *)
Definition F_bound s N := ∀t m n, length s >= N ->
  σ F (m :: t ++ s) = true /\ σ F (n :: t ++ s) = true -> n = m.

(* Δ is a good branching degree function. *)
Definition Δ_good := ∀s,
  match Δ s with
  (* Finite branching *)
  | Degree 0 =>
    (* There exists an upper bound after which no branching occurs. *)
    ∃N, F_bound s N
  (* Infinite branching along some path *)
  | Degree (S _) =>
    (* We can find a next node. *)
    (∃t m n, F_node m n (t ++ s)) /\
    (* All continuations have a similar or lower degree. *)
    (∀n, σ F (n :: s) = true -> Δ (n :: s) <=° Δ s) /\
    (* At least one continuation has the same degree. *)
    (∃n, σ F (n :: s) = true /\ Δ (n :: s) = Δ s)
  (* Infinite branching into infinite branching *)
  | ωDegree =>
    (* We can find a next node with two ωDegree continuations. *)
    ∃t m n, F_node m n (t ++ s) /\
      Δ (m :: t ++ s) = ωDegree /\
      Δ (n :: t ++ s) = ωDegree
  end. 

End DegreeMapping.

(* Δ is an optimal branching degree function. *)
Definition Δ_optimal F Δ := Δ_good F Δ /\ ∀δ, Δ_good F δ -> ∀s, Δ s <=° δ s.

(* If an optimal branching degree can be computed, it indicates ≼. *)
Theorem dle_preceq F E ΔF ΔE :
  Δ_optimal F ΔF -> Δ_optimal E ΔE -> ΔF [] <=° ΔE [] -> F ≼ E.
Proof.
(*
This proof appears like it may be very difficult. The idea is to define an
injective function that given an α ∈ F traces out a path in G with a matching
degree for all prefixes. When dealing with a bottom degree (Degree 0) this
function has to explore all existing nodes to define an injective ordering.
*)
Abort.

End Generalization.
