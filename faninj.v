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
Theorem τ_preceq k l :
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

(* Summary; the relation ≼ is decidable for τ. *)
Corollary τ_preceq_dec k l :
  τ 0 k ≼ τ 0 l \/ τ 0 l ≺ τ 0 k.
Proof.
destruct (le_gt_dec k l).
left; now apply τ_preceq.
right; now apply τ_prec.
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
  let deg := Δ s in
  match deg with
  (* Finite branching *)
  | Degree 0 =>
    (* There exists an upper bound after which no branching occurs. *)
    ∃N, F_bound s N
  (* Infinite branching along some path *)
  | Degree (S deg') =>
    (* We can find a next node where one branch has a degree one step lower. *)
    (∃t m n, F_node m n (t ++ s) /\ Δ (n :: t ++ s) = Degree deg') /\
    (* This degree forms an upper bound. *)
    (∀n, σ F (n :: s) = true -> Δ (n :: s) <=° deg) /\
    (* At least one continuation has the same degree. *)
    (∃n, σ F (n :: s) = true /\ Δ (n :: s) = deg)
  (* Infinite branching into infinite branching *)
  | ωDegree =>
    (* We can find a next node with two ωDegree continuations. *)
    ∃t m n, F_node m n (t ++ s) /\
      Δ (m :: t ++ s) = ωDegree /\
      Δ (n :: t ++ s) = ωDegree
  end. 

End DegreeMapping.

(* If the branching degree can be computed we can determine ≼. *)
Theorem dle_preceq F E ΔF ΔE :
  Δ_good F ΔF -> Δ_good E ΔE -> ΔF [] <=° ΔE [] -> F ≼ E.
Proof.
(*
It seems this may be hard to prove formally in Coq (it is easier on paper of
course). The idea is to define an injective function that given an α ∈ F traces
out a path in G with a matching degree for all prefixes. When dealing with a
bottom degree (Degree 0) this function has to explore all existing nodes to
define an ordering.
*)
Abort.

End Generalization.

(*
With a degree function we tried to generalize the notion of how long we can
continue branching before getting stuck, as we saw with τ. However writing down
formal proofs about this notion is not so easy. A simpler and perhaps more
elegant approach is to consider all fans whose σ function is a DFA.
*)
Section Automatons.

(* A Discrete Finite Automaton *)
Record dfa := DFA {
  dfa_size : nat;
  dfa_init : nat;
  dfa_next : nat -> nat -> nat;
}.

(* Process input s with DFA a. *)
Fixpoint dfa_run (a : dfa) (state : nat) s :=
  match s with
  | [] => state
  | n :: t => dfa_run a (dfa_next a state n) t
  end.

(* All state within the size bound are accept states. *)
Definition dfa_accept a n := n <? dfa_size a.

(* The fan F is described by DFA a. *)
Definition dfa_fan (F : fan) a :=
  ∀s, σ F s = dfa_accept a (dfa_run a (dfa_init a) (rev s)).

Lemma dfa_run_app a init s1 s2 :
  dfa_run a init (s1 ++ s2) = dfa_run a (dfa_run a init s1) s2.
Proof. revert init; induction s1; simpl; auto. Qed.

(* DFA's for Bin and τ. *)
Section ExampleDFAFans.

Definition PointSpace_dfa k := DFA 1 0 (λ s n, n - k + s).

Theorem PointSpace_dfa_fan k :
  dfa_fan (PointSpace k) (PointSpace_dfa k).
Proof.
intros s; simpl. induction s; auto.
simpl; rewrite IHs. rewrite dfa_run_app; simpl. destruct (a <=? k) eqn:E.
- rewrite andb_true_r. now replace (a - k) with 0 by bool_lia.
- rewrite andb_false_r. destruct (a - k) eqn:F; auto. bool_lia.
Qed.

Corollary Bin_dfa_fan : ∃a, dfa_fan Bin a.
Proof. exists (PointSpace_dfa 1). apply PointSpace_dfa_fan. Qed.

Definition τ_dfa_next k l state n :=
  if l <? state then state
  else if (k <=? n) && (n <=? k + l) && (state <=? n - k)
  then n - k else S l.

Definition τ_dfa k l := DFA (S l) 0 (τ_dfa_next k l).

Theorem τ_dfa_fan k l :
  dfa_fan (τ k l) (τ_dfa k l).
Proof.
intros s; simpl. induction s as [|n]; auto.
simpl; rewrite IHs, dfa_run_app, <-andb_assoc.
unfold dfa_accept; simpl; unfold τ_dfa_next; simpl.
remember (dfa_run (τ_dfa k l) 0 (rev s)) as state eqn:Hstate.
destruct ((k <=? n) && (n <=? k + l)) eqn:E; simpl.
- rewrite andb_true_r. destruct s as [|m].
  + simpl in Hstate; subst; simpl. bool_lia.
  + destruct (l <? state) eqn:F.
    replace (state <? S l) with false by bool_lia. now rewrite andb_false_r.
    replace (state <? S l) with true by bool_lia. rewrite andb_true_r.
    revert Hstate. simpl; rewrite dfa_run_app; simpl. unfold τ_dfa_next.
    remember (dfa_run (τ_dfa k l) 0 (rev s)) as state' eqn:Hstate'.
    destruct (l <? state') eqn:G; intros. subst; now rewrite F in G.
    destruct ((k <=? m) && (m <=? k + l) && (state' <=? m - k)) eqn:H;
    subst state. destruct (m <=? n) eqn:K.
    * replace (m - k <=? n - k) with true by bool_lia. bool_lia.
    * replace (m - k <=? n - k) with false by bool_lia. bool_lia.
    * exfalso; bool_lia.
- rewrite andb_false_r. destruct (l <? state) eqn:F; bool_lia.
Qed.

End ExampleDFAFans.

(*
We compare two DFAs by checking how many phases they go through.
For simplicity we recycle the degree type for to denote this.
*)

(* For DFA fans the relation ≼ is decidable. *)
Theorem dfa_fan_preceq_dec F1 F2 :
  (∃a1, dfa_fan F1 a1) -> (∃a2, dfa_fan F2 a2) -> F1 ≼ F2 \/ F2 ≺ F1.
Proof.
intros [a1 H1] [a2 H2].
Admitted.

End Automatons.
