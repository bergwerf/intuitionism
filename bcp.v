(* Brouwer's Continuity Principle (BCP) and related notions. *)

From intuitionism Require Import lib set seq spr func classic choice.

(* Brouwers Continuity Principle *)
Axiom BCP : ∀(R : seq -> nat -> Prop),
  (∀α, ∃n, R α n) ->
  (∀α, ∃m n, ∀β, eqn m α β -> R β n).

(* BCP generalizes to spreads *)
Theorem BCPext (X : spread) (R : seq -> nat -> Prop) :
  (∀α, α ∈ X -> ∃n, R α n) ->
  (∀α, α ∈ X -> ∃m n, ∀β, β ∈ X -> eqn m α β -> R β n).
Proof.
intros Rall.
pose(rσ := (Retract.r X)).
pose(T := (λ α n, R (rσ α) n)).
assert(HT: ∀α, ∃n, T α n).
- intros; pose(Hα := Retract.r_image X α); apply Rall in Hα.
  destruct Hα as [n Hn]; exists n; auto.
- intros; destruct (BCP T HT α) as [m [n P]]. exists m, n; intros.
  apply P in H1; unfold T, rσ in H1; rewrite Retract.r_id in H1; auto.
Qed.

(* Continuity of functions from sequences to numbers. *)
Theorem BCPf (f : seq -> nat) α :
  ∃n, ∀β, eqn n α β -> f α = f β.
Proof.
assert(Hf: ∀γ, ∃n, f γ = n) by (intros; now exists (f γ)).
destruct (BCP _ Hf α) as [m [n H]]. exists m; intros.
rewrite H. symmetry; now rewrite H. apply eqn_refl.
Qed.

(* Continuity of functions from spreads to numbers. *)
Theorem BCPfext {X : spread} (f : dom X -> nat) α :
  α ∈ X -> ∃n, ∀β, β ∈ X -> eqn n α β -> f α = f β.
Proof.
assert(Hf: ∀γ, γ ∈ X -> ∃n, f γ = n) by (intros; now exists (f γ)).
intros Hα. destruct (BCPext X _ Hf α) as [m [n H]]; auto. exists m; intros.
rewrite H; auto. symmetry; now rewrite H. apply eqn_refl.
Qed.

(* Pointwise continuity of functions from sequences to sequences. *)
Theorem BCPf2_point (f : seq -> seq) α i :
  ∃n, ∀β, eqn n α β -> f α i = f β i.
Proof.
assert(Hf: ∀γ, ∃n, f γ i = n) by (intros; now exists (f γ i)).
destruct (BCP _ Hf α) as [m [n H]]. exists m; intros.
rewrite H. symmetry; now rewrite H. apply eqn_refl.
Qed.

(* Continuity of functions from sequences to sequences. *)
Theorem BCPf2 (f : seq -> seq) α k :
  ∃n, ∀β, eqn n α β -> eqn k (f α) (f β).
Proof.
assert(H: ∀i, i < k -> ∃n, ∀β, eqn n α β -> f α i = f β i).
{ intros. destruct (BCPf2_point f α i) as [n Hn].
  exists n; intros. now apply Hn. }
apply bounded_choice_nat in H as [N HN]. exists (upb (map N (iota 0 k))).
intros β Hβ i Hi. apply HN; auto. intros j Hj; apply Hβ.
apply upb_le_map_iota with (i:=i); auto. lia.
Qed.

(* Some initial contradictions with classical logic. *)
Section ClassicContradictions.

(* LPO is provably incorrect. *)
Theorem not_lpo :
  ~LPO.
Proof.
intros LPO.
assert(P: ∀α : seq, ∃i,
  (i = 0 /\ ∃n, α n <> 0) \/
  (i > 0 /\ ∀n, α n = 0)).
{ intros; destruct (LPO α). exists 0; left; auto. exists 1; right; auto. }
destruct (BCP _ P (0^ω)) as [m [n H]]. destruct (eq_dec n 0) as [n0|n1].
- assert(Hα : eqn m (0^ω) (0^ω)). apply eqn_refl.
  apply H in Hα as [[_ [i E]]|[n1 _]]; try lia.
  apply E; auto.
- pose(β := pre m (0^ω) (1^ω)).
  assert(Hβ: eqn m (0^ω) β). apply eqn_pre_n.
  apply H in Hβ as [[n0 _]|[_ A]]; try lia.
  assert(Hβ1: β (m + 1) <> 0). unfold β; now rewrite pre_r.
  auto.
Qed.

(*
It is reckless to assume that ω-infinity implies Dedekind-infinity.
To see this, suppose we have a sequence (R n) of reckless statements. We will
construct an ω-infinite subset of the Baire space using R such that
Dedekind-infinity implies a reckless statement based on R.
*)
Theorem ω_infinite_dedekind_reckless (R : nat -> Prop) :
  (∀V, Nat ≼ V -> Dedekind_infinite V) -> (∃n, R n) \/ (∃n m, R n -> R m).
Proof.
pose(inV α := del 1 α = 0^ω \/ R (α 0)).
pose(V := Baire inV). assert(Hω: Nat ≼ V).
{ exists (λ n, pre 1 (n^ω) (0^ω)); split.
  - intros n _; simpl; left. extensionality i. now rewrite del_access, pre_r.
  - intros m n _ _ Hmn. exists 0. rewrite <-(add_0_l 1), ?pre_l. easy. }
intros H; apply H in Hω as [γ [f [Hγ [f_wd [f_inj f_nsurj]]]]]; clear H.
assert(Hfγ: f γ ∈ V) by (now apply f_wd). revert Hγ Hfγ.
simpl; unfold inV. remember (γ 0) as i; remember (f γ 0) as j.
intros [Hγ|Hγ] [Hfγ|Hfγ].
- (* Both are of the form n0^ω. *)
  right. exists i, j. intros Ri.
  assert(Hbcp: ∀α, ∃n, (n = 0 /\ f α 0 = j) \/ (n <> 0) /\ (f α 0 <> j)).
  { intros. destruct (eq_dec (f α 0) j).
    exists 0; now left. exists 1; now right. }
  apply BCP with (α:=γ) in Hbcp as [m [n Hmn]]. destruct n. (* n must be 0 *)
  + pose(β := pre m γ (pre 1 (i^ω) (1^ω))).
    assert(Hβ: β ∈ V).
    { simpl; right; unfold β. destruct m.
      now rewrite pre0, pre_l0. now rewrite pre_l0, <-Heqi. }
    assert(Hfβ: f β ∈ V) by (now apply f_wd).
    assert(Hγβ: f γ # f β).
    { apply f_inj; auto. now left. exists (m + 1).
      unfold β. rewrite pre_r, add_comm; intros C.
      eapply equal_f in Hγ; unfold del in Hγ. now rewrite Hγ in C. }
    destruct (Hmn β); try easy.
    apply eqn_pre_n. destruct H as [_ Hj].
    destruct Hfβ. 2: now rewrite Hj in H.
    (* Contradiction: f β now coincides with f γ. *)
    exfalso. eapply apart_spec. 2: apply Hγβ.
    extensionality k. destruct k. now rewrite Hj.
    eapply equal_f in Hfγ; eapply equal_f in H. unfold del in *.
    now rewrite <-add_1_l, Hfγ, H.
  + exfalso. destruct (Hmn γ). apply eqn_refl.
    easy. now rewrite Heqj in H.
- left; now exists j.
- left; now exists i.
- left; now exists j.
Qed.

End ClassicContradictions.

(* BCPf with a sigma type for the prefix length is inconsistent. *)
(* From: doc/bcp_sig.pdf *)
Section BCPsig.

(*
This is much stronger than BCP since it also implies a choice function. We will
see it is also stronger than AC_10 since the choice function is not continuous.
*)
Definition BCPfsig := ∀(f : seq -> nat) α,
  {n | ∀β, eqn n α β -> f α = f β}.

Theorem not_BCPfsig :
  BCPfsig -> 0 = 1.
Proof.
intros BCPfsig.
(* M : seq -> nat, gives us the prefix length of any f to compute its image. *)
pose(M f := proj1_sig (BCPfsig f (0^ω))).
assert(L1: ∀f β, eqn (M f) (0^ω) β -> f (0^ω) = f β).
{ intros. apply (proj2_sig (BCPfsig f (0^ω))). auto. }
(* We now construct a function f that is not continuous. *)
pose(m := M (λ _, 0)).
pose(f β := M (λ α, β (α m))).
assert(f0: f (0^ω) = m) by easy.
assert(L2a: ∀β, eqn (M f) (0^ω) β -> f β = m).
{ intros. rewrite <-f0. symmetry; apply L1; auto. }
assert(L2b: ∀β α, eqn (f β) (0^ω) α -> β 0 = β (α m)).
{ intros. unfold f in H. now apply L1 in H. }
pose(β := pre (M f + 1) (0^ω) (1^ω)).
assert(Hβ: ∀α, eqn m (0^ω) α -> β 0 = β (α m)).
{ intros. apply L2b. rewrite L2a; auto. apply eqn_pre. }
pose(α := pre m (0^ω) ((M f + 1)^ω)).
assert(H1α: α m = M f + 1). { unfold α. rewrite pre_r0; auto. }
assert(H2α: β 0 = β (α m)). { apply Hβ. apply eqn_pre_n. }
(* We are ready to show 0 = 1. *)
replace 1 with (β (M f + 1)). rewrite <-H1α, <-H2α. unfold β.
replace (M f + 1) with (0 + S (M f)) by lia. rewrite pre_l. auto.
unfold β. replace (M f + 1) with ((M f + 1) + 0) at 2 by lia.
rewrite pre_r; auto.
Qed.

End BCPsig.
