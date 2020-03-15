(* The Tau fan *)

From intuitionism Require Import lib set seq spr fan func classic bcp.

Section TauFan.

(* The Tau fan contains all monotone sequences with a given bounds. *)
Variable lower : nat.
Variable range : nat.

Fixpoint τσ (s : fseq) :=
  match s with
  | [] => true
  | n :: s' =>
    match s' with
    | [] => true
    | m :: s'' => (m <=? n) && τσ s'
    end && (lower <=? n) && (n <=? lower + range)
  end.

Lemma τσ_nil : τσ [] = true.
Proof. auto. Qed.

Lemma τσ_cons s : τσ s = true <-> ∃n, τσ (n :: s) = true.
Proof.
split; intros. destruct s.
- exists lower; simpl; bool_lia.
- exists n; simpl in *; destruct s; repeat bool_to_Prop; try lia; auto.
- destruct H as [n H]; simpl in H; destruct s; auto; repeat bool_to_Prop; auto.
Qed.

Lemma τσ_fan s :
  τσ s = true -> ∃n, ∀m, τσ (m :: s) = true -> m <= n.
Proof.
intros; exists (lower + range); intros.
simpl in H0; destruct s; bool_lia.
Qed.

Definition τ := Fan (Spr τσ τσ_nil τσ_cons) τσ_fan.

(* Alternative membership criteria *)
Definition τP α := ∀n, lower <= α n <= lower + range /\ α n <= α (S n).

Lemma intro_τP α n :
  τP α -> τσ ⟨α;n⟩ = true.
Proof.
intros H; induction n; simpl; auto.
destruct ⟨α;n⟩ eqn:E; repeat bool_to_Prop; auto; try apply H.
destruct n; simpl in *. discriminate. inversion_clear E; apply H.
Qed.

Lemma member_τP α :
  α ∈ τ <-> τP α.
Proof.
split.
- intros H n; eapply unfold_inspr with (m:=S (S n)) in H; simpl in H.
  destruct ⟨α;n⟩ eqn:E; bool_lia.
- intros H m. apply intro_τP; auto.
Qed.

Lemma τ_mono α :
  α ∈ τ -> ∀i j, i <= j -> α i <= α j.
Proof.
intros. apply le_exists_sub in H0 as [d [Hd _]]. rewrite Hd; clear Hd.
revert i; induction d; intros; simpl; try lia.
replace (S (d + i)) with (d + S i) by lia.
transitivity (α (S i)); auto. apply member_τP; auto.
Qed.

Lemma τ_mono_lwb α n i j :
  α ∈ τ -> i <= j -> n <= α i -> n <= α j <= lower + range.
Proof.
intros H1 H2 H3; split. transitivity (α i); auto.
apply τ_mono; auto. apply member_τP; auto.
Qed.

Lemma τ_cseq c : lower <= c <= lower + range -> c^ω ∈ τ.
Proof. intros; apply member_τP; intros i. unfold cseq; lia. Qed.

Lemma τ_pre_cseq n c α :
  lower <= c <= α 0 -> α ∈ τ -> pre n (c^ω) α ∈ τ.
Proof.
intros Hc Hα; apply member_τP; intros i.
apply member_τP in Hα. destruct (lt_dec i n).
- replace n with (i + S (n - i - 1)) by lia. rewrite ?pre_l. split.
  + unfold cseq. assert(H0 := Hα 0). lia.
  + destruct (eq_dec (S i) n); subst.
    replace (i + S _) with (S i) by lia. rewrite pre_r0; unfold cseq; lia.
    replace (i + S _) with (S i + S (n - i - 2)) by lia.
    rewrite pre_l; now unfold cseq.
- replace i with (n + (i - n)) by lia; rewrite pre_r.
  replace (S _) with (n + S (i - n)) by lia; rewrite pre_r. apply Hα.
Qed.

End TauFan.

Definition τ1 := τ 0 0.
Definition τ2 := τ 0 1.
Definition τ3 := τ 0 2.
Definition τ4 := τ 0 3.

(* Tactic for destructing α ∈ τ for the i-th index. *)
Ltac tau_member H i := apply member_τP in H; let P := fresh in assert(P := H i).

(* Weaken bounds on a τ sequence. *)
Lemma τ_member_weaken α m n k : α ∈ τ m n -> α ∈ τ m (n + k).
Proof. intros H; apply member_τP; intros i. tau_member H i; lia. Qed.

(* Some results about τ2. *)
Module Tau2.

(* Any element of τ2 is 0 or 1. *)
Lemma τ2_cases α n :
  α ∈ τ2 -> α n = 0 \/ α n = 1.
Proof.
intros; apply member_τP in H; destruct (α n) eqn:E; auto.
right; rewrite <-E. assert(D: α n <= 1). apply H. lia.
Qed.

(* Any function τ2 -> Nat has a finite image. *)
Theorem τ2_to_Nat_fin_image (f : seq -> nat) :
  ∃image, ∀α, α ∈ τ2 -> In (f α) image.
Proof.
(* Number of leading zeros after which f outputs a result. *)
destruct (BCPf f (0^ω)) as [m Hbcp].
(* Full image is generated by the sequences up to 0^m. *)
exists (map (λ k, f (pre k (0^ω) (1^ω))) (0..m)).
intros α Hα. pose(k := compare m α (0^ω)).
assert(klem: k <= m). { unfold k; apply compare_le. }
assert(Hk: eqn k α (0^ω)). { apply eqn_compare. }
apply in_map_iff. exists k; split.
2: apply in_range; lia. destruct (eq_dec k m).
- rewrite e in *; clear e. rewrite <-Hbcp. apply Hbcp.
  now apply eqn_sym. apply eqn_pre_n.
- apply f_equal. extensionality i. unfold pre, replace, fill.
  destruct (i <? k) eqn:E; bool_to_Prop; symmetry. now apply Hk.
  destruct (τ2_cases α i); auto. exfalso.
  assert(Hlt: k < m). lia. assert(Heqk: k = compare m α (0^ω)). auto.
  apply compare_lt in Hlt. rewrite <-Heqk in Hlt.
  apply Hlt. apply (τ_mono _ _ α) in E; auto. unfold cseq; lia.
Qed.

(*
Classical surjection is different from intuitionistic surjection.
See classic.v for a proof that f is surjective under LPO.
*)
Definition f n :=
  match n with
  | 0 => 0^ω
  | S m => pre m (0^ω) (1^ω)
  end.

Lemma f_image n :
  f n ∈ τ2.
Proof.
apply intro_inspr; intros; apply intro_τP. unfold f; destruct n.
- intros n; unfold cseq; lia.
- intros i. split. split; apply pre_prop; intros; unfold cseq; lia.
  unfold pre, replace, fill, cseq.
  destruct (i <? n) eqn:E1, (S i <? n) eqn:E2; bool_lia.
Qed.

(* f is injective. *)
Theorem f_inj :
  injective Nat τ2 f.
Proof.
intros n m _ _; simpl; unfold dec_apart; intros H.
assert(C: n < m \/ m < n). lia. destruct C, n, m; try lia; simpl.
- exists m. rewrite <-(add_0_r m) at 3; rewrite pre_r. unfold cseq; lia.
- exists n. apply le_exists_sub in H0 as [k [Hk _]].
  replace m with (n + S k) by lia. rewrite pre_l.
  rewrite <-(add_0_r n) at 2; rewrite pre_r. unfold cseq; lia.
- exists n. rewrite <-(add_0_r n) at 2; rewrite pre_r.
  unfold cseq; lia.
- exists m. apply le_exists_sub in H0 as [k [Hk _]].
  replace n with (m + S k) by lia. rewrite pre_l.
  rewrite <-(add_0_r m) at 3; rewrite pre_r. unfold cseq; lia.
Qed.

(* f is not surjective. *)
Theorem f_not_surj :
  ~surjective Nat τ2 f.
Proof.
assert(P0: 0^ω ∈ τ2). apply member_τP; intros n; unfold cseq; lia.
intros H; destruct (BCPext τ2 _ H (0^ω) P0) as [m [n Q]].
assert(P1: f (S (m + n)) ∈ τ2). apply f_image. apply Q in P1 as [_ P1].
revert P1; destruct n; simpl; intros P1.
- apply equal_f with (x:=m) in P1; revert P1.
  rewrite add_0_r; rewrite pre_r0. unfold cseq; lia.
- apply equal_f with (x:=n) in P1; revert P1. rewrite pre_r0.
  replace (m + S n) with (n + S m) by lia. rewrite pre_l. unfold cseq; lia.
- intros i Hi; unfold f. unfold pre, replace, fill.
  replace (i <? m + n) with true by bool_lia. lia.
Qed.

(* f is surjective under LPO. *)
Theorem lpo_f_surj :
  LPO -> surjective Nat τ2 Tau2.f.
Proof.
intros LPO; intros β Hβ; destruct (LPO β).
- apply epsilon_smallest in H as [n Hn]. 2: intros; apply neq_dec.
  exists (S n); split. apply I. simpl; extensionality i.
  unfold pre, replace, fill, cseq.
  destruct (i <? n) eqn:E; bool_to_Prop. apply Hn in E; lia.
  eapply τ_mono_lwb with (n:=1)(j:=i) in Hβ. lia. apply E. lia.
- exists 0; split. apply I. simpl.
  extensionality n; auto.
Qed.

End Tau2.
