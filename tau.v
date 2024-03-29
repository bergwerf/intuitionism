(* The Tau fan *)

From intuitionism Require Import lib set seq spr fan func.
From intuitionism Require Import classic choice bcp bar.

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
destruct (BCPf_10 f (0^ω)) as [m Hbcp].
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

(* Classical surjection is different from intuitionistic surjection. *)
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
- apply epsilon_smallest in H as [n [Hn1 Hn2]]. 2: intros; apply neq_dec.
  exists (S n); split. apply I. simpl; extensionality i.
  unfold pre, replace, fill, cseq.
  destruct (i <? n) eqn:E; bool_to_Prop. assert(Hi := Hn2 i); lia.
  eapply τ_mono_lwb with (n:=1)(j:=i) in Hβ. lia. apply E. lia.
- exists 0; split. apply I. simpl.
  extensionality n; auto.
Qed.

End Tau2.

(* The Fan Theorem holds constructively for τ. *)
Section TauFanTheorem.

(* Additional facts about Forall. *)
Section Forall.

Variable T : Type.
Variable S : Type.
Variable P : T -> Prop.
Variable Q : S -> Prop.

Lemma Forall_map f s :
  Forall Q s -> (∀n, Q n -> P (f n)) -> Forall P (map f s).
Proof.
intros Hs HQP. apply Forall_forall. intros y Hy.
apply in_map_iff in Hy as [x [Hf Hxl]]; subst.
apply HQP. revert Hxl; now apply Forall_forall.
Qed.

Lemma Forall_app s t :
  Forall P s -> Forall P t -> Forall P (s ++ t).
Proof.
intros Hs Ht. apply Forall_forall; intros n Hn.
apply in_app_or in Hn as [H|H]; eapply Forall_forall.
apply Hs. easy. apply Ht. easy. 
Qed.

Lemma Forall_concat b :
  Forall (Forall P) b -> Forall P (concat b).
Proof.
induction b; simpl. easy. intros. inversion_clear H.
apply Forall_app; auto.
Qed.

End Forall.

Theorem tau_fan_theorem k l B :
  barred (τ k l) B -> ∃b : fbar, Forall B b /\ barred (τ k l) b.
Proof.
revert B k; induction l; intros.
- (* Base case: there are no branches. *)
  destruct (H (k^ω)) as [m Hm]. apply τ_cseq; lia.
  exists [⟨k^ω;m⟩]; split. apply Forall_cons; auto.
  intros α Hα; exists m. replace α with (k^ω). now left.
  extensionality n. unfold cseq; tau_member Hα n. lia.
- (* Step: IH gives a bar for branches. *)
  (*
  We cannot use epsilon_smallest because B is in general undecidable. Instead
  we anticipate the discovery of a smaller M (and no bar in a sub-branch) with
  exLtM1 and exLtM2.
  *)
  destruct (H (k^ω)) as [M HM]. apply τ_cseq; lia.
  pose(exLtM1 m b := ∃N, N <= m /\ b = [⟨k^ω;N⟩]).
  pose(exLtM2 m := ∃N, N <= m /\ B ⟨k^ω;N⟩).
  assert(Hchoice: ∀m, m < M -> ∃b : fbar, Forall B b /\
    (exLtM1 m b \/ barred (τ k (S l) ∩ ⟨k^ω;m⟩ \ ⟨k^ω;S m⟩) b)).
  + (* Create a new bar for the branch under k^m. *)
    intros m Hm.
    pose(B1 s := B (s ++ ⟨k^ω;m⟩)).
    pose(B2 s := B1 s \/ (s = [] /\ exLtM2 m)).
    assert(HB2: barred (τ (S k) l) B2).
    { intros α Hα. destruct (H (pre m (k^ω) α)) as [m' Hm'].
      apply τ_pre_cseq. tau_member Hα 0; lia.
      apply member_τP; intros n. tau_member Hα n; lia.
      destruct (le_gt_dec m' m).
      - exists 0; right. split; auto. exists m'; split; auto.
        replace m with (m' + (m - m')) in Hm' by lia.
        now rewrite pre_get_l in Hm'.
      - exists (m' - m); left; unfold B2, B1. rewrite <-pre_get.
        now replace (m + (m' - m)) with m' by lia. }
    (* Create a finite bar using IHl. Check if it contains []. *)
    apply IHl in HB2 as [b [Bb Hb]].
    destruct (In_dec (List.list_eq_dec eq_dec) [] b) as [Hnil|Hnil].
    (* We found a case of exLtM1. *)
    { eapply Forall_forall in Bb. 2: apply Hnil.
      unfold B2, B1 in Bb. destruct Bb as [Bb|[_ [N [H1N H2N]]]].
      - rewrite app_nil_l in Bb. exists [⟨k^ω;m⟩]; split.
        now apply Forall_cons. left; exists m; auto.
      - exists [⟨k^ω;N⟩]; split. now apply Forall_cons. left; now exists N. }
    (* Otherwise continue as usual. *)
    exists (map (λ s, s ++ ⟨k^ω;m⟩) b); split.
    * apply Forall_map with (Q:=B1). apply Forall_forall; intros.
      eapply Forall_forall in Bb. 2: apply H0.
      destruct Bb as [|[R Bb]]; auto. now subst.
      easy.
    * right. intros α [[H1α H2α] H3α]. rewrite get_length in *.
      destruct (Hb (del m α)) as [m' Hm'].
      (* Prove del m α ∈ τ (S k) l. *)
      apply member_τP; intros n; unfold del.
      assert(H4α := H1α); tau_member H4α (m + n).
      rewrite add_succ_r. repeat split. 2,3: lia.
      destruct (le_gt_dec (S k) (α (m + n))); auto. exfalso.
      apply H3α. simpl. rewrite <-H2α. replace k with (α m). easy.
      assert(α m < S k). eapply le_trans. 2: apply g.
      apply le_n_S. eapply τ_mono. apply H1α. lia.
      assert(H2 := H4α m); lia.
      (* Prove ⟨α;m + m'⟩ is in the bar. *)
      exists (m + m'). apply in_map_iff.
      exists ⟨del m α;m'⟩; split; auto.
      now rewrite <-H2α, <-get_app_del.
  + apply bounded_choice in Hchoice as [c Hc]. 2: apply [].
    exists (⟨k^ω;M⟩ :: concat (map c (iota 0 M))); split.
    * apply Forall_cons; auto. apply Forall_concat, Forall_forall.
      intros b Hb. apply in_map_iff in Hb as [n [Hcn HnM]]; subst.
      apply in_iota in HnM as [_ HnM]. simpl in HnM.
      now apply Hc in HnM as [HBcn _].
    * (* Find the first position >k in α up to M. *)
      intros α Hα. clear HM; induction M. exists 0; now left.
      destruct IHM as [n Hn]. intros n Hn. apply Hc; auto.
      { destruct Hn as [Hn|Hn]. apply get_n_eq in Hn as HMn; subst n.
      destruct (eq_dec (α M) k) as [αM|αM].
      - (* α is barred by ⟨k^ω;S M⟩ *)
        exists (S M). replace ⟨α;S M⟩ with ⟨k^ω;S M⟩. apply in_eq.
        simpl; now rewrite Hn, αM.
      - (* α is barred by (c M). *)
        rewrite <-add_1_r, iota_add_app_r, map_app, concat_app; simpl.
        rewrite app_nil_r. destruct (Hc M) as [_ [[N [H1N H2N]]|HcM]]. lia.
        + (* By exLtM1 *)
          exists N; apply in_cons. apply in_or_app; right.
          rewrite H2N. replace ⟨k^ω;N⟩ with ⟨α;N⟩. apply in_eq.
          apply eqn_eq_get; apply eqn_eq_get in Hn.
          eapply eqn_le. apply eqn_sym, Hn. easy.
        + (* By a bar in the corresponding sub-branch *)
          destruct (HcM α) as [m Hm].
          repeat split; auto; rewrite get_length. easy.
          simpl. intros C; apply αM. now injection C.
          exists m; apply in_cons. apply in_or_app; now right.
      - (* α is barred by the IH bar. *)
        exists n. apply in_cons. rewrite <-add_1_r, iota_add_app_r.
        rewrite map_app, concat_app. apply in_or_app. now left.
      }
Qed.

End TauFanTheorem.
