(* The Tau fan *)

From intuitionism Require Import lib set seq bcp spr fan func.

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

Lemma τσ_cons s : τσ s = true <-> exists n, τσ (n :: s) = true.
Proof.
split; intros. destruct s.
- exists lower; simpl; bool_omega.
- exists n; simpl in *; destruct s; repeat bool_to_Prop; try omega; auto.
- destruct H as [n H]; simpl in H; destruct s; auto; repeat bool_to_Prop; auto.
Qed.

Lemma τσ_fan s :
  τσ s = true -> exists n, forall m, τσ (m :: s) = true -> m <= n.
Proof.
intros; exists (lower + range); intros.
simpl in H0; destruct s; bool_omega.
Qed.

Definition τ := Fan (Spr τσ τσ_nil τσ_cons) τσ_fan.

(* Alternative membership criteria *)
Definition τP α := forall n, lower <= α n <= lower + range /\ α n <= α (S n).

Lemma intro_τP α n :
  τP α -> τσ ⟨α;n⟩ = true.
Proof.
intros H; induction n; simpl; auto.
destruct ⟨α;n⟩ eqn:E; repeat bool_to_Prop; auto; try apply H.
destruct n; simpl in *. discriminate. inversion_clear E; apply H.
Qed.

Lemma member_τP α :
  α : τ <-> τP α.
Proof.
split.
- intros H n; eapply unfold_inspr with (m:=S (S n)) in H; simpl in H.
  destruct ⟨α;n⟩ eqn:E; bool_omega.
- intros H m. apply intro_τP; auto.
Qed.

(* τ is monotone. *)
Lemma τ_mono α :
  α : τ -> forall i j, i <= j -> α i <= α j.
Proof.
intros. apply le_exists_sub in H0 as [d [Hd _]]. rewrite Hd; clear Hd.
revert i; induction d; intros; simpl; try omega.
replace (S (d + i)) with (d + S i) by omega.
transitivity (α (S i)); auto. apply member_τP; auto.
Qed.

(* Restrict range. *)
Lemma τ_mono_ext α n i j :
  α : τ -> i <= j -> n <= α i -> n <= α j <= lower + range.
Proof.
intros H1 H2 H3; split. transitivity (α i); auto.
apply τ_mono; auto. apply member_τP; auto.
Qed.

End TauFan.

Definition τ1 := τ 0 0.
Definition τ2 := τ 0 1.
Definition τ3 := τ 0 2.
Definition τ4 := τ 0 3.

(* Some results about τ2. *)
Module Tau2.

(* Any element of τ2 is 0 or 1. *)
Lemma τ2_cases α n :
  α : τ2 -> α n = 0 \/ α n = 1.
Proof.
intros; apply member_τP in H; destruct (α n) eqn:E; auto.
right; rewrite <-E. assert(D: α n <= 1). apply H. omega.
Qed.

(* Any function τ2 -> Nat has a finite image. *)
Theorem τ2_to_Nat_fin_image (f : seq -> nat) :
  exists image, forall α, α : τ2 -> In (f α) image.
Proof.
(* Number of leading zeros after which f outputs a result. *)
destruct (BCP _ (f_computable f) (0^ω)) as [m [n Hbcp]].
(* Full image consists of all sequences up to 0^m. *)
exists (map (fun k => f (pre k (0^ω) (1^ω))) (0..m)).
intros α Hα. pose(k := compare m α (0^ω)).
assert(kleqm: k <= m). unfold k; apply compare_leq.
assert(Hk: eqn k α (0^ω)). apply eqn_compare.
apply in_map_range with (k0:=k); auto. destruct (eq_nat_dec k m).
- rewrite e. rewrite Hbcp. symmetry; apply Hbcp.
  apply eqn_pre_n. rewrite <-e. apply eqn_sym; auto.
- apply f_equal. extensionality i. unfold pre, replace, fill.
  destruct (i <? k) eqn:E; bool_to_Prop; unfold cseq.
  apply Hk; omega. destruct (τ2_cases α i); auto.
  assert(Hlt: k < m). omega. assert(Heqk: k = compare m α (0^ω)). auto.
  apply compare_lt in Hlt. rewrite <-Heqk in Hlt.
  exfalso. apply Hlt; unfold cseq.
  apply (τ_mono _ _ α) in E; auto. omega.
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
  f n : τ2.
Proof.
apply intro_inspr; intros; apply intro_τP. unfold f; destruct n.
- intros n; unfold cseq; omega.
- intros i. split. split; apply pre_prop; intros; unfold cseq; omega.
  unfold pre, replace, fill, cseq.
  destruct (i <? n) eqn:E1; destruct (S i <? n) eqn:E2; bool_omega.
Qed.

(* f is injective. *)
Theorem f_inj :
  injective Nat τ2 f.
Proof.
intros n m _ _; simpl; unfold dec_apart; intros H.
assert(C: n < m \/ m < n). omega. destruct C, n, m; try omega; simpl.
- exists m. rewrite <-(add_0_r m) at 3; rewrite pre_r.
  unfold cseq; omega.
- exists n. apply le_exists_sub in H0 as [k [Hk _]].
  replace m with (n + S k) by omega. rewrite pre_l.
  rewrite <-(add_0_r n) at 2; rewrite pre_r. unfold cseq; omega.
- exists n. rewrite <-(add_0_r n) at 2; rewrite pre_r.
  unfold cseq; omega.
- exists m. apply le_exists_sub in H0 as [k [Hk _]].
  replace n with (m + S k) by omega. rewrite pre_l.
  rewrite <-(add_0_r m) at 3; rewrite pre_r. unfold cseq; omega.
Qed.

(* f is not surjective. *)
Theorem f_not_surj :
  ~surjective Nat τ2 f.
Proof.
assert(P0: 0^ω : τ2). apply member_τP; intros n; unfold cseq; omega.
intros H; destruct (BCPext τ2 _ H (0^ω) P0) as [m [n Q]].
assert(P1: f (S (m + n)) : τ2). apply f_image. apply Q in P1 as [_ P1].
revert P1; destruct n; simpl; intros P1.
- apply equal_f with (x:=m) in P1; revert P1.
  rewrite add_0_r; rewrite pre_r0.
  unfold cseq; intros; omega.
- apply equal_f with (x:=n) in P1; revert P1. rewrite pre_r0.
  replace (m + S n) with (n + S m) by omega. rewrite pre_l.
  unfold cseq; intros; omega.
- intros i Hi; unfold f. unfold pre, replace, fill.
  replace (i <? m + n) with true by bool_omega. omega.
Qed.

End Tau2.
