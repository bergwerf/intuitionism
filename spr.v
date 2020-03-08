(* Finitary spreads *)

From intuitionism Require Import lib set seq.

(* Spread: a subset of the entire Baire space *)
Record spread := Spr {
  σ : fseq -> bool;
  σ_nil : σ [] = true;
  σ_cons : ∀s, σ s = true <-> ∃n, σ (n :: s) = true;
}.

(* Coerce spreads to baire. *)
Section SpreadBaire.

Definition spread_member X α := ∀m, σ X ⟨α;m⟩ = true.
Definition spread_biare (X : spread) := Baire (spread_member X).
Coercion spread_biare : spread >-> baire.

Lemma unfold_inspr (X : spread) α :
  α ∈ X -> ∀m, σ X ⟨α;m⟩ = true.
Proof. auto. Qed.

Lemma intro_inspr (X : spread) α :
  (∀m, σ X ⟨α;m⟩ = true) -> α ∈ X.
Proof. auto. Qed.

End SpreadBaire.

(* Function to retract the the Baire space onto any spread. *)
Module Retract.
Section Retract.
Arguments exist {_ _}.

Variable X : spread.

(* X is decidable *)
Lemma X_dec s n : {σ X (n :: s) = true} + {~σ X (n :: s) = true}.
Proof. apply bool_dec. Qed.

(* Retract any finite sequence onto the spread. *)
Fixpoint ρ (s : fseq) : {t | σ X t = true} :=
  match s with
  | [] => exist [] (σ_nil X)
  | n :: t =>
    let ρt := proj1_sig (ρ t) in
    let ρtP := proj2_sig (ρ t) in
    match X_dec ρt n with
    | left accept => exist (n :: ρt) accept
    | right _ =>
      let ex := proj1 (σ_cons X ρt) ρtP in
      let n0 := epsilon_smallest _ (X_dec ρt) ex in
      exist (proj1_sig n0 :: ρt) (proj1 (proj2_sig n0))
    end
  end.

(* Retract function *)
Definition r α n := hd 0 (proj1_sig (ρ ⟨α;n+1⟩)).

(* r is the same as ρ *)
Lemma r_eq_ρ α n :
  ⟨r α;n⟩ = proj1_sig (ρ ⟨α;n⟩).
Proof.
induction n; simpl; auto.
destruct (ρ ⟨α;n⟩) as [ρt Hρ] eqn:Rρ; simpl in *.
destruct (X_dec ρt (α n)) eqn:RX; simpl;
rewrite IHn; apply cons_split; auto;
unfold r; rewrite add_1_r; simpl;
rewrite Rρ; simpl; rewrite RX; auto.
Qed.

(* ρ does not alter sequences in X. *)
Lemma ρ_id α n :
  α ∈ X -> proj1_sig (ρ ⟨α;n⟩) = ⟨α;n⟩.
Proof.
intros; induction n; simpl; auto.
destruct (ρ ⟨α;n⟩); simpl in *; subst.
destruct (X_dec ⟨α;n⟩ (α n)); simpl; auto.
exfalso; apply unfold_inspr with (m:=S n) in H; auto.
Qed.

(* r does not alter sequences in X. *)
Lemma r_id α :
  α ∈ X -> r α = α.
Proof.
intros; apply functional_extensionality; intros n.
unfold r; rewrite ρ_id; auto. rewrite add_1_r; simpl; auto.
Qed.

(* The image of r is in X. *)
Lemma r_image α :
  (r α) ∈ X.
Proof.
intros m; rewrite r_eq_ρ.
destruct (ρ ⟨α;m⟩) as [ρt Hρ]; auto.
Qed.

End Retract.
End Retract.

(* All spreads are inhabited. *)
Corollary spread_inhabited (X : spread) : inhabited X.
Proof. exists (Retract.r X (0^ω)). apply Retract.r_image. Qed.
