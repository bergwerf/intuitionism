(* Finitary spreads *)

From intuitionism Require Import lib set seq bcp.

(* Spread: a subset of the entire Baire space *)
Record spread := Spr {
  σ : fseq -> bool;
  σ_nil : σ [] = true;
  σ_cons : forall s, σ s = true <-> exists n, σ (n :: s) = true;
}.

(* Coerce spreads to aset *)
Section SprCSet.

(* Spread membership *)
Definition spread_member X α := forall m, σ X ⟨α;m⟩ = true.

Definition spread_aset (X : spread) :=
  ASet seq (spread_member X) seq_apart
    seq_apart_spec seq_apart_neq seq_apart_sym.

Coercion spread_aset : spread >-> aset.

Lemma unfold_inspr (X : spread) α :
  α : X -> forall m, σ X ⟨α;m⟩ = true.
Proof. auto. Qed.

Lemma intro_inspr (X : spread) α :
  (forall m, σ X ⟨α;m⟩ = true) -> α : X.
Proof. auto. Qed.

End SprCSet.

(* Branch of an existing spread. *)
Section SpreadBranch.

Variable S : spread.
Variable root : {s | σ S s = true}.

Definition Bσ s := σ S (s ++ (proj1_sig root)).

Lemma Bσ_nil : Bσ [] = true.
Proof. unfold Bσ; destruct root; simpl. auto. Qed.

Lemma Bσ_cons s :
  Bσ s = true <-> exists n, Bσ (n :: s) = true.
Proof.
split; unfold Bσ.
- intros. apply (σ_cons S) in H as [n Hn].
  exists n. rewrite <-app_comm_cons; auto.
- intros [n Hn]. rewrite <-app_comm_cons in Hn.
  assert(Hn': exists n, σ S (n :: s ++ proj1_sig root) = true).
  exists n; auto. apply (σ_cons S (s ++ proj1_sig root)) in Hn'; auto.
Qed.

Definition SprBranch := Spr Bσ Bσ_nil Bσ_cons.

End SpreadBranch.

(* Function to retract the the Baire space onto any spread. *)
Module Retract.
Section Retract.
Notation "'σπ1'" := proj1_sig.
Notation "'σπ2'" := proj2_sig.
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
    let ρt := σπ1 (ρ t) in
    let ρtP := σπ2 (ρ t) in
    match X_dec ρt n with
    | left accept => exist (n :: ρt) accept
    | right _ =>
      let ex := proj1 (σ_cons X ρt) ρtP in
      let n0 := epsilon_smallest _ (X_dec ρt) ex in
      exist (σπ1 n0 :: ρt) (proj1 (σπ2 n0))
    end
  end.

(* Retract function *)
Definition r α n := hd 0 (σπ1 (ρ ⟨α;n+1⟩)).

(* r is the same as ρ *)
Lemma r_eq_ρ α n :
  ⟨r α;n⟩ = σπ1 (ρ ⟨α;n⟩).
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
  α : X -> σπ1 (ρ ⟨α;n⟩) = ⟨α;n⟩.
Proof.
intros; induction n; simpl; auto.
destruct (ρ ⟨α;n⟩); simpl in *; subst.
destruct (X_dec ⟨α;n⟩ (α n)); simpl; auto.
exfalso; apply unfold_inspr with (m:=S n) in H; auto.
Qed.

(* r does not alter sequences in X. *)
Lemma r_id α :
  α : X -> r α = α.
Proof.
intros; apply functional_extensionality; intros n.
unfold r; rewrite ρ_id; auto. rewrite add_1_r; simpl; auto.
Qed.

(* The image of r is in X. *)
Lemma r_image α :
  (r α) : X.
Proof.
intros m; rewrite r_eq_ρ.
destruct (ρ ⟨α;m⟩) as [ρt Hρ]; auto.
Qed.

End Retract.
End Retract.

(* BCP generalizes to spreads *)
Theorem BCPext (X : spread) (R : seq -> nat -> Prop) :
  (forall α, α : X -> exists n, R α n) ->
  (forall α, α : X -> exists m n, forall β, β : X -> eqn m α β -> R β n).
Proof.
intros Rall.
pose(rσ := (Retract.r X)).
pose(T := (fun α n => R (rσ α) n)).
assert(HT: forall α, exists n, T α n).
{ intros; pose (Hα := Retract.r_image X α); apply Rall in Hα.
  destruct Hα as [n Hn]; exists n; auto. }
intros; destruct (BCP T HT α) as [m [n P]]. exists m; exists n; intros.
apply P in H1; unfold T, rσ in H1; rewrite Retract.r_id in H1; auto.
Qed.
