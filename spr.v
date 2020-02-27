(* Finitary spreads *)

From intuitionism Require Import seq bcp.
Import Brouwer.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Import Nat.

(* Spread: a subset of the entire Baire space *)
Record spread := Spr {
  σ : fseq -> bool;
  σ_nil : σ [] = true;
  σ_cons : forall s, σ s = true <-> exists n, σ (n :: s) = true;
}.

(* Spread membership *)
Definition inspr X : seqset := fun α => forall m, σ X ⟨α;m⟩ = true.
Coercion inspr : spread >-> seqset.

Lemma unfold_inspr (X : spread) α :
  α : X -> forall m, σ X ⟨α;m⟩ = true.
Proof. auto. Qed.

(* Baire space as a spread. *)
Section Baire.

Definition Nσ (s : fseq) := true.

Lemma Nσ_nil : Nσ [] = true.
Proof. auto. Qed.

Lemma Nσ_cons s : Nσ s = true <-> exists n, Nσ (n :: s) = true.
Proof. split; intros; auto. exists 0; auto. Qed.

Definition N := Spr Nσ Nσ_nil Nσ_cons.

End Baire.

(* Function to retract the the Baire space onto a spread. *)
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
  (forall α, α : X -> exists m n, forall β, β : X -> con m α β -> R β n).
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













