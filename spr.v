(* Finitary spreads *)

From intuitionism Require Import seq bcp.
Import Brouwer.

Require Import Coq.Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Import ListNotations.

(* Spread: a subset of the entire Baire space *)
Record spread := Spr {
  σ :> fseq -> bool;
  σ_nil : σ [] = true;
  σ_cons : forall s, σ s = true <-> exists n, σ (n :: s) = true;
}.

(* Spread membership *)
Definition elementof (σ : fseq -> bool) α := forall m, σ ⟨α;m⟩ = true.

Notation "α 'of' σ" := (elementof σ α)(at level 50).

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
Section Retract.

Arguments exist {_ _}.
Variable S : spread.

(* S is decidable *)
Lemma S_dec s n : {S (n :: s) = true} + {~S (n :: s) = true}.
Proof. apply bool_dec. Qed.

(* Retract any finite sequence onto the spread. *)
Fixpoint ρ (s : fseq) : {t | S t = true} :=
  match s with
  | [] => exist [] (σ_nil S)
  | n :: t =>
    let ρt := proj1_sig (ρ t) in
    let ρtP := proj2_sig (ρ t) in
    match S_dec ρt n with
    | left accept => exist (n :: ρt) accept
    | right _ =>
      let ext := proj1 (σ_cons S ρt) ρtP in
      let min := epsilon_smallest _ (S_dec ρt) ext in
      exist (proj1_sig min :: ρt) (proj1 (proj2_sig min))
    end
  end.

(* Retract function *)
Definition r α n := hd 0 (proj1_sig (ρ ⟨α;n⟩)).

Lemma r_id α :
  α of S -> r α = α.
Proof.
Admitted.

Lemma retract_image α :
  (r α) of S.
Proof.
Admitted.

End Retract.













