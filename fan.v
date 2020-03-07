(* Finitary spreads *)

From intuitionism Require Import lib set seq spr.

(* Fan: a spread with a finite number of extensions *)
Record fan := Fan {
  spr :> spread;
  fanP : ∀ s, σ spr s = true ->
    ∃ n, ∀ m, σ spr (m :: s) = true -> m <= n;
}.

(* An N-point (such as the Cantor space) space is a fan. *)
Section PointSpace.
Variable N : nat.

Definition Pσ (s : fseq) := fold_right (λ n b, b && (n <=? N)) true s.

Lemma Pσ_nil : Pσ [] = true.
Proof. auto. Qed.

Lemma Pσ_cons s :
  Pσ s = true <-> ∃ n, Pσ (n :: s) = true.
Proof.
split. intros; exists 0; simpl; rewrite H; auto.
intros [n Hn]; simpl in Hn. apply andb_prop in Hn as [P _]; auto.
Qed.

Lemma Pσ_fan s :
  Pσ s = true -> ∃ n, ∀ m, Pσ (m :: s) = true -> m <= n.
Proof.
intros; exists N; intros. simpl in H0; apply andb_prop in H0 as [_ P].
apply leb_le; auto.
Qed.

Definition PointSpace := Fan (Spr Pσ Pσ_nil Pσ_cons) Pσ_fan.
End PointSpace.

(* The cantor space, or binary sequences. *)
Definition Bin := PointSpace 1.
