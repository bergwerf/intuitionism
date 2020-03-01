(* Finitary spreads *)

From intuitionism Require Import lib set seq bcp spr.

(* Fan: a spread with a finite number of extensions *)
Record fan := Fan {
  spr :> spread;
  fanP : forall s, σ spr s = true ->
    exists n, forall m, σ spr (m :: s) = true -> m <= n;
}.

(* An N-point (such as the Cantor space) space is a fan. *)
Section PointSpace.
Variable N : nat.

Definition Pσ (s : fseq) := fold_right (fun n b => b && (n <=? N)) true s.

Lemma Pσ_nil : Pσ [] = true.
Proof. auto. Qed.

Lemma Pσ_cons s :
  Pσ s = true <-> exists n, Pσ (n :: s) = true.
Proof.
split. intros; exists 0; simpl; rewrite H; auto.
intros [n Hn]; simpl in Hn. apply andb_prop in Hn as [P _]; auto.
Qed.

Lemma Pσ_fan s :
  Pσ s = true -> exists n, forall m, Pσ (m :: s) = true -> m <= n.
Proof.
intros; exists N; intros. simpl in H0; apply andb_prop in H0 as [_ P].
apply leb_le; auto.
Qed.

Definition PointSpace := Fan (Spr Pσ Pσ_nil Pσ_cons) Pσ_fan.
End PointSpace.

Definition Cantor := PointSpace 1.

(* Branch of an existing fan. *)
Section FanBranch.

Variable F : fan.
Variable root : {s | σ F s = true}.

Lemma Bσ_fan s :
  Bσ F root s = true -> exists n, forall m, Bσ F root (m :: s) = true -> m <= n.
Proof.
unfold Bσ; intros. apply (fanP F) in H as [n Hn].
exists n; intros. apply Hn. rewrite app_comm_cons; auto.
Qed.

Definition FanBranch := Fan (SprBranch F root) Bσ_fan.

End FanBranch.
