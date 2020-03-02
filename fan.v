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

(* Intersection of a fan. *)
Section FanIntersection.

Variable F : fan.
Variable root : fseq.
Variable rootP :  σ F root = true.

Lemma Intσ_fan s :
  Intσ F root s = true ->
  exists n, forall m, Intσ F root (m :: s) = true -> m <= n.
Proof.
unfold Intσ; intros; bool_to_Prop. apply (fanP F) in H as [n Hn].
exists n; intros; bool_to_Prop; auto.
Qed.

Definition fanint := Fan (sprint F root rootP) Intσ_fan.

End FanIntersection.
