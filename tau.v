(* The Tau fan *)

From intuitionism Require Import lib set seq bcp spr fan.

Section Tau.

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
- exists lower; simpl; repeat bool_to_Prop; auto; omega.
- exists n; simpl in *; destruct s; repeat bool_to_Prop; try omega; auto.
- destruct H as [n H]; simpl in H; destruct s; auto; repeat bool_to_Prop; auto.
Qed.

Lemma τσ_fan s :
  τσ s = true -> exists n, forall m, τσ (m :: s) = true -> m <= n.
Proof.
intros; exists (lower + range); intros.
simpl in H0; destruct s; repeat bool_to_Prop; omega.
Qed.

Definition τ := Fan (Spr τσ τσ_nil τσ_cons) τσ_fan.

(* Alternative membership criteria *)
Definition τP α := forall n, lower <= α n <= lower + range /\ α n <= α (S n).

Lemma intro_τP α n :
  τP α -> τσ ⟨α;n⟩ = true.
Proof.
intros H; induction n; simpl; auto.
destruct ⟨α;n⟩ eqn:E; repeat bool_to_Prop; auto; try apply H.
destruct n; simpl in *; inversion_clear E. apply H.
Qed.

Lemma member_τP α :
  α : τ <-> τP α.
Proof.
split.
- intros H n; eapply unfold_inspr with (m:=S (S n)) in H; simpl in H.
  destruct ⟨α;n⟩ eqn:E; repeat bool_to_Prop; omega.
- intros H m. apply intro_τP; auto.
Qed.

(* τ is monotone. *)
Lemma τ_mono α :
  α : τ -> forall i j, i <= j -> α i <= α j.
Proof.
intros. apply le_exists_sub in H0 as [d [Hd _]]. rewrite Hd; clear Hd.
revert i; induction d; intros; simpl; try omega.
assert(R: S (d + i) = d + S i). omega. rewrite R.
transitivity (α (S i)); auto. apply member_τP; auto.
Qed.

End Tau.

Definition τ1 := τ 0 1.
Definition τ2 := τ 0 2.
Definition τ3 := τ 0 3.
