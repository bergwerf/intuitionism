(* Bar induction and the Fan Law *)

From intuitionism Require Import lib set seq bcp spr fan tau.

(* A bar is a proposition on finite sequences. *)
Definition bar := fseq -> Prop.
Definition fbar := list fseq.

(* We will coerce finite bars to such a proposition. *)
Definition fbar_bar (B : fbar) : bar := fun s => In s B.
Coercion fbar_bar : fbar >-> bar.

(* X is barred by B if all sequences in X have a prefix in B. *)
Definition barred (X : baire) (B : bar) :=
  forall α, α isin X -> exists n, B ⟨α;n⟩.

(* Define prefix intersection. *)
Definition isect_member (X : baire) s α := α isin X /\ ⟨α;length s⟩ = s.
Definition isect X s := Baire (isect_member X s).
Notation "X '∩' s" := (isect X s) (at level 50).

(* Some results about intersections. *)
Section Intersection.

Variable X : baire.
Variable Xσ : spread.
Variable s : fseq.

Lemma isin_isect_nil α : α isin X -> α isin (X ∩ []).
Proof. intros. simpl; now unfold isect_member. Qed.

Lemma isin_isect_inv α : α isin (X ∩ s) -> α isin X.
Proof. intros H; simpl in H; unfold isect_member in H. easy. Qed.

Lemma isin_isect_σ_false α :
  α isin (Xσ ∩ s) -> ~(σ Xσ s = false).
Proof.
intros [H1α H2α] H. revert H1α; simpl; unfold spread_member; intros.
now rewrite <-H2α, H1α in H.
Qed.

End Intersection.

(* s is in F safe with respect to B. *)
Definition safe (F : fan) B s := barred (F ∩ s) B.

(* If B bars F, then [] is in F safe with respect to B. *)
Lemma safe_nil (F : fan) B : barred F B -> safe F B [].
Proof. intros H m Hm. apply (H m). apply isin_isect_inv; auto. Qed.

(* Brouwer suggest safe F B [] must have a canonical proof. *)
Inductive safe_can (F : fan) (B : bar) s :=
  | safe_skip (H1 : σ F s = false)
  | safe_intro (H1 : σ F s = true) (H2 : B s)
  | safe_forward N
    (H1 : forall n, σ F (n :: s) = true -> n <= N)
    (H2 : forall n, n <= N -> safe_can F B (n :: s))
  | safe_backward n t
    (H1 : s = n :: t)
    (H2 : σ F s = true)
    (H3 : safe_can F B t).

(* safe_can is as strong as safe. *)
Theorem safe_can_safe F B s :
  safe_can F B s -> safe F B s.
Proof.
intros can; induction can; unfold safe; simpl.
- (* Skip *)
  intros α Hα. exfalso. eapply isin_isect_σ_false. apply Hα. auto.
- (* Introduction *)
  intros α [H1α H2α]. exists (length s). now rewrite H2α.
- (* Forward *)
  intros α [H1α H2α]; clear H2.
  pose(αs := α (length s)). assert(Hαs: αs <= N).
  { apply H1. replace (αs :: s) with ⟨α;S (length s)⟩.
    apply H1α. now rewrite <-H2α at 2. }
  apply H in Hαs; auto. apply Hαs.
  simpl; unfold isect_member; split; auto.
  simpl. now rewrite <-H2α at 3.
- (* Backward *)
  intros α [H1α H2α]. subst s. apply IHcan.
  simpl; unfold isect_member; split; auto.
  simpl in H2α. now injection H2α.
Qed.

(* It is possible to contruct safe_can from a finite bar. *)
Theorem fbar_safe_safe_can F (B : fbar) s :
  safe F B s -> safe_can F B s.
Proof.
Abort.

(* It is possible to directly construct a finite bar for τ fans. *)
Theorem τ_fbar m n s :
  exists B : fbar, safe (τ m n) B s.
Proof.
Abort.

(* In the lecture notes they call this property supersafe. *)
Definition supersafe F s := {B' : fbar | safe F B' s}.

(* Concatenate all bars up to N given H. *)
Section BarInductionUnion.

Variable F : fan.
Variable s : fseq.
Variable N : nat.
Variable H : forall n : nat, n <= N -> supersafe F (n :: s).

Definition fbar_union_nth n :=
  match le_dec n N with
  | left P => proj1_sig (H n P)
  | right _ => []
  end.

Definition fbar_union : fbar :=
  concat (map fbar_union_nth (0..N)).

Lemma fbar_union_safe n :
  n <= N -> safe F fbar_union (n :: s).
Proof.
Admitted.

End BarInductionUnion.

(* Given a canonical safe proof, we can construct a finite bar in F. *)
(* Very similar proof script as safe_can_safe. *)
Theorem safe_can_supersafe F B s :
  safe_can F B s -> supersafe F s.
Proof.
intros can; induction can.
- (* Skip *)
  exists []. intros α Hα. exfalso; eapply isin_isect_σ_false. apply Hα. auto.
- (* Introduction *)
  exists [s]. intros α [_ Hα]. exists (length s). simpl. now left.
- (* Forward: this step requires sigma types. *)
  clear H2. pose(B' := fbar_union F s N H). exists B'.
  intros α [H1α H2α]. pose(αs := α (length s)). assert(Hαs: αs <= N).
  { apply H1. replace (αs :: s) with ⟨α;S (length s)⟩.
    apply H1α. now rewrite <-H2α at 2. }
  eapply fbar_union_safe in Hαs. apply Hαs.
  simpl; unfold isect_member; split; auto.
  simpl. now rewrite <-H2α at 3.
- (* Backward *)
  subst. exists (proj1_sig IHcan).
  intros α [H1α H2α]. apply (proj2_sig IHcan).
  simpl; unfold isect_member; split; auto.
  simpl in H2α. now injection H2α.
Qed.

(* Let us assume the existence of a canonical proof for arbitrary fans. *)
Axiom safe_can_ex : forall F B s, safe F B s -> safe_can F B s.

(* We can remove safe to obtain the final Fan Theorem. *)
Theorem fan_theorem (F : fan) B :
  barred F B -> exists B' : fbar, barred F B'.
Proof.
intros. apply safe_nil in H. apply safe_can_ex in H.
apply safe_can_supersafe in H as [B' HB']. exists B'.
intros α Hα. apply HB'. now apply isin_isect_nil.
Qed.
