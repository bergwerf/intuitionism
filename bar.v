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
Variable s : fseq.

Lemma isin_isect_nil α : α isin X -> α isin (X ∩ []).
Proof. intros. simpl; now unfold isect_member. Qed.

Lemma isin_isect_inv α : α isin (X ∩ s) -> α isin X.
Proof. intros H; simpl in H; unfold isect_member in H. easy. Qed.

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
    (H2: forall n, n <= N -> safe_can F B (n :: s))
  | safe_backward n t
    (H1 : s = n :: t)
    (H2 : σ F s = true)
    (H3 : safe_can F B t).

(* safe_can is as strong as safe. *)
Theorem safe_can_safe F B s (can : safe_can F B s) :
  safe F B s.
Proof.
induction can; unfold safe; simpl; intros α [H1α H2α].
- (* Skip *)
  exfalso. revert H1α; simpl; unfold isect_member; intros.
  revert H1. rewrite <-H2α; rewrite H1α. discriminate.
- (* Introduction *)
  exists (length s). now rewrite H2α.
- (* Forward *)
  clear H2. pose(αs := α (length s)).
  assert(σαs: σ F (αs :: s) = true).
  { replace (αs :: s) with ⟨α;S (length s)⟩.
    apply H1α. now rewrite <-H2α at 2. }
  assert(αsN: αs <= N). { now apply H1. }
  apply H in αsN; auto. apply αsN.
  simpl; unfold isect_member; split; auto.
  simpl. now rewrite <-H2α at 3.
- (* Backward *)
  subst s. apply IHcan.
  simpl; unfold isect_member; split; auto.
  simpl in H2α. now injection H2α.
Qed.

(*
To build some confidence in the existence of a canonical proof, we show that
such a proof can be constructed directly when a finite bar is given.
*)
Theorem fbar_safe_can F (B : fbar) s :
  safe F B s -> safe_can F B s.
Proof.
Admitted.

(* We can directly construct a finite bar for τ fans. *)
Theorem τ_fbar m n s :
  exists B : fbar, safe (τ m n) B s.
Proof.
Admitted.

(* Given a canonical safe proof, we can construct a finite bar in F. *)
Theorem fan_fbar F B s :
  safe_can F B s -> exists B' : fbar, safe F B' s.
Proof.
Admitted.

(* Let us assume the existence of a canonical proof for arbitrary fans. *)
Axiom safe_can_ex : forall F B s, safe F B s -> safe_can F B s.

(* We can remove safe to obtain the final Fan Theorem. *)
Theorem fan_theorem (F : fan) B :
  barred F B -> exists B' : fbar, barred F B'.
Proof.
intros. apply safe_nil in H. apply safe_can_ex in H.
apply fan_fbar in H as [B' HB']. exists B'.
intros α Hα. apply HB'. now apply isin_isect_nil.
Qed.
