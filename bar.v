(* Bar induction and the Fan Law *)

From intuitionism Require Import lib set seq bcp spr fan.

(* A bar is a proposition on finite sequences. *)
Definition bar := fseq -> Prop.
Definition fbar := list fseq.

(* We will coerce finite bars to such a proposition. *)
Definition fbar_bar (B : fbar) : bar := fun s => In s B.
Coercion fbar_bar : fbar >-> bar.

(* X is barred by B if all sequences in X have a prefix in B. *)
Definition barred (X : baire) (B : bar) :=
  forall α, α : X -> exists n, B ⟨α;n⟩.

(* Define prefix intersection. *)
Definition isect_member (X : baire) s α := α : X /\ starts s α.
Definition isect X s := Baire (isect_member X s).
Notation "X '∩' s" := (isect X s) (at level 50).

(* Some results about intersections. *)
Section Intersection.

Variable X : baire.
Variable s : fseq.

Lemma isect_in_parent α :
  α : (X ∩ s) -> α : X.
Proof.
Admitted.

End Intersection.

(* s is in F safe with respect to B. *)
Definition safe (F : fan) B s := barred (F ∩ s) B.

(* If B bars F, then [] is in F safe with respect to B. *)
Lemma safe_nil (F : fan) B : barred F B -> safe F B [].
Proof. intros H m Hm. apply (H m). apply isect_in_parent; auto. Qed.

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
  σ F s = true -> safe F B s.
Proof.
intros σs; induction can; unfold safe; simpl.
- (* Skip *)
  exfalso. rewrite σs in H1. discriminate.
- (* Introduction step *)
  intros α Hα. exists (length s). replace ⟨α;length s⟩ with s; auto.
  admit.
- (* Forward step *)
  intros α Hα. clear H2. pose(αs := α (length s)).
  assert(σαs: σ F (αs :: s) = true). admit.
  assert(αsN: αs <= N). now apply H1.
  apply H in αsN; auto. apply αsN. admit.
- (* Backward step *)
  intros α Hα. subst s; clear H2.
  assert(H: exists n, σ F (n :: t0) = true). now exists n.
  apply σ_cons in H. apply IHcan in H. apply H.
  admit.
Admitted.
















