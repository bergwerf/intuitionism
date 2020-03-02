(* Bar induction and the Fan Law *)

From intuitionism Require Import lib set seq bcp spr fan.

(* A bar is a proposition on finite sequences. *)
Definition bar := fseq -> Prop.
Definition fbar := list fseq.

(* F is barred by B if all sequences in F have a prefix in B. *)
Definition barred (F : fan) (B : bar) :=
  forall α, α : F -> exists n, B ⟨α;n⟩.

(* We will coerce finite bars to such a proposition. *)
Definition fbar_bar (B : fbar) : bar := fun s => In s B.
Coercion fbar_bar : fbar >-> bar.

(* Note: using a sigma type for s created a mess. *)
(* s is in F safe with respect to B. *)
Definition safe (F : fan) B s := barred (fanint F s) B.

(* If B bars F, then [] is in F safe with respect to B. *)
Lemma safe_nil F B :
  barred F B -> safe F B [].
Proof.
intros H. intros α Hα. apply (H α).
intros m. assert(M := Hα m). simpl in M; unfold Intσ in M.
bool_to_Prop; auto.
Qed.

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
- (* Intro *)
  intros α Hα. exists (length s). admit.
- (* Forward step *)
  intros α Hα. admit.
- (* Backward step *)
  intros α Hα. subst s; clear H2.
  apply IHcan. apply σ_cons. exists n; auto.
  intros m. assert(Hm := Hα m). revert Hm; simpl.
  unfold Intσ. intros; repeat bool_to_Prop; auto.
  admit.
Abort.













