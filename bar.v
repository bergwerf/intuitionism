(* Bar induction and the Fan Law *)

From intuitionism Require Import lib set seq bcp spr fan.

(* A bar is a proposition on finite sequences. *)
Definition bar := fseq -> Prop.
Definition fbar := list fseq.

(* F is barred by B if all sequences in F have a finite part in B. *)
Definition barred (F : fan) (B : bar) :=
  forall α, α : F -> exists n, B ⟨α;n⟩.

(* We will coerce finite bars to such a proposition. *)
Definition fbar_bar (B : fbar) : bar := fun s => In s B.
Coercion fbar_bar : fbar >-> bar.

(* Restrict bar to a branch. *)
Definition restrict (B : bar) s t := B (t ++ s).

Lemma restrict_nil B : restrict B [] = B.
Proof. extensionality s. unfold restrict; rewrite app_nil_r; auto. Qed.

(* s is in F safe with respect to B. *)
Definition safe (F : fan) B (s : {s | σ F s = true}) :=
  barred (FanBranch F s) (restrict B (proj1_sig s)).

(* If B bars F, then [] is in F safe with respect to B. *)
Lemma safe_nil F B :
  barred F B -> safe F B (exist [] (σ_nil F)).
Proof.
intros H; unfold safe. simpl. rewrite restrict_nil. intros α Hα. apply (H α).
intros m. pose (M := Hα m). simpl in M; unfold Bσ in M; simpl in M.
rewrite app_nil_r in M; auto.
Qed.

(* Brouwer suggest safe F B [] must have a canonical proof. *)
Inductive safe_can (F : fan) (B : bar) s :=
| safe_intro (H1 : σ F s = true) (H2 : B s)
| safe_forward (ns : list {n & safe_can F B (n :: s)})
| safe_backward n t (H1 : s = n :: t) (H2 : safe_can F B t) (H3 : σ F s = true).

(* safe_can is as strong as safe. *)
Theorem safe_can_safe F B s (can : safe_can F B (proj1_sig s)) :
  safe F B s.
Proof.
destruct s as [s σs]; simpl in can. induction can; unfold safe; simpl.
- intros α Hα. exists 0; simpl. unfold restrict. rewrite app_nil_l; auto.
- (* We have no bottom up induction hypothesis. *)
Abort.



















