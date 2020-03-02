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
Definition safe (F : fan) B s :=
  exists H : σ F s = true, barred (fanint F s H) B.

(* If B bars F, then [] is in F safe with respect to B. *)
Lemma safe_nil F B :
  barred F B -> safe F B [].
Proof.
intros H. exists (σ_nil F). intros α Hα. apply (H α).
intros m. assert(M := Hα m). simpl in M; unfold Intσ in M.
now bool_to_Prop.
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

Lemma fanint_get_root F s Hs α :
  α : fanint F s Hs -> ⟨α;length s⟩ = s.
Proof.
Admitted.

Lemma in_fanint_forward1 F s α H :
  α : fanint F s H -> σ F (α (length s) :: s) = true.
Proof.
Admitted.

Lemma in_fanint_forward2 F s α H1 H2:
  α : fanint F s H1 -> α : fanint F (α (length s) :: s) H2.
Proof.
Admitted.

Lemma in_fanint_backward F n s α H1 H2 :
  α : fanint F (n :: s) H1 -> α : fanint F s H2.
Proof.
intros Hα m. assert(Hm := Hα m). revert Hm; simpl.
unfold Intσ; intros. repeat bool_to_Prop; auto.
simpl in Hm0. eapply fcompare_app_inv; apply Hm0.
Qed.

(* safe_can is as strong as safe. *)
Theorem safe_can_safe F B s (can : safe_can F B s) :
  σ F s = true -> safe F B s.
Proof.
intros σs; induction can; unfold safe; simpl; exists σs.
- (* Skip *)
  exfalso. rewrite σs in H1. discriminate.
- (* Introduction step *)
  intros α Hα. exists (length s). replace ⟨α;length s⟩ with s; auto.
  now rewrite fanint_get_root.
- (* Forward step *)
  intros α Hα. clear H2. pose(αs := α (length s)).
  assert(σαs: σ F (αs :: s) = true). now apply in_fanint_forward1 in Hα.
  assert(αsN: αs <= N). now apply H1.
  apply H in αsN; auto. clear σαs; destruct αsN as [σαs Bαs]. apply Bαs.
  unfold αs. eapply in_fanint_forward2; apply Hα.
- (* Backward step *)
  intros α Hα. subst s; clear H2.
  assert(Hex: exists n, σ F (n :: t0) = true). now exists n.
  apply σ_cons in Hex. apply IHcan in Hex as [Ht0 Bt0]. apply Bt0.
  eapply in_fanint_backward; apply Hα.
Qed.













