(* Bar induction and the Fan Theorem *)

From intuitionism Require Import lib set seq spr fan func bcp choice.

(* A bar is a proposition on finite sequences. *)
Definition bar := fseq -> Prop.
Definition fbar := list fseq.

(* We will coerce finite bars to such a proposition. *)
Definition fbar_bar (B : fbar) : bar := λ s, In s B.
Coercion fbar_bar : fbar >-> bar.

(* X is barred by B if all sequences in X have a prefix in B. *)
Definition barred (X : baire) (B : bar) := ∀α, α ∈ X -> ∃n, B ⟨α;n⟩.

(* Positive definition for a failing bar. *)
Definition not_barred (X : baire) (B : bar) := ∃α, α ∈ X /\ ∀n, ~B ⟨α;n⟩.

(* Positive definition for a failing finite bar. *)
Definition not_barred_fbar (X : baire) (b : fbar) :=
  ∃α, α ∈ X /\ Forall (λ s, ⟨α;length s⟩ <> s) b.

Theorem not_barred_fbar_weaken X b :
  not_barred_fbar X b -> not_barred X b.
Proof.
intros [α [H1 H2]]. exists α; split; auto. intros n Hn.
unfold fbar_bar in Hn. eapply Forall_forall in H2. 2: apply Hn.
apply H2. now rewrite get_length.
Qed.

Theorem not_barred_weaken X B : not_barred X B -> ~barred X B.
Proof. intros [α [Hα HB]] H. apply H in Hα as [n Hn]. eapply HB, Hn. Qed.

Theorem spread_not_barred_fbar_nil (X : spread) : not_barred_fbar X [].
Proof. destruct (spread_inhabited X). exists x; split; auto. Qed.

(* Proof of the Fan Theorem. *)
Section FanTheorem.

(* Define prefix intersection. *)
Definition isect_member (X : baire) s α := α ∈ X /\ ⟨α;length s⟩ = s.
Definition isect X s := Baire (isect_member X s).
Notation "X '∩' s" := (isect X s) (at level 50).

(* Some results about intersections. *)
Section Intersection.

Variable X : baire.
Variable Xσ : spread.
Variable s : fseq.

Lemma isect_nil α : α ∈ X -> α ∈ (X ∩ []).
Proof. easy. Qed.

Lemma isect_cons n α : α ∈ (X ∩ (n :: s)) -> α ∈ (X ∩ s).
Proof. intros [H1 H2]. split; auto. now injection H2. Qed.

Lemma isect_inv α : α ∈ (X ∩ s) -> α ∈ X.
Proof. now intros [H _]. Qed.

Lemma isect_σ_false α : α ∈ (Xσ ∩ s) -> ~(σ Xσ s = false).
Proof. intros [H1 H2]. now rewrite <-H2, H1. Qed.

Lemma isect_cons_length α : α ∈ (X ∩ s) -> α ∈ (X ∩ (α (length s) :: s)).
Proof. intros [H1 H2]. split; auto. simpl. now rewrite H2. Qed.

End Intersection.

(* s is in F safe with respect to B. *)
Definition safe (F : fan) B s := barred (F ∩ s) B.

(* If B bars F, then [] is in F safe with respect to B. *)
Lemma safe_nil (F : fan) B : barred F B -> safe F B [].
Proof. intros H m Hm. apply (H m). apply isect_inv; auto. Qed.

(* Brouwer suggest safe F B [] must have a canonical proof. *)
Inductive safe_can (F : fan) (B : bar) s :=
  | safe_skip (H1 : σ F s = false)
  | safe_intro (H1 : σ F s = true) (H2 : B s)
  | safe_forward N
    (H1 : ∀n, σ F (n :: s) = true -> n <= N)
    (H2 : ∀n, n <= N -> safe_can F B (n :: s))
  | safe_backward n t
    (H1 : s = n :: t)
    (H2 : σ F s = true)
    (H3 : safe_can F B t).

(* α (length s) is below the given extension upper bound. *)
Lemma fan_s_extension F s N α :
  (∀n : nat, σ F (n :: s) = true -> n <= N) ->
  α ∈ (F ∩ s) -> α (length s) <= N.
Proof.
intros H [H1α H2α]. apply H.
replace (α (length s) :: s) with ⟨α;S (length s)⟩.
apply H1α. simpl. now rewrite H2α.
Qed.

(* safe_can is as strong as safe. *)
Theorem safe_can_safe F B s :
  safe_can F B s -> safe F B s.
Proof.
intros can; induction can; unfold safe; simpl.
- intros α Hα. exfalso. eapply isect_σ_false. apply Hα. auto.
- intros α [H1α H2α]. exists (length s). now rewrite H2α.
- intros α Hα. eapply fan_s_extension in Hα as αN; auto.
  apply H in αN. apply αN. now apply isect_cons_length.
- intros α Hα. apply IHcan. subst; now apply isect_cons.
Qed.

(* In the lecture notes they call this property supersafe. *)
Definition supersafe F B s := {b : fbar | Forall B b /\ safe F b s }.

(* Concatenate all bars up to N given H. *)
Section BarInductionUnion.

Variable F : fan.
Variable B : bar.
Variable s : fseq.
Variable N : nat.
Variable Hsupersafe : ∀n : nat, n <= N -> supersafe F B (n :: s).

Definition fbar_union_nth n :=
  match le_dec n N with
  | left P => proj1_sig (Hsupersafe n P)
  | right _ => []
  end.

Definition fbar_union : fbar := flat_map fbar_union_nth (0..N).

Lemma in_flat_map {X Y} (f : X -> list Y) xs y :
  In y (flat_map f xs) <-> ∃x, In x xs /\ In y (f x).
Proof.
induction xs; simpl; split.
- intros H; now exfalso.
- now intros [_ [Fex _]].
- intros. apply in_app_or in H as [H|H].
  exists a; auto. apply IHxs in H as [x [Hxs Hx]]. exists x; auto.
- intros [x [[Hx|Hx] Hy]]; apply in_or_app. subst; now left.
  right; apply IHxs. now exists x.
Qed.

Lemma fbar_union_subset :
  Forall B fbar_union.
Proof.
apply Forall_forall; intros bs Hbs.
apply in_flat_map in Hbs as [n [HnN Hn]].
apply in_range in HnN as [H0n H1n].
unfold fbar_union_nth in Hn. destruct (le_dec n N); try easy.
assert(Hbs := proj1 (proj2_sig (Hsupersafe n l))); simpl in Hbs.
eapply Forall_forall in Hbs. apply Hbs. auto.
Qed.

Lemma fbar_union_safe n :
  n <= N -> safe F fbar_union (n :: s).
Proof.
intros nN. intros α Hα. destruct (le_dec n N) eqn:E. 2: easy.
assert(nsafe := proj2 (proj2_sig (Hsupersafe n l))); simpl in nsafe.
destruct (nsafe α) as [m Hm]; auto. exists m; apply in_flat_map.
exists n; split. apply in_range; lia.
unfold fbar_union_nth. now rewrite E.
Qed.

End BarInductionUnion.

(* Given a canonical safe proof, we can construct a finite bar in F. *)
Theorem safe_can_supersafe F B s :
  safe_can F B s -> supersafe F B s.
Proof.
intros can; induction can.
- (* Skip *)
  exists []; split; auto. intros α Hα.
  exfalso; eapply isect_σ_false. apply Hα. auto.
- (* Introduction *)
  exists [s]; split. now apply Forall_cons.
  intros α [_ Hα]. exists (length s). simpl. now left.
- (* Forward: this step requires sigma types. *)
  pose(b := fbar_union F B s N H).
  exists b; split. apply fbar_union_subset.
  intros α Hα. eapply fan_s_extension in Hα as αN; auto.
  eapply fbar_union_safe in αN. apply αN. now apply isect_cons_length.
- (* Backward *)
  destruct IHcan as [b [Bb b_safe]]. exists b; split; auto.
  intros α Hα. apply b_safe. subst; now apply isect_cons.
Qed.

(* Let us assume the existence of a canonical proof for arbitrary fans. *)
Axiom safe_can_ex : ∀F B s, safe F B s -> safe_can F B s.

(* We can remove safe to obtain the final Fan Theorem. *)
Theorem fan_theorem (F : fan) B :
  barred F B -> ∃b : fbar, Forall B b /\ barred F b.
Proof.
intros. apply safe_nil in H. apply safe_can_ex in H.
apply safe_can_supersafe in H as [b [Bb b_safe]].
exists b; split; auto. intros α Hα. apply b_safe. now apply isect_nil.
Qed.

End FanTheorem.

(* The Fan Theorem has implications for functions from or to a fan. *)
Section FanFunctions.

Variable F : fan.

(* Any function from F to nat has a finite image. *)
Theorem fan_to_nat_image (f : dom F -> nat) :
  ∃image, ∀α, α ∈ F -> In (f α) image.
Proof.
assert(H := BCPext _ _ (fully_defined_aset_dom f)).
pose(B s := ∃n, ∀β, β ∈ F -> ⟨β;length s⟩ = s -> f β = n).
assert(HB: barred F B).
{ intros α Hα. apply H in Hα as [m [n Hmn]]. exists m, n; intros.
  apply Hmn; auto. apply eqn_eq_get. now apply get_eq_r in H1. }
apply fan_theorem in HB as [b [bB Hb]].
assert(choiceH: ∀s, In s b -> ∃n, ∀β, β ∈ F -> ⟨β;length s⟩ = s -> f β = n).
{ intros s Hs. eapply Forall_forall in bB. 2: apply Hs. apply bB. }
apply fseq_list_choice in choiceH as [c Hc]. 2: apply 0.
exists (map c b); intros α Hα. apply Hb in Hα as Bα; destruct Bα as [n Hn].
eapply Hc in Hn as Cn. 2: apply Hα. rewrite Cn; now apply in_map.
now rewrite get_length.
Qed.

(* Any surjective function from nat to F has a finite pre-image. *)
Theorem nat_to_fan_preimage (f : nat -> dom F) :
  surjective Nat F f -> ∃pre_image, (∃n, In n pre_image) /\
    ∀α, α ∈ F -> ∃n, In n pre_image /\ f n = α.
Proof.
pose(B s := ∃n, ∀β, β ∈ F -> ⟨β;length s⟩ = s -> f n = β).
intros f_surj. assert(HB: barred F B).
{ intros α Hα. eapply BCPext in f_surj as [m [n Hmn]]. 2: apply Hα. exists m, n.
  intros. apply Hmn; auto. apply eqn_eq_get. now rewrite <-H0, get_length. }
apply fan_theorem in HB as [b [bB Hb]].
assert(choiceH: ∀s, In s b -> ∃n, ∀β, β ∈ F -> ⟨β;length s⟩ = s -> f n = β).
{ intros s Hs. eapply Forall_forall in bB. 2: apply Hs. apply bB. }
apply fseq_list_choice in choiceH as [c Hc]. 2: apply 0.
exists (map c b); split.
- destruct b; simpl. exfalso. eapply not_barred_weaken.
  apply not_barred_fbar_weaken. apply spread_not_barred_fbar_nil. apply Hb.
  exists (c l). now left.
- intros α Hα. apply Hb in Hα as Bα; destruct Bα as [n Hn].
  eapply Hc in Hn as Cn. 2: apply Hα. exists (c ⟨α;n⟩); split; auto.
  now apply in_map. now rewrite get_length.
Qed.

(* To use these results it is useful to have a max function over lists. *)
Section Maximum.

Definition upb s := fold_right max 0 s.

Lemma upb_leq s :
  forall n, In n s -> n <= upb s.
Proof.
induction s; simpl. easy. intros n [Hn|Hn].
subst; lia. apply IHs in Hn. lia.
Qed.

End Maximum.

(* No fan is denumerable. *)
Theorem fan_not_denumerable :
  ~denumerable F.
Proof.
intros [f [f_wd [f_inj f_surj]]]. apply injective_weaken in f_inj.
apply nat_to_fan_preimage in f_surj as [preI [_ Hpre]].
(* Take a number outside of the given pre-image and contradict f_inj. *)
pose(N := upb preI + 1). destruct (Hpre (f N)) as [n [H1n H2n]].
now apply f_wd. apply f_inj in H2n; try easy; subst.
unfold N in H1n. apply upb_leq in H1n. lia.
Qed.

End FanFunctions.
