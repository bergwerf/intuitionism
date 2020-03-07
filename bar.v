(* Bar induction and the Fan Theorem *)

From intuitionism Require Import lib set seq spr fan func bcp.

(* A bar is a proposition on finite sequences. *)
Definition bar := fseq -> Prop.
Definition fbar := list fseq.

(* We will coerce finite bars to such a proposition. *)
Definition fbar_bar (B : fbar) : bar := λ s, In s B.
Coercion fbar_bar : fbar >-> bar.

(* X is barred by B if all sequences in X have a prefix in B. *)
Definition barred (X : baire) (B : bar) := ∀ α, α isin X -> ∃ n, B ⟨α;n⟩.

(* Positive definition for a failing bar. *)
Definition not_barred (X : baire) (B : bar) := ∃ α, α isin X /\ ∀ n, ~B ⟨α;n⟩.

(* Positive definition for a failing finite bar. *)
Definition not_barred_fbar (X : baire) (b : fbar) :=
  ∃ α, α isin X /\ Forall (λ s, ⟨α;length s⟩ <> s) b.

Theorem not_barred_fbar_weaken X b :
  not_barred_fbar X b -> not_barred X b.
Proof.
intros [α [H1 H2]]. exists α; split; auto. intros n Hn.
unfold fbar_bar in Hn. eapply Forall_forall in H2. 2: apply Hn.
apply H2. now rewrite get_length.
Qed.

Theorem not_barred_weaken X B : not_barred X B -> ~barred X B.
Proof. intros [α [Hα HB]] H. apply H in Hα as [n Hn]. eapply HB, Hn. Qed.

(* Proof of the Fan Theorem. *)
Section FanTheorem.

(* Define prefix intersection. *)
Definition isect_member (X : baire) s α := α isin X /\ ⟨α;length s⟩ = s.
Definition isect X s := Baire (isect_member X s).
Notation "X '∩' s" := (isect X s) (at level 50).

(* Some results about intersections. *)
Section Intersection.

Variable X : baire.
Variable Xσ : spread.
Variable s : fseq.

Lemma isect_nil α : α isin X -> α isin (X ∩ []).
Proof. easy. Qed.

Lemma isect_cons n α : α isin (X ∩ (n :: s)) -> α isin (X ∩ s).
Proof. intros [H1 H2]. split; auto. now injection H2. Qed.

Lemma isect_inv α : α isin (X ∩ s) -> α isin X.
Proof. now intros [H _]. Qed.

Lemma isect_σ_false α : α isin (Xσ ∩ s) -> ~(σ Xσ s = false).
Proof. intros [H1 H2]. now rewrite <-H2, H1. Qed.

Lemma isect_cons_length α : α isin (X ∩ s) -> α isin (X ∩ (α (length s) :: s)).
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
    (H1 : ∀ n, σ F (n :: s) = true -> n <= N)
    (H2 : ∀ n, n <= N -> safe_can F B (n :: s))
  | safe_backward n t
    (H1 : s = n :: t)
    (H2 : σ F s = true)
    (H3 : safe_can F B t).

(* α (length s) is below the given extension upper bound. *)
Lemma fan_s_extension F s N α :
  (∀ n : nat, σ F (n :: s) = true -> n <= N) ->
  α isin (F ∩ s) -> α (length s) <= N.
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
Variable Hsupersafe : ∀ n : nat, n <= N -> supersafe F B (n :: s).

Definition fbar_union_nth n :=
  match le_dec n N with
  | left P => proj1_sig (Hsupersafe n P)
  | right _ => []
  end.

Definition fbar_union : fbar := flat_map fbar_union_nth (0..N).

Lemma in_flat_map {X Y} (f : X -> list Y) xs y :
  In y (flat_map f xs) <-> ∃ x, In x xs /\ In y (f x).
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
Axiom safe_can_ex : ∀ F B s, safe F B s -> safe_can F B s.

(* We can remove safe to obtain the final Fan Theorem. *)
Theorem fan_theorem (F : fan) B :
  barred F B -> ∃ b : fbar, Forall B b /\ barred F b.
Proof.
intros. apply safe_nil in H. apply safe_can_ex in H.
apply safe_can_supersafe in H as [b [Bb b_safe]].
exists b; split; auto. intros α Hα. apply b_safe. now apply isect_nil.
Qed.

End FanTheorem.

(* The Fan Theorem has implications for functions with a fan domain. *)
Section FanFunctions.

Variable F : fan.

(* Any function from F to nat has a finite image. *)
Theorem fan_to_nat_image (f : dom F -> nat) :
  ∃ image : fseq, ∀ α, In (f α) image.
Proof.
assert(H := BCPext _ _ (fully_defined_aset_dom f)).
pose(B s := ∃ n, ∀ β, β isin F -> ⟨β;length s⟩ = s -> f β = n).
assert(HB: barred F B).
{ intros α Hα. apply H in Hα as [m [n Hmn]]. exists m; exists n; intros.
  apply Hmn; auto. apply eqn_eq_get. now apply get_eq_r in H1. }
apply fan_theorem in HB as [b [bB Hb]].
Admitted.

(* Any function from nat to F has a finite pre-image. *)
Theorem nat_to_fan_preimage (f : nat -> dom F) :
  ∃ image : fseq, ∀ α, ∃ n, In n image /\ f n = α.
Proof.
Admitted.

End FanFunctions.
