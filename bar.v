(* Bar induction and the Fan Theorem *)

From intuitionism Require Import lib set seq bcp spr fan tau func.

(* A bar is a proposition on finite sequences. *)
Definition bar := fseq -> Prop.
Definition fbar := list fseq.

(* We will coerce finite bars to such a proposition. *)
Definition fbar_bar (B : fbar) : bar := fun s => In s B.
Coercion fbar_bar : fbar >-> bar.

(* X is barred by B if all sequences in X have a prefix in B. *)
Definition barred (X : baire) (B : bar) :=
  forall α, α isin X -> exists n, B ⟨α;n⟩.

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
    (H1 : forall n, σ F (n :: s) = true -> n <= N)
    (H2 : forall n, n <= N -> safe_can F B (n :: s))
  | safe_backward n t
    (H1 : s = n :: t)
    (H2 : σ F s = true)
    (H3 : safe_can F B t).

(* α (length s) is below the given extension upper bound. *)
Lemma fan_s_extension F s N α :
  (forall n : nat, σ F (n :: s) = true -> n <= N) ->
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
Variable H : forall n : nat, n <= N -> supersafe F B (n :: s).

Definition fbar_union_nth n :=
  match le_dec n N with
  | left P => proj1_sig (H n P)
  | right _ => []
  end.

Definition fbar_union : fbar :=
  concat (map fbar_union_nth (0..N)).

Lemma fbar_union_subset :
  Forall B fbar_union.
Proof.
Admitted.

Lemma fbar_union_safe n :
  n <= N -> safe F fbar_union (n :: s).
Proof.
Admitted.

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
Axiom safe_can_ex : forall F B s, safe F B s -> safe_can F B s.

(* We can remove safe to obtain the final Fan Theorem. *)
Theorem fan_theorem (F : fan) B :
  barred F B -> exists b : fbar, Forall B b /\ barred F b.
Proof.
intros. apply safe_nil in H. apply safe_can_ex in H.
apply safe_can_supersafe in H as [b [Bb b_safe]].
exists b; split; auto. intros α Hα. apply b_safe. now apply isect_nil.
Qed.

End FanTheorem.

(* Under the fan theorem the number of sequences cannot be denumerable. *)
Section Computability.

(* s is a prefix in X. *)
Definition prefix_in (X : baire) s := exists α, α isin X /\ ⟨α;length s⟩ = s.

(* Function that is diagonalized from b. *)
Definition prefix_diagonal (b : list fseq) n :=
  if n <? length b then 1 - nth n (nth n b []) 0 else 0.

(* X allows a sequence that is defined as a diagonalization. *)
Definition contains_diagonal (X : baire) :=
  forall s : list fseq, Forall (prefix_in X) s -> prefix_diagonal s isin X.

(*
If we only want to consider computable sequences (those enumerated by a Turing
Machine), then the fan theorem does not hold. More generally, any denumerable
fan (such as the computable subspace of C) where diagonalization is possible
yields a contradiction.
*)
Theorem not_fan_theorem (F : fan) :
  contains_diagonal F -> ~denumerable F.
Proof.
intros D [f [f_wd [f_inj f_surj]]].
(* We create a bar in F from f. *)
pose(B s := exists n, s = ⟨f n;n + 1⟩).
assert(HB: barred F B).
{ intros α Hα. destruct (f_surj α) as [n [_ Hn]]; auto.
  exists (n + 1). exists n. now rewrite Hn. }
apply fan_theorem in HB as [b [Bb bbar]].
(* We define an α that cannot occur in b by diagonalization. *)
pose(α := prefix_diagonal b).
assert(Hα: α isin F).
{ apply D. clear bbar. induction b. apply Forall_nil.
  inversion_clear Bb. apply Forall_cons. 2: now apply IHb.
  unfold B in H; destruct H as [n Hn]. exists (f n); split.
  now apply f_wd. now rewrite Hn, get_length. }
apply bbar in Hα as [m Hm].
(* There is only one bar of length m, and α escapes it. *)
unfold fbar_bar in Hm. eapply Forall_forall in Bb. 2: apply Hm.
destruct Bb as [n Hn]. rewrite Hn in Hm. apply get_n_eq in Hn as Hnm; subst.
Admitted.

End Computability.
