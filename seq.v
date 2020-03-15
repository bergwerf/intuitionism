(* Finite and infinite sequences *)

From intuitionism Require Import lib set.

(* Infinite sequence *)
Notation "'seq'" := (nat -> nat).

(* Finite sequence *)
(* For technical reasons the head represents the last element. *)
Notation "'fseq'" := (list nat).

(* Infinite constant sequence *)
Definition cseq (c i : nat) := c.

(* Finite constant sequence *)
Definition cfseq (c n : nat) := repeat c n.

(* The first n elements of α and β coincide. *)
Definition eqn n (α β : seq) := ∀i, i < n -> α i = β i.

(* Apartness relation. *)
Definition seq_apart (α β : seq) := ∃n, α n <> β n.

(* Delete first n elements. *)
Definition del n (α : seq) i := α (n + i).

(* Add n times (α 0) as prefix. *)
Definition fill n (α : seq) i := α (i - n).

(* Overwrite the first n elements of α with β. *)
Definition replace n (α β : seq) i := if i <? n then β i else α i.

(* Add n elements from α as prefix to β. *)
Definition pre n α β := replace n (fill n β) α.

(* Get first n elements of α. *)
Fixpoint get n (α : seq) : fseq :=
  match n with
  | 0 => []
  | S m => α m :: (get m α)
  end.

(* Check, up to n, how many elements of α and β coincide. *)
Fixpoint compare (n : nat) (α β : seq) :=
  match n with
  | 0 => 0
  | S m => if α 0 =? β 0 then S (compare m (del 1 α) (del 1 β)) else 0
  end.

(* Increasing sequence from n .. n + k *)
Fixpoint iota (n k : nat) : fseq :=
  match k with
  | 0 => []
  | S l => n :: (iota (S n) l)
  end.

(* Alternative notation for iota *)
Definition range n m := iota n (1 + m - n).

(* Get upperbound for a finite sequence. *)
Definition upb s := fold_right max 0 s.

Notation "c '^ω'" := (cseq c) (at level 10, format "c '^ω'").
Notation "n '..' m" := (range n m) (at level 10, format "n '..' m").
Notation "'⟨' α ';' n '⟩'" := (get n α) (at level 0, format "'⟨' α ';' n '⟩'").

(* Apartness set for finite sequences. *)
Definition FSeq := ASet fseq fullset (dec_apart fseq)
  (dec_apart_spec fseq (List.list_eq_dec eq_dec)) (dec_apart_neq fseq)
  (dec_apart_sym fseq).

(* Apartness set of all infinite sequences *)
Section BaireSpace.

Lemma seq_apart_spec α β :
  ~seq_apart α β <-> α = β.
Proof.
unfold seq_apart; split; intros.
- extensionality n. destruct (eq_dec (α n) (β n)); auto.
  exfalso; apply H; exists n; auto.
- intros [n P]; subst; auto.
Qed.

Lemma seq_apart_neq α β : seq_apart α β -> α <> β.
Proof. intros [n H] P; subst; apply H; auto. Qed.

Lemma seq_apart_sym α β : seq_apart α β -> seq_apart β α.
Proof. intros [n H]; exists n; auto. Qed.

Record baire := Baire {
  baire_member : seq -> Prop;
}.

Definition baire_aset (X : baire) :=
  ASet seq (baire_member X) seq_apart
    seq_apart_spec seq_apart_neq seq_apart_sym.

Coercion baire_aset : baire >-> aset.
Definition Seq := Baire fullset.

End BaireSpace.

(* Facts about the coincedence relation *)
Section Coincedence.

Lemma eqn_refl n α : eqn n α α.
Proof. intros i; auto. Qed.

Lemma eqn_sym n α β : eqn n α β -> eqn n β α.
Proof. intros H i Hi. symmetry; apply H; auto. Qed.

Lemma eqn_trans n α β γ : eqn n α β -> eqn n β γ -> eqn n α γ.
Proof. intros Hαβ Hβγ i Hi. rewrite Hαβ. apply Hβγ. all: lia. Qed.

(* A smaller prefix of a coincedence also coincides. *)
Lemma eqn_le n m α β : eqn (n + m) α β -> eqn n α β.
Proof. intros H i Hi; apply H; lia. Qed.

(* Delete part of a coincedence. *)
Lemma eqn_del n m α β :
  eqn (n + m) α β <-> eqn n α β /\ eqn m (del n α) (del n β).
Proof.
split; unfold del; simpl.
- intros H; split. eapply eqn_le; apply H.
  intros i Hi; apply H; lia.
- intros [H1 H2] i Hi. assert(C: i < n \/ i >= n). lia.
  destruct C. apply H1; auto. replace i with (n + (i - n)) by lia.
  apply H2; lia.
Qed.

(* α and β coincide iff their first n elements are the same. *)
Lemma eqn_eq_get n α β :
  eqn n α β <-> ⟨α;n⟩ = ⟨β;n⟩.
Proof.
revert α β; induction n; simpl; intros; split; auto.
- intros _ i Hi; lia.
- intros H; rewrite H; auto. rewrite (proj1 (IHn α β)); auto.
  intros i Hi; apply H; auto.
- intros H i Hi. destruct (eq_dec i n).
  + subst; injection H; auto.
  + apply IHn; try lia. injection H; auto.
Qed.

(* Apartness must occur after any coincedence. *)
Lemma eqn_le_apart α β m n : eqn m α β -> α n <> β n -> m <= n.
Proof. intros Heq Hneq. apply not_gt; intros H. apply Hneq. apply Heq, H. Qed.

End Coincedence.

(* Facts about delete and fill *)
Section DeleteFill.

(* Delete 0 elements. *)
Lemma del0 α : del 0 α = α.
Proof.
apply functional_extensionality.
intros; unfold del; rewrite add_0_l; auto.
Qed.

(* Fill 0 elements. *)
Lemma fill0 α : fill 0 α = α.
Proof.
apply functional_extensionality.
intros; unfold fill; rewrite sub_0_r; auto.
Qed.

(* Rewrite deletion. *)
Lemma del_access α m n : del m α n = α (m + n).
Proof. auto. Qed.

(* Repeated deletion *)
Lemma del_add_distr n m α :
  del n (del m α) = del (m + n) α.
Proof.
unfold del; apply functional_extensionality.
intros. rewrite add_assoc; auto.
Qed.

(* Append element back to deletion. *)
Lemma del_app_S n m α :
  ⟨del (S n) α;m⟩ ++ [α n] = ⟨del n α;S m⟩.
Proof.
induction m; simpl. unfold del; rewrite add_0_r; auto.
rewrite IHm; simpl; unfold del.
replace (S n + m) with (n + S m) by lia; auto.
Qed.

(* Deletion and append *)
Lemma del_app_distr n m α :
  ⟨α;n + m⟩ = ⟨del n α;m⟩ ++ ⟨α;n⟩.
Proof.
revert α. induction n, m; simpl; intros; auto.
- rewrite del0, app_nil_r; auto.
- rewrite add_0_r; auto.
- apply cons_split.
  + unfold del. replace (n + S m) with (S n + m) by lia. auto.
  + assert(R: ∀x (v w : fseq), v ++ x :: w = (v ++ [x]) ++ w).
    { intros; induction v; simpl; auto. rewrite IHv; auto. }
    rewrite R, del_app_S, <-IHn; auto.
Qed.

End DeleteFill.

(* Facts about sequence comparison *)
Section Compare.

Lemma compare_comm n α β :
  compare n α β = compare n β α.
Proof.
revert α β; induction n; simpl; intros; auto.
rewrite eqb_sym. destruct (β 0 =? α 0); auto.
Qed.

(* Comparison returns at most its input. *)
Lemma compare_le n α β :
  compare n α β <= n.
Proof.
revert α β; induction n; simpl; intros; auto.
destruct (α 0 =? β 0); try lia. apply (succ_le_mono _ n). auto.
Qed.

(* If comparison returns less than its input there is an inequality. *)
Lemma compare_lt n α β :
  compare n α β < n -> α (compare n α β) <> β (compare n α β).
Proof.
revert α β; induction n; simpl; intros. lia.
destruct (α 0 =? β 0) eqn:E; bool_to_Prop; auto.
apply succ_lt_mono in H. apply IHn in H.
rewrite ?del_access, ?add_1_l in H; auto.
Qed.

(* Comparison implies coincedence. *)
Lemma eqn_compare n α β :
  eqn (compare n α β) α β.
Proof.
remember (compare n α β) as k.
revert Heqk; revert n α β. induction k; intros n α β Hk i Hi. lia.
revert Hk. destruct n; simpl. discriminate. intros.
destruct (α 0 =? β 0) eqn:E; bool_to_Prop; try discriminate.
injection Hk; intros. apply IHk in H. destruct (eq_dec i 0); subst; auto.
replace i with (1 + (i - 1)) by lia. apply H; lia.
Qed.

End Compare.

(* Facts about properties of sequence elements *)
Section SeqProp.

Variable P : nat -> Prop.

Lemma pre_prop n α β :
  (∀i, P (α i))
  -> (∀i, P (β i))
  -> (∀i, P (pre n α β i)).
Proof.
intros Hα Hβ i; unfold pre, replace, fill.
destruct (i <? n); auto.
Qed.

End SeqProp.

(* Facts about get *)
Section GetPrefix.

(* Equality implies the same length prefix. *)
Lemma get_n_eq n m α β :
  ⟨α;n⟩ = ⟨β;m⟩ -> n = m.
Proof.
revert m; induction n; simpl.
- now destruct m.
- destruct m. now simpl. simpl; intros H.
  injection H; intros. apply IHn in H0. now subst.
Qed.

Corollary get_eq_l n m α β : ⟨α;n⟩ = ⟨β;m⟩ -> ⟨α;n⟩ = ⟨β;n⟩.
Proof. intros; apply get_n_eq in H as R; now subst. Qed.

Corollary get_eq_r n m α β : ⟨α;n⟩ = ⟨β;m⟩ -> ⟨α;m⟩ = ⟨β;m⟩.
Proof. intros; apply get_n_eq in H as R; now subst. Qed.

Corollary get_n_neq n m α β : n <> m -> ⟨α;n⟩ <> ⟨β;m⟩.
Proof. intros H P. apply H. eapply get_n_eq. apply P. Qed.

(* Get finite part of a partially constant sequence. *)
Lemma get_cseq_eq_cfseq c n α :
  (eqn n α (c^ω)) <-> ⟨α;n⟩ = cfseq c n.
Proof.
induction n;simpl; split; auto.
- intros _ i Hi; lia.
- rewrite <-add_1_r; intros H1; apply eqn_le in H1 as H2.
  apply cons_split. apply H1; lia. apply IHn; auto.
- intros H i Hi; inversion H; subst. destruct (eq_dec i n).
  subst; auto. apply IHn in H2; apply H2; lia.
Qed.

Corollary get_cseq c n : ⟨c^ω;n⟩ = cfseq c n.
Proof. apply get_cseq_eq_cfseq, eqn_refl. Qed.

Lemma get_length α n : length ⟨α;n⟩ = n.
Proof. induction n; simpl; auto. Qed.

End GetPrefix.

(* Facts about prefix *)
Section Prefix.

(* A prefixed sequence coincides with itself. *)
Lemma eqn_pre n m α β :
  eqn n α (pre (n + m) α β).
Proof.
intros i Hi; unfold pre, replace, fill.
replace (i <? n + m) with true by bool_lia; auto.
Qed.

Corollary eqn_pre_n n α β : eqn n α (pre n α β).
Proof. rewrite <-add_0_r at 2. apply eqn_pre. Qed.

(* Prefix zero elements. *)
Lemma pre0 α β :
  pre 0 α β = β.
Proof.
extensionality n. unfold pre, replace, fill.
replace (n <? 0) with false by bool_lia.
rewrite sub_0_r; auto.
Qed.

(* Access sequence after prefix. *)
Lemma pre_l n m α β :
  (pre (n + S m) α β) n = α n.
Proof.
unfold pre, replace, fill.
replace (n <? n + S m) with true by bool_lia; auto.
Qed.

(* Access prefix. *)
Lemma pre_r n m α β :
  (pre n α β) (n + m) = β m.
Proof.
unfold pre, replace, fill.
replace (n + m <? n) with false by bool_lia.
replace (n + m - n) with m by lia.
auto.
Qed.

Corollary pre_l0 n α β : (pre (S n) α β) 0 = α 0.
Proof. rewrite <-(add_0_l (S n)). apply pre_l. Qed.

Corollary pre_r0 n α β : (pre n α β) n = β 0.
Proof. rewrite <-(add_0_r n) at 2. apply pre_r. Qed.

Lemma pre_get_l n m α β :
  ⟨pre (n + m) α β;n⟩ = ⟨α;n⟩.
Proof.
revert m; induction n; simpl; intros; auto.
replace (S (n + m)) with (n + S m) by lia.
rewrite pre_l, IHn; auto.
Qed.

(* Get prefixed elements. *)
Lemma pre_get n m α β :
  ⟨pre n α β;n + m⟩ = ⟨β;m⟩ ++ ⟨α;n⟩.
Proof.
revert n; induction m; simpl; intros.
- rewrite add_0_r. rewrite <-(add_0_r n) at 2. rewrite pre_get_l; auto.
- replace (n + S m) with (S (n + m)) by lia; simpl. rewrite <-IHm.
  rewrite pre_r; auto.
Qed.

End Prefix.

(* Facts about iota and range *)
Section IotaRange.

Lemma iota_cons n k :
  iota n (S k) = n :: iota (S n) k.
Proof. auto. Qed.

Lemma iota_add_app_r n k l :
  iota n (k + l) = iota n k ++ iota (n + k) l.
Proof.
revert n l; induction k; intros; simpl.
- rewrite add_0_r; auto.
- rewrite IHk. replace (S n + k) with (n + S k) by lia; auto.
Qed.

Lemma range_add_app_r n m k :
  n <= m -> n..(m + S k) = n..m ++ (S m)..(m + S k).
Proof.
unfold range; intros H.
replace (1 + (m + S k) - n) with (1 + m - n + S k) by lia.
rewrite iota_add_app_r; apply app_split; auto.
replace (n + (1 + m - n)) with (S m) by lia.
replace (1 + (m + S k) - S m) with (S k) by lia; auto.
Qed.

Lemma in_iota n k x :
  In x (iota n k) <-> n <= x < n + k.
Proof.
revert n; induction k; simpl. lia. split.
- intros [H|H]. subst; lia. apply IHk in H; lia.
- intros H. destruct (eq_dec n x). now left. right. apply IHk; lia.
Qed.

Corollary in_range n m x : In x (range n m) <-> n <= x <= m.
Proof. split; intros. apply in_iota in H; lia. apply in_iota; lia. Qed.

End IotaRange.

(* Facts about upb *)
Section Upb.

Lemma in_upb_le s n :
  In n s -> n <= upb s.
Proof.
induction s; simpl. easy. intros [H|H].
subst; lia. apply IHs in H. lia.
Qed.

Lemma upb_le_map_iota f k l i n :
  k <= i < k + l -> n <= f i -> n <= upb (map f (iota k l)).
Proof.
revert k; induction l; intros; simpl. lia.
apply max_le_iff. destruct (eq_dec k i); subst.
now left. right. apply IHl; auto. lia.
Qed.

End Upb.
