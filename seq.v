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
Definition eqn n (α β : seq) := forall i, i < n -> α i = β i.

(* Apartness relation. *)
Definition seq_apart (α β : seq) := exists n, α n <> β n.

(* Delete first n elements. *)
Definition del n (α : seq) i := α (i + n).

(* Prepend n times (α 0) to the sequence. *)
Definition fill n (α : seq) i := α (i - n).

(* Overwrite the first n elements of α with β. *)
Definition replace n (α β : seq) i := if i <? n then β i else α i.

(* Prepend first n elements of α to β. *)
Definition prepend n α β := replace n (fill n β) α.

(* Check if α starts with s. *)
Fixpoint starts s (α : seq) := 
  match s with
  | [] => True
  | s0 :: t => α 0 = s0 /\ starts t (del 1 α)
  end.

(* Get first n elements of α. *)
Fixpoint get n (α : seq) : fseq :=
  match n with
  | 0 => []
  | S m => α m :: (get m α)
  end.

(* Increasing sequence from n .. n + k *)
Fixpoint iota (n k : nat) : fseq :=
  match k with
  | 0 => []
  | S l => n :: (iota (S n) l)
  end.

(* Check, up to n, how many elements of α and β coincide. *)
Fixpoint compare (n : nat) (α β : seq) :=
  match n with
  | 0 => 0
  | S m => if α 0 =? β 0 then S (compare m (del 1 α) (del 1 β)) else 0
  end.

(* Alternative notation *)
Definition range n m := iota n (1 + m - n).

Notation "c '..ω'" := (cseq c) (at level 10, format "c '..ω'").
Notation "n '..' m" := (range n m) (at level 10, format "n '..' m").
Notation "'⟨' α ';' n '⟩'" := (get n α) (at level 0, format "'⟨' α ';' n '⟩'").
Notation "s '⊏' α" := (starts s α) (at level 50).

(* Set of all infinite and finite sequences *)
Section SeqSet.

Lemma seq_apart_spec α β :
  ~seq_apart α β <-> α = β.
Proof.
unfold seq_apart; split; intros.
- extensionality n. destruct (eq_nat_dec (α n) (β n)); auto.
  exfalso; apply H; exists n; auto.
- intros [n P]; subst; auto.
Qed.

Lemma seq_apart_neq α β : seq_apart α β -> α <> β.
Proof. intros [n H] P; subst; apply H; auto. Qed.

Lemma seq_apart_sym α β : seq_apart α β -> seq_apart β α.
Proof. intros [n H]; exists n; auto. Qed.

Definition Seq := ASet seq full_set seq_apart
  seq_apart_spec seq_apart_neq seq_apart_sym.

Definition FSeq := ASet fseq full_set (dec_apart fseq)
  (dec_apart_spec fseq (list_eq_dec eq_nat_dec)) (dec_apart_neq fseq)
  (dec_apart_sym fseq).

End SeqSet.

(* Shortcuts for proofs about sequences *)
Section Shortcuts.

Lemma app_split (a b x y : fseq) : a = b -> x = y -> a ++ x = b ++ y.
Proof. intros; subst; auto. Qed.

Lemma cons_split h1 h2 (t1 t2 : fseq) :
  h1 = h2 -> t1 = t2 -> h1 :: t1 = h2 :: t2.
Proof. intros; subst; auto. Qed.

End Shortcuts.

(* Facts about the coincedence relation *)
Section Coincedence.

(* A sequence coincides with itself. *)
Lemma eqn_id n α : eqn n α α.
Proof. intros i; auto. Qed.

(* A smaller part of a coincedence also coincides. *)
Lemma eqn_leq n m α β : eqn (n + m) α β -> eqn n α β.
Proof. intros H i Hi; apply H; omega. Qed.

(* Delete part of a coincedence. *)
Lemma eqn_del n m α β :
  eqn (n + m) α β <-> eqn n α β /\ eqn m (del n α) (del n β).
Proof.
split; unfold del; simpl.
- intros H; split. eapply eqn_leq; apply H.
  intros i Hi; apply H; omega.
- intros [H1 H2] i Hi. assert(C: i < n \/ i >= n). omega.
  destruct C. apply H1; auto. replace i with ((i - n) + n) by omega.
  apply H2; omega.
Qed.

(* α and β coincide iff their first n elements are the same. *)
Lemma eqn_eq_get n α β :
  eqn n α β <-> ⟨α;n⟩ = ⟨β;n⟩.
Proof.
revert α β; induction n; simpl; intros; split; auto.
- intros _ i Hi; omega.
- intros H; rewrite H; auto. rewrite (proj1 (IHn α β)); auto.
  intros i Hi; apply H; auto.
- intros H i Hi. destruct (eq_dec i n).
  + subst; injection H; auto.
  + apply IHn; try omega. injection H; auto.
Qed.

(* Comparison returns at most its input. *)
Lemma compare_leq n α β :
  compare n α β <= n.
Proof.
revert α β; induction n; simpl; intros; auto.
destruct (α 0 =? β 0); try omega. apply (succ_le_mono _ n). auto.
Qed.

(* Comparison implies coincedence. *)
Lemma compare_con n α β :
  eqn (compare n α β) α β.
Proof.
remember (compare n α β) as k.
revert Heqk; revert n α β. induction k; intros n α β Hk i Hi. omega.
revert Hk. destruct n; simpl. discriminate. intros.
destruct (α 0 =? β 0) eqn:E; bool_to_Prop; try discriminate.
injection Hk; intros. apply IHk in H. destruct (eq_nat_dec i 0); subst; auto.
replace i with ((i - 1) + 1) by omega. apply H; omega.
Qed.

End Coincedence.

(* Facts about delete and fill *)
Section DeleteFill.

(* Delete 0 elements. *)
Lemma del0 α : del 0 α = α.
Proof.
apply functional_extensionality.
intros; unfold del; rewrite add_0_r; auto.
Qed.

(* Fill 0 elements. *)
Lemma fill0 α : fill 0 α = α.
Proof.
apply functional_extensionality.
intros; unfold fill; rewrite sub_0_r; auto.
Qed.

(* Repeated deletion *)
Lemma del_add_distr n m α :
  del n (del m α) = del (n + m) α.
Proof.
unfold del; apply functional_extensionality.
intros; rewrite add_assoc; auto.
Qed.

(* Append element back to deletion. *)
Lemma del_app_S n m α :
  ⟨del (S n) α;m⟩ ++ [α n] = ⟨del n α;S m⟩.
Proof.
induction m; simpl; auto.
rewrite IHm; simpl; unfold del.
replace (m + S n) with (S m + n) by omega; auto.
Qed.

(* Deletion and append *)
Lemma del_app_distr n m α :
  ⟨α;n + m⟩ = ⟨del n α;m⟩ ++ ⟨α;n⟩.
Proof.
revert α. induction n, m; simpl; intros; auto.
- rewrite del0, app_nil_r; auto.
- rewrite add_0_r; auto.
- apply cons_split.
  + unfold del. replace (n + S m) with (m + S n) by omega. auto.
  + assert(R: forall x (v w : fseq), v ++ x :: w = (v ++ [x]) ++ w).
    { intros; induction v; simpl; auto. rewrite IHv; auto. }
    rewrite R, del_app_S, <-IHn; auto.
Qed.

End DeleteFill.

(* Facts about properties of sequence elements *)
Section SeqProp.

Variable P : nat -> Prop.

Lemma cseq_prop c :
  P c -> forall n, P (c..ω n).
Proof. unfold cseq; intros; auto. Qed.

Lemma prepend_prop n α β :
  (forall i, P (α i))
  -> (forall i, P (β i))
  -> (forall i, P (prepend n α β i)).
Proof.
intros Hα Hβ i; unfold prepend, replace, fill.
destruct (i <? n); auto.
Qed.

End SeqProp.

(* Facts about get (finite start sequence) *)
Section GetStart.

(* Different length parts are never equal. *)
Lemma get_neq n m α β :
  n <> m -> ⟨α;n⟩ <> ⟨β;m⟩.
Proof.
revert m; induction n; intros; simpl.
- destruct m; try omega; simpl. apply nil_cons.
- destruct m; simpl; intros P; inversion P.
  apply IHn in H2; auto.
Qed.

(* Get finite part of a partially constant sequence. *)
Lemma get_cseq_eq_cfseq c n α :
  (eqn n α (c..ω)) <-> ⟨α;n⟩ = cfseq c n.
Proof.
induction n; simpl; split; auto.
- intros _ i Hi; omega.
- rewrite <-add_1_r; intros H1; apply eqn_leq in H1 as H2.
  apply cons_split. apply H1; omega. apply IHn; auto.
- intros H i Hi; inversion H; subst. destruct (eq_dec i n).
  subst; auto. apply IHn in H2; apply H2; omega.
Qed.

Corollary get_cseq c n :
  ⟨c..ω;n⟩ = cfseq c n.
Proof.
apply get_cseq_eq_cfseq. apply eqn_id.
Qed.

Lemma get_S_cons α m n s :
  ⟨α;S m⟩ = n :: s -> α m = n.
Proof.
destruct m; simpl; intros; inversion H; auto.
Qed.

End GetStart.

(* Facts about prepend *)
Section Prepend.

(* A prepended sequence coincides with itself. *)
Lemma eqn_prepend n α β :
  eqn n α (prepend n α β).
Proof.
intros i Hi; unfold prepend, replace, fill.
apply ltb_lt in Hi; rewrite Hi; auto.
Qed.

(* Prepend zero elements. *)
Lemma prepend_zero α β :
  prepend 0 α β = β.
Proof.
extensionality n. unfold prepend, replace, fill.
replace (n <? 0) with false by bool_omega.
rewrite sub_0_r; auto.
Qed.

(* Access left sequence of prepend. *)
Lemma prepend_access_l n m α β :
  prepend (n + S m) α β n = α n.
Proof.
unfold prepend, replace, fill.
replace (n <? n + S m) with true by bool_omega; auto.
Qed.

(* Access right sequence of prepend. *)
Lemma prepend_access_r n m α β :
  prepend n α β (n + m) = β m.
Proof.
unfold prepend, replace, fill.
replace (n + m <? n) with false by bool_omega.
replace (n + m - n) with m by omega.
auto.
Qed.

Corollary prepend_access_r0 n α β :
  prepend n α β n = β 0.
Proof.
rewrite <-(add_0_r n) at 2. apply prepend_access_r.
Qed.

End Prepend.

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
- rewrite IHk. replace (S n + k) with (n + S k) by omega; auto.
Qed.

Lemma range_add_app_r n m k :
  n <= m -> n..(m + S k) = n..m ++ (S m)..(m + S k).
Proof.
unfold range; intros H.
replace (1 + (m + S k) - n) with (1 + m - n + S k) by omega.
rewrite iota_add_app_r; apply app_split; auto.
replace (n + (1 + m - n)) with (S m) by omega.
replace (1 + (m + S k) - S m) with (S k) by omega; auto.
Qed.

End IotaRange.
