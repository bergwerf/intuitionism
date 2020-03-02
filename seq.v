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
Definition del n (α : seq) i := α (n + i).

(* Add n times (α 0) as prefix. *)
Definition fill n (α : seq) i := α (i - n).

(* Overwrite the first n elements of α with β. *)
Definition replace n (α β : seq) i := if i <? n then β i else α i.

(* Add n elements from α as prefix to β. *)
Definition pre n α β := replace n (fill n β) α.

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

(* Match two finite sequences until either runs out. *)
Fixpoint fseq_match (s t : fseq) := 
  match s, t with
  | s1 :: s', t1 :: t' => (s1 =? t1) && fseq_match s' t'
  | _, _ => true
  end.

(* Alternative notation *)
Definition range n m := iota n (1 + m - n).

Notation "c '^ω'" := (cseq c) (at level 10, format "c '^ω'").
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

Lemma eqn_refl n α : eqn n α α.
Proof. intros i; auto. Qed.

Lemma eqn_sym n α β : eqn n α β -> eqn n β α.
Proof. intros H i Hi. symmetry; apply H; auto. Qed.

Lemma eqn_trans n α β γ : eqn n α β -> eqn n β γ -> eqn n α γ.
Proof. intros Hαβ Hβγ i Hi. rewrite Hαβ. apply Hβγ. all: omega. Qed.

(* A smaller prefix of a coincedence also coincides. *)
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
  destruct C. apply H1; auto. replace i with (n + (i - n)) by omega.
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
replace (S n + m) with (n + S m) by omega; auto.
Qed.

(* Deletion and append *)
Lemma del_app_distr n m α :
  ⟨α;n + m⟩ = ⟨del n α;m⟩ ++ ⟨α;n⟩.
Proof.
revert α. induction n, m; simpl; intros; auto.
- rewrite del0, app_nil_r; auto.
- rewrite add_0_r; auto.
- apply cons_split.
  + unfold del. replace (n + S m) with (S n + m) by omega. auto.
  + assert(R: forall x (v w : fseq), v ++ x :: w = (v ++ [x]) ++ w).
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
Lemma compare_leq n α β :
  compare n α β <= n.
Proof.
revert α β; induction n; simpl; intros; auto.
destruct (α 0 =? β 0); try omega. apply (succ_le_mono _ n). auto.
Qed.

(* If comparison returns less than its input there is an inequality. *)
Lemma compare_lt n α β :
  compare n α β < n -> α (compare n α β) <> β (compare n α β).
Proof.
revert α β; induction n; simpl; intros. omega.
destruct (α 0 =? β 0) eqn:E; bool_to_Prop; auto.
apply succ_lt_mono in H. apply IHn in H.
rewrite ?del_access, ?add_1_l in H; auto.
Qed.

(* Comparison implies coincedence. *)
Lemma eqn_compare n α β :
  eqn (compare n α β) α β.
Proof.
remember (compare n α β) as k.
revert Heqk; revert n α β. induction k; intros n α β Hk i Hi. omega.
revert Hk. destruct n; simpl. discriminate. intros.
destruct (α 0 =? β 0) eqn:E; bool_to_Prop; try discriminate.
injection Hk; intros. apply IHk in H. destruct (eq_nat_dec i 0); subst; auto.
replace i with (1 + (i - 1)) by omega. apply H; omega.
Qed.

End Compare.

(* Facts about properties of sequence elements *)
Section SeqProp.

Variable P : nat -> Prop.

Lemma cseq_prop c :
  P c -> forall n, P (c^ω n).
Proof. unfold cseq; intros; auto. Qed.

Lemma pre_prop n α β :
  (forall i, P (α i))
  -> (forall i, P (β i))
  -> (forall i, P (pre n α β i)).
Proof.
intros Hα Hβ i; unfold pre, replace, fill.
destruct (i <? n); auto.
Qed.

End SeqProp.

(* Facts about get (finite start sequence) *)
Section GetStart.

(* Different length prefixes are never equal. *)
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
  (eqn n α (c^ω)) <-> ⟨α;n⟩ = cfseq c n.
Proof.
induction n; simpl; split; auto.
- intros _ i Hi; omega.
- rewrite <-add_1_r; intros H1; apply eqn_leq in H1 as H2.
  apply cons_split. apply H1; omega. apply IHn; auto.
- intros H i Hi; inversion H; subst. destruct (eq_dec i n).
  subst; auto. apply IHn in H2; apply H2; omega.
Qed.

Corollary get_cseq c n :
  ⟨c^ω;n⟩ = cfseq c n.
Proof.
apply get_cseq_eq_cfseq. apply eqn_refl.
Qed.

Lemma get_S_cons α m n s :
  ⟨α;S m⟩ = n :: s -> α m = n.
Proof.
destruct m; simpl; intros; inversion H; auto.
Qed.

End GetStart.

(* Facts about prefix *)
Section Prefix.

(* A prefixed sequence coincides with itself. *)
Lemma eqn_pre n m α β :
  eqn n α (pre (n + m) α β).
Proof.
intros i Hi; unfold pre, replace, fill.
replace (i <? n + m) with true by bool_omega; auto.
Qed.

Corollary eqn_pre_n n α β : eqn n α (pre n α β).
Proof. rewrite <-add_0_r at 2. apply eqn_pre. Qed.

(* Prefix zero elements. *)
Lemma pre0 α β :
  pre 0 α β = β.
Proof.
extensionality n. unfold pre, replace, fill.
replace (n <? 0) with false by bool_omega.
rewrite sub_0_r; auto.
Qed.

(* Access sequence after prefix. *)
Lemma pre_l n m α β :
  (pre (n + S m) α β) n = α n.
Proof.
unfold pre, replace, fill.
replace (n <? n + S m) with true by bool_omega; auto.
Qed.

(* Access prefix. *)
Lemma pre_r n m α β :
  (pre n α β) (n + m) = β m.
Proof.
unfold pre, replace, fill.
replace (n + m <? n) with false by bool_omega.
replace (n + m - n) with m by omega.
auto.
Qed.

Corollary pre_r0 n α β : (pre n α β) n = β 0.
Proof. rewrite <-(add_0_r n) at 2. apply pre_r. Qed.

Lemma pre_get_l n m α β :
  ⟨pre (n + m) α β;n⟩ = ⟨α;n⟩.
Proof.
revert m; induction n; simpl; intros; auto.
replace (S (n + m)) with (n + S m) by omega.
rewrite pre_l, IHn; auto.
Qed.

(* Get prefixed elements. *)
Lemma pre_get n m α β :
  ⟨pre n α β;n + m⟩ = ⟨β;m⟩ ++ ⟨α;n⟩.
Proof.
revert n; induction m; simpl; intros.
- rewrite add_0_r. rewrite <-(add_0_r n) at 2. rewrite pre_get_l; auto.
- replace (n + S m) with (S (n + m)) by omega; simpl. rewrite <-IHm.
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

Lemma in_map_iota {T} (f : nat -> T) k n m x :
  n <= k < n + m -> x = f k -> In x (map f (iota n m)).
Proof.
revert n; induction m; intros; simpl. omega.
destruct (eq_nat_dec n k); subst; auto.
right; apply IHm; auto. omega.
Qed.

Corollary in_map_range {T} (f : nat -> T) k n x :
  k <= n -> x = f k -> In x (map f (0..n)).
Proof. intros; apply in_map_iota with (k0:=k). omega. auto. Qed.

End IotaRange.
