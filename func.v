(* Functions *)

From intuitionism Require Import lib set seq spr fan.

(* A well defined function from A to B. *)
Definition well_defined A B (f : dom A -> dom B) :=
  ∀α, α ∈ A -> f α ∈ B.

(* Strong converse of a = b -> f a = f b. *)
Definition strong_extensional A B (f : dom A -> dom B) :=
  ∀α β, α ∈ A -> β ∈ A -> f α # f β -> α # β.

(* Classic injective function. *)
Definition weak_injective A B (f : dom A -> dom B) :=
  ∀a α, a ∈ A -> α ∈ A -> f a = f α -> a = α.

(* Strong injective function. *)
Definition injective A B (f : dom A -> dom B) :=
  ∀a α, a ∈ A -> α ∈ A -> a # α -> f a # f α.

(* Surjective function. *)
Definition surjective A B (f : dom A -> dom B) :=
  ∀β, β ∈ B -> ∃α, α ∈ A /\ f α = β.

(* An injective and surjective function is bijective. *)
Definition bijective A B f := injective A B f /\ surjective A B f.

(* Notation for 'there exists an injective mapping from A to B'. *)
Definition preceq A B f := well_defined A B f /\ injective A B f.
Notation "A ≼ B" := (∃f, preceq A B f) (at level 50).
Notation "A ⋠ B" := (~(A ≼ B)) (at level 50).

(* Notation for 'there exists an extensional injective mapping from A to B'. *)
Definition preceqext A B f := preceq A B f /\ strong_extensional A B f.
Notation "A ≼' B" := (∃f, preceqext A B f) (at level 50).

(* Notation for 'there exists a one-to-one mapping between A and B'. *)
Definition equivalent A B := ∃f, well_defined A B f /\ bijective A B f.
Notation "A === B" := (equivalent A B) (at level 50).

(* Definition of denumerable and uncountable sets. *)
Definition denumerable A := Nat === A.
Definition uncountable A := ∀f, well_defined Nat A f -> ~surjective Nat A f.

(* A definition of infinity without natural numbers by Dedekind. *)
Definition Dedekind_infinite A :=
  ∃x f, x ∈ A /\ well_defined A A f /\ injective A A f /\ ∀y, f y # x.

Theorem injective_weaken A B f :
  injective A B f -> weak_injective A B f.
Proof.
intros H a α Ha Hα Hf. apply apart_spec; intros P.
apply H in P; auto. apply apart_spec in P; auto.
Qed.

Theorem seq_uncountable :
  uncountable Seq.
Proof.
intros f f_wd f_surj.
pose(γ (n : nat) := f n n + 1).
assert(P: γ ∈ Seq). apply I.
apply f_surj in P as [n [Hn Hf]].
apply equal_f with (x:=n) in Hf.
unfold γ in Hf. lia.
Qed.

(*
The following is a formalization of the fact that FSeq is denumerable and that
Seq and Bin are equivalent. Although both are quite straightforward on paper,
the formal proofs require quite a number of definitions and lemmas.
*)
Require Import Coq.PArith.BinPosDef.
Import Pnat.

(*
All finite sequences are denumerable. We translate finite sequences to a binary
sequence (of type positive) and encode this as a number rather than using prime
factorization (which is often used in mathematics).
*)
Section FSeqDenumerable.

(* Process xI as S and xO/xH as separator. *)
Fixpoint pos_to_fseq (p : positive) (acc : nat) : fseq :=
  match p with
  | xI q => pos_to_fseq q (S acc)
  | xO q => acc :: pos_to_fseq q 0
  | xH => [acc]
  end.

(* Prepend n 1 bits before p. *)
Fixpoint repeat_xI n p :=
  match n with
  | 0 => p
  | S m => xI (repeat_xI m p)
  end.

(* Inverse of pos_to_fseq (injective for s <> []). *)
Fixpoint fseq_to_pos (s : fseq) :=
  match s with
  | [] => xH
  | [n] => repeat_xI n xH
  | n :: t => repeat_xI n (xO (fseq_to_pos t))
  end.

Definition nat_to_fseq n :=
  if n =? 0 then [] else pos_to_fseq (Pos.of_nat n) 0.

Definition fseq_to_nat s :=
  if length s =? 0 then 0 else Pos.to_nat (fseq_to_pos s).

Lemma pos_to_fseq_nil p acc :
  pos_to_fseq p acc <> [].
Proof.
revert acc; induction p; simpl; intros.
apply IHp. easy. easy.
Qed.

Lemma pos_to_fseq_neq p tl acc n :
  acc :: tl <> pos_to_fseq p (acc + S n).
Proof.
revert n; induction p; simpl; intros.
1: replace (S (acc + S n)) with (acc + (S (S n))) by lia; apply IHp.
all: intros H; injection H; lia.
Qed.

Corollary pos_to_fseq_neq_S p tl acc : acc :: tl <> pos_to_fseq p (S acc).
Proof. rewrite <-add_1_r; apply pos_to_fseq_neq. Qed.

Lemma pos_to_fseq_weak_inj p q acc :
  pos_to_fseq p acc = pos_to_fseq q acc -> p = q.
Proof.
revert p acc; induction q; simpl; intros; destruct p; simpl in H.
- replace q with p. easy. eapply IHq; apply H.
- exfalso; eapply pos_to_fseq_neq_S. apply H.
- exfalso; eapply pos_to_fseq_neq_S. apply H.
- exfalso; eapply pos_to_fseq_neq_S. symmetry; apply H.
- replace q with p. easy. eapply IHq. injection H; intros E; apply E.
- injection H; intros. exfalso; eapply pos_to_fseq_nil. symmetry; apply H0.
- exfalso; eapply pos_to_fseq_neq_S. symmetry; apply H.
- injection H; intros. exfalso; eapply pos_to_fseq_nil. apply H0.
- easy.
Qed.

Lemma nat_to_fseq_weak_inj :
  weak_injective Nat FSeq nat_to_fseq.
Proof.
intros m n _ _. unfold nat_to_fseq. destruct m, n; auto.
- cbn; intros; exfalso; eapply pos_to_fseq_nil. symmetry; apply H.
- cbn; intros; exfalso; eapply pos_to_fseq_nil. apply H.
- replace (S m =? 0) with false by easy; replace (S n =? 0) with false by easy.
  intros; apply pos_to_fseq_weak_inj in H. now apply Nat2Pos.inj.
Qed.

Lemma pos_to_fseq_repeat_xI_xH m n :
  pos_to_fseq (repeat_xI m xH) n = [m + n].
Proof.
revert n; induction m; simpl; intros; auto.
rewrite IHm. now replace (m + S n) with (S (m + n)) by lia.
Qed.

Lemma pos_to_fseq_repeat_xI_xO m n p :
  pos_to_fseq (repeat_xI m (xO p)) n = (m + n) :: pos_to_fseq p 0.
Proof.
revert n; induction m; simpl; intros; auto.
rewrite IHm. now replace (m + S n) with (S (m + n)) by lia.
Qed.

Lemma pos_to_fseq_inv s :
  s <> [] -> pos_to_fseq (fseq_to_pos s) 0 = s.
Proof.
induction s; simpl. easy. destruct s.
- now rewrite pos_to_fseq_repeat_xI_xH, add_0_r.
- rewrite pos_to_fseq_repeat_xI_xO, add_0_r. rewrite IHs; easy.
Qed.

Lemma nat_to_fseq_involutive s :
  nat_to_fseq (fseq_to_nat s) = s.
Proof.
destruct s. easy. unfold nat_to_fseq, fseq_to_nat.
replace (length _ =? 0) with false by easy.
edestruct Pos2Nat.is_succ; rewrite H at 1.
replace (S _ =? 0) with false by easy; clear H x.
rewrite Pos2Nat.id. now apply pos_to_fseq_inv.
Qed.

Theorem fseq_denumerable :
  denumerable FSeq.
Proof.
exists nat_to_fseq; split. easy. split.
- intros n m nN mN Hnm. simpl in *; unfold dec_apart in *.
  intros H; apply Hnm. apply nat_to_fseq_weak_inj; auto.
- intros s _. exists (fseq_to_nat s); split.
  apply I. apply nat_to_fseq_involutive.
Qed.

End FSeqDenumerable.

(*
It is possible to construct an injection from Seq (Baire space) to
Bin (Cantor space). We use the same scheme as in the previous part, but without
the positive type (which we needed to encode and decode nat).
*)
Module SeqToBin.

(*
We determine the n-th value by counting down starting with i = 0 where i
tracks the next index of α to check. The difference with fseq_to_pos is that we
always start with 0 (this makes the algorithm simpler). To avoid a custom
termination proof we count down one by one in c.
*)
Fixpoint f i c α n :=
  match c with
  | 0 =>
    (* separator *)
    match n with
    | 0 => 0
    | S n' =>  f (S i) (α i) α n'
    end
  | S c' =>
    (* counting down *)
    match n with
    | 0 => 1
    | S n' => f i c' α n'
    end
  end.

Lemma f_wd i c α :
  f i c α ∈ Bin.
Proof.
intros m; simpl. induction m; simpl; auto. repeat bool_to_Prop; auto. clear IHm.
revert i c; induction m; simpl; intros; destruct c; try lia; apply IHm.
Qed.

(* Skip n numbers in the image of α. *)
Definition skipn n α := n + fold_right add 0 ⟨α;n⟩.

(* Count zeros in the first n elements of α. *)
Fixpoint count n α := fold_right (λ b j, if b =? 0 then S j else j) 0 ⟨α;n⟩.

(* If α and β are first apart at n, their image is apart at: *)
Definition apart_at (α β : seq) n := skipn n α + (1 + min (α n) (β n)).

Lemma f_count_down α i n k : f i (α n) α (α n + k) = f i 0 α k.
Proof. induction (α n); simpl; auto. Qed.

Lemma skipn_S α n : skipn (S n) α = skipn n α + 1 + α n.
Proof. unfold skipn; simpl. lia. Qed.

Lemma skipn_f α m n :
  f 0 0 α (skipn m α + n) = f m 0 α n.
Proof.
revert n; induction m; intros. easy. rewrite skipn_S; simpl.
replace (skipn m α + 1 + α m + n) with (skipn m α + (1 + (α m + n))) by lia.
rewrite IHm; simpl. now rewrite f_count_down.
Qed.

Lemma different_at α β n k :
  β n = α n + S k -> f n 0 α (1 + α n) <> f n 0 β (1 + α n).
Proof.
simpl. intros R; rewrite R; clear R.
induction (α n); simpl; auto.
Qed.

Lemma f_inj α β n :
  eqn n α β -> α n <> β n -> exists m, f 0 0 α m <> f 0 0 β m.
Proof.
intros H1 H2; exists (apart_at α β n); unfold apart_at.
assert(R: skipn n α = skipn n β).
{ unfold skipn. now replace ⟨β;n⟩ with ⟨α;n⟩ by (now apply eqn_eq_get). }
rewrite skipn_f, R, skipn_f. destruct (min_dec (α n) (β n)); rewrite e.
- apply different_at with (k:=β n - α n - 1). lia.
- apply neq_sym. apply different_at with (k:=α n - β n - 1). lia.
Qed.

Lemma count_shift α n :
  count n (f 0 0 α) = S (count (n - (1 + α 0)) (f 0 0 (del 1 α))).
Proof.
Admitted.

Lemma f_del1_sub α n :
  1 + α 0 <= n -> f 0 0 α n = f 0 0 (del 1 α) (n - (1 + α 0)).
Proof.
Admitted.

Lemma f_del1_add α n :
  f 0 0 (del 1 α) n = f 0 0 α (n + (1 + α 0)).
Proof.
Admitted.

Lemma f_ext_eq0 α β n N :
  eqn n (f 0 0 α) (f 0 0 β) ->
  N = pred (count n (f 0 0 α)) ->
  α N = β N -> α 0 = β 0.
Proof.
Admitted.

Lemma f_ext_base α β n :
  pred (count n (f 0 0 α)) = 0 -> α 0 = β 0 -> f 0 0 α n = f 0 0 β n.
Proof.
Admitted.

Lemma f_ext_contra α n :
  pred (count n (f 0 0 α)) > 0 -> n > α 0.
Proof.
Admitted.

Lemma f_ext (α β : dom Seq) n :
  eqn n (f 0 0 α) (f 0 0 β) -> f 0 0 α n <> f 0 0 β n -> α # β.
Proof.
intros Heq Hneq. exists (pred (count n (f 0 0 α))).
intros H; apply Hneq; clear Hneq.
remember (pred (count n (f 0 0 α))) as N eqn:C.
revert C H Heq; revert α β n. induction N; intros.
- now apply f_ext_base.
- (* Induction by shifting α and β. *)
  assert(R: α 0 = β 0). { eapply f_ext_eq0. apply Heq. apply C. easy. }
  destruct (le_dec (1 + α 0) n).
  + replace (f 0 0 α n) with (f 0 0 (del 1 α) (n - (1 + α 0))).
    replace (f 0 0 β n) with (f 0 0 (del 1 β) (n - (1 + α 0))).
    apply IHN.
    * rewrite count_shift in C; simpl in C. simpl; rewrite  <-C. easy. 
    * unfold del; now rewrite add_1_l.
    * intros m Hm. rewrite ?f_del1_add, ?add_assoc, <-R. apply Heq. lia.
    * rewrite R; symmetry; apply f_del1_sub. now rewrite <-R.
    * symmetry; now apply f_del1_sub.
  + (* Yields a contradiction with C. *)
    exfalso; apply n0. apply f_ext_contra. rewrite <-C; lia.
Qed.

End SeqToBin.

Theorem bin_preceq_seq :
  Bin ≼' Seq.
Proof.
pose(f (α : seq) := α). exists f; repeat split.
intros α β Hα Hβ. now unfold f. easy.
Qed.

Theorem seq_preceq_bin :
  Seq ≼' Bin.
Proof.
exists (SeqToBin.f 0 0); repeat split.
- intros α _. apply SeqToBin.f_wd.
- intros α β _ _ H.
  apply epsilon_smallest in H as [n [H1n H2n]]. 2: intros; apply neq_dec.
  apply SeqToBin.f_inj with (n:=n); auto.
  intros m Hm. apply H2n in Hm; lia.
- intros α β _ _ H.
  apply epsilon_smallest in H as [n [H1n H2n]]. 2: intros; apply neq_dec.
  apply SeqToBin.f_ext with (n:=n); auto.
  intros m Hm. apply H2n in Hm; lia.
Qed.
