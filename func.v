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
Notation "A ⪯ B" := (∃f, preceq A B f) (at level 50).

(* Notation for 'there exists an extensional injective mapping from A to B'. *)
Definition preceqext A B f := preceq A B f /\ strong_extensional A B f.
Notation "A ⪯' B" := (∃f, preceqext A B f) (at level 50).

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
All finite sequences are denumerable. We use binary sequences to encode finite
and infinite sequences rather than using prime factorization (which is often
used in mathematics).
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

Lemma nat_to_fseq_inv s :
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
  apply I. apply nat_to_fseq_inv.
Qed.

End FSeqDenumerable.

(*
It is possible to construct an injection from Seq (Baire space) to
Bin (Cantor space) and vice versa.
*)
Section InjSeqBin.

Theorem bin_preceq_seq :
  Bin ⪯' Seq.
Proof.
pose(f (α : seq) := α). exists f; repeat split.
intros α β Hα Hβ. now unfold f. easy.
Qed.

Fixpoint nth_bit n (p : positive) :=
  match n with
  | 0 =>
    match p with
    | xI _ => 1
    | _ => 0
    end
  | S m =>
    match p with
    | xI q => nth_bit m q
    | xO q => nth_bit m q
    | xH => 0
    end
  end.

Definition seq_to_bin α n := nth_bit n (fseq_to_pos (rev ⟨α;n⟩)).

Lemma neq_dec (n m : nat) : {n <> m} + {~(n <> m)}.
Proof. intros; destruct (eq_dec n m). now right. now left. Qed.

Lemma nth_bit_leq_1 n p : nth_bit n p <= 1.
Proof. revert p; induction n; simpl; destruct p; try lia; apply IHn. Qed.

Lemma seq_to_bin_wd α :
  seq_to_bin α ∈ Bin.
Proof.
intros m; simpl. induction m; simpl; auto. repeat bool_to_Prop; auto.
unfold seq_to_bin. apply nth_bit_leq_1.
Qed.

(* If α and β in Seq are first apart at n, then their image is apart at: *)
Definition to_bin_apart_at (α β : seq) n :=
  fold_right add 0 ⟨α;n⟩ + n + min (α n) (β n).

(* If α and β in Bin are first apart at n, then their pre-image is apart at: *)
Definition to_seq_apart_at (α : seq) n :=
  fold_right (λ bit acc, acc + (1 - bit)) 0 ⟨α;n⟩.

Lemma to_bin_apart_at_works α β n :
  (∀m, m < n -> α m = β m) -> α n <> β n ->
  seq_to_bin α (to_bin_apart_at α β n) <> seq_to_bin β (to_bin_apart_at α β n).
Proof.
Admitted.

Lemma to_seq_apart_at_works α β n :
  (∀m, m < n -> seq_to_bin α m = seq_to_bin β m) ->
  seq_to_bin α n <> seq_to_bin β n ->
  α (to_seq_apart_at α n) <> β (to_seq_apart_at α n).
Proof.
Admitted.

Theorem seq_preceq_bin :
  Seq ⪯' Bin.
Proof.
exists seq_to_bin; repeat split.
- intros α _. apply seq_to_bin_wd.
- intros α β _ _ H.
  apply epsilon_smallest in H as [n [H1n H2n]]. 2: intros; apply neq_dec.
  exists (to_bin_apart_at α β n). apply to_bin_apart_at_works; auto.
  intros. apply H2n in H; lia.
- intros α β _ _ H.
  apply epsilon_smallest in H as [n [H1n H2n]]. 2: intros; apply neq_dec.
  exists (to_seq_apart_at α n). apply to_seq_apart_at_works; auto.
  intros. apply H2n in H; lia.
Qed.

End InjSeqBin.
