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

(* All finite sequences are denumerable. *)
Require Import Coq.PArith.BinPosDef.
Section FSeqDenumerable.

(* Process xI as S and xO/xH as separator. *)
Fixpoint pos_to_fseq (p : positive) (acc : nat) : fseq :=
  match p with
  | xI q => pos_to_fseq q (S acc)
  | xO q => acc :: pos_to_fseq q 0
  | xH => [acc]
  end.

(* Prepend n 1 bits before p. *)
Fixpoint prepend_ones n p :=
  match n with
  | 0 => p
  | S m => prepend_ones m (xI p)
  end.

(* Inverse of pos_to_fseq. *)
Fixpoint fseq_to_pos (s : fseq) :=
  match s with
  | n :: t => prepend_ones n (xO (fseq_to_pos t))
  | [] => xH
  end.

Definition nat_to_fseq n :=
  if n =? 0 then [] else pos_to_fseq (Pos.of_nat n) 0.

Definition fseq_to_nat s :=
  if length s =? 0 then 0 else Pos.to_nat (fseq_to_pos s).

Lemma nat_to_fseq_weak_inj :
  weak_injective Nat FSeq nat_to_fseq.
Proof.
Admitted.

Lemma fseq_to_nat_inv s :
  nat_to_fseq (fseq_to_nat s) = s.
Proof.
Admitted.

Theorem fseq_denumerable :
  denumerable FSeq.
Proof.
(* The classic approach is to use prime factorization. *)
exists nat_to_fseq; split. easy. split.
- intros n m nN mN Hnm. simpl in *; unfold dec_apart in *.
  intros H; apply Hnm. apply nat_to_fseq_weak_inj; auto.
- intros s _. exists (fseq_to_nat s); split.
  apply I. apply fseq_to_nat_inv.
Qed.

End FSeqDenumerable.

(*
It is possible to construct an injection from Seq (Baire space) to
Bin (Cantor space) and vice versa.
*)
Section InjSeqBin.

(* Trivial direction *)
Theorem bin_preceq_seq :
  Bin ⪯' Seq.
Proof.
pose(f (α : seq) := α). exists f; repeat split.
intros α β Hα Hβ. now unfold f. easy.
Qed.

(* Hard direction *)
Fixpoint pos_to_list (p : positive) :=
  match p with
  | xI q => 1 :: pos_to_list q
  | xO q => 0 :: pos_to_list q
  | xH => [1]
  end.

Definition seq_to_bin α n := nth n (rev (pos_to_list (fseq_to_pos ⟨α;n⟩))) 0.

Theorem seq_preceq_bin :
  Seq ⪯' Bin.
Proof.
exists seq_to_bin; repeat split.
- intros α Hα. admit.
- intros α β _ _ Hαβ.
  apply epsilon_smallest in Hαβ as [n Hn].
  (* We then find the first location at which the image is apart. *)
  admit. admit.
- admit.
Admitted.

End InjSeqBin.
