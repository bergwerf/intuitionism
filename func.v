(* Functions *)

From intuitionism Require Import lib set seq bcp spr fan.

(* Classic injective function. *)
Definition weak_injective A B (f : dom A -> dom B) :=
  forall a α, a isin A -> α isin A -> f a = f α -> a = α.

(* Strong injective function. *)
Definition injective A B (f : dom A -> dom B) :=
  forall a α, a isin A -> α isin A -> a#α -> f a # f α.

(* Surjective function. *)
Definition surjective A B (f : dom A -> dom B) :=
  forall β, β isin B -> exists α, α isin A /\ f α = β.

Definition bijective A B f := injective A B f /\ surjective A B f.

(* Strong injective implies weak injective. *)
Theorem injective_to_weak A B f :
  injective A B f -> weak_injective A B f.
Proof.
intros H a α Ha Hα Hf. apply apart_spec; intros P.
apply H in P; auto. apply apart_spec in P; auto.
Qed.

(* The set of all sequences is not denumerable. *)
Theorem seqs_uncountable :
  ~exists f, surjective Nat Seq f.
Proof.
intros H; destruct H as [f H].
pose(γ (n : nat) := f n n + 1).
assert(P: γ isin Seq). apply I.
apply H in P as [n [Hn Hf]].
apply equal_f with (x:=n) in Hf.
unfold γ in Hf. lia.
Qed.

Require Import Coq.PArith.BinPosDef.

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

(* The set of all finite sequences is denumerable. *)
Theorem fseq_eq_nat :
  exists f, bijective Nat FSeq f.
Proof.
(* The classic approach is to use prime factorization. *)
exists nat_to_fseq; split.
- intros n m nN mN Hnm. simpl in *; unfold dec_apart in *.
  intros H; apply Hnm. apply nat_to_fseq_weak_inj; auto.
- intros s _. exists (fseq_to_nat s); split.
  apply I. apply fseq_to_nat_inv.
Qed.

Fixpoint pos_to_list (p : positive) :=
  match p with
  | xI q => 1 :: pos_to_list q
  | xO q => 0 :: pos_to_list q
  | xH => [1]
  end.

Definition seq_to_bin α n := nth n (rev (pos_to_list (fseq_to_pos ⟨α;n⟩))) 0.

(*
There exists an injection from the Baire space (natural number sequences) to the
Cantor space (binary sequences). With the Fan Theorem we can later prove that a
bijection is not possible.
*)
Theorem seq_eq_bin :
  exists f, injective Seq Bin f.
Proof.
exists seq_to_bin. intros α β _ _ Hαβ.
(* We need the smallest n at which α an β are apart. *)
(* We then find the first location at which the image is apart. *)
Admitted.
