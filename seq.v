(* Finite and infinite sequences *)

Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Omega.
Import Nat.
Import ListNotations.
Export Coq.Lists.List.

(* Infinite sequence *)
Notation "'seq'" := (nat -> nat).

(* Finite sequence *)
Notation "'fseq'" := (list nat).

(* Infinite constant sequence *)
Definition cseq (c i : nat) := c.

(* Finite constant sequence *)
Definition cfseq (c n : nat) := repeat c n.

(* The first n elements of α and β coincide. *)
Definition con n (α β : seq) := forall i, i < n -> α i = β i.

(* Apartness relation. *)
Definition apart (α β : seq) := exists n, α n <> β n.

(* Shift a sequence n elements forward. *)
Definition shift n (α : seq) i := α (i - n).

(* Overwrite the first n elements of α with β. *)
Definition replace n (α β : seq) i := if i <? n then β i else α i.

(* Prepend first n elements of α to β. *)
Definition prepend n α β := replace n (shift n β) α.

(* Check if α starts with s. *)
Fixpoint starts s (α : seq) := 
  match s with
  | [] => True
  | s0 :: t => α 0 = s0 /\ starts t (shift 1 α)
  end.

(* Get first n elements of α. *)
Fixpoint get n (α : seq) : fseq :=
  match n with
  | 0 => []
  | S m => (α 0) :: (get m (shift 1 α))
  end.

Notation "α '#' β" := (apart α β) (at level 50, format "α '#' β").
Notation "α '..' n" := (get n α) (at level 10, format "α '..' n").
Notation "s '⊏' α" := (starts s α) (at level 70).

Lemma app_split (a b x y : fseq) : a = b -> x = y -> a ++ x = b ++ y.
Proof. intros; subst; auto. Qed.

(* Shifting withing the coincedence. *)
Lemma con_shift n m α β :
  con (n + m) α β <-> con m (shift n α) (shift n β).
Proof.
Admitted.

(* α and β coincide iff their first n elements are the same. *)
Lemma con_eq_get n α β :
  con n α β <-> α..n = β..n.
Proof.
split; revert α β.
- induction n; simpl; auto; intros.
  erewrite H, IHn; auto; try omega; apply con_shift; auto.
- induction n; simpl; intros. intros i Hi; omega.
  rewrite <-add_1_r, add_comm; apply con_shift, IHn; inversion_clear H; auto.
Qed.

(* Addition distributes over get/shift/append. *)
Lemma add_shift_distr n m α :
  α..(n + m) = α..n ++ (shift n α)..m.
Proof.
Admitted.

(* Different length parts are never equal. *)
Lemma get_neq n m α β :
  n <> m -> α..n <> β..m.
Proof.
Admitted.

(* Get finite part of a partially constant sequence. *)
Lemma get_cseq_eq_cfseq c n α :
  (con n α (cseq c)) <-> α..n = cfseq c n.
Proof.
Admitted.

(* A prepended constant part coincides with a constant sequence. *)
Lemma get_prepend_eq_repeat n c α :
  con n (cseq c) (prepend n (cseq c) α).
Proof.
Admitted.









