(* Finite and infinite sequences *)

Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Import Nat.
Import ListNotations.
Export Coq.Lists.List.

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
Definition con n (α β : seq) := forall i, i < n -> α i = β i.

(* Apartness relation. *)
Definition apart (α β : seq) := exists n, α n <> β n.

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

Notation "c '..'" := (cseq c)(at level 10, format "c '..'").
Notation "α '#' β" := (apart α β)(at level 50, format "α '#' β").
Notation "'⟨' α ';' n '⟩'" := (get n α)(at level 0, format "'⟨' α ';' n '⟩'").
Notation "s '⊏' α" := (starts s α)(at level 50).

Lemma app_split (a b x y : fseq) : a = b -> x = y -> a ++ x = b ++ y.
Proof. intros; subst; auto. Qed.

(* A sequence coincides with itself. *)
Lemma con_id n α : con n α α.
Proof. intros i; auto. Qed.

(* A smaller part of a coincedence also coincides. *)
Lemma con_leq n m α β : con (n + m) α β -> con n α β.
Proof. intros H i Hi; apply H; omega. Qed.

(* Delete part of a coincedence. *)
Lemma con_del n m α β :
  con (n + m) α β <-> con n α β /\ con m (del n α) (del n β).
Proof.
split; unfold del; simpl.
- intros H; split. eapply con_leq; apply H.
  intros i Hi; apply H; omega.
- intros [H1 H2] i Hi. assert(C: i < n \/ i >= n). omega.
  destruct C. apply H1; auto. assert(R: i = (i - n) + n). omega.
  rewrite R; apply H2; omega.
Qed.

(* α and β coincide iff their first n elements are the same. *)
Lemma con_eq_get n α β :
  con n α β <-> ⟨α;n⟩ = ⟨β;n⟩.
Proof.
revert α β; induction n; simpl; intros; split; auto.
- intros _ i Hi; omega.
- intros H; rewrite H; auto. rewrite (proj1 (IHn α β)); auto.
  intros i Hi; apply H; auto.
- intros H i Hi. destruct (eq_dec i n).
  + subst; inversion_clear H; auto.
  + apply IHn; try omega; inversion_clear H; auto.
Qed.

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
assert(R: m + S n = S m + n). omega.
rewrite R; auto.
Qed.

(* Deletion and append *)
Lemma del_app_distr n m α :
  ⟨α;n + m⟩ = ⟨del n α;m⟩ ++ ⟨α;n⟩.
Proof.
revert α. induction n, m; simpl; intros; auto.
- rewrite del0, app_nil_r; auto.
- rewrite add_0_r; auto.
- assert(Split: forall x y (v w : fseq), x = y -> v = w -> x :: v = y :: w).
  { intros; subst; auto. } apply Split.
  + unfold del. assert(R: n + S m = m + S n). omega. auto.
  + assert(R: forall x (v w : fseq), v ++ x :: w = (v ++ [x]) ++ w).
    { intros; induction v; simpl; auto. }
    rewrite R, del_app_S, <-IHn; auto.
Qed.

(* Different length parts are never equal. *)
Lemma get_neq n m α β :
  n <> m -> ⟨α;n⟩ <> ⟨β;m⟩.
Proof.
Admitted.

(* Get finite part of a partially constant sequence. *)
Lemma get_cseq_eq_cfseq c n α :
  (con n α (c..)) <-> ⟨α;n⟩ = cfseq c n.
Proof.
Admitted.

(* A prepended sequence coincides with itself. *)
Lemma con_prepend n α β :
  con n α (prepend n α β).
Proof.
intros i Hi; unfold prepend, replace, fill.
apply ltb_lt in Hi; rewrite Hi; auto.
Qed.

(* Access elements after prepend *)
Lemma prepend_access n m α β :
  prepend n α β (n + m) = β m.
Proof.
unfold prepend, replace, fill.
assert(R1: n + m <? n = false). apply ltb_ge; omega.
assert(R2: n + m - n = m). omega.
rewrite R1, R2; auto.
Qed.
