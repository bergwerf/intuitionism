(* Choice functions *)

From intuitionism Require Import lib set seq spr fan func bcp.

(* Choice with an upper-bound in nat *)
Theorem nat_lt_choice {W} N (P : nat -> W -> Prop) (inhabitant : W) :
  (∀n, n < N -> ∃m, P n m) -> ∃f, ∀n, n < N -> P n (f n).
Proof.
intros H; induction N. now exists (λ _, inhabitant).
destruct IHN as [f Hf]. intros; apply H; auto.
destruct (H N) as [m Hm]; auto.
exists (λ n, if n =? N then m else f n); intros n Hn.
inversion_clear Hn. now rewrite eqb_refl.
replace (n =? N) with false by bool_lia. apply Hf; auto.
Qed.

(* Choice for a lists *)
Section ListChoice.

Variable W : Type.
Variable inhabitant : W.

Section General.

Variable T : Type.
Variable P : T -> W -> Prop.
Variable eq_T : T -> T -> bool.
Variable eq_T_ext : ∀x y, eq_T x y = true <-> x = y.

Theorem list_choice s :
  (∀x, In x s -> ∃w, P x w) -> ∃f, ∀x, In x s -> P x (f x).
Proof.
intros H; induction s. now exists (λ _, inhabitant).
destruct IHs as [f Hf]. intros x Hx. apply H; now right.
destruct (H a) as [w Hw]. apply in_eq.
exists (λ x, if eq_T a x then w else f x); intros x Hx.
inversion_clear Hx. apply eq_T_ext in H0 as R; subst; now rewrite R.
destruct (eq_T a x) eqn:E. apply eq_T_ext in E. now subst. auto.
Qed.

End General.

(* Choice for finite sequences *)
Corollary fseq_choice (P : nat -> W -> Prop) (s : fseq) :
  (∀n, In n s -> ∃w, P n w) -> ∃f, ∀n, In n s -> P n (f n).
Proof. apply list_choice with (eq_T:=eqb). split; intros; bool_lia. Qed.

(* Choice for lists of finite sequences *)
Corollary fseq_list_choice (P : fseq -> W -> Prop) (b : list fseq) :
  (∀s, In s b -> ∃w, P s w) -> ∃f, ∀s, In s b -> P s (f s).
Proof.
apply list_choice with (eq_T:=list_beq _ eqb). split; intros.
- apply internal_list_dec_bl with (eq_A:=eqb); auto. intros; bool_lia.
- apply internal_list_dec_lb with (eq_A:=eqb); auto. intros; bool_lia.
Qed.

End ListChoice.
