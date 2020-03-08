(* Choice functions *)

From intuitionism Require Import lib set seq spr fan func bcp.

(* Choice on finite domains. *)
Section FiniteChoice.

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

(* Choice for lists *)
Section ListChoice.

Variable W : Type.
Variable inhabitant : W.

Section GenericList.

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

End GenericList.

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
End FiniteChoice.

(* Unprovable choice statements. *)
Section AxiomsOfChoice.

(* Choice on countable sets. *)
Section CountableChoice.

Definition AC_00 := ∀(R : nat -> nat -> Prop),
  (∀m, ∃n, R m n) -> ∃f, ∀m, R m (f m).

Definition AC_01 := ∀(R : nat -> seq -> Prop),
  (∀n, ∃α, R n α) -> ∃f, ∀n, R n (f n).

End CountableChoice.

(* Choice on continuous sets. *)
Section ContinuousChoice.

(*
To force a continuous choice function f : seq -> nat to be itself continuous,
we define them in a particular way.
*)
Section ContinuousChoiceFunction.

Inductive answer := wait | ready (n : nat).
Record cfun := CFun {
  ϕ : fseq -> answer;
  ϕ_spec : ∀α, ∃n, ϕ ⟨α;n⟩ <> wait;
}.

Variable φ : cfun.
Variable α : seq.

Lemma answer_dec : ∀n, {ϕ φ ⟨α;n⟩ <> wait} + {~(ϕ φ ⟨α;n⟩ <> wait)}.
Proof. intros; destruct (ϕ φ ⟨α;n⟩). now right. now left. Qed.

(* Given such a function, we compute its answer here. *)
Definition cfun_compute :=
  let Σn := epsilon_smallest _ answer_dec (ϕ_spec φ α) in
  let n := proj1_sig Σn in
  match ϕ φ ⟨α;n⟩ with
  | ready k => k
  | wait => 0
  end.

End ContinuousChoiceFunction.

Notation "φ '∣' α" := (cfun_compute φ α) (at level 50, format "φ '∣' α").

Definition AC_10 := ∀(R : seq -> nat -> Prop),
  (∀α, ∃n, R α n) -> ∃φ, ∀α, R α (φ∣α).

Definition AC_11 := ∀(R : seq -> seq -> Prop),
  (∀α, ∃β, R α β) -> ∃Φ, ∀α, R α (λ n, Φ n∣α).

(* AC_11 has the a controversial implication. *)
Theorem AC_11_controversy :
  AC_11 -> ~∀α, ∃β, (∀n : nat, α n = 0) <-> ∃n : nat, β n <> 0.
Proof.
intros AC H. apply AC in H as [Φ HΦ].
Admitted.

End ContinuousChoice.
End AxiomsOfChoice.
