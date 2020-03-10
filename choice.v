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

(*
We first define an encoding for a continuous choice function f : seq -> nat such
that f is itself continuous.
*)
Section ContinuousChoiceFunction.

Inductive cfun_answer := CFContinue | CFDecide (n : nat).
Record cfun := CFun {
  cfun_σ : fseq -> cfun_answer;
  cfun_terminate : ∀α, ∃n, cfun_σ ⟨α;n⟩ <> CFContinue;
}.

Variable φ : cfun.
Variable α : seq.

Lemma answer_dec :
  ∀n, {cfun_σ φ ⟨α;n⟩ <> CFContinue} + {~(cfun_σ φ ⟨α;n⟩ <> CFContinue)}.
Proof. intros; destruct (cfun_σ φ ⟨α;n⟩). now right. now left. Qed.

Definition cfun_time := epsilon_smallest _ answer_dec (cfun_terminate φ α).
Definition cfun_compute :=
  let n := proj1_sig cfun_time in
  match cfun_σ φ ⟨α;n⟩ with
  | CFDecide k => k
  | CFContinue => 0
  end.

End ContinuousChoiceFunction.

Notation "φ '∣' α" := (cfun_compute φ α) (at level 50, format "φ '∣' α").

Lemma cfun_eqn φ α :
  ∃m, ∀β, eqn m α β -> φ∣α = φ∣β.
Proof.
unfold cfun_compute. destruct (cfun_time φ α) as [Nα [H1 H2]]; simpl.
exists Nα; intros. destruct (cfun_time φ β) as [Nβ [H3 H4]]; simpl.
apply eqn_eq_get in H. replace Nβ with Nα. now rewrite H.
apply eq_dne; intros E. apply not_eq in E as [E|E].
- apply H4 in E; apply E. now rewrite <-H.
- apply eqn_eq_get in H. replace Nα with (Nβ + (Nα - Nβ)) in H by lia.
  apply eqn_leq, eqn_eq_get in H. apply H2 in E; apply E. now rewrite H.
Qed.

(* Choice on continuous sets. *)
Section ContinuousChoice.

Definition AC_10 := ∀(R : seq -> nat -> Prop),
  (∀α, ∃n, R α n) -> ∃φ, ∀α, R α (φ∣α).

Definition AC_11 := ∀(R : seq -> seq -> Prop),
  (∀α, ∃β, R α β) -> ∃Φ, ∀α, R α (λ n, Φ n∣α).

(* AC_11 has a controversial implication. *)
Theorem AC_11_controversy :
  AC_11 -> ~∀α, ∃β, (∀n : nat, α n = 0) <-> ∃n : nat, β n <> 0.
Proof.
intros AC H. apply AC in H as [Φ HΦ].
destruct (proj1 (HΦ (0^ω))) as [n Hn]. easy.
destruct (cfun_eqn (Φ n) (0^ω)) as [m Hm].
pose(β := pre m (0^ω) (1^ω)). assert(Hβ : eqn m (0^ω) β) by apply eqn_pre_n.
apply Hm in Hβ. assert(H: ∃n, Φ n∣β <> 0) by (exists n; lia).
eapply HΦ with(n:=m) in H. unfold β in H.
rewrite pre_r0 in H. discriminate.
Qed.

End ContinuousChoice.
End AxiomsOfChoice.
