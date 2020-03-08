(* Some contradictory results in classical mathematics. *)

From intuitionism Require Import lib set seq spr fan func.

(* Principle of Omniscience, or the Law of the Excluded Middle *)
Definition LEM := ∀P, P \/ ~P.

(* Limited Principle of Omniscience *)
Definition LPO := ∀(α : seq), (∃n, α n <> 0) \/ (∀n, α n = 0).

(* Lesser Limited Principle of Omniscience *)
Definition LLPO := ∀(α : seq),
  (∀k, ((∀i, i < k -> α i = 0) /\ α k <> 0) -> Even k) \/
  (∀k, ((∀i, i < k -> α i = 0) /\ α k <> 0) -> Odd k).

(* Markov's Principle; a weaker version of LPO. *)
Definition MarkovsPrinciple := ∀α : seq, ~(∀n, α n = 0) -> ∃n, α n <> 0.

(*
Some statements do not directly imply LPO or LLPO, yet intuitionists still do
not want to consider them as true. In particular these are statements that can
prove properties about a number which is still unknown to mathematics and that
might not even exist at all. An example is the length of the first cycle in a
a Collatz sequence that does not contain 1, or the first position at which the
decimal expansion of π contains 99 consecutive nines. This notion is embodied by
Recklessness; a weaker version of LLPO.
*)
Definition Recklessness := ∀α, ~(∀n, α n = 0) ->
  (∀k, ((∀i, i < k -> α i = 0) /\ α k <> 0) -> Even k) \/
  (∀k, ((∀i, i < k -> α i = 0) /\ α k <> 0) -> Odd k).

(* A definition of infinity without numbers by Dedekind. *)
Definition Dedekind_infinite A := ∃x f,
  x isin A /\ well_defined A A f /\ injective A A f /\ ∀y, f y # x.

(* LEM is as least as strong as LPO. *)
Theorem lem_lpo :
  LEM -> LPO.
Proof.
intros PO α; destruct (PO (∃n, α n <> 0)). left; auto.
right; intros n; destruct (eq_dec (α n) 0); auto.
exfalso; apply H; exists n; auto.
Qed.

Lemma neq0_dec (α : seq) n : {α n <> 0} + {~(α n <> 0)}.
Proof. intros; destruct (eq_dec (α n) 0). right; lia. left; lia. Qed.

Lemma nat_nltgt_eq n m : ~(n < m) -> ~(n > m) -> n = m.
Proof. lia. Qed.

Lemma even_false_odd n : even n = false -> Odd n.
Proof. intros; apply odd_spec; unfold odd; rewrite H; auto. Qed.

(* LPO is as least as strong as LLPO. *)
Theorem lpo_llpo :
  LPO -> LLPO.
Proof.
intros LPO α. destruct (LPO α).
- destruct (epsilon_smallest _ (neq0_dec α) H) as [l [L1 L2]].
  destruct (even l) eqn:E.
  1: apply even_spec in E; left.
  2: apply even_false_odd in E; right.
  all: intros k [H1 H2]; replace k with l; auto.
  all: apply nat_nltgt_eq; intros P.
  all: try apply L2 in P; auto.
  all: try apply H1 in P; auto.
- left; intros k [H1 H2]; exfalso; auto.
Qed.

(* LPO is as least as strong as Markov's Principle. *)
Theorem lpo_markov :
  LPO -> MarkovsPrinciple.
Proof.
intros LPO α H. destruct (LPO α).
- destruct H0 as [n Hn]; exists n; auto.
- exfalso; apply H; auto.
Qed.

(* Markov's Principle is reckless. *)
Theorem markov_reckless :
  MarkovsPrinciple -> Recklessness.
Proof.
intros SR α Hα. apply (SR α) in Hα.
assert(n0 := epsilon_smallest _ (neq0_dec α) Hα);
destruct n0 as [n0 [H1 H2]]; destruct (even n0) eqn:E.
1: apply even_spec in E; left.
2: apply even_false_odd in E; right.
all: intros n [Hn1 Hn2]; replace n with n0; auto.
all: apply nat_nltgt_eq; intros P.
all: try apply H2 in P; auto.
all: apply Hn1 in P; rewrite H1 in P; discriminate.
Qed.

(* Some results related to apartness of sequences. *)
Section Apartness.

(* Under LPO sequence apartness is equivalent to inequality. *)
Theorem lpo_neq_seq_apart α β :
  LPO -> α <> β -> seq_apart α β.
Proof.
(* Define a sequence which is non-zero where α anb β are not equal. *)
pose(γ n := if α n =? β n then 0 else 1).
assert(Hγ: ∀n, γ n = 0 -> α n = β n).
{ unfold γ; intros n. destruct (α n =? β n) eqn:H; bool_lia. }
intros LPO H; destruct (LPO γ) as [[n Hn]|Hn].
- exists n; intros P; revert Hn; unfold γ.
  replace (α n =? β n) with true by bool_lia; auto.
- exfalso; apply H; extensionality n. apply Hγ; auto.
Qed.

(* If sequence inequality implies apartness, then we have Markov's Principle. *)
Theorem neq_seq_apart_markov :
  (∀α β, α <> β -> seq_apart α β) -> MarkovsPrinciple.
Proof.
intros H α Hα. assert(αneq0: α <> (0^ω)).
- intros P; apply Hα; rewrite P; auto.
- apply H in αneq0 as [n Hn]. exists n; auto.
Qed.

(* If weak injective is strong injective, then we have Markov's Principle. *)
Theorem weak_injective_strong_markov :
  (∀A B f, weak_injective A B f -> injective A B f) -> MarkovsPrinciple.
Proof.
intros WIS α Hα.
(* A weakly injective function s.t. strong injectivity proves the goal *)
pose(f (b : bool) := if b then α else (0^ω)).
assert(weak_inj: weak_injective Bool Seq f).
{ intros a b _ _ H. destruct a, b; auto; exfalso; apply Hα; intros.
  all: simpl in H; eapply equal_f in H; unfold cseq in H.
  apply H. symmetry; apply H. }
assert(apartness: @apart Bool true false).
{ simpl; unfold dec_apart. discriminate. }
apply WIS in weak_inj as inj.
apply inj in apartness; auto; apply I.
Qed.

End Apartness.

(* Apply f n times to x. *)
Fixpoint appn {A} f (x : A) n :=
  match n with 0 => x | S m => f (appn f x m) end.

Lemma appn_isin {A : aset} x f n :
  x isin A -> well_defined A A f -> appn f x n isin A.
Proof. intros; induction n; simpl; auto. Qed.

Lemma appn_apart {A : aset} x f m n :
  x isin A -> well_defined A A f -> injective A A f -> (∀y, f y # x) ->
  appn f x n # appn f x (n + S m).
Proof.
intros; induction n; simpl; auto; intros.
- induction m; simpl; apply apart_sym; auto.
- apply H1; auto; apply appn_isin; auto.
Qed.

(* If A is Dedekind infinite, then A is as least as big as Nat. *)
Theorem dedekind_ω_inifinite A :
  Dedekind_infinite A -> Nat >-> A.
Proof.
intros [x [f [Ax [f_wd [f_inj f_y]]]]].
(* We define an injection by repeated application of f. *)
exists (appn f x); split.
- intros n _. clear f_y; revert Ax; revert x. induction n; simpl; auto.
- intros n m _ _. simpl; intros Hnm. apply not_eq in Hnm; destruct Hnm.
  replace m with (n + S (m - n - 1)) by lia; now apply appn_apart.
  apply apart_sym. replace n with (m + S (n - m - 1)) by lia;
  now apply appn_apart.
Qed.

(* A classic proof for the Cantor-Schröder-Bernstein theorem. *)
(* www.cs.cornell.edu/courses/cs2800/2017fa/lectures/lec14-cantor.html *)
Module SchröderBernstein.
Section Proof.

Variable A B : aset.
Variable f : dom A -> dom B.
Variable g : dom B -> dom A.
Variable f_wd : well_defined A B f.
Variable g_wd : well_defined B A g.
Variable f_inj : injective A B f.
Variable g_inj : injective B A g.

(* y in B is a chain bottom (there is no x in A s.t. f x = y). *)
Definition Bbot y := ∀x, x isin A -> f x # y.

(* Chain c connects x to y backwards. *)
Fixpoint Bchain x c y :=
  match c with
  | [] => g y = x
  | (a, b) :: cc => g b = x /\ f a = b /\ Bchain a cc y
  end.

(* Get inverse of x given that (Bchain x c y). *)
Definition g_inv (c : list (dom A * dom B)) y := hd y (map snd c).

(* x is in a chain with a bottom in B. *)
Definition in_Bchain x := {y : dom B & Bbot y & {c | Bchain x c y}}.

(* positive negation of in_Bchain. *)
Definition notin_Bchain x := forall y, Bbot y -> forall c, ~Bchain x c y.

(* We need to decide the chain type for any x. *)
Inductive chain_type x :=
  | ChainTypeA (H : notin_Bchain x)
  | ChainTypeB (H : in_Bchain x).

(* We need to be able to decide the chain type. This is stronger than LEM. *)
Variable in_Bchain_dec : forall x, chain_type x.

(* We define the bijective function h using in_Bchain_dec. *)
Definition h x :=
  match in_Bchain_dec x with
  | ChainTypeA _ _ => f x
  | ChainTypeB _ (existT2 _ _ y _ (exist c _)) => g_inv c y
  end.

Theorem h_wd :
  well_defined A B h.
Proof.
Admitted.

Theorem h_inj :
  injective A B h.
Proof.
Admitted.

Theorem h_surj :
  surjective A B h.
Proof.
Admitted.

Corollary A_equiv_B : A ≡ B.
Proof. exists h; repeat split. apply h_wd. apply h_inj. apply h_surj. Qed.

End Proof.
End SchröderBernstein.
