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
The Equivalence theorem (often called the Cantor–Schröder–Bernstein theorem) for
the sets A and B with strong requirements. A proof that relies on decidability
of the chain type for any x in A is included in this file.
*)
Definition EquivalenceTheorem A B := A ≼ B /\ B ≼ A -> A === B.

(*
Some statements are weaker than the previous principles, yet intuitionists still
do not want to consider them as true. In particular these are statements that
can prove properties about a number which is still unknown to mathematics and
that might not even exist at all. An example is the length of the first cycle in
a a Collatz sequence that does not contain 1, or the first position at which the
decimal expansion of π contains 99 consecutive nines. Such statements are then
called reckless ('vermetel' in Dutch). I do not have a good formalization yet.
*)

(* LEM is equivalent to the principle of double negation. *)
Theorem lem_pdn :
  LEM <-> ∀P, ~~P -> P.
Proof.
split; intros PO P.
intros nnP. now destruct (PO P).
apply PO. apply nnLEM.
Qed.

(* LEM is as least as strong as LPO. *)
Theorem lem_lpo :
  LEM -> LPO.
Proof.
intros PO α; destruct (PO (∃n, α n <> 0)). left; auto.
right; intros n; destruct (eq_dec (α n) 0); auto.
exfalso; apply H; exists n; auto.
Qed.

Lemma even_false_odd n : even n = false -> Odd n.
Proof. intros; apply odd_spec; unfold odd; rewrite H; auto. Qed.

(* LPO is as least as strong as LLPO. *)
Theorem lpo_llpo :
  LPO -> LLPO.
Proof.
intros LPO α. destruct (LPO α).
- apply epsilon_smallest in H as [l [L1 L2]]. 2: intros; apply neq_dec.
  destruct (even l) eqn:E.
  1: apply even_spec in E; left.
  2: apply even_false_odd in E; right.
  all: intros k [H1 H2]; replace k with l; auto.
  all: assert(L: ~(l < k) -> ~(l > k) -> l = k) by lia; apply L; intros H.
  all: auto. all: assert(Hk := L2 k); lia.
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

(* Relation between Dedekind-infinity and ω-infinity. *)
Section DedekindInfinity.

(* Vpply f n times to x. *)
Fixpoint applyn {V} f (x : V) n :=
  match n with 0 => x | S m => f (applyn f x m) end.

Lemma applyn_isin {V : aset} x f n :
  x ∈ V -> well_defined V V f -> applyn f x n ∈ V.
Proof. intros; induction n; simpl; auto. Qed.

Lemma applyn_apart {V : aset} x f m n :
  x ∈ V -> well_defined V V f -> injective V V f -> (∀y, f y # x) ->
  applyn f x n # applyn f x (n + S m).
Proof.
intros; induction n; simpl; auto; intros.
- induction m; simpl; apply apart_sym; auto.
- apply H1; auto; apply applyn_isin; auto.
Qed.

(* If V is Dedekind infinite, then V is as least as big as Nat. *)
Theorem dedekind_ω_inifinite V :
  Dedekind_infinite V -> Nat ≼ V.
Proof.
intros [x [f [Vx [f_wd [f_inj f_y]]]]].
(* We define an injection by repeated application of f. *)
exists (applyn f x); split.
- intros n _. clear f_y; revert Vx; revert x. induction n; simpl; auto.
- intros n m _ _. simpl; intros Hnm. apply not_eq in Hnm; destruct Hnm.
  replace m with (n + S (m - n - 1)) by lia; now apply applyn_apart.
  apply apart_sym. replace n with (m + S (n - m - 1)) by lia;
  now apply applyn_apart.
Qed.

End DedekindInfinity.

(* Some results related to apartness of sequences. *)
Section Apartness.

(* Under LEM apartness is equivalent to inequality. *)
Theorem lem_apart_if_neq {A} (α : dom A) (β : dom A) :
  LEM -> α <> β -> α # β.
Proof.
intros. apply lem_pdn; auto.
intros Hna. now apply apart_spec in Hna.
Qed.

(* Under LPO sequence apartness is equivalent to inequality. *)
Theorem lpo_seq_apart_if_neq α β :
  LPO -> α <> β -> seq_apart α β.
Proof.
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
  all: simpl in H; eapply equal_f in H.
  apply H. symmetry; apply H. }
assert(apartness: @apart Bool true false).
{ simpl; unfold dec_apart. discriminate. }
apply WIS in weak_inj as inj.
apply inj in apartness; auto; apply I.
Qed.

(* We can prove strong extensionality in baire -> baire with LPO. *)
Theorem lpo_strong_extensional (A B : baire) f :
  LPO -> strong_extensional A B f.
Proof.
intros LPO α β Hα Hβ Hαβ. apply lpo_seq_apart_if_neq; auto.
intros H; subst. now apply apart_neq in Hαβ.
Qed.

End Apartness.

(* A classic proof for the Equivalence theorem. *)
(* www.cs.cornell.edu/courses/cs2800/2017fa/lectures/lec14-cantor.html *)
Module EquivThm.
Section EquivThm.

Variable A B : aset.
Variable f : dom A -> dom B.
Variable g : dom B -> dom A.
Variable f_wd : well_defined A B f.
Variable g_wd : well_defined B A g.
Variable g_ext : strong_extensional B A g.
Variable f_inj : injective A B f.
Variable g_inj : injective B A g.

(* Apply (f ∘ g) n times to y. *)
Definition stepn := applyn (λ y, f (g y)).

(* y in B is a chain bottom (there is no x in A s.t. f x = y). *)
Definition B_bot y := y ∈ B /\ ∀x, x ∈ A -> f x # y.

(* x is in a chain with a bottom in B. *)
Definition B_chain x := {y : dom B & B_bot y & {n | g (stepn y n) = x}}.

(* x is apart from any B-chain (needed for injectivity). *)
Definition A_chain_apart x := ∀y, B_bot y -> ∀n, x # g (stepn y n).

(* If y steps to x it is not a B-chain bottom (needed for surjectivity). *)
Definition A_chain_no_B_bot x :=
  ∀y, (y ∈ B /\ ∃n, g (stepn y n) = x) -> ∃z, z ∈ A /\ f z = y.

(* A_chain_apart and A_chain_no_B_bot are classically equivalent. *)
Theorem A_chain_apart_no_B_bot :
  LEM -> ∀x, A_chain_apart x <-> A_chain_no_B_bot x.
Proof.
intros PO x; split.
- intros H y [Hy [n Hn]]. apply lem_pdn; auto. intros Hnex.
  assert(HyB: B_bot y). { split; auto. intros z Hz.
    apply lem_apart_if_neq; auto; intros Hzy. apply Hnex; now exists z. }
  apply H in HyB. assert(Hnn := HyB n). now apply apart_spec in Hnn.
- intros H y [H1y H2y] n. apply lem_apart_if_neq; auto; intros Hx.
  destruct (H y) as [z [H1z H2z]]. split; auto. now exists n.
  apply H2y in H1z. now apply apart_spec in H1z.
Qed.

(* A B-chain cannot be an A-chain. *)
Theorem B_chain_A_chain :
  LEM -> ∀x, B_chain x -> ~A_chain_apart x.
Proof.
intros PO x [y Hy [n Hn]] xA. apply xA in Hy.
assert(Hyn := Hy n). now apply apart_spec in Hyn. 
Qed.

(* We need to decide the chain type for any x. *)
Inductive chain x :=
  | AChain (H1 : A_chain_apart x) (H2 : A_chain_no_B_bot x)
  | BChain (H : B_chain x).

(* We need to be able to decide the chain type. This is stronger than LEM. *)
Variable chain_dec : ∀x, chain x.

(* We define the bijective function h using in_Bchain_dec. *)
Definition h x :=
  match chain_dec x with
  | AChain _ _ _ => f x
  | BChain _ (existT2 _ _ y _ (exist n _)) => stepn y n
  end.

Lemma stepn_isin y n :
  y ∈ B -> stepn y n ∈ B.
Proof.
intros; apply applyn_isin; auto.
intros b Hb; now apply f_wd, g_wd.
Qed.

Corollary g_stepn_isin y n : y ∈ B -> g (stepn y n) ∈ A.
Proof. intros; now apply g_wd, stepn_isin. Qed.

Theorem h_wd :
  well_defined A B h.
Proof.
intros x Hx. unfold h; destruct (chain_dec x). now apply f_wd.
destruct H as [y [Hy _] [n _]]. apply applyn_isin. easy.
intros b Hb. now apply f_wd, g_wd.
Qed.

Theorem h_inj :
  injective A B h.
Proof.
intros x1 x2 Hx1 Hx2 Hx12.
unfold h; destruct (chain_dec x1), (chain_dec x2);
try destruct H as [y Hy [n Hn]].
- (* Both in an A-chain. *)
  now apply f_inj.
- (* Both in a different chain. *)
  destruct n. now apply Hy.
  replace (stepn y (S n)) with (f (g (stepn y n))) by easy.
  apply f_inj; auto. apply g_stepn_isin; apply Hy.
- (* Both in a different chain. *)
  apply apart_sym. destruct n. now apply Hy.
  replace (stepn y (S n)) with (f (g (stepn y n))) by easy.
  apply f_inj; auto. apply g_stepn_isin; apply Hy.
- (* Both in a B-chain. *)
  destruct H0 as [y' Hy' [n' Hn']]; subst.
  apply g_ext; auto. apply stepn_isin; apply Hy. apply stepn_isin; apply Hy'.
Qed.

Theorem h_surj :
  surjective A B h.
Proof.
intros y Hy. destruct (chain_dec (g y)) eqn:E.
- (* A chain: we need to invert g. *)
  destruct (H2 y) as [yinv [H1y H2y]]. split; auto. now exists 0.
  exists yinv; split; auto. unfold h; destruct (chain_dec yinv); auto.
  (* yinv cannot be in a B-chain.  *)
  exfalso. destruct H as [bot [B1 B2] [n Hn]].
  destruct (H2 bot) as [z [H1z H2z]]. split; auto. exists (S n).
  unfold stepn in *; simpl; now rewrite Hn, H2y.
  apply (B2 z) in H1z. now apply apart_spec in H2z.
- (* B chain: f (g y) is mapped to y. *)
  exists (g y); split. now apply g_wd. unfold h; rewrite E; clear E.
  destruct H as [y' [Hy' _] [n Hn]]. apply injective_weaken in g_inj.
  apply g_inj in Hn; auto. apply applyn_isin; auto.
  intros b Hb. now apply f_wd, g_wd.
Qed.

Corollary equivalent : A === B.
Proof. exists h; repeat split. apply h_wd. apply h_inj. apply h_surj. Qed.

End EquivThm.
End EquivThm.

(* Final Equivalence theorem *)
Theorem equivalence_theorem A B :
  (∀f g, ∀x, EquivThm.chain A B f g x) ->
  (∀g, strong_extensional B A g) ->
  EquivalenceTheorem A B.
Proof.
intros C E [[f [f_wd f_inj]] [g [g_wd g_inj]]].
now apply EquivThm.equivalent with (f:=f)(g:=g).
Qed.
