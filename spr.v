(* Finitary spreads *)

From intuitionism Require Import lib set seq bcp.

(* Spread: a subset of the entire Baire space *)
Record spread := Spr {
  σ : fseq -> bool;
  σ_nil : σ [] = true;
  σ_cons : forall s, σ s = true <-> exists n, σ (n :: s) = true;
}.

(* Coerce spreads to aset *)
Section SprCSet.

(* Spread membership *)
Definition spread_member X α := forall m, σ X ⟨α;m⟩ = true.

Definition spread_aset (X : spread) :=
  ASet seq (spread_member X) seq_apart
    seq_apart_spec seq_apart_neq seq_apart_sym.

Coercion spread_aset : spread >-> aset.

Lemma unfold_inspr (X : spread) α :
  α : X -> forall m, σ X ⟨α;m⟩ = true.
Proof. auto. Qed.

Lemma intro_inspr (X : spread) α :
  (forall m, σ X ⟨α;m⟩ = true) -> α : X.
Proof. auto. Qed.

End SprCSet.

(* Intersection of a spread. *)
Section SpreadIntersection.

Variable X : spread.
Variable root : fseq.
Variable rootP : σ X root = true.

(* Note that get and σ use a reveresed list ordering. *)
Definition Intσ s := (fcompare (rev s) (rev root)) && σ X s.

Lemma Intσ_nil : Intσ [] = true.
Proof. unfold Intσ; simpl; auto. apply σ_nil. Qed.

Lemma Intσ_true s : Intσ s = true -> σ X s = true.
Proof. unfold Intσ; intros. now bool_to_Prop. Qed.

Lemma app_nth_firstn (s t : fseq) :
  length s < length t -> fcompare s t = true
  -> s ++ [nth (length s) t 0] = firstn (length s + 1) t.
Proof.
revert t; induction s; simpl; intros.
- destruct t0. now simpl in H. easy.
- destruct t0; simpl in H. easy. repeat bool_to_Prop; subst.
  simpl. rewrite IHs; auto. omega.
Qed.

Lemma σ_firstn n s :
  σ X s = true -> σ X (rev (firstn n (rev s))) = true.
Proof.
induction s; intros. simpl; now rewrite firstn_nil.
simpl; rewrite firstn_app; simpl_list. destruct (lt_dec (length s) n) as [N|N].
- replace (n - length s) with (S (n - 1 - length s)) by omega; simpl.
  rewrite firstn_nil. rewrite firstn_all2; simpl_list. auto. omega.
- replace (n - length s) with 0 by omega. rewrite firstn_O, app_nil_r.
  apply IHs. apply σ_cons. now exists a.
Qed.

Lemma Intσ_cons s :
  Intσ s = true <-> exists n, Intσ (n :: s) = true.
Proof.
unfold Intσ; simpl; split.
- intros; bool_to_Prop.
  destruct (lt_dec (length (rev s)) (length (rev root))) as [L|L].
  + (* Extend along the root path. *)
    pose(n := nth (length (rev s)) (rev root) 0). exists n. bool_to_Prop.
    unfold n; rewrite app_nth_firstn; auto. apply fcompare_sym, fcompare_firstn.
    replace (n :: s) with (rev ((rev s) ++ [n])) by (simpl_list; auto).
    unfold n; rewrite app_nth_firstn; auto. apply σ_firstn; auto.
  + (* Extend using σ_cons. *)
    apply σ_cons in H as [n Hn]; exists n. bool_to_Prop; auto.
    apply fcompare_trans with (t:=rev s); auto. omega.
    apply fcompare_sym, fcompare_app.
- intros [n Hn]; repeat bool_to_Prop.
  + apply fcompare_sym; eapply fcompare_app_inv. apply fcompare_sym, Hn0.
  + apply σ_cons. exists n; auto.
Qed.

Definition sprint := Spr Intσ Intσ_nil Intσ_cons.

End SpreadIntersection.

(* Function to retract the the Baire space onto any spread. *)
Module Retract.
Section Retract.
Notation "'σπ1'" := proj1_sig.
Notation "'σπ2'" := proj2_sig.
Arguments exist {_ _}.

Variable X : spread.

(* X is decidable *)
Lemma X_dec s n : {σ X (n :: s) = true} + {~σ X (n :: s) = true}.
Proof. apply bool_dec. Qed.

(* Retract any finite sequence onto the spread. *)
Fixpoint ρ (s : fseq) : {t | σ X t = true} :=
  match s with
  | [] => exist [] (σ_nil X)
  | n :: t =>
    let ρt := σπ1 (ρ t) in
    let ρtP := σπ2 (ρ t) in
    match X_dec ρt n with
    | left accept => exist (n :: ρt) accept
    | right _ =>
      let ex := proj1 (σ_cons X ρt) ρtP in
      let n0 := epsilon_smallest _ (X_dec ρt) ex in
      exist (σπ1 n0 :: ρt) (proj1 (σπ2 n0))
    end
  end.

(* Retract function *)
Definition r α n := hd 0 (σπ1 (ρ ⟨α;n+1⟩)).

(* r is the same as ρ *)
Lemma r_eq_ρ α n :
  ⟨r α;n⟩ = σπ1 (ρ ⟨α;n⟩).
Proof.
induction n; simpl; auto.
destruct (ρ ⟨α;n⟩) as [ρt Hρ] eqn:Rρ; simpl in *.
destruct (X_dec ρt (α n)) eqn:RX; simpl;
rewrite IHn; apply cons_split; auto;
unfold r; rewrite add_1_r; simpl;
rewrite Rρ; simpl; rewrite RX; auto.
Qed.

(* ρ does not alter sequences in X. *)
Lemma ρ_id α n :
  α : X -> σπ1 (ρ ⟨α;n⟩) = ⟨α;n⟩.
Proof.
intros; induction n; simpl; auto.
destruct (ρ ⟨α;n⟩); simpl in *; subst.
destruct (X_dec ⟨α;n⟩ (α n)); simpl; auto.
exfalso; apply unfold_inspr with (m:=S n) in H; auto.
Qed.

(* r does not alter sequences in X. *)
Lemma r_id α :
  α : X -> r α = α.
Proof.
intros; apply functional_extensionality; intros n.
unfold r; rewrite ρ_id; auto. rewrite add_1_r; simpl; auto.
Qed.

(* The image of r is in X. *)
Lemma r_image α :
  (r α) : X.
Proof.
intros m; rewrite r_eq_ρ.
destruct (ρ ⟨α;m⟩) as [ρt Hρ]; auto.
Qed.

End Retract.
End Retract.

(* BCP generalizes to spreads *)
Theorem BCPext (X : spread) (R : seq -> nat -> Prop) :
  (forall α, α : X -> exists n, R α n) ->
  (forall α, α : X -> exists m n, forall β, β : X -> eqn m α β -> R β n).
Proof.
intros Rall.
pose(rσ := (Retract.r X)).
pose(T := (fun α n => R (rσ α) n)).
assert(HT: forall α, exists n, T α n).
{ intros; pose(Hα := Retract.r_image X α); apply Rall in Hα.
  destruct Hα as [n Hn]; exists n; auto. }
intros; destruct (BCP T HT α) as [m [n P]]. exists m; exists n; intros.
apply P in H1; unfold T, rσ in H1; rewrite Retract.r_id in H1; auto.
Qed.
