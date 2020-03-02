(* Spread and fan prefix intersections. *)

From intuitionism Require Import lib set seq bcp spr fan.

(* Finite sequence comparison. *)
Section FiniteCompare.

(* Check if two sequences have a shared prefix. *)
Fixpoint fcompare (s t : fseq) := 
  match s, t with
  | s1 :: s', t1 :: t' => (s1 =? t1) && fcompare s' t'
  | _, _ => true
  end.

Lemma fcompare_refl s : fcompare s s = true.
Proof. intros; induction s; simpl; auto. repeat bool_to_Prop; auto. Qed.

Lemma fcompare_sym s t :
  fcompare s t = true -> fcompare t s = true.
Proof.
revert s; induction t; simpl; intros; auto.
destruct s; auto; simpl in H. repeat bool_to_Prop; auto.
Qed.

Lemma fcompare_trans s t u :
  length t >= length u ->
  fcompare s t = true -> fcompare t u = true -> fcompare s u = true.
Proof.
revert s t; induction u; simpl; intros s t.
- destruct s, t; simpl; auto.
- destruct s, t; simpl; auto; intros L H1 H2. omega.
  repeat bool_to_Prop. omega. apply IHu with (t:=t0); auto.
  apply le_S_n; auto.
Qed.

Lemma fcompare_nil_r s : fcompare s [] = true.
Proof. now apply fcompare_sym. Qed.

Lemma fcompare_app s t : fcompare s (s ++ t) = true.
Proof. induction s; simpl; auto. repeat bool_to_Prop; auto. Qed.

Lemma fcompare_app_inv s t u :
  fcompare s (t ++ u) = true -> fcompare s t = true.
Proof.
intros; eapply fcompare_trans. 2: apply H. rewrite app_length; omega.
apply fcompare_sym; apply fcompare_app.
Qed.

Lemma fcompare_firstn n s :
  fcompare s (firstn n s) = true.
Proof.
revert n; induction s; simpl; auto. destruct n; simpl; auto.
repeat bool_to_Prop; auto.
Qed.

End FiniteCompare.

(* Some extra lemmas *)
Section Lemmas.

Lemma app_nth_firstn (s t : fseq) :
  length s < length t -> fcompare s t = true
  -> s ++ [nth (length s) t 0] = firstn (length s + 1) t.
Proof.
revert t; induction s; simpl; intros.
- destruct t0. now simpl in H. easy.
- destruct t0; simpl in H. easy. repeat bool_to_Prop; subst.
  simpl. rewrite IHs; auto. omega.
Qed.

End Lemmas.

(* Spread intersection *)
Section SpreadIntersection.

Variable X : spread.
Variable root : fseq.
Variable rootP : σ X root = true.

(* Note that get and σ use a reveresed list ordering. *)
Definition Iσ s := (fcompare (rev s) (rev root)) && σ X s.

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

Lemma Iσ_nil : Iσ [] = true.
Proof. unfold Iσ; simpl; auto. apply σ_nil. Qed.

Lemma Iσ_true s : Iσ s = true -> σ X s = true.
Proof. unfold Iσ; intros. now bool_to_Prop. Qed.

Lemma Iσ_cons s : Iσ s = true <-> exists n, Iσ (n :: s) = true.
Proof.
unfold Iσ; simpl; split.
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

Definition spread_isect := Spr Iσ Iσ_nil Iσ_cons.

End SpreadIntersection.

Section FanInterection.

Variable F : fan.
Variable root : fseq.
Variable rootP : σ F root = true.

Lemma Iσ_fan s :
  Iσ F root s = true ->
  exists n, forall m, Iσ F root (m :: s) = true -> m <= n.
Proof.
unfold Iσ; intros; bool_to_Prop. apply (fanP F) in H as [n Hn].
exists n; intros; bool_to_Prop; auto.
Qed.

Definition fan_isect := Fan (spread_isect F root rootP) Iσ_fan.

End FanInterection.
