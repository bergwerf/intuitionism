(* Injective functions between finitary spreads. *)

From intuitionism Require Import lib set seq spr fan func bcp bar tau.

(*
This file explores when an injective function between two fans is
intuitionistically possible. This relation is denoated ≼ and is introduced in
func.v. (the ≼' relation adds a strong extensionality requirement).
*)

(* First we consider τ fans. *)
Section Tau.

(* Injection between similar bounds. *)
Theorem τ_preceq_translate n m k :
  τ n k ≼ τ m k.
Proof.
exists (λ α, λ i,  α i - n + m); split.
- intros α H. apply member_τP; intros i.
  apply member_τP in H; assert(Hi := H i). lia.
- intros α β Hα Hβ [i Hi]. exists i.
  apply member_τP in Hα; apply member_τP in Hβ.
  assert(Hαi := Hα i); assert(Hβi := Hβ i). lia.
Qed.

(* Injection to a larger bound. *)
Theorem τ_preceq_id m n :
  m <= n -> τ 0 m ≼ τ 0 n.
Proof.
intros LE. exists (λ α, α); split.
- intros α H. apply member_τP; intros i.
  apply member_τP in H; assert(Hi := H i). lia.
- intros α β _ _ [i Hi]. now exists i.
Qed.

(* Injection to a smaller bound is impossible. *)
Theorem τ_noq_preceq m n :
  n < m -> τ 0 m ≺ τ 0 n.
Proof.
intros LT [f [f_wd f_inj]].
Admitted.

End Tau.

(* Next we consider arbitrary fans with the help of a branching factor. *)
Section BranchingFactor.

End BranchingFactor.