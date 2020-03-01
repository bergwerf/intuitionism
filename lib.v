(* All imports *)

Require Export Coq.Init.Nat.
Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Logic.ConstructiveEpsilon.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Omega.
Export Nat.
Export ListNotations.

Arguments In {_}.
Arguments Forall {_}.
Arguments exist {_ _}.

Ltac bool_to_Prop :=
  match goal with
  | [H : _ && _ = true |- _] =>
    let P := fresh H in (apply andb_prop in H as [P H])
  | [H : _ =? _ = true |- _]   => apply eqb_eq in H
  | [H : _ =? _ = false |- _]  => apply eqb_neq in H
  | [H : _ <=? _ = true |- _]  => apply leb_le in H
  | [H : _ <=? _ = false |- _] => apply leb_gt in H
  | [H : _ <? _ = true |- _]   => apply ltb_lt in H
  | [H : _ <? _ = false |- _]  => apply ltb_ge in H
  | |- (_ && _ = true)   => apply andb_true_intro; split
  | |- (_ =? _ = true)   => apply eqb_eq
  | |- (_ =? _ = false)  => apply eqb_neq
  | |- (_ <=? _ = true)  => apply leb_le
  | |- (_ <=? _ = false) => apply leb_gt
  | |- (_ <? _ = true)   => apply ltb_lt
  | |- (_ <? _ = false)  => apply ltb_ge
  | _ => idtac
  end.

Ltac bool_omega :=
  repeat bool_to_Prop;
  try (symmetry; repeat bool_to_Prop);
  omega.