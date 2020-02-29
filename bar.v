(* Bar induction and the Fan Law *)

From intuitionism Require Import lib set seq bcp spr fan.

(* A bar is a complete set (Ensemble) of finite start sequences of a fan. *)
Record bar (F : fan) := Bar {
  barred : fseq -> Prop;
  barP : forall α, α : F -> exists n, barred ⟨α;n⟩;
}.

(* Coerce bar to a cset. *)
Definition bar_cset F (B : bar F) :=
  CSet fseq (barred F B) (dec_apart fseq)
  (dec_apart_spec fseq (list_eq_dec eq_nat_dec)) (dec_apart_neq fseq)
  (dec_apart_sym fseq).

Coercion bar_cset : bar >-> cset.

(* Finite bar *)
Record fbar (F : fan) := FiniteBar {
  bars : list fseq;
  fbarP : forall α, α : F -> exists n, In ⟨α;n⟩ bars;
}.
