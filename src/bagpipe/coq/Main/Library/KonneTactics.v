Require Import ProofIrrelevance.
Require Import Coq.Logic.Eqdep.
 
Ltac inline_all := repeat match goal with x := _ |- _ => subst x end.

Ltac is_identifier H :=
  let foo := fresh in 
    assert True as foo by (clear; assert True as H by trivial; trivial); clear foo.

Ltac proof_irrelevance := repeat
  match goal with
  | h:?T, h':?T |- _ =>
    match type of T with 
    | Prop => try (rewrite <- (proof_irrelevance _ h h') in *); clear h'
    end
  end.

Ltac generalize_proofs := (repeat 
  match goal with
  | |- context[?H] => 
    match type of H with
    | ?T =>
      match type of T with
      | Prop => first [is_identifier H; fail 1 | generalize H; intro]
      end
    end
  end); proof_irrelevance.
