Require Import Misc.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import KonneTactics.
Require Import Equality.
Require Import EqDec.
Import EqNotations.

Ltac novel_injection H := 
  injection H; 
  repeat match goal with
  | |- ?P -> _ =>
     match goal with
     | _:P |- _ => let x := fresh in intro x; clear x
     | _ => intro
     end
  end.

Ltac novel_injections := repeat
  match goal with
  | h:_ = _ |- _ => novel_injection h
  end.

Ltac simpl_eq :=
  unfold eq_rect_r in *;
  unfold eq_rect in *;
  unfold eq_sym in *;
  repeat simpl_uip;
  novel_injections;
  simpl_existTs;
  subst_max.

Ltac inline_sth := match goal with x := _ |- _ => subst x end.

Ltac destruct_match e :=
  match e with
  | context [ match ?p with _ => _ end ] =>
    first [
        destruct_match p
      | match type of p with
        | sumbool _ _ => destruct p
        | _ => destruct p eqn:?
        end
      ]
  end.

Ltac branch :=
  match goal with
    | |- ?g => destruct_match g
    | _ : ?h |- _ => destruct_match h
  end.

Ltac symbolic_execution'' discharge := (
  repeat (simpl_eq; inline_all; autounfold in *; cbn in *); 
  (try discharge);
  (try branch; (try discharge))).
