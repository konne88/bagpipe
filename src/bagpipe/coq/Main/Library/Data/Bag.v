Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Misc.
Require Import CpdtTactics.

Section Bag.
  Variable A : Type.
  
  Definition bag := A -> Type.

  Definition elem a (b:bag) := b a.

End Bag.

Arguments elem {_} _ _. 
