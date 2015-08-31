Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Misc.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import KonneTactics.
Require Import Coq.Program.Basics.
Require Import EqDec.
Require Import Equality.

Section DepDict.
  Variable K : Type.
  Variable V : K -> Type.
  Context `{eqDec K}.

  Definition depDict := forall k, V k.

  Definition lookup (d:depDict) k := d k.

  Definition build f : depDict := f.

  Definition overwrite' (d:depDict) (k:K) (v:V k) : depDict.
    intro k'.
    refine (if k' =? k then _ else d k').
    subst. apply v.
  Defined.

  Definition update' (d:depDict) (k:K) (f:V k -> V k): depDict :=
    overwrite' d k (f (lookup d k)).

  Lemma buildOk : forall f k, lookup (build f) k = f k.
    reflexivity.
  Qed.

  Lemma assocOverwriteOk (d:depDict) (k k':K) (v:V k) : 
    k <> k' -> lookup (overwrite' d k v) k' = lookup d k'.
  Proof.
    unfold lookup, overwrite'.
    break_match; crush.
  Qed.

  Lemma assocLookupOk (d:depDict) (k:K) (v:V k) : lookup (overwrite' d k v) k = v.
    unfold lookup, overwrite'.
    break_match; crush.
    simpl_uip.
    crush.
  Qed.
End DepDict.

Arguments update' {_ _ _} _ _ _ _.
Arguments overwrite' {_ _ _} _ _ _ _.
Arguments lookup {_ _} _ _.
Arguments build {_ _} _ _.

Section Dict.

  Variable K : Type.
  Variable V : Type.
  Context `{eqDec K}.

  Definition dict := depDict K (const V).

  Definition overwrite (d:dict) (k:K) (v:V) : dict := 
    fun k' => if k' =? k then v else d k'.

  Definition update (d:dict) (k:K) (v:V) : dict := 
    fun k' => if k' =? k then v else d k'.

End Dict.

Arguments update {_ _ _} _ _ _ _.
Arguments overwrite {_ _ _} _ _ _ _.

Definition overwrite'' {A B V} `{eqDec A} `{eqDec B} (d:dict (A * B) V) k (v:V) :=
  fun k' =>
    let ' (a , b ) := k in
    let ' (a', b') := k' in
      if b =? b' then
        if a =? a' then
          v
        else d k'
      else
        d k'.

Arguments overwrite'' {_ _ _ _ _} _ _ _ _.