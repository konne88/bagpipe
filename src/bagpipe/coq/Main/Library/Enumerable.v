Require Import NArith.
Require Import Arith.
Require Import List.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import Coq.Program.Basics.
Require Import EqDec.
Require Import Misc.
Require Import Bag.
Require Import Omega.
Require Import KonneTactics.
Import ListNotations.

Class enumerable A := {
  enumerate : list A;
  enumerateContainsEverything : forall a, In a enumerate
}.

Lemma concatIn {A} {a:A} l {L} `{eqDec A} : In a l -> In l L -> In a (concat L).
  intros.
  induction L as [|l' L'].
  + crush.
  + simpl.
    apply in_or_app.
    destruct (l =? l').
    - subst_max.
      intuition.
    - crush.
Qed.

Instance enumerableSigT {A B} `{eqDec A} `{enumerable A} 
                              `{forall a:A, eqDec (B a)} `{forall a:A, enumerable (B a)} : 
                              enumerable {a : A & B a}.
  refine {|
    enumerate := bindList 
      (enumerate (A := A)) (fun a => 
      map (existT _ a) (enumerate (A := B a)))
  |}.
Proof.
  Opaque concat.
  Opaque map.
  intros.
  destruct a as [a b].
  unfold bindList.
  apply (concatIn (existT _ a <$> enumerate)).
  + apply in_map.
    apply enumerateContainsEverything.
  + match goal with 
    | |- In ?A (?F <$> _) => remember F as f; assert (A = f a) as R by crush
    end.
    rewrite R.
    apply in_map.
    apply enumerateContainsEverything.
Defined. 

Instance enumerableProd {A B} `{eqDec A} `{enumerable A} `{eqDec B} `{enumerable B} : enumerable (A * B).
  refine {|
    enumerate := bindList 
      enumerate (fun a => pair a <$> enumerate)
  |}.
Proof.
  Opaque concat.
  Opaque map.
  intros.
  destruct a as [a b].
  unfold bindList.
  apply (concatIn (pair a <$> enumerate)).
  + apply in_map.
    apply enumerateContainsEverything.
  + match goal with 
    | |- In ?A (?F <$> _) => remember F as f; assert (A = f a) as R by crush
    end.
    rewrite R.
    apply in_map.
    apply enumerateContainsEverything.
Defined. 

Instance enumerableEmptySet : enumerable Empty_set.
  refine {|enumerate := []|}.
Proof.
  crush.
Defined.

Instance enumerableUnit : enumerable unit.
  refine {|enumerate := [tt]|}.
Proof.
  crush.
Defined.

Instance enumerableSigT' {A B} `{eqDec A} `{enumerable A} 
                            `{forall a:A, eqDec (B a)} `{forall a:A, enumerable (B a)} : 
                            enumerable (sigT B).
  apply enumerableSigT.
Defined.

Instance enumerableSum {A B} `{enumerable A} `{enumerable B} : enumerable (A + B).
  refine {|enumerate := inl <$> enumerate ++ inr <$> enumerate|}.
Proof.
  intro.
  rewrite in_app_iff.
  destruct a.
  - left. 
    apply in_map. 
    apply enumerateContainsEverything.
  - right. 
    apply in_map. 
    apply enumerateContainsEverything.
Defined.    

Instance eqDecUnit : eqDec unit.
  constructor.
  decide equality.
Defined.

Fixpoint argMax'' {A} (f:A->nat) (l:list A) {struct l} : l <> [] -> A.
  refine(
  match l with
  | [] => _
  | a::l' => fun _ =>
    (match l' as l'' return l' = l'' -> A with
    | [] => fun _ => a
    | _ =>  fun _ => let a' := argMax'' _ f l' _ in
            if f a' <=? f a then a else a'
    end) _
  end).
Proof.
  - congruence.
  - congruence.
  - congruence.
Defined.

Lemma allSmallerThanArgMax'' {A} :
  forall f l (a:A) (H : l <> []), In a l -> 
    f a <= f (argMax'' f l H).
Proof.
  intro f.
  induction l as [|a' l' IHl].
  - congruence.
  - intros.
    match goal with H:In _ _ |- _ => rename H into H' end.
    cbn.
    break_match; [crush|].
    generalize_proofs.
    specialize (IHl a p).
    subst_max.
    break_match.
    + specialize (leb_complete _ _ Heqb); intro; clear Heqb.
      destruct H' as [|H'].
      * subst_max. omega.
      * specialize (IHl H'). omega.
    + specialize (leb_complete_conv _ _ Heqb); intro; clear Heqb.
      destruct H' as [|H'].
      * subst_max. omega.
      * specialize (IHl H'). omega.
Defined.

Definition argMax' {A} `{enumerable A} (f:A->nat) (a:A) : A.
  refine(argMax'' f enumerate _).
Proof.
  specialize (enumerateContainsEverything a).
  intros; intro.
  find_rewrite.
  specialize in_nil. 
  crush.
Defined.

Lemma allSmallerThanArgMax {A} `{enumerable A} :
  forall f (a' a:A), f a <= f (argMax' f a').
Proof.
  intros.
  unfold argMax'.
  apply allSmallerThanArgMax''.
  apply enumerateContainsEverything.
Qed.


Fixpoint argMaxL  {A} (f:A->nat) (l:list A) {struct l} : list A :=
  match l with
    | [] => []
    | a :: l' =>
      match (argMaxL f l') with
        | [] => [a]
        | a' :: as' =>
          if f a <? f a' then
            a' :: as'
          else
            if f a =? f a' then
              a :: a' :: as'
            else
              [a]
      end
  end.

Lemma argMaxL_all_same :
  forall A l f (a : A) a',
    In a (argMaxL f l) ->
    In a' (argMaxL f l) ->
    f a' = f a.
Proof.
  induction l; intros; simpl in *; intuition.
  repeat break_match; simpl in *; auto;
  intuition; repeat find_rewrite; auto;
    match goal with
      | |- f ?a = f ?a' =>
        try solve [specialize (IHl f a a'); forward IHl; repeat find_rewrite; simpl; intuition];
        try solve [specialize (IHl f a' a); forward IHl; repeat find_rewrite; simpl; intuition]
    end.
Qed.

Lemma argMaxL_non_empty :
  forall A l f (a : A),
    In a l ->
    argMaxL f l <> [].
Proof.
  destruct l; intros; simpl in *; intuition; subst;
  repeat break_match; simpl in *; congruence.
Qed.

Lemma allSmallerThanArgMaxL :
  forall A l f (a : A) a',
    In a (argMaxL f l) ->
    In a' l ->
    f a' <= f a.
Proof.
  induction l; intros; simpl in *; intuition.
  - subst. repeat break_match; simpl in *; auto.
    + intuition. subst. auto.
    + apply Nat.ltb_lt in Heqb.
      intuition; subst; try omega.
      assert (f a = f a0); try omega.
      eapply argMaxL_all_same; eauto; rewrite Heql0; simpl in *; intuition.
    + intuition; repeat find_rewrite; auto.
      assert (f a = f a0); try omega.
      eapply argMaxL_all_same; eauto; rewrite Heql0; simpl in *; intuition.
    + intuition. subst. auto.
  - repeat break_match; simpl in *; auto.
    + intuition. subst.
      exfalso; eapply argMaxL_non_empty; eauto.
    + intuition; repeat find_rewrite; auto;
      eapply IHl; eauto; repeat find_rewrite; simpl; auto.
    + intuition; repeat find_rewrite; auto;
      eapply IHl; eauto; repeat find_rewrite; simpl; auto.
    + intuition. subst.
      apply Nat.ltb_ge in Heqb.
      eapply le_trans; [|eauto].
      eapply IHl; eauto; repeat find_rewrite; simpl; auto.
Qed.

Definition argMax {A} `{enumerable A} (f:A->nat) : A -> {a:A | forall a', f a' <= f a}.
  intro P.
  refine (exist _ (argMax' f P) _).
  apply allSmallerThanArgMax.
Defined.
