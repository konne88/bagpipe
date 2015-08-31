Require Import Coq.Setoids.Setoid.
Require Import List.
Require Import JamesTactics.
Require Import Misc.
Require Import EqDec.
Import ListNotations.

Class SpaceSearch := {
  Space : Type -> Type;
  empty : forall {A}, Space A;
  single : forall {A}, A -> Space A;
  union : forall {A}, Space A -> Space A -> Space A;
  bind : forall {A B}, Space A -> (A -> Space B) -> Space B;
  search : forall {A}, Space A -> option A;

  contains : forall {A}, A -> Space A -> Prop;
  emptyOk : forall {A} {a:A}, ~contains a empty;
  singleOk : forall {A} {a a':A}, a = a' <-> contains a' (single a);
  unionOk : forall {A S T} {a:A}, (contains a S \/ contains a T) <-> contains a (union S T);
  bindOk : forall {A B S f} {b:B}, (exists a:A, contains a S /\ contains b (f a)) <-> contains b (bind S f);
  searchOk : forall {A S} {a:A}, search S = Some a -> contains a S;
  searchOk' : forall {A S} {a:A}, search S = None -> ~contains a S
}.

Section SpaceSearch.
  Context `{SpaceSearch}.

  Class Free A := {
    free : Space A;
    freeOk : forall (a:A), contains a free
  }.

  Arguments free _ [_].

  Instance freeBool : Free bool. 
    refine {|
      free := union (single true) (single false)
    |}.
  Proof.
    intro b.
    rewrite <- unionOk.
    destruct b.
    - left. apply singleOk. reflexivity.
    - right. apply singleOk. reflexivity.
  Defined.

  Instance freeSigT {A B} `{Free A} 
                          `{forall a:A, Free (B a)} : 
                            Free {a : A & B a}.
    refine {|
      free := bind (free A) (fun a => 
              bind (free (B a)) (fun b =>
              single [a & b]))
    |}.
  Proof.
    intros [a b].
    rewrite <- bindOk; eexists.
    constructor; [apply freeOk|].
    rewrite <- bindOk; eexists.
    constructor; [apply freeOk|].
    apply singleOk.
    reflexivity.
  Defined.

  Instance freeEmpty : Free Empty_set.
    refine {| free := empty |}.
  Proof.
    intros [].
  Defined.

  Instance freeUnit : Free unit.
    refine {| free := single tt |}.
  Proof.
    intros [].
    apply singleOk.
    reflexivity.
  Defined.
End SpaceSearch.

Arguments free [_] _ [_].

Instance listSpaceSearch : SpaceSearch.
  refine {|
    Space := list;
    empty A := [];
    single A a := [a];
    union A l l' := l ++ l';
    bind A B S f := concat (f <$> S);
    search A l := match l with [] => None | a::_ => Some a end;
    contains := In
  |}.
Proof.
  - compute. 
    trivial.
  - compute. 
    intros. 
    constructor.
    * left. 
      trivial.
    * intro h. 
      destruct h; intuition.
  - symmetry. 
    apply in_app_iff.
  - intros A B l f b.
    constructor.
    * intro h.
      destruct h as [a [al bfa]].
      induction l as [|a'].
      + compute in *.
        intuition.
      + cbn in *.
        rewrite in_app_iff.
        destruct al. {
          left.
          subst_max.
          intuition.
        } {
          right.
          intuition.
        }
    * intro h.
      induction l.
      + compute in h.
        intuition.
      + cbn in h.
        rewrite in_app_iff in *.
        destruct h. {
          exists a.
          cbn.
          intuition.
        } {
          specialize (IHl H).
          destruct IHl as [a' []].
          exists a'.
          intuition.
        }
  - intros.
    break_match.
    * intuition.
      inversion H.
    * intuition.
      inversion H.
      subst_max.
      cbn.
      left. 
      reflexivity.
  - intros.
    break_match.
    * cbn.
      intuition.
    * inversion H.
Defined.
