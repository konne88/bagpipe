Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Bag.
Require Import Dict.
Require Import Misc.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import Coq.Program.Basics.
Require Import EqDec.
Require Import Enumerable.
Require Import BGPSpec.
Require Import Tracking.
Require Import KonneTactics.
Require Import Equality.
Require Import BGPSpecFacts.
Require Import Policy.
Import EqNotations.
Import ListNotations.

Section FastPolicy.
  Variable plainPrefix : PrefixClass.
  Variable plainTopology : TopologyClass.
  Variable plainAttributes : PathAttributesClass.
  Variable plainConfiguration : forall r, ConfigurationClass r.

  Definition trackingAttributes' := @trackingAttributes _ plainAttributes.
  Definition trackingConfiguration' := @trackingConfiguration _ _ plainAttributes plainConfiguration.
  Existing Instance trackingAttributes' | 0.
  Existing Instance trackingConfiguration' | 0.
  Typeclasses Transparent trackingAttributes'.
  Typeclasses Transparent trackingConfiguration'.
  Existing Instance enumerableIncoming.
  Existing Instance eqDecIncoming.

  Definition fastPolicy (P:forall r, incoming r -> outgoing r -> Prefix ->
                       RoutingInformation -> RoutingInformation -> 
                       RoutingInformation -> bool) : Prop :=
    forall r s d p s' ai ai',
      forwardable r s p ai ->
      forwardable r s' p ai' ->
      let al' := @import' _ trackingAttributes' _ r _ s  p ai in
      let al  := @import' _ trackingAttributes' _ r _ s' p ai' in
      let ao  := @export' _ trackingAttributes' _ r _ s' d p al in
        localPref'(al') <= localPref'(al) -> P r s d p ai al ao = true.

  Theorem fastPolicyImpliesPolicy : forall P, fastPolicy P -> (@policy _ _ trackingAttributes' trackingConfiguration' P).
    intros P Q. unfold policy, fastPolicy in *. 
    intros r s d p ns R.
    specialize (routerStateOk r s d p ns R); intro S.
    destruct S as [s' S].
    destruct S as [S S']. destruct S' as [S' S'']. 
    unfold build, lookup in *.
    unfold trackingAttributes' in *.
    rewrite S'. rewrite S''.
    pose (in_ := adjRIBsIn (lookup (routerState ns) r)).
    pose (ai  := lookup in_ (s, p)).
    pose (ai' := lookup in_ (s', p)).
    specialize (reachableImpliesForwardable ns R); intros F. destruct F as [F _].
    refine ((fun F' => _) F).
    specialize (F r s p).
    specialize (F' r s' p).
    specialize (Q r s d p s' ai ai' F F' S).
    inline_all.
    unfold build, lookup in *.
    trivial.
  Qed.
End FastPolicy.
