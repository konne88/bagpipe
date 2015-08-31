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
Import EqNotations.
Import ListNotations.

Section Policy.
  Variable plainPrefix : PrefixClass.
  Variable plainTopology : TopologyClass.
  Variable plainAttributes : PathAttributesClass.
  Variable plainConfiguration : forall r, ConfigurationClass r.

  Definition policy (P:forall r, incoming r -> outgoing r -> Prefix ->
                       RoutingInformation -> RoutingInformation -> 
                       RoutingInformation -> bool) : Prop :=
    forall r s d p ns, reachable ns ->
      let rs := lookup (routerState ns) r in
        P r s d p (lookup (adjRIBsIn rs) (s, p)) 
                  (lookup (locRIB rs) p)
                  (lookup (adjRIBsOut rs) (d, p)) = true.
End Policy.
