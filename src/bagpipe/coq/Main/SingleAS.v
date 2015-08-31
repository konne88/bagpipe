Require Import Graph.
Require Import NArith.
Require Import Arith. 
Require Import Bool.
Require Import List.
Require Import Omega.
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
Require Import FastPolicy.
Require Import SpaceSearch.
Import EqNotations.
Import ListNotations.

Definition decide P := {P} + {~P}.

Section SingleAS.
  Existing Instance enumerableIncoming.
  Existing Instance eqDecIncoming.
  Existing Instance eqDecSigT.
  Existing Instance enumerableSigT.
  Existing Instance enumerableRoutingInformation. 
  Existing Instance eqDecRoutingInformation. 

  Inductive RouterType := internal | external.
  Instance eqDecRouterType : eqDec RouterType.
    constructor.
    decide equality.
  Defined.
  Instance enumerableRouterType : enumerable RouterType.
    refine {|enumerate:=[internal; external]|}.
    intros []; crush.
  Defined.

  Context `{plainPrefix : PrefixClass}.
  Context `{plainAttributes : PathAttributesClass}.

  Class SingleASTopologyClass := {
    router : RouterType -> Type;
    neighbor : router internal -> router external -> Type;
    eqDecRouters :> forall t, eqDec (router t);
    enumerableRouters :> forall t, enumerable (router t);
    eqDecNeighbor :> forall s d, eqDec (neighbor s d);
    enumerableNeighbor :> forall s d, enumerable (neighbor s d)
  }.

  Context `{SingleASTopologyClass}.

  Definition singleASConnections : Graph.graph {t:RouterType & router t}.
    intros [[] s] [[] d].
    - exact (if s =? d then Empty_set else unit).
    - exact (neighbor s d).
    - exact (neighbor d s).
    - exact Empty_set.
  Defined.

  Definition singleASMode s d (_ : singleASConnections s d) : Mode.
    destruct s as [[] ?]; destruct d as [[] ?].
    - exact ibgp.
    - exact ebgp.
    - exact ebgp.
    - exfalso. crush.
  Defined.

  Instance singleASTopology : TopologyClass. 
  refine {|
    Router := sigT router;
    connections := singleASConnections;
    mode := singleASMode
  |}.
  - intros.
    constructor.
    unfold singleASConnections.
    unfold Graph.edge.
    intros.
    repeat break_match; first [decide equality|apply eqDecide].
  - intros.
    unfold singleASConnections.
    unfold Graph.edge.
    repeat break_match; first [apply enumerableEmptySet|apply enumerableUnit|idtac]. 
    apply enumerableNeighbor.
    apply enumerableNeighbor.
  Defined.

  Class SingleASConfigurationClass := {
    intImport : forall r, incoming [internal & r] -> Prefix -> PathAttributes -> RoutingInformation;
    intExport : forall r, incoming [internal & r] ->
                          outgoing [internal & r] -> Prefix -> PathAttributes -> RoutingInformation
  }.

  Context `{SingleASConfigurationClass}.

  Instance singleASConfiguration : forall r:Router, ConfigurationClass r.
    intros [[] ?].
    - refine {|
        import i p a := intImport r i p a;
        export o p a := intExport r o p a;
        originate p a := false
      |}.
    - refine {|
        import i p a := match i with injected => available a | _ => notAvailable end;
        export i o p a := available a;
        originate p a := true
      |}.
  Defined.
End SingleAS.
