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
Require Import KonneTactics.
Require Import Equality.
Require Import Graph.
Require Import FunctionalExtensionality.
Require Import SymbolicExecution.
Import EqNotations.
Import ListNotations.

Section BGPSpecFacts.
  Context `{PrefixClass}.
  Context `{TopologyClass}.
  Context `{PathAttributesClass}.
  Context `{forall r, ConfigurationClass r}.
  Existing Instance enumerableIncoming.
  Existing Instance eqDecIncoming.

  Opaque eqDecide.
  Opaque enumerate.
  Hint Unfold lookup update update' overwrite overwrite' build edge.
  Hint Unfold fst snd proj1_sig const id.
  Hint Unfold routerHandler messageHandling import' export' bindRoutingInformation 
              connection emptyRIB argMax.

  Lemma routerStateOk : forall r s d p ns (R:reachable ns),
    let ribs := lookup (routerState ns) r in
    let outs := build(fun s => import' r s p (lookup (adjRIBsIn ribs) (s,p))) in 
    exists s', localPref' (lookup outs s) <= localPref' (lookup outs s') /\ 
               (lookup (locRIB ribs) p = lookup outs s') /\
               (lookup (adjRIBsOut ribs) (d,p) = export' r s' d p (lookup outs s')).
  Proof.
    intros.
    exists(argMax' (fun s => localPref' (lookup outs s)) injected).
    constructor. {
      specialize (allSmallerThanArgMax (fun s => localPref' (lookup outs s))); intro.
      intuition.
    } {
      induction R as [|ns ns'' _ IHR t].
      - constructor; repeat symbolic_execution'' congruence.
      - destruct t as [m r' rs' ls' | m c rs' ls']. 
        + unfold build in *. 
          intuition.
          * repeat symbolic_execution'' congruence.
          * repeat symbolic_execution'' congruence.
        + unfold build in *.
          destruct c as [s'r' c].
          destruct s'r' as [s' r'].
          intuition. 
          * repeat symbolic_execution'' congruence.
          * repeat symbolic_execution'' congruence.
    }
  Qed.

  Lemma routerStateOk' : forall r d p ns (R:reachable ns),
    let ribs := lookup (routerState ns) r in
    let outs := build (fun s => import' r s p (lookup (adjRIBsIn ribs) (s,p))) in 
    let s' := argMax' (fun s => localPref' (lookup outs s)) injected in 
      lookup (locRIB ribs) p = lookup outs s' /\
      lookup (adjRIBsOut ribs) (d,p) = export' r s' d p (lookup outs s').
  Proof.
    intros.
    induction R as [|ns ns'' _ IHR t].
    - constructor; repeat symbolic_execution'' congruence.
    - destruct t as [m r' rs' ls' | m c rs' ls']. 
      + unfold build in *. 
        intuition.
        * repeat symbolic_execution'' congruence.
        * repeat symbolic_execution'' congruence.
      + unfold build in *.
        destruct c as [s'r' c].
        destruct s'r' as [s'' r'].
        intuition. 
        * repeat symbolic_execution'' congruence.
        * repeat symbolic_execution'' congruence.
  Qed.
End BGPSpecFacts.
