Extraction Language Scheme.

Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Bag.
Require Import Dict.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import KonneTactics.
Require Import Coq.Program.Basics.
Require Import EqDec.
Require Import Enumerable.
Require Import BGPSpec.
Require Import Equality.
Require Import SymbolicExecution.
Require Import Graph.
Require Import SingleAS.
Require Import BGPV.
Require Import SpaceSearch.
Require Import Rosette.
Require Import Misc.
Import ListNotations.
Import EqNotations.

(* LOCAL_PREF nat does not match the ones used in Racket *)
(* router lists do not match the one used in Racket *)

  Instance freeList `{SpaceSearch} {A} (l:list A) : Free {a | In a l}.
    induction l.
    - refine {| free := empty |}.
      intros [? []].
    - refine {| free := _ |}.
      + refine (union _ _).
        * refine (single (exist _ a _)).
          cbn.
          left.
          reflexivity.
        * refine (bind (free {a | In a l}) _).
          intros [a' ?].
          refine (single (exist _ a' _)).
          cbn in *.
          right.
          trivial.
      + intros [a' inl'].
        cbn in *.
        rewrite <- unionOk.
        destruct inl' as [|inl'].
        * left.
          subst_max.
          apply singleOk.
          reflexivity.
        * right.
          rewrite <- bindOk.
          exists (exist _ a' inl').
          constructor; [apply freeOk|].
          apply singleOk.
          reflexivity.
  Defined.

  Instance enumerableFree {A} {h:forall (S:SpaceSearch), @Free S A} : enumerable A.
    specialize (h listSpaceSearch).
    destruct h.
    cbn in *.
    refine {|enumerate := free|}.
    trivial.
  Defined.

Parameter IP : Type.
Parameter eqDecideIP : forall (r r':IP), decide (r = r').

Extract Constant IP => "__".
Extract Constant eqDecideIP => "eq-dec?".

Instance eqDecIP : eqDec IP.
  constructor.
  apply eqDecideIP.
Defined. 

Parameter CIDR : Type.
Parameter eqDecideCIDR : forall (r r':CIDR), decide (r = r').
Parameter freeCIDR : Space CIDR.
Axiom freeCIDROk : forall p, contains p freeCIDR.

Extract Constant CIDR => "__".
Extract Constant eqDecideCIDR => "eq-dec?".
Extract Constant freeCIDR => "(lambda (_) (symbolic-prefix))".

Instance FreeCIDR : Free CIDR := {|
  free := freeCIDR;
  freeOk := freeCIDROk
|}.

Instance eqDecCIDR : eqDec CIDR.
  constructor.
  apply eqDecideCIDR.
Defined.

Instance cidrPrefix : PrefixClass := {|
  Prefix := CIDR
|}.

Section BGPV.
  Existing Instance freeUnit.

  Parameter AS : Type.
  Parameter BGPAttributes : AS -> Type.

  Variable setup:AS.

  Definition LOCAL_PREF (_:BGPAttributes setup) := 0.  (* TODO local-pref is still broken *)
  (* Parameter LOCAL_PREF : BGPAttributes -> nat. *)
  Parameter eqDecideBGPAttributes : forall (r r':BGPAttributes setup), decide (r = r').

  Instance eqDecBGPAttributes : eqDec (BGPAttributes setup).
    constructor.
    apply eqDecideBGPAttributes.
  Defined.

  Instance bgpAttributes : PathAttributesClass := {|
    PathAttributes := BGPAttributes setup;
    localPref := LOCAL_PREF
  |}.

  Parameter freeBGPAttributes : Space (BGPAttributes setup).
  Parameter freeBGPAttributesOk : forall p, contains p (freeBGPAttributes).
  Instance FreeBGPAttributes : Free (BGPAttributes setup) := {|
    free := freeBGPAttributes;
    freeOk := freeBGPAttributesOk
  |}.

  Parameter internals : AS -> list IP.
  Parameter neighbors : {ri | In ri (internals setup)} -> list IP.

  Definition bagpipeRouter (t:RouterType) := 
    match t with
    | internal => {ri | In ri (internals setup)}
    | external => {re | exists riOk, In re (neighbors riOk)} 
    end.

  Definition bagpipeNeighbor (ri:bagpipeRouter internal) (re:bagpipeRouter external) : Type.
    cbn in *.
    destruct re as [re ?].
    exact (In re (neighbors ri)).
  Defined.

  Instance freeRouter `{SpaceSearch} : forall t, Free (bagpipeRouter t).
    intros []; cbn.
    - refine {| free := bind (free {a | In a (internals setup)}) single |}.
      intros i.
      rewrite <- bindOk.
      exists i.
      constructor; [apply freeOk|].
      rewrite <- singleOk.
      reflexivity.
    - refine {| free := _ |}.
      + refine (bind (free {a | In a (internals setup)}) _).
        intros ri.
        refine (bind (free {a | In a (neighbors ri)}) _).
        intros [re ?].
        apply single.
        refine (exist _ re _).
        exists ri.
        intuition.
      + intros [re [riOk reOk]].
        rewrite <- bindOk.
        exists riOk.
        constructor; [apply freeOk|].
        rewrite <- bindOk.
        exists (exist _ re reOk).
        constructor; [apply freeOk|].
        apply singleOk.
        reflexivity.
  Defined.

  Instance freeNeighbors `{SpaceSearch} : forall s, Free {d : bagpipeRouter external & bagpipeNeighbor s d}.
    intro r.
    refine {| free := bind (free {a | In a (neighbors r)}) _ |}. {
      cbn in *.
      intros [d n].
      refine (single [exist _ d _ & n]).
      exists r. 
      exact n.
    }
  Proof.
    intros [[d [r' n']] n].
    cbn in *.
    apply bindOk.
    exists (exist _ d n).
    constructor; [apply freeOk|].
    apply singleOk.
    generalize_proofs.
    reflexivity.
  Defined.

  Instance freeNeighbor `{SpaceSearch} : forall s d, Free (bagpipeNeighbor s d).
    unfold bagpipeNeighbor.
    cbn.
    intros riOk [re reOk'].
    cbn.
    refine {| free := _ |}.
    - destruct (@in_dec _ eqDecide re (neighbors riOk)).
      + apply single.
        trivial.
      + apply empty.
    - intros reOk.
      cbn.
      break_match.
      + proof_irrelevance.
        apply singleOk.
        reflexivity.
      + intuition.
  Defined.

  Instance bagpipeTopology : SingleASTopologyClass. 
    refine {|
      router := bagpipeRouter;
      neighbor := bagpipeNeighbor
    |}.
  Proof.
  - intros []; constructor; apply eqDecide.
  - cbn.
    intros [s ?] [d ?].
    cbn.
    constructor.
    intros c c'.
    left.
    proof_irrelevance.
    reflexivity.
  Defined.
  
  Existing Instance singleASTopology.

  Parameter denoteImport : forall r:router internal, incoming [internal & r] -> Prefix -> PathAttributes -> RoutingInformation.
  Parameter denoteExport : forall r:router internal, outgoing [internal & r] -> Prefix -> PathAttributes -> RoutingInformation.

  Parameter Query : Type.
  Parameter denoteQuery : Query -> forall r, incoming [internal & r] -> outgoing [internal & r] -> Prefix ->
                          @RoutingInformation trackingAttributes' ->
                          @RoutingInformation trackingAttributes' ->
                          @RoutingInformation trackingAttributes' -> bool.
 
  Instance bagpipeConfiguration : SingleASConfigurationClass.
    refine {|
      intImport := denoteImport;
      intExport r i := denoteExport r
    |}.
  Defined.

  Definition bgpvCore' := @bgpvCore rosette _ _ _ _ _ _ Query denoteQuery.

  Definition listSearch {A} := @search listSpaceSearch A.
  Definition listBind {A B} := @bind listSpaceSearch A B.

  Parameter bgpvScheduler : forall Q v, {o | o = listSearch (listBind v (compose optionToSpace (bgpvCore' Q)))}.

  Definition bgpv := @parallelBGPV rosette _ _ _ _ _ _ _ _ Query denoteQuery listSpaceSearch bgpvScheduler.
  Definition bgpvImport := @parallelBGPVImport rosette _ _ _ _ _ _ _ _ Query denoteQuery listSpaceSearch bgpvScheduler.

(* Definition bgpv := @fastPolicyDec' rosette _ _ _ _ _ _ _ _ Query denoteQuery. *)
End BGPV.

Extract Constant Query => "__".
Extract Constant denoteQuery => "(lambdas (_) denote-query)".

Extract Constant AS => "__".
Extract Constant BGPAttributes => "__".
Extract Constant eqDecideBGPAttributes => "(lambdas (_) eq-dec?)".
Extract Constant freeBGPAttributes => "(lambdas (as _) (symbolic-announcement (as->environment as)))".
Extract Constant denoteImport => "denote-import".
Extract Constant denoteExport => "denote-export".
Extract Constant internals => "denote-internals".
Extract Constant neighbors => "denote-neighbors".

(* Extract Constant LOCAL_PREF => "announcement-pref". *)

Extract Constant bgpvScheduler => "distributed-bgpv-scheduler".

Extraction "bgpv" bgpv bgpvImport bgpvCore' optionToSpace.
