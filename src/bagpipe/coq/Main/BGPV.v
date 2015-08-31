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
Require Import SingleAS.
Import EqNotations.
Import ListNotations.

Section BGPV.
  Context `{S:SpaceSearch}.
  Arguments policy [_ _ _ _] _.

  Context `{plainPrefix : PrefixClass}.
  Context `{freePrefix : @Free S Prefix}.

  Context `{plainAttributes : PathAttributesClass}.
  Context `{eqDecPathAttributes : eqDec PathAttributes}.
  Context `{freePathAttributes : @Free S PathAttributes}.

  Context `{SingleASTopologyClass}.
  Context `{@SingleASConfigurationClass _ _ _}.

  Context {freeNeighbors : forall {S:SpaceSearch} s, @Free S {d : router external & neighbor s d}}.
  Context {freeRouters : forall {S:SpaceSearch} t, @Free S (router t)}.

  Existing Instance singleASTopology.
  Existing Instance singleASConfiguration.
  Existing Instance enumerableIncoming.
  Existing Instance eqDecIncoming.
  Existing Instance eqDecSigT.
  Existing Instance enumerableSigT.
  Existing Instance enumerableRoutingInformation. 
  Existing Instance eqDecRoutingInformation. 
  Existing Instance eqDecRouterType.
  Existing Instance enumerableRouterType.
  Existing Instance freeEmpty.
  Existing Instance freeUnit.
  Existing Instance freeSigT.

  Definition trackingAttributes' := trackingAttributes.
  Definition trackingConfiguration' := @trackingConfiguration _ _ plainAttributes _.
  Existing Instance trackingAttributes' | 0.
  Existing Instance trackingConfiguration' | 0.
  Typeclasses Transparent trackingAttributes'.
  Typeclasses Transparent trackingConfiguration'.

  Ltac specialize_props := repeat 
    match goal with
    | h:?P -> _, p:?P |- _ => match type of P with Prop => specialize (h p) end
    end.

  Notation "n <=? m" := (le_dec n m).

  Arguments fastPolicy [_ _ _ _] _.
  Arguments free [_] _ [_].

  Instance freeRouterType {S:SpaceSearch} : @Free S RouterType.
    refine {| free := union (single internal) (single external) |}.
  Proof.    
    intros [].
    - apply unionOk.
      left.
      apply singleOk.
      reflexivity.
    - apply unionOk.
      right.
      apply singleOk.
      reflexivity.
  Defined.

  Instance freeOutgoing {S:SpaceSearch} : forall r, @Free S (outgoing [internal & r]).
    unfold outgoing.
    intro r.
    refine {| free := union (bind (free (router internal)) _)
                            (bind (free {d:router external & neighbor r d}) _) |}. {
      (* internal router *)
      intro d.
      destruct (r =? d).
      - exact empty.  
      - refine (single [[internal & d] & _]).
        compute.
        break_match.
        + congruence.
        + exact tt.
    } {
      (* external router *)
      intros [d n].
      exact (single [[external & d] & n]).
    } 
  Proof.
    (* freeOk *)
    cbn.
    intros [[[] d] c].
    - apply unionOk.
      left.
      apply bindOk.
      exists d.
      constructor; [apply freeOk|].
      case (r =? d).
      + intro.
        subst.
        exfalso.
        break_match.
        * destruct c.
        * congruence.
      + intro.
        apply singleOk.
        break_match.
        match goal with
        | |- [_ & ?E] = _ => generalize E
        end. 
        intro c'.
        f_equal.
        clear -c c' n.
        cbn in *.
        compute in *.
        break_match; [destruct c'|].
        destruct c, c'.
        reflexivity.
    - apply unionOk.
      right.
      apply bindOk.
      exists [d & c].
      constructor; [apply freeOk|].
      apply singleOk.
      reflexivity.
  Defined.

  (* compied from freeOutgoing *)
  Instance freeReceivedIncoming {S:SpaceSearch} : forall r, @Free S {s : Router & connection s [internal & r]}.
    intro r.
    refine {| free := union (bind (free (router internal)) _)
                            (bind (free {d:router external & neighbor r d}) _) |}. {
      (* internal router *)
      intro d.
      destruct (r =? d).
      - exact empty.  
      - refine (single [[internal & d] & _]).
        compute.
        break_match.
        + congruence.
        + exact tt.
    } {
      (* external router *)
      intros [d n].
      exact (single [[external & d] & n]).
    } 
  Proof.
    (* freeOk *)
    cbn.
    intros [[[] d] c].
    - apply unionOk.
      left.
      apply bindOk.
      exists d.
      constructor; [apply freeOk|].
      case (r =? d).
      + intro.
        subst.
        exfalso.
        cbn in c.
        break_match.
        * destruct c.
        * congruence.
      + intro.
        apply singleOk.
        break_match.
        match goal with
        | |- [_ & ?E] = _ => generalize E
        end. 
        intro c'.
        f_equal.
        clear -c c' n.
        cbn in *.
        compute in *.
        break_match; [destruct c'|].
        destruct c, c'.
        reflexivity.
    - apply unionOk.
      right.
      apply bindOk.
      exists [d & c].
      constructor; [apply freeOk|].
      apply singleOk.
      reflexivity.
  Defined.

  Instance freeIncoming {S:SpaceSearch} : forall r, @Free S (incoming [internal & r]).
    intros r.
    refine {| free := union (single injected) (bind (free _) (fun i => single (received i))) |}.
  Proof.
    intros s.
    rewrite <- unionOk.
    destruct s as [|s].
    - left.
      apply singleOk.
      reflexivity.
    - right.
      rewrite <- bindOk.
      exists s.
      constructor; [apply freeOk|].
      apply singleOk.
      reflexivity.
  Defined.

  Definition Forwardable r p :=
    {ai:@RoutingInformation trackingAttributes' & {s:incoming r | forwardable r s p ai}}.

  Instance eqDecForwardable : forall r p, eqDec (Forwardable r p).
    intros.
    unfold Forwardable.
    apply eqDecSigT.
  Defined.

  Definition feasiblePath (r ri:router internal) (re:router external) 
                          (n:neighbor ri re) : incoming [internal & r] * Path.
    refine(match r =? ri with left e => _ | right e => _ end).
    - refine (let c : connection [external & re] [internal & r] := _ in (_,_)).
      + apply (rew <- [fun ri => neighbor ri re] e in n).
      + refine (received [[external & re] & _]).
        apply c.
      + exact (hop [external & re] [internal & r] c 
              (start [external & re])).
    - refine (let c : connection [internal & ri] [internal & r] := _ in (_,_)).
      + cbn.
        break_match.
        * exfalso. 
          apply e.
          symmetry.
          trivial.
        * exact tt.
      + refine (received [[internal & ri] & _]).
        apply c.
      + exact (hop [internal & ri] [internal & r] c
              (hop [external & re] [internal & ri] n 
              (start [external & re]))).
  Defined.

  Definition transmit' (r ri:router internal) (re:router external) (n:neighbor ri re) (p:Prefix) 
                       (a0:@PathAttributes plainAttributes) : incoming [internal & r] * RoutingInformation.
    refine(let sP := feasiblePath r ri re n in ((fst sP),_)).
    refine(match transmit (snd sP) p (available a0) _ with
    | available a => available {|current:=a; original:=a0; path:=(snd sP)|} 
    | notAvailable => notAvailable 
    end).
  Proof.
    abstract (
      inline_all;
      unfold feasiblePath;
      destruct (r =? ri); compute; intuition
    ).
  Defined.

  Lemma longPathsAreNotForwardable r s p (a0 a:@PathAttributes plainAttributes) r0 r1 r2 r3 r4 r5 P c01 c23 c45 :
    ~@forwardable _ _ plainAttributes _ [internal & r] s p (available {| original := a0; current := a; path := hop r0 r1 c01 (hop r2 r3 c23 (hop r4 r5 c45 P)) |}).
  Proof.
    unfold forwardable, not.
    intros [pok tok].
    specialize_props.
    destruct tok as [tok pok'].
    cbn in pok'.
    destruct pok' as [? pok'].
    subst_max.
    specialize (pok' eq_refl).
    cbn in pok'.
    subst_max.
    cbn in pok.
    break_and.
    subst_max.
    unfold path in *.
    Opaque transmit.
    cbn in *.
    rename r3 into ri.
    rename r5 into re.
    rename c01 into crri.
    rename c23 into crire.
    enough (available a = notAvailable) by congruence.
    rewrite <- tok; clear tok.
    destruct ri as [[] ri].
    Set Printing Width 200.
    - (* ri is internal *)
      destruct re as [[] re].
      + (* re is internal *)
        Transparent transmit.
        cbn.
        reflexivity.
      + (* ri is external *)
        cbn.
        unfold import'. 
        unfold bindRoutingInformation. 
        cbn.
        repeat break_match; congruence.
    - (* ri is external *)
      cbn.
      unfold import'. 
      unfold bindRoutingInformation. 
      cbn.
      repeat break_match; congruence.
  Qed.

  Definition forwardableImpliesTransmit r s p ai : 
    @forwardable _ _ plainAttributes _ [internal & r] s p (available ai) -> {ri:router internal & {re:router external & {n:neighbor ri re |
          fst (transmit' r ri re n p (original ai)) = s /\ snd (transmit' r ri re n p (original ai)) = available ai}}}.
  Proof.
    intro tok.
    destruct ai as [a0 a P].
    refine (match P as P' return P = P' -> _ with
    | hop r' ri' c (hop ri re' n (start re)) => fun _ => _
    | hop r' re' c (start re) => fun _ => _
    | _ => fun _ => False_rect _ _
    end eq_refl).
    + (* path length is 0 *)
      idtac.
      subst_max.
      unfold forwardable in *.
      intuition.
      specialize_props.
      intuition.
      cbn in *.
      destruct r0 as [[] r'].
      - (* router is internal, which cannot originate *)
        cbn in *.
        congruence.
      - (* router is external, which means it's <> r *)
        intuition.
        congruence.
    + (* path length is 1 *)
      subst_max.
      Opaque transmit.
      Set Printing Width 200.
      cbn in tok.
      unfold original.
      destruct tok as [[] tok].
      subst_max.
      specialize (tok (conj I eq_refl)).
      destruct tok as [tok [? eq]].
      subst_max.
      specialize (eq eq_refl). 
      cbn in eq.
      subst_max.
      exists r.
      destruct re as [[] re].
      - (* re coming from internal *)
        exfalso.
        Transparent transmit.
        cbn in *.
        congruence.
      - (* re coming from external *)
        Opaque transmit.
        exists re. 
        exists c.
        intuition.
        * unfold transmit'.
          cbn.
          unfold feasiblePath.
          cbn in c.
          generalize (r =? r) at 1.
          intro.
          destruct s; [|congruence].
          cbn.
          simpl_eq.
          cbn.
          reflexivity.
        * unfold transmit'.
          cbn in *.
          assert (snd (feasiblePath r r re c) = hop [external & re] [internal & r] c (start [external & re])) as e. {
            clear.
            unfold feasiblePath.
            cbn.
            generalize (r =? r) at 1.
            intro s; destruct s; [|congruence].
            cbn.
            simpl_eq.
            cbn.
            reflexivity.
          }
          revert tok.
          generalize_proofs.
          revert p1.
          cbn in *.
          rewrite e.
          intros.
          unfold pathOk in p1.
          generalize_proofs.
          rewrite tok.
          reflexivity.
    + (* path length is 2 *)
      subst_max.
      Opaque transmit.
      Set Printing Width 200.
      cbn in tok.
      unfold original.
      destruct tok as [[[] ?] tok].
      subst_max.
      specialize (tok (conj (conj I eq_refl) eq_refl)).
      destruct tok as [tok [? eq]].
      subst_max.
      specialize (eq eq_refl). 
      cbn in eq.
      subst_max.
      rename re' into ri.
      destruct ri as [[] ri]; destruct re as [[] re].
      - (* re coming from internal *)
        exfalso.
        Transparent transmit.
        cbn in *.
        congruence.
      - exists ri.
        exists re. 
        exists n.
        intuition.
        * unfold transmit'.
          cbn.
          unfold feasiblePath.
          destruct (r =? ri). {
            exfalso.
            subst_max.
            clear -c.
            cbn in c.
            break_match; [|congruence].
            inversion c.
          } { 
            cbn.
            f_equal.
            f_equal.
            cbn in c.
            clear.
            destruct (ri =? r).
            - congruence.
            - destruct c.
              reflexivity.
          }
        * unfold transmit'.
          cbn.
          case (ri =? r). {
            intro.
            exfalso.
            subst_max.
            clear -c.
            cbn in c.
            break_match; [|congruence].
            inversion c.
          } {
            intro.
            assert (snd (feasiblePath r ri re n) = (hop [internal & ri] [internal & r] c (hop [external & re] [internal & ri] n (start [external & re])))) as E. {
              clear -n0.
              unfold feasiblePath.
              break_match; [congruence|].
              cbn.
              f_equal.
              clear.
              cbn in c.
              break_match; [congruence|].
              destruct c.
              reflexivity.
            }
            generalize_proofs.
            revert p2.
            cbn.
            rewrite E.
            intro p2.
            revert tok.
            generalize_proofs.
            cbn.
            intro.
            rewrite tok.
            reflexivity.
          }
      - exfalso.
        Transparent transmit.
        cbn in *.
        congruence.
      - exfalso.
        Transparent transmit.
        cbn in *.
        break_match; congruence.
    + (* paths with length > 2 *)
      subst_max.
      apply longPathsAreNotForwardable in tok.
      trivial.
  Defined.

  Lemma transmitIsForwardable r ri re n p a0 :
    @forwardable _ _ plainAttributes _ [internal & r] (fst (transmit' r ri  re  n  p a0 )) p (snd (transmit' r ri  re  n  p a0 )).
  Proof.
    unfold forwardable.
    break_match; [|intuition].
    intuition.
    - cbn in *. 
      break_match; [|congruence].
      find_inversion.
      clear.
      cbn.
      unfold feasiblePath.
      break_match.
      + cbn. intuition.
      + cbn. intuition.
    - cbn in *. 
      break_match; [|congruence].
      find_inversion.
      cbn in *.
      match goal with h:_ = ?A |- _ = ?A => rewrite <- h end.
      generalize_proofs.
      congruence.
    - rename Heqr0 into e.  
      unfold transmit' in e.
      revert e.
      generalize_proofs.
      cbn.
      intro.
      destruct (transmit (snd (feasiblePath r ri re n)) p (available a0) p1); [|congruence].
      find_inversion.
      clear.
      cbn.
      unfold feasiblePath.
      destruct (r =? ri).
      + cbn. 
        intuition.
        simpl_eq.
        cbn. 
        reflexivity.
      + cbn.
        intuition.
        simpl_eq.
        cbn.
        reflexivity.
  Qed.

  Definition localPolicy 
    (Q:forall r, incoming [internal & r] -> outgoing [internal & r] -> Prefix ->
                 @RoutingInformation trackingAttributes' ->
                 @RoutingInformation trackingAttributes' ->
                 @RoutingInformation trackingAttributes' -> bool)
    (r:Router) (i:incoming r) (o:outgoing r) (p:Prefix)
    (ai:@RoutingInformation trackingAttributes')
    (al:@RoutingInformation trackingAttributes')
    (ae:@RoutingInformation trackingAttributes') : bool.
  destruct r as [[] r].
  - exact (Q r i o p ai al ae).
  - exact true.
  Defined.

  Definition TrackingOk r p := {s : incoming [internal & r] & {a : @RoutingInformation trackingAttributes' | @forwardable _ _ plainAttributes _ [internal & r] s p a}}.

  Instance freeNeighbor `{SpaceSearch} : forall s d, Free (neighbor s d).
    intros.
    refine {| free := bind (free {d':router external & neighbor s d'}) _ |}. {
      intros [d' c].
      destruct (d' =? d).
      + subst_max.
        exact (single c).
      + exact empty.
    }    
  Proof.
    intro c.
    apply bindOk.
    exists [d & c].
    constructor; [apply freeOk|].
    cbn.
    break_match; [|congruence].
    simpl_eq.
    cbn.
    apply singleOk.
    reflexivity.
  Defined.

  Instance freeTrackingOk : forall r p, Free (TrackingOk r p). 
    intros r p.
    refine {| free:=_; freeOk:=_ |}. {
    refine (union _ _).
    - refine (bind (free (incoming [internal & r])) (fun s => _)).
      refine (single _).
      refine [s & exist _ notAvailable _].
      cbn; trivial.
    - refine (bind (free (@PathAttributes plainAttributes)) (fun a0 => _)).
      refine (bind (free (router internal)) (fun ri => _)).
      refine (bind (free (router external)) (fun re => _)).
      refine (bind (free (neighbor ri re)) (fun n => _)).
      refine (single _).
      refine (let sai := transmit' r ri re n p a0 in _).
      refine [fst sai & exist _ (snd sai) _]. 
      inline_all.
      apply (transmitIsForwardable r ri re n p a0).
    } {
      idtac.
      unfold TrackingOk.
      intros [s [a F]].
      rewrite <- unionOk.
      destruct a as [a|].
      - right.
        specialize (forwardableImpliesTransmit r s p a F); intro T.
        destruct T as [ri [re [n [? h]]]].
        rewrite <- bindOk; exists (original a).
        constructor; [apply freeOk|].
        rewrite <- bindOk; exists ri.
        constructor; [apply freeOk|].
        rewrite <- bindOk; exists re.
        constructor; [apply freeOk|].
        rewrite <- bindOk; exists n.
        constructor; [apply freeOk|].
        rewrite <- singleOk.
        subst_max.
        f_equal.
        generalize_proofs.
        f_equal; [|trivial].
        intro P.
        revert f F.
        rewrite <- P.
        intros.
        generalize_proofs.
        reflexivity.
      - left.
        rewrite <- bindOk; exists s.
        constructor; [apply freeOk|].
        rewrite <- singleOk.
        generalize_proofs.
        reflexivity.
    }
  Defined.      

  Require Import Coq.Logic.Classical_Pred_Type.
  Require Import Coq.Logic.Classical_Prop.

  Lemma bindFreeOk {A B} `{S':SpaceSearch} `{@Free S' A} {f} {b:B} (a:A) : ~contains b (bind (free A) f) -> ~contains b (f a).
    clear.
    intros h. 
    rewrite <- bindOk in h.
    apply not_ex_all_not with (n:=a) in h. 
    apply not_and_or in h.
    destruct h as [h|]. {
      exfalso.
      apply h.
      apply freeOk.
    }
    intuition.
  Qed.

  Definition constrain (b:bool) := if b then single tt else empty.

  Variable Query : Type.
  Variable denoteQuery : Query -> forall r, incoming [internal & r] -> outgoing [internal & r] -> Prefix ->
                         @RoutingInformation trackingAttributes' ->
                         @RoutingInformation trackingAttributes' ->
                         @RoutingInformation trackingAttributes' -> bool.

  Definition fastPolicyDec' (Q:Query) :
    option {r:router internal & incoming [internal & r] * outgoing [internal & r] * Prefix * 
                 @RoutingInformation trackingAttributes' * 
                 @RoutingInformation trackingAttributes' * 
                 @RoutingInformation trackingAttributes' * 
                 @RoutingInformation trackingAttributes'} % type.
    apply search.
    refine (bind (free (router internal)) (fun r => _)).
    refine (bind (free (outgoing [internal & r])) (fun d => _)).
    refine (bind (free Prefix) (fun p => _)).
    refine (bind (free (TrackingOk r p)) _); intros [s  [ai  _]].
    refine (bind (free (TrackingOk r p)) _); intros [s' [ai' _]].
    refine (let al' := @import' _ trackingAttributes' _ [internal & r] _ s  p ai in _).
    refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
    refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
    refine (if (_:bool) then single _ else empty).
    exact (sumBoolAnd (localPref'(al') <=? localPref'(al)) (bool2sumbool (negb (denoteQuery Q r s d p ai al ao)))).
    exact [r & (s, d, p, ai, ai', al, ao)].
  Defined.

  Definition fastPolicyDec Q : decide (fastPolicy (localPolicy (denoteQuery Q))).
    unfold decide.
    destruct (fastPolicyDec' Q) as [res|] eqn:e.
    - right.
      unfold fastPolicyDec' in *.
      apply searchOk in e.
      apply bindOk in e; destruct e as [r [_ e]].
      apply bindOk in e; destruct e as [d [_ e]].
      apply bindOk in e; destruct e as [p [_ e]].
      unfold TrackingOk in e.
      apply bindOk in e; destruct e as [[s  [ai  T ]] [_ e]].
      apply bindOk in e; destruct e as [[s' [ai' T']] [_ e]].
      unfold constrain in *.
      break_if; revgoals. {
        apply emptyOk in e.
        intuition.
      }
      Set Printing All.
      idtac.
      unfold sumbool2bool in *.
      break_match; [|congruence].
      Unset Printing All.
      idtac.
      break_and.
      unfold fastPolicy, not.
      intro h.
      specialize (h [internal & r] s d p s' ai ai' T T'). 
      intuition.
      rewrite negb_true_iff in *.
      unfold localPolicy in *.
      clear Heqb.
      enough (true = false) by congruence;
      match goal with 
      | F:_ = false, T:_ = true |- _ => rewrite <- F; rewrite <- T
      end.
      reflexivity.
    - left.
      unfold fastPolicy.
      intros r s d p s' ai ai' F F' L.
      unfold fastPolicyDec' in *.
      destruct r as [[] r].
      + (* r is internal  *)
        cbn.
        eapply searchOk' in e.

        assert (forall {A B} `{S:SpaceSearch} `{@Free S A} {f} {b:B} (a:A), ~contains b (bind (free A) f) -> ~contains b (f a)) as bindFreeOk. {
          clear.
          intros A B ? ? f b a h.
          rewrite <- bindOk in h.
          apply not_ex_all_not with (n:=a) in h. 
          Require Import Coq.Logic.Classical_Prop.
          apply not_and_or in h.
          destruct h as [h|]. {
            exfalso.
            apply h.
            apply freeOk.
          }
          intuition.
        }
        apply bindFreeOk  with (a:=r) in e.
        apply bindFreeOk with (a:=d) in e.
        apply bindFreeOk with (a:=p) in e.
        unfold TrackingOk in *.
        apply bindFreeOk with (a:=[s  & exist _ ai  F ]) in e.
        apply bindFreeOk with (a:=[s' & exist _ ai' F']) in e.
        unfold constrain in *.
        break_if. {
          exfalso.
          apply e.
          assert (forall {A} {a:A}, contains a (single a)) as singleOk'. {
            clear.
            intros.
            apply singleOk.
            reflexivity.
          }
          apply singleOk'.
        }
        Set Printing All.
        idtac.
        unfold sumbool2bool in *.
        break_match; [congruence|].
        Unset Printing All.
        idtac.
        apply not_and_or in n.
        destruct n; [intuition;fail|].
        rewrite negb_true_iff in *.
        rewrite not_false_iff_true in *.
        intuition.
      + (* policy always holds for external neighbors*)
        clear.
        cbn.
        reflexivity.
  Defined.

  Definition policySemiDec Q : option (policy (localPolicy (denoteQuery Q))).
    refine(if fastPolicyDec Q then Some _ else None).
    apply fastPolicyImpliesPolicy; trivial.
  Defined.

  Inductive Routing (r:router internal) := 
  | onlyNotAvailable : incoming [internal & r] -> Routing r
  | allAvailable (ri:router internal) (re:router external) : neighbor ri re -> Routing r.

  Arguments onlyNotAvailable [_] _.
  Arguments allAvailable [_] _ _ _.

  Definition routingToTracking r p (R:Routing r) : Space (TrackingOk r p).
    refine (match R with
    | onlyNotAvailable s => _
    | allAvailable ri re n => _
    end).
    - refine (single _).
      refine [s & exist _ notAvailable _].
      cbn; trivial.
    - refine (bind (free (@PathAttributes plainAttributes)) (fun a0 => _)).
      refine (single _).
      refine (let sai := transmit' r ri re n p a0 in _).
      refine [fst sai & exist _ (snd sai) _]. 
      inline_all.
      apply (transmitIsForwardable r ri re n p a0).
  Defined.      

  Definition bgpvCore (Q:Query) (v:{r:router internal & (outgoing [internal & r] * Routing r * Routing r) % type}) :
    option {r:router internal & (incoming [internal & r] * outgoing [internal & r] * Prefix * 
                     @RoutingInformation trackingAttributes' * 
                     @RoutingInformation trackingAttributes' * 
                     @RoutingInformation trackingAttributes' * 
                     @RoutingInformation trackingAttributes') % type}.
    destruct v as [r [[d R] R']].
    apply search.
    refine (bind (free Prefix) (fun p => _)).
    refine (bind (routingToTracking r p R ) _); intros [s  [ai  _]].
    refine (bind (routingToTracking r p R') _); intros [s' [ai' _]].
    refine (let al' := @import' _ trackingAttributes' _ [internal & r] _ s  p ai in _).
    refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
    refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
    refine (if (_:bool) then single _ else empty).
    exact (sumBoolAnd (localPref'(al') <=? localPref'(al)) (bool2sumbool (negb (denoteQuery Q r s d p ai al ao)))).
    refine [r & (s, d, p, ai, ai', al, ao)].
  Defined.

  Definition optionToSpace `{SpaceSearch} {A} (o:option A) : Space A :=
    match o with None => empty | Some a => single a end.

  Context {S':SpaceSearch}.

  Variable bgpvScheduler : forall Q v, {o | o = search (bind v (compose optionToSpace (bgpvCore Q)))}.

  (*
  Variable parallelSearch : forall A B, (A -> option B) * Space A -> option B.
  Arguments parallelSearch [_ _] _.
  Variable parallelSearchOk : forall A B (f:A -> option B) S, parallelSearch (f,S) = search (bind S (compose optionToSpace f)).
  *)

  Instance freeRouting `{SpaceSearch} r : Free (Routing r).
    refine {|free := _ |}.
    refine (union _ _). {
      refine (bind (free (incoming [internal & r])) (fun s => _)).
      refine (single (onlyNotAvailable s)).
    } {
      refine (bind (free (router internal)) (fun ri => _)).
      refine (bind (free (router external)) (fun re => _)).
      refine (bind (free (neighbor ri re)) (fun n => _)).
      refine (single (allAvailable ri re n)).
    }
  Proof.
    intros R.
    rewrite <- unionOk.
    destruct R as [s|ri re n].
    - left.
      rewrite <- bindOk; exists s.
      constructor; [apply freeOk|].
      rewrite <- singleOk.
      reflexivity.
    - right.
      rewrite <- bindOk; exists ri.
      constructor; [apply freeOk|].
      rewrite <- bindOk; exists re.
      constructor; [apply freeOk|].
      rewrite <- bindOk; exists n.
      constructor; [apply freeOk|].
      rewrite <- singleOk.
      reflexivity.
  Defined.

  Instance freeSigT {A B} `{Free A} `{forall a:A, Free (B a)} : Free {a : A & B a}.
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

  Instance freeProd {A B} `{S:SpaceSearch} `{@Free S A} `{@Free S B} : @Free S (A * B).
    refine {|
      free := bind (free A) (fun a => 
              bind (free B) (fun b =>
              single (a, b)))
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

  Definition parallelBGPV (Q:Query) := let ' exist _ v _ := bgpvScheduler Q (free _) in v.
 
  Definition pickOne `{SpaceSearch} {A} : Space A -> Space A := compose optionToSpace search.
 
  Definition parallelBGPVImport (Q:Query) : option {r : router internal & (incoming [internal & r] * outgoing [internal & r] * Prefix * RoutingInformation * RoutingInformation * RoutingInformation * RoutingInformation)%type}.
    refine (let ' exist _ v _ := bgpvScheduler Q _ in v).
    refine (bind (free (router internal)) (fun r => _)).
    refine (bind (pickOne (free (outgoing [internal & r]))) (fun o => _)).
    refine (bind (free (Routing r)) (fun R => _)).
    refine (single [r & (o,R,R)]).
  Defined.

  Definition forwardableToRouting {r} {s} {p} {ai:@RoutingInformation trackingAttributes'} (F:@forwardable _ _ plainAttributes _ [internal & r] s p ai) : Routing r.
    destruct ai as [ai|].
    + destruct (forwardableImpliesTransmit r s p ai F) as [ri [re [n _]]].
      exact (allAvailable ri re n).
    + exact (onlyNotAvailable s).
  Defined.             

  Lemma routingToTrackingComposedWithForwardableToRouting {B r s p ai f F} {b:B}:
    ~contains b (bind (routingToTracking r p (forwardableToRouting F)) f) -> ~contains b (f [s & exist _ ai F]).
  Proof.
    clear.
    intro e.
    unfold TrackingOk in *.
    Lemma bindOk' : forall {A B} `{SpaceSearch} {S} {f} {b:B} (a:A), ~contains b (bind S f) -> ~contains a S \/ ~contains b (f a).
        clear.
        intros A B ? S f b a h.
        rewrite <- bindOk in h.
        apply not_ex_all_not with (n:=a) in h. 
        Require Import Coq.Logic.Classical_Prop.
        apply not_and_or in h.
        destruct h; intuition. 
    Qed. 
    refine (let e' := bindOk' _ e in _). {
      exact [s & exist _ ai F].
    }
    refine ((fun e'' => _) e'); clear e e'; rename e'' into e.
    destruct e; [|intuition;fail].
    exfalso.
    apply H1; clear H1.
    unfold forwardableToRouting.
    Require Import SymbolicExecution.
    branch; cbn.
    - branch.
      branch.
      branch.
      subst_max.
      clear Heqs0.
      rename x into ri.
      rename x0 into re.
      rename x1 into n.
      rename p0 into ai.
      idtac.
      unfold routingToTracking.
      apply bindOk.
      exists (original ai).
      constructor; [apply freeOk; fail|].
      apply singleOk.
      destruct a as [e e'].
      subst_max.
      f_equal.
      assert (forall {A} {P : A -> Prop} {a a':A} {p:P a} {p':P a'}, a = a' -> exist _ a p = exist _ a' p') as e. {
        intros.
        subst_max.
        f_equal.
        proof_irrelevance.
        reflexivity.
      }
      apply e.
      intuition.
    - apply singleOk.
      f_equal.
      f_equal.
      cbn in *.
      destruct F.
      reflexivity.
  Qed.

  Definition parallelBGPVDec Q : decide (fastPolicy (localPolicy (denoteQuery Q))).
    unfold decide.
    destruct (parallelBGPV Q) as [res|] eqn:e.
    - right.
      unfold parallelBGPV in *.
      break_match.
      subst_max.
      clear Heqs.
      apply searchOk in e.
      apply bindOk in e; destruct e as [[r [[d R] R']] [_ e]]. 
      unfold compose in e.
      unfold optionToSpace in e.
      branch; revgoals. {
        apply emptyOk in e.
        destruct e.
      }
      apply singleOk in e.
      subst_max.
      rename Heqo into e.
      unfold bgpvCore in e.
      apply searchOk in e.
      apply bindOk in e; destruct e as [p [_ e]].
      unfold TrackingOk in e.
      apply bindOk in e; destruct e as [[s  [ai  F ]] [? e]].
      apply bindOk in e; destruct e as [[s' [ai' F']] [? e]].
      branch; revgoals. {
        apply emptyOk in e.
        destruct e.
      }
      unfold sumbool2bool in *.
      break_match; [|congruence].
      break_and.
      unfold fastPolicy, not.
      intro h.
      specialize (h [internal & r] s d p s' ai ai' F F'). 
      intuition.
      rewrite negb_true_iff in *.
      unfold localPolicy in *.
      clear Heqb.
      enough (true = false) by congruence;
      match goal with 
      | F:_ = false, T:_ = true |- _ => rewrite <- F; rewrite <- T
      end.
      reflexivity.
    - left.
      unfold parallelBGPV in *.
      unfold fastPolicy.
      intros r s d p s' ai ai' F F' L.
      destruct r as [[] r].
      + (* r is internal  *)
        cbn.
        break_match.
        subst_max.
        clear Heqs0.
        (* COPIED FROM fastPolicyDec *)
        assert (forall {A B} `{S:SpaceSearch} `{@Free S A} {f} {b:B} (a:A), ~contains b (bind (free A) f) -> ~contains b (f a)) as bindFreeOk. {
          clear.
          intros A B ? ? f b a h.
          rewrite <- bindOk in h.
          apply not_ex_all_not with (n:=a) in h. 
          Require Import Coq.Logic.Classical_Prop.
          apply not_and_or in h.
          destruct h as [h|]. {
            exfalso.
            apply h.
            apply freeOk.
          }
          intuition.
        }
        assert (forall {A B} `{SpaceSearch} `{Free A} {f:A->Space B} {a:A}, search (bind (free A) f) = None -> forall b, ~contains b (f a)) as searchOk''. {
          clear -bindFreeOk.
          intros.
          rename H into e.
          eapply searchOk' in e.
          eapply bindFreeOk with (a:=a) in e.
          apply e.
        }          
        refine (let e' := searchOk'' _ _ _ _ _ _ _ e in _). {
          refine [r & (d, forwardableToRouting F, forwardableToRouting F')].
        }
        refine ((fun e'' => _) e').
        clear e' e; rename e'' into e.
        unfold compose in e.
        unfold optionToSpace in e.
        break_match. {
          exfalso.
          specialize (e s0).
          apply e.
          apply singleOk.
          reflexivity.
        }
        clear e.
        rename Heqo into e.
        clear searchOk''.
        unfold bgpvCore in e.
        refine (let al  := @import' _ trackingAttributes' _ [internal & r] _ s' p ai' in _).
        refine (let ao  := @export' _ trackingAttributes' _ [internal & r] _ s' d p al in _).
        apply (searchOk' (a :=[r & (s, d, p, ai, ai', al, ao)])) in e.
        apply bindFreeOk with (a:=p) in e.
        unfold TrackingOk in *.
        apply routingToTrackingComposedWithForwardableToRouting in e.
        apply routingToTrackingComposedWithForwardableToRouting in e.
        cbn in e.
        break_match. {
          exfalso.
          apply e; clear e.
          apply singleOk.
          reflexivity.
        }
        clear e.
        rename Heqb into e.
        unfold sumbool2bool in *.
        break_match; [congruence|].
        apply not_and_or in n.
        destruct n; [intuition;fail|].
        rewrite negb_true_iff in *.
        rewrite not_false_iff_true in *.
        intuition; fail.
      + (* policy always holds for external neighbors*)
        clear.
        cbn.
        reflexivity.
  Qed.

  Definition parallelPolicySemiDec Q : option (policy (localPolicy (denoteQuery Q))).
    refine(if parallelBGPVDec Q then Some _ else None).
    apply fastPolicyImpliesPolicy; trivial.
  Defined.
End BGPV.