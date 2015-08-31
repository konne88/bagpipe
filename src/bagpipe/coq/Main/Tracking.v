Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Bag.
Require Import Dict.
Require Import Misc.
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
Import ListNotations.
Import EqNotations.

Section Tracing.
  Context `{PrefixClass}. 
  Context `{TopologyClass}. 
  Context {plainAttributes : PathAttributesClass}. 
  Context {plainConfiguration : forall r, ConfigurationClass r}.
  Existing Instance enumerableIncoming.
  Existing Instance eqDecIncoming.
  Existing Instance eqDecUpdateMessage.

  Inductive Path : Type := 
  | start : Router -> Path
  | hop r d : connection r d -> Path -> Path.

  Fixpoint eqDecidePath (P P':Path) : {P = P'}+{P <> P'}.
    destruct P as [r|r d c p]; destruct P' as [r'|r' d' c' p'].
    - destruct (r =? r').
      + subst_max. left. reflexivity.
      + right. crush. 
    - right. intro H'. inversion H'.
    - right. intro H'. inversion H'.
    - destruct ((r =? r') && (d =? d')).
      + break_and; subst_max.
        destruct ((c =? c') && (eqDecidePath p p')).
        * left; crush.
        * right. 
          unfold not.
          intro X; inversion X.
          crush.  
      + right. 
        unfold not. 
        intro X; inversion X.
        crush.
  Defined.

  Instance eqDecPath : eqDec Path.
    constructor.
    apply eqDecidePath.
  Defined.    

  Fixpoint pathOk (P:Path) := 
    match P with
    | start _ => True
    | hop r d c P' => pathOk P' /\ 
                      r = match P' with 
                      | start r' => r' 
                      | hop _ d' _ _ => d' 
                      end
    end.

  Record Tracking := {
    original : PathAttributes;
    current : PathAttributes;
    path : Path
  }.

  Instance eqDecTracking : eqDec Tracking.
    constructor. repeat decide equality; repeat apply eqDecide.
  Defined.

  Instance trackingAttributes : PathAttributesClass. 
    refine {|
      PathAttributes := Tracking;
      localPref t := localPref (current t)
    |}.
  Defined.

  Instance trackingConfiguration r : ConfigurationClass r.
    refine {|
      import s p a :=
        let ' {| path:=P; current:=a; original:=a0 |} := a in
        match import r s p a with
        | notAvailable => notAvailable
        | available a' => available {| path:=P; original:=a0; current:=a' |}
        end;
      export s d p a := 
        let ' {| path:=P; current:=a; original:=a0 |} := a in
        match export r s d p a with
        | notAvailable => notAvailable
        | available a' => available {| path:=hop r (projT1 d) (projT2 d) P; original:=a0; current:=a' |}
        end;
      originate p a :=
        let ' {| path:=P; current:=a; original:=a0 |} := a in
        bool2sumbool (originate r p a) && (a =? a0) && (P =? start r)
    |}.
  Defined.

  Fixpoint transmit (P:Path) (p:Prefix) (a:@RoutingInformation plainAttributes) {struct P} : pathOk P -> @RoutingInformation plainAttributes.
    intro pok.
    refine(
      match P as P' return P = P' -> RoutingInformation with
      | start r => fun _ => if originate' r p a then a else notAvailable
      | hop r d c P' => fun _ => _
      end (eq_refl P)).
    subst. cbn in *. destruct pok. 
    refine(
      let i := 
        match P' as P'' return P' = P'' -> incoming r with
        | start r => fun _ => injected
        | hop s r c _ => fun e => _
        end (eq_refl P')
      in export' r i [d & c] p (import' r i p (transmit P' p a _))
    ).
    subst. exact (received [s & c]).
  Proof.
    trivial.
  Defined.

  Definition forwardable r (s:incoming r) (p:Prefix) (a:@RoutingInformation trackingAttributes) : Prop.
    refine(match a with
    | notAvailable => True
    | available a => let P := path a in 
      pathOk P /\ forall pok:pathOk P, 
        transmit P p (available (original a)) pok = available (current a) /\
        match P with
        | start r' => r = r' /\ s = injected
        | hop r' d' c _ => r = d' /\ forall e:r = d', s = rew <- e in received [r' & c]
        end
    end).
  Defined.

  Opaque eqDecide.
  Opaque enumerate.
  Hint Unfold lookup update update' overwrite overwrite' build edge.
  Hint Unfold fst snd proj1_sig projT1 projT2 const id.
  Hint Unfold routerHandler messageHandling decisionProcess updateSendProcess 
              import' export' originate' bindRoutingInformation connection emptyRIB argMax.

  Lemma trackingOk : forall r s d (c:connection r d) p a,
    forwardable r s p a -> 
    forwardable d (received [r & c]) p (export' r s [d & c] p (import' r s p a)).
  Proof.
    intros.
    unfold forwardable in *.
    break_match; trivial.
    destruct a as [a|].
    - (* a is available *)
      rename p0 into a''.
      break_and.
      specialize (H2 H1).
      break_and.
      destruct (path a) eqn:?.
      + (* message was originated in router *)
        intuition; repeat symbolic_execution'' congruence.
        * intuition.
        * intuition; repeat symbolic_execution'' congruence.
      + (* message already had multiple hops through the network *)
        break_exists.
        subst_max.
        unfold eq_rect_r in *.
        unfold eq_rect in *.
        unfold eq_sym in *.
        subst.
        destruct a as [a0 a P].
        destruct a'' as [a0'' a'' P''].
        unfold path, original, current in *.
        unfold export', import' in *.
        unfold export, import in *.
        unfold trackingConfiguration in *.
        unfold bindRoutingInformation in *.
        break_and.
        subst_max.
        specialize (H4 eq_refl).
        subst_max.
        break_match. 
        * repeat symbolic_execution'' congruence.
        * subst.
          break_match; try congruence.
          break_match; try congruence.
          break_match; try congruence.
          break_match; try congruence.
          break_match; try congruence.
          subst.
          subst_max.
          find_inversion.
          subst.
          subst_max.
          find_inversion.
          simpl_existTs.
          subst.
          rename d1 into d.
          rename current0 into a'.
          rename r0 into s.
          rename c1 into crd.
          rename c0 into csr.
          rename p0 into P.
          find_inversion.
          intuition.
          {
            cbn; cbn in H1.
            break_and.
            intuition.
          } {
            rename a0'' into a0.
            intuition. {
              cbv delta [transmit].
              cbv iota.
              fold transmit.
              Opaque export' import' transmit.
              cbn.
              break_match.
              subst.
              generalize_proofs.
              simpl_uip.
              cbn.
              Transparent export' import' transmit.
              unfold export', import'.
              break_match; crush.
           } } 
           {
             repeat symbolic_execution'' congruence.
           }
    - (* a is not available *)
      exfalso.
      repeat symbolic_execution'' congruence.
  Qed.

  Lemma reachableImpliesForwardable :
    forall ns (R:reachable ns), (
      forall r (s:incoming r) p,
        let a := lookup (adjRIBsIn (lookup (routerState ns) r)) (s,p) in 
        forwardable r s p a
    ) /\ (
      forall s d (c:connection s d),
        let ms := lookup (linkState ns) [(s,d) & c] in
        forall m (mInMs:In m ms), forwardable d (received [s & c]) (nlri m) (attributes m)
    ).
  Proof.
    intros.
    induction R as [|ns ns'']. { crush. }
    destruct IHR as [Hrs Hls].
    constructor. 
    - (* router state *)
      intros.       
      destruct t as [m r' rs ls | ].
      + (* gen *)
        destruct m as [p' a'].
        unfold snd, fst in *.
        destruct (r =? r'); destruct (p =? p'). 
        subst. destruct (s =? injected).
        * subst.
          clear Hrs.
          clear Hls.
          unfold originate' in *.
          break_match. {
            (* injected available *)
            unfold originate in *.
            unfold trackingConfiguration in *.
            destruct p.
            unfold attributes, nlri in *.
            unfold sumbool2bool in *.
            break_match; try congruence.
            break_and.
            subst_max.
            inline_all.
            cbn.
            repeat symbolic_execution'' congruence.
            intuition.
          } {
            (* injected unavailable *)
            repeat symbolic_execution'' congruence.
            exact I.
          }
        * repeat symbolic_execution'' intuition.
        * repeat symbolic_execution'' intuition.
        * repeat symbolic_execution'' intuition.
        * repeat symbolic_execution'' intuition.
     + (* fwd *)
        destruct c as [sr' c].
        destruct sr' as [s' r'].
        destruct m as [p' a'].
        unfold snd, fst in *.
        destruct (r =? r'); destruct (p =? p'). 
        subst. destruct (s =? received [s' & c]).
        * subst. specialize (Hls s' r' c (updateMessage p' a')).
          unfold update' in Hls.
          simpl in Hls.
          rewrite assocLookupOk in Hls.
          specialize (Hls (in_eq _ _)).
          assert (a = a') as H'. {
            repeat symbolic_execution'' congruence.
          }
          rewrite H'. trivial.
        * repeat symbolic_execution'' intuition.
        * repeat symbolic_execution'' intuition.
        * repeat symbolic_execution'' intuition.
        * repeat symbolic_execution'' intuition.
    - (* link state *)
      intros.
      destruct t as [m' r|m' c'].
      + (* gen *)
        unfold build, lookup in ms. simpl in ms.
        clear R.
        destruct (s =? r); destruct (nlri m =? nlri m').
        subst. 
        apply in_app_or in mInMs. 
        destruct mInMs.
        * (* s = r, r = p', m in old ms*)
          repeat symbolic_execution'' intuition.
        * destruct m as [p a].
          destruct m' as [p' a'].
          subst ms.
          simpl.
          clear Hls.
          unfold nlri in *.
          subst_max.
          specialize (fun i=>Hrs r i p').
          inline_all.
          rename H1 into X.
          unfold generateHandler in X.
          unfold routerHandler in X.
          unfold build in X.
          simpl in *.
          destruct (r =? r); crush.
          Require Import Coq.Logic.Eqdep.
          simpl_eq.
          simpl in *.
          unfold const, fst, snd, id in *.
          simpl in *.
          unfold updateSendProcess in *.
          unfold build in *.
          unfold lookup in X at 1.
          break_if. {
            (* out = out' *)
            solve_by_inversion.
          } {
            (* out <> out' *)
            simpl in *. 
            clear n.
            destruct X; crush.
            simpl in *.
            destruct (p' =? p'); crush.
            match goal with
            | |- context[argMax' ?A ?B] => generalize (argMax' A B); intro
            end.
            unfold lookup.
            break_if; try congruence.
            unfold overwrite''.
            break_if; try congruence.
            break_if.
            - (* the generate announcement had highest local pref *)
              subst.
              unfold lookup. unfold overwrite.
              unfold originate' in *.
              cbn in e.
              apply trackingOk.
              clear Hrs.
              break_match; [|cbn; trivial].
              break_match.
              cbn in *.
              unfold sumbool2bool in *.
              break_if; try congruence.
              break_and.
              subst_max.
              assert (pathOk (start r)) as pok by crush. 
              intuition.
              cbn.
              break_match; congruence.
            - simpl. 
              unfold lookup. unfold overwrite.
              specialize (Hrs i).
              apply trackingOk.
              unfold lookup in *.
              trivial.
          }
        * (* r = s, p <> p' *)
          specialize (Hls s d c m).
          clear Hrs.
          cbn in Hls.
          apply Hls.
          clear Hls.
          unfold update'.
          unfold overwrite'.
          subst ms.
          subst_max.
          apply in_app_or in mInMs.
          intuition.
          unfold lookup.
          exfalso.
          subst Ers'.
          revert H1.
          subst E.
          subst rs'.
          unfold generateHandler.
          unfold routerHandler.
          break_match.
          unfold fst.
          unfold build in *.
          break_match; try congruence.
          Opaque messageHandling.
          simpl_eq.
          revert H3.
          unfold lookup in *.
          Set Printing Width 150.
          idtac.
          Transparent messageHandling.
          clear Heqp.
          cbn.
          unfold build.
          cbn.
          break_match; try congruence.
          match goal with 
          | |- context[updateSendProcess _ _ _ ?x] => generalize x
          end.
          unfold updateSendProcess.
          unfold build.
          intro.
          break_match; try auto.
          unfold In.
          intuition.
          destruct m.
          destruct m'.
          cbn in *.
          congruence.
        * (* s <> r *)
          specialize (Hls s d c m).
          clear Hrs.
          cbn in Hls.
          apply Hls.
          clear Hls.
          unfold update'.
          unfold overwrite'.
          subst ms.
          apply in_app_or in mInMs.
          intuition.
          exfalso.
          match goal with
          | h:In m ?E |- _ => enough (E = []) by (find_rewrite; auto)
          end.
          clear H1.
          inline_all.
          symbolic_execution'' congruence.
        * (* s <> r, p <> p' *)
          specialize (Hls s d c m).
          clear Hrs.
          cbn in Hls.
          apply Hls.
          clear Hls.
          unfold update'.
          unfold overwrite'.
          subst ms.
          apply in_app_or in mInMs.
          intuition.
          exfalso.
          match goal with
          | h:In m ?E |- _ => enough (E = []) by (find_rewrite; auto)
          end.
          clear H1.
          inline_all.
          symbolic_execution'' congruence.
     + (* fwd *)
        destruct c' as [s'r c'].
        destruct s'r as [s' r].
        unfold snd, fst in *.
        unfold build, lookup in ms. simpl in ms.
        clear R.
        destruct (s =? r); destruct (nlri m =? nlri m').
        subst. 
        apply in_app_or in mInMs. 
        destruct mInMs.
        * (* s = r, r = p', m in old ms*)
          specialize (Hls r d c m).
          repeat symbolic_execution'' intuition.
        * destruct m as [p a].
          destruct m' as [p' a'].
          subst ms.
          simpl.
          simpl in Hls.
          simpl in Hrs.
          specialize (Hls s' r c' (updateMessage p' a')).
          simpl in Hls.
          unfold update' in Hls.
          rewrite assocLookupOk in Hls.
          simpl in Hls.
          specialize (Hls (or_introl (eq_refl))).
          subst rs'.
          subst E.
          subst Ers'.
          rename H1 into X.
          unfold forwardHandler in X.
          unfold routerHandler in X.
          unfold build in X.
          simpl in *.
          destruct (r =? r); crush.
          Require Import Coq.Logic.Eqdep.
          unfold eq_rect_r in *.
          unfold eq_rect in *.
          unfold eq_sym in *.
          rewrite (UIP_refl _ _ e) in *.
          simpl in *.
          clear e.
          unfold const, fst, snd, id in *.
          simpl in *.
          unfold updateSendProcess in *.
          unfold build in *.
          unfold lookup in X at 1.
          break_match. {
            (* out = out' *)
            solve_by_inversion.
          } {
            (* out <> out' *)
            simpl in *. 
            clear n.
            destruct X; crush.
            simpl in *.
            destruct (p' =? p'); crush.
            match goal with
            | |- context[argMax' ?A ?B] => generalize (argMax' A B); intro
            end.
            destruct (i =? (received [s' & c'])).
            - (* the incomming announcement had highest local pref *)
              subst.
              unfold lookup. unfold overwrite.
              break_match; try solve_by_inversion.
              apply trackingOk.
              repeat symbolic_execution'' congruence.
            - simpl. 
              unfold lookup. unfold overwrite.
              break_match; try solve_by_inversion.
              specialize (Hrs r i p').
              unfold lookup in Hrs.
              apply trackingOk.
              repeat symbolic_execution'' congruence.
          }
        * (* r = s, p <> p' *)
          specialize (Hls s d c m).
          clear Hrs.
          cbn in Hls.
          apply Hls.
          clear Hls.
          unfold update'.
          unfold overwrite'.
          subst ms.
          break_match. {
            (* message was removed from link to be delivered *)
            novel_injections.
            subst_max.
            unfold connection in *.
            unfold edge in *.
            assert (c = c') by crush.
            subst_max.
            simpl_eq.
            Hint  Resolve in_cons in_split in_nil.
            apply in_cons.
            apply in_app_or in mInMs.
            intuition.
            unfold lookup.
            exfalso.
            subst Ers'.
            revert H1.
            subst E.
            subst rs'.
            unfold forwardHandler.
            unfold routerHandler.
            break_match.
            break_match.
            unfold build in *.
            injection Heqp.
            intros _ ?.
            clear Heqp.
            subst_max.
            break_match; try auto.
            Opaque messageHandling.
            simpl_eq.
            revert H3.
            unfold lookup in *.
            Set Printing Width 150.
            idtac.
            Transparent messageHandling.
            clear Heqp0.
            cbn.
            idtac.
            unfold build.
            cbn.
            break_match; try congruence.
            match goal with 
            | |- context[updateSendProcess _ _ _ ?x] => generalize x
            end.
            unfold updateSendProcess.
            unfold build.
            intro.
            break_match; try auto.
            unfold In.
            intuition.
            destruct m.
            destruct m'.
            cbn in *.
            congruence.
          } { 
            subst_max.
            apply in_app_or in mInMs.
            intuition.
            unfold lookup.
            exfalso.
            subst Ers'.
            revert H1.
            subst E.
            subst rs'.
            unfold forwardHandler.
            unfold routerHandler.
            break_match.
            break_match.
            unfold build in *.
            injection Heqp.
            intros _ ?.
            clear Heqp.
            subst_max.
            break_match; try auto.
            Opaque messageHandling.
            simpl_eq.
            revert H3.
            unfold lookup in *.
            Set Printing Width 150.
            idtac.
            Transparent messageHandling.
            clear Heqp0.
            cbn.
            idtac.
            unfold build.
            cbn.
            break_match; try congruence.
            match goal with 
            | |- context[updateSendProcess _ _ _ ?x] => generalize x
            end.
            unfold updateSendProcess.
            unfold build.
            intro.
            break_match; try auto.
            unfold In.
            intuition.
            destruct m.
            destruct m'.
            cbn in *.
            congruence.
          }
        * (* s <> r *)
          specialize (Hls s d c m).
          clear Hrs.
          cbn in Hls.
          apply Hls.
          clear Hls.
          unfold update'.
          unfold overwrite'.
          subst ms.
          break_match. {
            (* message was removed from link to be delivered *)
            novel_injections.
            subst_max.
            assert (c = c') by crush.
            subst_max.
            simpl_eq.
            Hint  Resolve in_cons in_split in_nil.
            apply in_cons.
            apply in_app_or in mInMs.
            intuition.
            unfold lookup.
            exfalso.
            match goal with
            | h:In m ?E |- _ => enough (E = []) by (find_rewrite; auto)
            end.
            clear H1.
            inline_all.
            symbolic_execution'' congruence.
          } {
            apply in_app_or in mInMs.
            intuition.
            exfalso.
            match goal with
            | h:In m ?E |- _ => enough (E = []) by (find_rewrite; auto)
            end.
            clear H1.
            inline_all.
            symbolic_execution'' congruence.
          }
        * (* s <> r, p <> p' *)
          specialize (Hls s d c m).
          clear Hrs.
          cbn in Hls.
          apply Hls.
          clear Hls.
          unfold update'.
          unfold overwrite'.
          subst ms.
          break_match. {
            (* message was removed from link to be delivered *)
            novel_injections.
            subst_max.
            assert (c = c') by crush.
            subst_max.
            simpl_eq.
            Hint  Resolve in_cons in_split in_nil.
            apply in_cons.
            apply in_app_or in mInMs.
            intuition.
            unfold lookup.
            exfalso.
            match goal with
            | h:In m ?E |- _ => enough (E = []) by (find_rewrite; auto)
            end.
            clear H1.
            inline_all.
            symbolic_execution'' congruence.
          } {
            apply in_app_or in mInMs.
            intuition.
            exfalso.
            match goal with
            | h:In m ?E |- _ => enough (E = []) by (find_rewrite; auto)
            end.
            clear H1.
            inline_all.
            symbolic_execution'' congruence.
          }
  Qed.

End Tracing.
