Extraction Language Haskell.

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

Section Simulation.

Definition decide P := {P} + {~P}.

Parameter CIDR : Type.
Parameter eqDecideCIDR : forall (c c':CIDR), decide (c = c').
Parameter IP : Type.
Parameter eqDecideIP : forall (i i':IP), decide (i = i').
Parameter ASN : Type.
Parameter eqDecideASN : forall (a a':ASN), decide (a = a').

Instance eqDecCIDR : eqDec CIDR.
  constructor.
  exact eqDecideCIDR.
Defined.

Instance eqDecIP : eqDec IP.
  constructor.
  exact eqDecideIP.
Defined.

Instance eqDecASN : eqDec ASN.
  constructor.
  exact eqDecideASN.
Defined.

Existing Instance eqDecProd.
Existing Instance eqDecMode.
Existing Instance eqDecUpdateMessage.

Instance natPrefix : PrefixClass := {| Prefix := CIDR |}.

(* see main bgp spec and https://tools.ietf.org/html/rfc1997 *)
Inductive BGPPathAttributes := {
  LOCAL_PREF : nat;
  COMMUNITIES : list nat;
  AS_PATH : list ASN
}.

Inductive Match :=
| RAny : Match
| RCommunityIs : nat -> Match
| RNot : Match -> Match
| RAnd : Match -> Match -> Match
| ROr : Match -> Match -> Match.

Inductive Modify :=
| MAddCommunity : nat -> Modify
| MStripCommunities : Modify.
  
Inductive Action :=
| AModify : Modify -> Action
| AAccept : Action
| AReject : Action.

Definition Rule := (Match * Action)%type.

Instance eqDecBGPPathAttributes : eqDec BGPPathAttributes.
  constructor.
  decide equality; apply eqDecide.
Defined.

Instance bgpPathAttributes : PathAttributesClass := {| 
  PathAttributes := BGPPathAttributes; 
  localPref := LOCAL_PREF 
|}.

Record Setup := {
  ases : list (ASN * list IP); 
  links : list ((ASN * IP * list Rule * list Rule) * (ASN * IP * list Rule * list Rule));
  injections : list ((ASN * IP) * CIDR)
}.

Inductive PolicyResult := replaced | filtered.

Fixpoint zipIn {A} `{eqDec A} l : list {a:A | In a l}.
  refine (match l with 
  | [] => []
  | a::l' => exist _ a _ :: (fun s => exist _ (proj1_sig s) _) <$> (zipIn _ _ l')
  end).
  - cbn. 
    left. 
    reflexivity.
  - destruct s as [a'].
    cbn.
    destruct (a =? a'); intuition.
Defined.

Lemma zipInOk {A} `{eqDec A} {l} : forall a : {a : A | In a l}, In a (zipIn l).
  intros.
  revert a.
  induction l.
  - cbn. 
    intros []. 
    trivial.
  - intros [a' ?].
    cbn.
    destruct (a =? a'). 
    + left.
      subst_max.
      generalize_proofs.
      reflexivity.
    + right.
      destruct i; [congruence|].
      specialize (IHl (exist _ a' i)).
      Arguments exist [_ _] _ _.
      idtac.
      Arguments exist [_] _ _ _.
Admitted.  

Instance enumerableSigIn {A} `{eqDec A} {l} : enumerable {a:A | In a l}.
  refine {| enumerate := zipIn l |}.
Proof.
  apply zipInOk.
Defined.     

Typeclasses Transparent const.

Instance eqDecProp {P:Prop} : eqDec P.
  constructor.
  intros.
  proof_irrelevance.
  left.
  reflexivity.
Defined.

Instance eqDecEmptySet : eqDec Empty_set.
  constructor.
  intros [].
Defined.

Definition routers (setup:Setup) : list (ASN * IP) := 
  bindList (ases setup) (fun asips => map (fun ip => (fst asips, ip)) (snd asips)).

Definition linkWithoutRules (l : ((ASN * IP * list Rule * list Rule) * (ASN * IP * list Rule * list Rule))) : ((ASN * IP) * (ASN * IP)) :=
  ((fst (fst (fst (fst l)))), (snd (fst (fst (fst l)))), (fst (fst (snd l)))).

Definition linksWithoutRules (s : Setup) : list ((ASN * IP) * (ASN * IP)).
  destruct s.
  exact (map linkWithoutRules links0).
Defined.

Variable setup:Setup.

Definition inDec {A} `{eqDec A} (a:A) l : decide (In a l).
  refine (in_dec _ a l).
Proof.
  intros a' a''.
  destruct (a' =? a'').
  - left. trivial.
  - right. trivial.
Defined.


Definition hasConnection (r r':ASN*IP) : bool :=
  (((fst r) =? (fst r')) && negb ((snd r) =? (snd r'))) || 
  inDec (r , r') (linksWithoutRules setup) || 
  inDec (r', r ) (linksWithoutRules setup).

Instance bgpTopology : TopologyClass. refine {|
  Router := {r:ASN * IP | In r (routers setup)};
  connections := fun r r' => if hasConnection (proj1_sig r) (proj1_sig r') then unit else Empty_set;
  mode := fun r r' _ => if (fst (proj1_sig r)) =? (fst (proj1_sig r'))
                        then ibgp else ebgp
|}.
Proof.
  - intros.
    unfold edge.
    break_match. 
    + exact eqDecUnit.
    + exact eqDecEmptySet.
  - intros.
    unfold edge.
    break_match.
    + exact enumerableUnit.
    + exact enumerableEmptySet.
Defined.

Definition extendPath (asn:ASN) (a:PathAttributes) : PathAttributes :=
  {| LOCAL_PREF := LOCAL_PREF a; COMMUNITIES := COMMUNITIES a; AS_PATH := asn :: AS_PATH a |}.

Definition setPref (pref : nat) (a : PathAttributes) : PathAttributes :=
  {| LOCAL_PREF := pref; COMMUNITIES := COMMUNITIES a; AS_PATH := AS_PATH a |}.

Fixpoint indexOf' {A} `{eqDec A} (l : list A) a (n : nat) : option nat :=
  match l with
    | a' :: l' =>
      if eqDecide a a' then
        Some n
      else
        indexOf' l' a (S n)
    | [] => None
  end.

Definition indexOf {A} `{eqDec A} (l : list A) a := indexOf' l a 0.

Definition pref {r} (i : incoming r) : option nat.
refine (match i with
          | injected => None
          | received r' => _
       end).
destruct r'. destruct x. destruct r.
destruct (indexOf (linksWithoutRules setup) ( x0, x )).
- exact (Some (100 + (2 * n))).
- destruct (indexOf (linksWithoutRules setup) ( x, x0 )).
  + exact (Some (S (100 + (2 * n)))).
  + exact None.
Defined.

Definition adjustPref {r}  (i : incoming r) a :=
  match pref i with
    | Some n => setPref n a
    | _ => a
  end.

Definition sameRouter {r} (i : incoming r) (o : outgoing r) : bool.
  destruct i.
  - exact false.
  - destruct s, o.
    destruct (eqDecide x x0).
    + exact true.
    + exact false.
Defined.

Definition inASPath {r} (o : outgoing r) (a : PathAttributes) : bool.
  destruct a. destruct o. destruct x.
  destruct (inDec (fst x) AS_PATH0).
  - exact true.
  - exact false.
Defined.

Fixpoint lookupRules (r r' : (ASN * IP)) (l : list ((ASN * IP * list Rule * list Rule) *
                                                   (ASN * IP * list Rule * list Rule))) :
  option ( list Rule * list Rule ).
refine (match l with
          | [] => None
          | c :: l' => _
        end).
destruct (eqDecide (r, r') (linkWithoutRules c)).
  - exact (Some (snd (fst (fst c)), (snd (fst c)))).
  - destruct (eqDecide (r', r) (linkWithoutRules c)).
    + exact (Some (snd (fst (snd c)), (snd (snd c)))).
    + exact (lookupRules r r' l').
Defined.

Definition importRules {r} (i : incoming r) : list Rule.
  destruct r. destruct i.
  - exact [].
  - destruct s. destruct x0.
    exact (match (lookupRules x x0 (links setup)) with
             | None => []
             | Some (i, e) => i
           end).
Defined.

Definition exportRules {r} (o : outgoing r) : list Rule.
  destruct r. destruct o. destruct x0.
  exact (match (lookupRules x x0 (links setup)) with
           | None => []
           | Some (i, e) => e
         end).
Defined.

Fixpoint matches (m : Match) (a : PathAttributes) :=
  match m with
    | RAny => true
    | RCommunityIs c => if inDec c (COMMUNITIES a) then true else false
    | RNot m' => negb (matches m' a)
    | RAnd m1 m2 => andb (matches m1 a) (matches m2 a)
    | ROr m1 m2 => orb (matches m1 a) (matches m2 a)
  end.

Definition modify (m : Modify) (a : PathAttributes) :=
  match m with
    | MAddCommunity c =>
      {| LOCAL_PREF := LOCAL_PREF a; COMMUNITIES := c :: COMMUNITIES a; AS_PATH := AS_PATH a |}
    | MStripCommunities =>
      {| LOCAL_PREF := LOCAL_PREF a; COMMUNITIES := []; AS_PATH := AS_PATH a |}
  end.

Fixpoint executeRules (rules : list Rule) (a : PathAttributes) : RoutingInformation :=
  match rules with
    | [] => available a
    | (m, ac) :: rules' =>
      if (matches m a) then
        match ac with
          | AAccept => available a
          | AReject => notAvailable
          | AModify mo => executeRules rules' (modify mo a)
        end
      else
        executeRules rules' a
  end.

Instance cbgpConfiguration r : ConfigurationClass r.
  refine {|
    import i p a := executeRules (importRules i) (adjustPref i a);
    export i o p a := if ((sameRouter i o) : bool) then notAvailable else
                        if (inASPath o a) then notAvailable else _;
    originate p a := true
    |}.
- destruct (executeRules (exportRules o) a) as [a'|].
  + destruct o as [d c]. 
    exact (available (if mode c =? ebgp then extendPath (fst (proj1_sig r)) a' else a')).
  + exact notAvailable.
Defined.

Definition TraceExists := NetworkState.

Definition BGPRouter : Type := ASN * IP.
Definition BGPAttributes : Type := option BGPPathAttributes.
Definition BGPMessage : Type := CIDR * BGPAttributes.

Typeclasses Transparent BGPRouter.
Typeclasses Transparent BGPAttributes.
Typeclasses Transparent BGPMessage.

Definition bgpAttributes (a:RoutingInformation) : BGPAttributes :=
  match a with available a => Some a | notAvailable => None end.

Definition bgpMessage (m:UpdateMessage) : BGPMessage := 
  (nlri m, bgpAttributes (attributes m)).

Record Event := {
  number : nat;
  srcRouter : BGPRouter;
  handlingRouter : BGPRouter;
  incomingNlri : option CIDR;
  incomingAnnouncement : BGPAttributes
                           (*
  eligibleAnnouncements : list BGPAttributes;
  oldBestAnnouncement : BGPAttributes;
  newBestAnnouncement : BGPAttributes;
  disseminates : list (BGPRouter * PolicyResult) *)
}.

Inductive TraceError :=
  handlerNotARouter (r:BGPRouter)
| sourceNotARouter (r:BGPRouter)
| sourceAndHandlerNotConnected (s d:BGPRouter)
| originationNotAllowed (a:BGPMessage)
| messageNotOnLink (sender : IP) (receiver : IP)  (e_num : nat) (m m':BGPMessage) (ms:list BGPMessage)
| linkEmpty (m : option BGPMessage) (e_num : nat)
| incorrectWithdraw
.
 
Fixpoint applyInjection (i : BGPRouter * CIDR) (ns:TraceExists) : TraceError + TraceExists.
  destruct i as [r p].
  refine (if inDec r (routers setup) then _ else inl (handlerNotARouter r)).
  refine (let a := available {| LOCAL_PREF := 0; COMMUNITIES := []; AS_PATH := [] |} in _).
  refine (let m := {| nlri := p; attributes := a |} in _).
  refine (if originate' (exist _ r _) p a then _ else inl (originationNotAllowed (bgpMessage m))); [trivial|].
  refine (let ls := linkState ns in _).
  refine (let rs := routerState ns in _).
  refine (let Ers' := generateHandler (exist _ r _) m rs in _); [trivial|].
  refine (let E := fst Ers' in _).
  refine (let rs' := snd Ers' in _).
  refine (inr {| routerState := rs'; linkState := build (fun c => lookup ls c ++ lookup E c) |}).
Defined. 

Instance eqDecOption {A} `{eqDec A} : eqDec (option A).
  constructor.
  decide equality.
  apply eqDecide.
Defined.

Definition messageWithoutCommunities (m : UpdateMessage) : UpdateMessage.
  destruct m. destruct attributes.
  - exact (updateMessage nlri (available (modify MStripCommunities p))).
  - exact (updateMessage nlri notAvailable).
Defined.

Definition applyEvent (e:Event) (ns:TraceExists) : TraceError + TraceExists.
  refine (let s := srcRouter e in _).
  refine (let r := handlingRouter e in _).
  refine (if inDec s (routers setup) then _ else inl (sourceNotARouter s)).
  refine (if inDec r (routers setup) then _ else inl (handlerNotARouter r)).
  destruct (hasConnection s r) eqn:?; [|exact (inl (sourceAndHandlerNotConnected s r))].
  refine (let ls0 := linkState ns in _).
  refine (let rs := routerState ns in _).
  refine (let ai := match incomingAnnouncement e with None => notAvailable | Some a => available a end in _).
  refine (let c : Connection := _ in _). {
    refine [ (exist _ s _, exist _ r _) & _].
    - trivial.
    - trivial.
    - cbn. 
      break_match; [|congruence].
      exact tt.
  }
  destruct (incomingNlri e).
  - refine (let m := {| nlri := c0; attributes := ai |} in _).
    refine (match ls0 c with 
              | [] => inl (linkEmpty (Some (bgpMessage m)) (number e))
              | m'::ms => if m =? (messageWithoutCommunities m') then _
                         else inl (messageNotOnLink (snd s) (snd r) (number e) (bgpMessage m) (bgpMessage m') (bgpMessage <$> ms))
            end).
    refine (let ls := overwrite ls0 c ms in _).
    refine (let Ers' := forwardHandler c m' rs in _).
    refine (let E := fst Ers' in _).
    refine (let rs' := snd Ers' in _).
    refine (inr {| routerState := rs'; linkState := build (fun c => lookup ls c ++ lookup E c) |}).
  - refine (match ls0 c with
              | [] => inl (linkEmpty None (number e))
              | m' :: ms => _
            end).
    destruct m'. destruct attributes.
    + exact (inl incorrectWithdraw).
    + remember ({| nlri := nlri; attributes := notAvailable |}) as m'.
      refine (let ls := overwrite ls0 c ms in _).
      refine (let Ers' := forwardHandler c m' rs in _).
      refine (let E := fst Ers' in _).
      refine (let rs' := snd Ers' in _).
      refine (inr {| routerState := rs'; linkState := build (fun c => lookup ls c ++ lookup E c) |}).
Defined.

(*
TODO: Check that the following matc
Record Event := {
  eligibleAnnouncements : list (option BGPPathAttributes);
  oldBestAnnouncement : option BGPPathAttributes;
  newBestAnnouncement : option BGPPathAttributes;
  disseminates : list ((ASN * IP) * PolicyResult)
}.
*)

Definition emptyNetwork : TraceExists := emptyNetworkState.

Definition debugTraceExists (ns:TraceExists) : 
    list (BGPRouter * BGPRouter * list (BGPMessage)).
  refine (bindList (routers setup) (fun s  => _)).
  refine (bindList (routers setup) (fun r => _)).
  refine (if inDec s (routers setup) then _ else []).
  refine (if inDec r (routers setup) then _ else []).
  destruct (hasConnection s r) eqn:?; [|exact []].
  refine (let c : Connection := _ in _). {
    refine [ (exist _ s _, exist _ r _) & _].
    - trivial.
    - trivial.
    - cbn. 
      break_match; [|congruence].
      exact tt.
  }
  refine (let ms := bgpMessage <$> linkState ns c in _).
  refine [(s, r, ms)].
Defined.

End Simulation.

(* TODO move connection into Prop *)
 
Require Import ExtractPrelude.

Extract Inlined Constant map => "Prelude.map".
Extract Inlined Constant concat => "List.concat".
Extract Inlined Constant bindList => "(Prelude.>>=)".

Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ]
                                    "(\fO fS n -> if n==0 then fO () else fS (n-1))".

Extract Inlined Constant plus => "(Prelude.+)".
Extract Inlined Constant mult => "(Prelude.*)".

Extract Inlined Constant Nat.leb => "(Prelude.<=)".

Extract Inlined Constant False_rect => "Prelude.undefined".

Extract Inlined Constant sumBoolAnd => "(Prelude.&&)".

Extract Inductive sigT => "(,)" [ "(,)" ].
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".

Extraction Inline sumbool_rec.
Extraction Inline sumbool_rect.

Extraction Inline eq_rect.
Extraction Inline eq_rect_r.
Extraction Inline eq_rec_r.
Extraction Inline eq_rec.

Extraction Inline unit_rec.
Extraction Inline unit_rect.

Extraction Inline nat_rec.
Extraction Inline nat_rect.

Extraction Inline list_rec.
Extraction Inline list_rect.

Extract Inlined Constant eqDecNat => "(Prelude.==)".

Extraction Inline Mode_rect.
Extraction Inline Mode_rec.
Extraction Inline incoming_rect.
Extraction Inline incoming_rec.
Extraction Inline RoutingInformation_rect.
Extraction Inline RoutingInformation_rec.
Extraction Inline BGPPathAttributes_rect.
Extraction Inline BGPPathAttributes_rec.

Extract Inlined Constant CIDR => "Prelude.String".
Extract Inlined Constant eqDecideCIDR => "(Prelude.==)".
Extract Inlined Constant IP => "Prelude.String".
Extract Inlined Constant eqDecideIP => "(Prelude.==)".
Extract Inlined Constant ASN => "Prelude.Int".
Extract Inlined Constant eqDecideASN => "(Prelude.==)".

Extraction "MessageHandling.hs" emptyNetwork applyEvent applyInjection injections emptyNetwork debugTraceExists PolicyResult.
