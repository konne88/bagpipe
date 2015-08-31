Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Bag.
Require Import Graph.
Require Import Dict.
Require Import Misc.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import Coq.Program.Basics.
Require Import EqDec.
Require Import Enumerable.
Import ListNotations.

Section BGP.
  (* the bgp spec: https://tools.ietf.org/html/rfc4271

     We don't care about error-handling, session management,
     low level bit representation, etc. This means we can
     ignore sections:
     - 4.1 Message Header Format
     - 4.2 OPEN Message Format
     - 4.4 KEEPALIVE Message Format
     - 4.5 NOTIFICATION Message Format
     - 6.  BGP Error Handling.
     - 7.  BGP Version Negotiation.
     - 8.  BGP Finite State machine.
     - 9.1.2.1.  Route Resolvability Condition

     We also don't support
     - Route aggregation and information reduction techniques 
     - Route reflectors
  *)

  Class PrefixClass := {
    Prefix : Type;
    eqDecPrefix :> eqDec Prefix
  }.
  Context `{PrefixClass}.

  (* 5.  Path Attributes *)
  Class PathAttributesClass := {
    PathAttributes : Type;
    eqDecPathAttributes :> eqDec PathAttributes;
    localPref : PathAttributes -> nat
  }.
  Context `{PathAttributesClass}.
  Arguments localPref {_} _.

  Inductive RoutingInformation :=
  | available (_:PathAttributes)
  | notAvailable.

  Instance eqDecRoutingInformation : eqDec RoutingInformation.
    constructor. decide equality. apply eqDecide. 
  Defined.

  Instance enumerableRoutingInformation `{enumerable PathAttributes} : enumerable RoutingInformation.
    refine {|enumerate := notAvailable :: map available enumerate |}.
  Proof.
    intro a.
    cbn.
    destruct a.
    - right.
      apply in_map.
      apply enumerateContainsEverything.
    - left.
      reflexivity.
  Qed.    

  Definition bindRoutingInformation (a:RoutingInformation) (f:PathAttributes -> RoutingInformation) : RoutingInformation :=
    match a with
    | notAvailable => notAvailable
    | available a => f a
    end.

  Inductive Mode := ibgp | ebgp.
  Instance eqDecMode : eqDec Mode. 
    constructor. decide equality.
  Defined.

  Class TopologyClass := {
    Router : Type;
    eqDecRouter :> eqDec Router;
    enumerableRouter :> enumerable Router;
    connections : graph Router;
    eqDecConnection s d :> eqDec (edge connections s d);
    enumerableConnection s d :> enumerable (edge connections s d);
    mode {s d} : edge connections s d -> Mode
  }.
  Context `{TopologyClass}.

  Definition connection s d := edge connections s d.
  Typeclasses Transparent connection.
  Definition Connection :=  {c : Router * Router & connection (fst c) (snd c)}.
  Typeclasses Transparent Connection.

  (* 4.3 UPDATE Message Format 

     The BGP Spec is very confusing regarding the meaning of multiple
     prefixes in the NLRI field of an Update Message. But the following
     sentence (added to RFC 4271) explains it:

     > Routes are advertised between BGP speakers in UPDATE messages.
     > Multiple routes that have the same path attributes can be advertised
     > in a single UPDATE message by including multiple prefixes in the NLRI
     > field of the UPDATE message.

     Update messages support the withdrawl and announcement of multiple routes
     at the same time. We limit it to one route withdrawl xor announcement.
  *)
  Record UpdateMessage : Type := updateMessage {
    (* the routes's prefix *)
    nlri : Prefix;
    attributes : RoutingInformation
  }.
  Instance eqDecUpdateMessage : eqDec UpdateMessage.
    idtac.
    constructor. 
    repeat decide equality; apply eqDecide.
  Defined.

  Section RouterInternal.
    Variable r:Router.

    Inductive incoming := 
    | injected : incoming
    | received : {s : Router & connection s r} -> incoming.

    Instance eqDecIncoming : eqDec incoming.
      constructor. 
      intros i i'.
      destruct i, i'.
      - left. reflexivity. 
      - decide equality. apply eqDecide.
      - decide equality. apply eqDecide.
      - decide equality. apply eqDecide.
    Defined.
    Instance enumerableIncoming : enumerable incoming.
      refine {|
        enumerate := injected :: (received <$> enumerate)
      |}.
      intro i; destruct i.
      + crush.
      + apply in_cons.
        apply in_map.
        apply enumerateContainsEverything.
    Defined.            
    Definition outgoing := {d : Router & connection r d}.
    Typeclasses Transparent outgoing.

    Class ConfigurationClass := {
      import : incoming -> Prefix -> PathAttributes -> RoutingInformation;
      export : incoming -> outgoing -> Prefix -> PathAttributes -> RoutingInformation;

      (* 9.4.  Originating BGP routes

         > A BGP speaker may originate BGP routes by injecting routing
         > information acquired by some other means (e.g., via an IGP) into BGP.
         > A BGP speaker that originates BGP routes assigns the degree of
         > preference (e.g., according to local configuration) to these routes
         > by passing them through the Decision Process (see Section 9.1).
         > These routes MAY also be distributed to other BGP speakers within the
         > local AS as part of the update process (see Section 9.2). 

         It's unclear which import filter is run, since import filters are
         defined per neighbor, and routes that I originate don't have a neighbor.

         Looking at real configs, it appears that there simply is no import filter 
         for internal routes, the routes are just injected directly into the locRIB,
         and then exported.

         A description of how to originate networks for Cisoc is here:
         http://www.cisco.com/c/en/us/support/docs/ip/border-gateway-protocol-bgp/26634-bgp-toc.html#networkcommand

         What we are doing now, is that we have a special adjRIBIn just for injected routes,
         which are then passed through the decision process as usual. The following
         function encodes the user's policy about installed static routes.
      *)
      originate : Prefix -> PathAttributes -> bool
    }.
    Context `{ConfigurationClass}.

    (* 3.2 Routing Information Bases *)

    (* The Routing Table (used for packet forwarding) is different from the RIB *)

    Record RIBs := {
      adjRIBsIn: dict (incoming * Prefix) RoutingInformation;
      locRIB: dict Prefix RoutingInformation;
      adjRIBsOut: dict (outgoing * Prefix) RoutingInformation
    }.

    Definition originate' p a := 
      match a with 
      | notAvailable => true 
      | available a => originate p a 
      end.

    Definition localPref' (a:RoutingInformation) : nat :=
      match a with
      | notAvailable => 0
      | available a => S (localPref a)
      end.

    Definition import' s p a := bindRoutingInformation a (import s p).

    Definition export' (i:incoming) (o:outgoing) (p:Prefix) (a:RoutingInformation) : RoutingInformation :=
      match i with
      | injected => bindRoutingInformation a (export i o p)
      | received (existT _ _ ci) => let ' existT _ _ co := o in 
                                    if (mode ci =? ibgp) && (mode co =? ibgp) 
                                    then notAvailable 
                                    else bindRoutingInformation a (export i o p)
      end.
      
    Definition decisionProcess (p:Prefix) (ribs:RIBs) : RIBs.
      refine(
      let in_ := adjRIBsIn ribs in
      let loc := locRIB ribs in
      let out := adjRIBsOut ribs in
      let in' := in_ in
      (* 9.1.  Decision Process 

         > Once the BGP speaker updates the Adj-RIB-In, the speaker SHALL run
         > its Decision Process.

         Since adjsRIBin only changed for the prefix p, it is sufficient to run 
         the decision process only the part of RIBs for prefix p.

         > The Decision Process takes place in three distinct phases, 
      *)

      (* 9.1.1.  Phase 1: Calculation of Degree of Preference

         > a) Phase 1 is responsible for calculating the degree of preference
         >   for each route received from a peer. 

         > The exact nature of this policy information, and the computation
         > involved, is a local matter.

         > The selection process is formalized by defining a function that takes
         > the attribute of a given route as an argument and returns either (a)
         > a non-negative integer denoting the degree of preference for the
         > route, or (b) a value denoting that this route is ineligible to be
         > installed in Loc-RIB and will be excluded from the next phase of
         > route selection.

         > If the AS_PATH attribute of a BGP route contains an AS loop, the BGP
         > route should be excluded from the Phase 2 decision function.

         We will implement that in the import function

         > The function that calculates the degree of preference for a given
         > route SHALL NOT use any of the following as its inputs: the existence
         > of other routes, the non-existence of other routes, or the path
         > attributes of other routes.  Route selection then consists of the
         > individual application of the degree of preference function to each
         > feasible route, followed by the choice of the one with the highest
         > degree of preference.
      *)
      
      (* 9.1.2.  Phase 2: Route Selection

         > The Phase 2 decision function is invoked on completion of Phase 1.

         > For each set of destinations for which a feasible route exists in the
         > Adj-RIBs-In, the local BGP speaker identifies the route that has:

         > a) the highest degree of preference of any route to the same set
         >    of destinations, or

         > c) is selected as a result of the Phase 2 tie breaking rules
         >    specified in Section 9.1.2.2.

         > The local speaker SHALL then install that route in the Loc-RIB,
         > replacing any route to the same destination that is currently being
         > held in the Loc-RIB.
      *)
      let n' := argMax' (fun s => localPref' (import' s p (lookup (adjRIBsIn ribs) (s,p)))) _ in
      let a' := import' n' p (lookup (adjRIBsIn ribs) (n',p)) in
      let loc' := overwrite loc p a' in

      (* 9.1.3.  Phase 3: Route Dissemination

         > The Phase 3 decision function is invoked on completion of Phase 2

         > c) Phase 3 is ...
         >    responsible for disseminating routes in the Loc-RIB to each
         >    peer      

         > All routes in the Loc-RIB are processed into Adj-RIBs-Out according
         > to configured policy.  This policy MAY exclude a route in the Loc-RIB
         > from being installed in a particular Adj-RIB-Out. 

         > 9.1.4.  Overlapping Routes

         > A BGP speaker may transmit routes with overlapping Network Layer
         > Reachability Information (NLRI) to another BGP speaker.

         We don't support aggregation

         > When a BGP speaker receives an UPDATE message from an internal peer,
         > the receiving BGP speaker SHALL NOT re-distribute the routing
         > information contained in that UPDATE message to other internal peers

         We implement that in the export' function
      *)
      let out' := build (fun k => let ' (o,p') := k in if p =? p' then export' n' o p a' else lookup out (o,p'))
      in  {| adjRIBsIn  := in'; locRIB := loc'; adjRIBsOut := out' |}
    ).
    Proof.
    - exact injected.
    Defined.
  
    Typeclasses Transparent const.

    Definition updateSendProcess (p:Prefix) (out out':dict (outgoing*Prefix) RoutingInformation) : dict outgoing (list UpdateMessage).
      (* 9.2 Update-Send Process 

         > As part of Phase 3 of the route selection process, the BGP speaker
         > has updated its Adj-RIBs-Out.  All newly installed routes and all
         > newly unfeasible routes for which there is no replacement route SHALL
         > be advertised to its peers by means of an UPDATE message.
      *)
      refine(build (fun o => if lookup out (o,p) =? lookup out' (o,p) 
                             then [] 
                             else [{| nlri:=p; attributes:=lookup out' (o,p) |}])).
    Defined.

    (* 9.  UPDATE Message Handling *)
    Definition messageHandling (s:incoming) (m:UpdateMessage) (ribs:RIBs) :
                               dict outgoing (list UpdateMessage) * RIBs.
      refine (
      let in_ := adjRIBsIn ribs in
      let loc := locRIB ribs in
      let out := adjRIBsOut ribs in
      let p := nlri m in 
      let a := attributes m in

      (* > If the UPDATE message contains a non-empty WITHDRAWN ROUTES field,
         > the previously advertised routes, whose destinations (expressed as IP
         > prefixes) are contained in this field, SHALL be removed from the
         > Adj-RIB-In.

         > If the UPDATE message contains a feasible route, the Adj-RIB-In will
         > be updated with this route as follows: if the NLRI of the new route
         > is identical to the one the route currently has stored in the Adj-
         > RIB-In, then the new route SHALL replace the older route in the Adj-
         > RIB-In, thus implicitly withdrawing the older route from service.
         > Otherwise, if the Adj-RIB-In has no route with NLRI identical to the
         > new route, the new route SHALL be placed in the Adj-RIB-In.
      *)
      let in' := overwrite'' in_ (s,p) a in
      let rib' := decisionProcess p {| adjRIBsIn := in'; locRIB := loc; adjRIBsOut := out |} in
      let out' := adjRIBsOut rib' in
      let E := updateSendProcess p out out'
      in  (E, rib')).
    Defined.
  
  End RouterInternal.

  Context `{forall r, ConfigurationClass r}.

  Record NetworkState : Type := networkState {
    routerState : depDict Router RIBs;
    linkState : dict Connection (list UpdateMessage)
  }.

  Definition routerHandler r (i:incoming r) (m:UpdateMessage) (rs:forall r, RIBs r) : 
                           dict Connection (list UpdateMessage) * (forall r, RIBs r).
    refine (let ' (E, ribs) := messageHandling r i m (lookup rs r) in _).
    refine (let rs' := overwrite' rs r ribs in _).
    refine (let E' := build(fun c' => _) in (E',rs')).
    unfold const.
    destruct c' as [r'd c'].
    destruct r'd as [r' d].
    refine (if r =? r' then _ else []).
    subst.
    unfold outgoing in *.
    refine(lookup E (existT _ d c')).
  Defined.

  Definition forwardHandler (c:Connection) (m:UpdateMessage) (rs:forall r, RIBs r) : 
                           dict Connection (list UpdateMessage) * (forall r, RIBs r).
    destruct c as [sr c].
    destruct sr as [s r].
    exact (routerHandler r (received r [s & c]) m rs).
  Defined.

  Definition generateHandler (r:Router) (m:UpdateMessage) (rs:forall r, RIBs r) : 
                             dict Connection (list UpdateMessage) * (forall r, RIBs r).
    exact (routerHandler r (injected r) m rs).
  Defined.

  (* TODO combine commonalities between the two *)
  Inductive transition : NetworkState -> NetworkState -> Type :=
  | generate m r rs ls : originate' r (nlri m) (attributes m) = true ->
      let Ers' := generateHandler r m rs in   (* Coq is weird and disallows: let ' (E, rs') := ... *)
      let E := fst Ers' in
      let rs' := snd Ers' in
      transition 
        {| routerState := rs;  linkState := ls |}
        {| routerState := rs'; linkState := build (fun c => lookup ls c ++ lookup E c) |}
  | forward m c rs ls :
      let Ers' := forwardHandler c m rs in   (* Coq is weird and disallows: let ' (E, rs') := ... *)
      let E := fst Ers' in
      let rs' := snd Ers' in
      transition
        {| routerState := rs;  linkState := update' ls c (fun ms => m::ms) |}
        {| routerState := rs'; linkState := build (fun c => lookup ls c ++ lookup E c) |}.

  Definition emptyRIB {A} : dict A RoutingInformation := build (const notAvailable). 

  Definition emptyNetworkState := {|
    routerState := build (fun _ => {|
        adjRIBsIn  := emptyRIB;
        locRIB     := emptyRIB;
        adjRIBsOut := emptyRIB
      |});
    linkState := build (fun _ => [])
  |}.

  Inductive star {S} {s0:S} {t:S->S->Type} : S -> Type :=
  | init : star s0
  | step {s s'} : star s -> t s s' -> star s'.

  Definition reachable := star (s0 := emptyNetworkState) (t := @transition).

End BGP.

Arguments adjRIBsIn {_ _ _ _} _ _.
Arguments locRIB {_ _ _ _} _ _.
Arguments adjRIBsOut {_ _ _ _} _ _.
Arguments available {_} _.
Arguments notAvailable {_}.
Arguments received {_ _} _.
Arguments injected {_ _}.
