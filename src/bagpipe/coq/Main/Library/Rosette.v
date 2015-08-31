Require Import SpaceSearch.

Parameter Symbolic : Type -> Type.
Parameter symbolicFail : forall {A}, Symbolic A.
Parameter symbolicReturn : forall {A}, A -> Symbolic A.
Parameter symbolicUnion : forall {A}, Symbolic A -> Symbolic A -> Symbolic A. 
Parameter symbolicBind : forall {A B},  Symbolic A -> (A -> Symbolic B) -> Symbolic B.
Parameter symbolicRun : forall {A}, Symbolic A -> option A.

Axiom  symbolicContains : forall {A}, A -> Symbolic A -> Prop.
Axiom  symbolicFailOk : forall {A} {a:A}, ~symbolicContains a symbolicFail.
Axiom  symbolicReturnOk : forall {A} {a a':A}, a = a' <-> symbolicContains a' (symbolicReturn a).
Axiom  symbolicUnionOk : forall {A S T} {a:A}, (symbolicContains a S \/ symbolicContains a T) <-> symbolicContains a (symbolicUnion S T).
Axiom  symbolicBindOk : forall {A B S f} {b:B}, (exists a:A, symbolicContains a S /\ symbolicContains b (f a)) <-> symbolicContains b (symbolicBind S f).
Axiom  symbolicRunOk : forall {A S} {a:A}, symbolicRun S = Some a -> symbolicContains a S.
Axiom  symbolicRunOk' : forall {A S} {a:A}, symbolicRun S = None -> ~symbolicContains a S.

Extract Constant Symbolic "a"   => "__".
Extract Constant symbolicFail   => "(lambda  (_) (assert false))".
Extract Constant symbolicReturn => "(lambdas (a _) a)".
Extract Constant symbolicUnion  => "(lambdas (s t v) (define-symbolic* b boolean?) (if b (s v) (t v)))".
Extract Constant symbolicBind   => "(lambdas (s f v) (@ f (s v) v))".
Extract Constant symbolicRun    => "(lambda  (e) (solve/evaluate/concretize e))".

Instance rosette : SpaceSearch := {|
  Space := Symbolic;
  empty := @symbolicFail;
  single := @symbolicReturn;
  union := @symbolicUnion;
  bind := @symbolicBind;
  search := @symbolicRun;

  contains := @symbolicContains;
  emptyOk := @symbolicFailOk;
  singleOk := @symbolicReturnOk;
  unionOk := @symbolicUnionOk;
  bindOk := @symbolicBindOk;
  searchOk := @symbolicRunOk;
  searchOk' := @symbolicRunOk'
|}.
