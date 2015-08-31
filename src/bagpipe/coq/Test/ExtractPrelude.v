Require Import Coq.Program.Basics.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Prelude.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].

Extract Inductive unit => "()" [ "()" ].
Extract Inlined Constant id => "(Prelude.id)".

Extract Inductive list => "([])" [ "([])" "(:)" ].
Extract Inlined Constant app => "(Prelude.++)".
Extract Inlined Constant length => "((\l -> Prelude.toInteger (Prelude.length l)))".

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".

Extract Inlined Constant compose => "(Prelude..)".
Extract Inlined Constant const => "(Prelude.const)".

Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sum => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].

Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant orb => "(Prelude.||)".
Extract Inlined Constant negb => "Prelude.not".

Extract Inductive positive => "Prelude.Integer" [
  "((\x -> 2 Prelude.* x Prelude.+ 1))"
  "((\x -> 2 Prelude.* x))"
  "1"
].

Extract Inductive Z => "Prelude.Integer" ["0" "" "Prelude.negate"].
Extract Constant Z.succ => "Prelude.succ".
Extract Constant Z.pred => "Prelude.pred".
Extract Inlined Constant Z.eq_dec => "(Prelude.==)".
Extract Inlined Constant Z.eqb => "(Prelude.==)".
Extract Inlined Constant Z.add => "(Prelude.+)".
Extract Inlined Constant Z.sub => "(Prelude.-)".
Extract Inlined Constant Z.mul => "(Prelude.*)".
Extract Inlined Constant Z.opp => "Prelude.negate".
Extract Inlined Constant Z.abs => "Prelude.abs".
Extract Inlined Constant Z.ltb => "(Prelude.<)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.gtb => "(Prelude.>)".
Extract Inlined Constant Z.geb => "(Prelude.>=)".
Extract Inlined Constant Z.min => "Prelude.min".
Extract Inlined Constant Z.max => "Prelude.max".
Extract Inlined Constant Z.div => "((\x y -> if y Prelude.== 0 then 0 else Prelude.div x y))".
Extract Inlined Constant Z.modulo => "((\x y -> if y Prelude.== 0 then 0 else Prelude.mod x y))".

Extract Inlined Constant Z.land => "(Data.Bits..&.)".
Extract Inlined Constant Z.lor => "(Data.Bits..|.)".

(* Just keep x for {x | P x }. *)
Extraction Inline Specif.proj1_sig.
