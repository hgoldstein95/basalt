/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
module

public meta import Lean.Elab.ElabRules

/-!
# Harvesting a fuzz target's literals

`harvested_literals% A B …` elaborates to the `Array Nat` of the natural-number literals in the
declarations in namespaces `A`, `B`, …: constants `--cmp` may *plant*, writing one into the bytes of
a draw (one `choose`) of an input before libFuzzer runs it, where no comparison at run time supplied
them. A definition contributes its body where it is visible here (`@[expose]`, or the current
module); a theorem its statement, which may name a value worth testing, and not its proof, which
never runs.
-/

public section

open Lean Elab Term

namespace Basalt.Fuzz

/-- The `Nat` literals below `2^64` in `e`, added to `acc`. -/
meta partial def natLits (e : Expr) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
  match e with
  | .lit (.natVal n) => if n < 2 ^ 64 then acc.insert n else acc
  | .app f a => natLits a (natLits f acc)
  | .lam _ t b _ | .forallE _ t b _ => natLits b (natLits t acc)
  | .letE _ t v b _ => natLits b (natLits v (natLits t acc))
  | .mdata _ b | .proj _ _ b => natLits b acc
  | _ => acc

/-- Elaborates to the distinct `Nat` literals, below `2^64`, in the declarations under the given
namespaces. -/
elab "harvested_literals% " nss:ident* : term => do
  let prefixes := nss.map (·.getId)
  let seen := (← getEnv).constants.fold (init := ({} : Std.HashSet Nat)) fun acc name info =>
    if !prefixes.any (·.isPrefixOf name) then acc
    else match info with
      | .thmInfo t => natLits t.type acc
      | _ => match info.value? with | some v => natLits v acc | none => acc
  let sorted := seen.toArray.qsort (· < ·)
  return mkApp2 (mkConst ``List.toArray [Level.zero]) (mkConst ``Nat)
    (sorted.foldr (fun n acc => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat)
      (mkRawNatLit n) acc) (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat)))

end Basalt.Fuzz
