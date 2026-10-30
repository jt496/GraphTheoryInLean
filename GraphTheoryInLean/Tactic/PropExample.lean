/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Lean

/-!
# Propositional examples elaborated as theorems

Lean elaborates an `example` like a `def`: every section variable is in its local
context, whether its statement mentions it or not. A binder with the same name as a
section variable then shadows it, and the variable shows up as `x✝` in every goal
state (and so in the goal states of the guide's HTML). A `theorem` only has the
section variables that its statement mentions.

This command elaborator takes over an `example` whose type is a proposition and
elaborates it as a theorem with an inaccessible name. Any other example (one with no
type, or a type that is not a proposition, or a `noncomputable`, `unsafe`, `partial`
or `meta` one) is left to the built-in elaborator. As in a theorem, a section
variable that only the proof uses must then be brought in with `include … in`.

Turn it off with `set_option stil.propExampleAsTheorem false`.
-/

open Lean Elab Command

namespace STIL.PropExample

register_option stil.propExampleAsTheorem : Bool := {
  defValue := true
  descr := "elaborate an `example` whose type is a proposition as a theorem, so that \
    it only has the section variables its statement mentions"
}

/-- Whether `type`, after the binders `bs`, elaborates to a proposition. The check
leaves no trace: its messages, info trees and other effects are discarded. -/
def isPropType (bs : Array (TSyntax ``Parser.Term.bracketedBinder)) (type : Term) :
    CommandElabM Bool := do
  let saved ← get
  try
    withEnableInfoTree false <| runTermElabM fun _ =>
      Term.elabBinders bs fun _ => do Meta.isProp (← Term.elabType type)
  catch _ =>
    pure false
  finally
    set saved

/-- Elaborate an `example` whose type is a proposition as a theorem (see the module
docstring); throw `unsupportedSyntax` for any other declaration. -/
@[command_elab Lean.Parser.Command.declaration]
def elabPropExample : CommandElab := fun stx => do
  unless stil.propExampleAsTheorem.get (← getOptions) do throwUnsupportedSyntax
  let `($mods:declModifiers example $bs:bracketedBinder* : $type:term $val:declVal) := stx
    | throwUnsupportedSyntax
  let m ← elabModifiers mods
  if m.isNoncomputable || m.isUnsafe || m.isPartial || m.isMeta then throwUnsupportedSyntax
  unless ← isPropType bs type do throwUnsupportedSyntax
  -- As for the built-in, the name takes the position of the `example` keyword, so that
  -- messages about the declaration (such as `declaration uses sorry`) are reported
  -- there rather than on the whole command.
  let id := mkIdentFrom stx[1][0] (← liftCoreM <| mkFreshUserName `example)
    (canonical := true)
  elabCommand (← `($mods:declModifiers theorem $id:ident $bs* : $type:term $val:declVal))

end STIL.PropExample
