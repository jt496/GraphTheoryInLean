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

The elaborator also removes the hover over the keyword `example`. The built-in
elaborator names every example `_example`, and the name takes the source info of the
keyword. So hovering over `example` shows something like
`SimpleGraph._example {p : Prop} (h : p) : Decidable p`, an internal name that nobody
wrote. An info node has a hover only if its syntax has canonical source info, so the
elaborator gives the built-in a copy of the command in which the keyword has synthetic,
non-canonical source info at the same position. Messages about the example are still
reported on the keyword. The theorem of a propositional example gets a name with the
same source info. This part is always on.
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

/-- `stx` with its source info replaced by synthetic, non-canonical source info at the
same position. An info node for syntax made from it has no hover. -/
def nonCanonical (stx : Syntax) : Syntax :=
  stx.setInfo (SourceInfo.fromRef stx)

/- Elaborate an `example`: as a theorem if its type is a proposition, and otherwise
with the built-in elaborator, in both cases with no hover over the keyword (see the
module docstring). Throw `unsupportedSyntax` for any other declaration.

This is deliberately not a docstring. Hovering over a part of a command that nothing
more specific covers (a space, a comment, the `:=`) shows the docstring of the
command's elaborator, so a docstring here would show on every gap of every example.
The built-in `elabDeclaration` has none, so a gap of a declaration shows nothing. -/
@[command_elab Lean.Parser.Command.declaration]
def elabExample : CommandElab := fun stx => do
  unless stx[1].isOfKind ``Parser.Command.example do throwUnsupportedSyntax
  let keyword := nonCanonical stx[1][0]
  if stil.propExampleAsTheorem.get (← getOptions) then
    if let `($mods:declModifiers example $bs:bracketedBinder* : $type:term $val:declVal) :=
        stx then
      let m ← elabModifiers mods
      unless m.isNoncomputable || m.isUnsafe || m.isPartial || m.isMeta do
        if ← isPropType bs type then
          -- As for the built-in, the name takes the position of the keyword, so that
          -- messages about the declaration (such as `declaration uses sorry`) are
          -- reported there rather than on the whole command.
          let id := mkIdentFrom keyword (← liftCoreM <| mkFreshUserName `_example)
          elabCommand
            (← `($mods:declModifiers theorem $id:ident $bs* : $type:term $val:declVal))
          return
  -- Called directly, as `elabCommand` would come back here.
  elabDeclaration (stx.setArg 1 (stx[1].setArg 0 keyword))

end STIL.PropExample
