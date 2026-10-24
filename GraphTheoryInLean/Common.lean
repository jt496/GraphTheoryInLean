import GraphTheoryInLean.Tactic.Source
import GraphTheoryInLean.Tactic.DocHover
import GraphTheoryInLean.Tactic.PropExample
import Mathlib.Data.Fintype.Basic
/-
Shared helpers for the chapters: `Repr` instances for finite functions and
function-like maps, so that `#eval` can print them, the `#source` command, and
hovers for the names in doc comments (see `Tactic/DocHover.lean`).
-/
-- 1. Format a finite function as `{v ↦ f v, ...}`
unsafe def formatFiniteFun {V W : Type*} [Fintype V] [Repr V] [Repr W] (f : V → W) :
    Std.Format :=
  let entries := (Finset.univ : Finset V).val.unquot.map fun v =>
    f!"{repr v} ↦ {repr (f v)}"
  Std.Format.bracket "{" (Std.Format.joinSep entries ", ") "}"

-- 2. Attach it to plain functions
unsafe instance {V W : Type*} [Fintype V] [Repr V] [Repr W] : Repr (V → W) where
  reprPrec f _ := formatFiniteFun f

-- 3. Attach it to bundled maps (using coercion to cast them to V → W)
unsafe instance {F V W : Type*} [Fintype V] [Repr V] [Repr W]
    [FunLike F V W] : Repr F where
  reprPrec f _ := formatFiniteFun (f : V → W)
