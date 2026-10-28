/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import GraphTheoryInLean.Common
import GraphTheoryInLean.C02_SimpleGraph.C02_SimpleGraph
namespace SimpleGraph
variable {V : Type*}
/-!
# Exercises

1. Show that the complement of the complete graph is the empty graph.
-/
example : (⊤ : SimpleGraph V)ᶜ = ⊥ := by
  sorry

/-!
2. Show that `G ≤ H` if and only if `Hᶜ ≤ Gᶜ`.
-/
example (G H : SimpleGraph V) : G ≤ H ↔ Hᶜ ≤ Gᶜ := by
  sorry

/-!
3. Show that `pathNat` has support `ℕ`. (Remember `ℕ` is a type not a set so we need
to use `Set.univ` to talk about `ℕ` as a `Set ℕ`.)
-/

example : pathNat.support = Set.univ := by
  sorry

/-!
4. Show that the neighbours of `n + 1` in `pathNat` are exactly `n` and `n + 2`.
-/
example (n : ℕ) : pathNat.neighborSet (n + 1) = {n, n + 2} := by
  sorry

/-!
In the next few exercises we follow a convention that we will use throughout this
guide. We use a prime " ' " to denote a version of a definition or result that
contains a `sorry`. This is so that we can use the same names (without a prime) in
the solutions below, thus ensuring that when we refer to them in later chapters they
resolve to the correct definition.
-/

/-!
5. For `i : ℕ`, define the graph `shiftedPathNat' i` to be a `SimpleGraph ℕ` with
edges from `n` to `n + 1` iff `i ≤ n`. (If `aesop_graph` can prove the `symm` and
`loopless` fields for your definition then you can simply delete those two lines.)
-/
def shiftedPathNat' (i : ℕ) : SimpleGraph ℕ where
  Adj n m := sorry
  symm := sorry
  loopless := sorry

/-!
6. Prove that `shiftedPathNat' 0 = pathNat`.
-/
example : shiftedPathNat' 0 = pathNat := by
  sorry

/-!
7. For `i : ℕ`, define the graph `shortPathNat' i` to be a `SimpleGraph ℕ` with edges
from `n` to `n + 1` iff `n < i`.
-/
def shortPathNat' (i : ℕ) : SimpleGraph ℕ where
  Adj n m := sorry
  symm := sorry
  loopless := sorry

/-!
8. Prove that `shortPathNat' i ⊔ shiftedPathNat' i = pathNat`.
-/
example (i : ℕ) : shortPathNat' i ⊔ shiftedPathNat' i = pathNat := by
  sorry

/-!
9. Show that the graph `shiftedPathNat' j` is a subgraph of `shiftedPathNat' i` if
and only if `i ≤ j`.
-/
example (i j : ℕ) : shiftedPathNat' j ≤ shiftedPathNat' i ↔ i ≤ j := by
  sorry

/-!
10. Prove that `shortPathNat' i ⊓ shiftedPathNat' i` is the empty graph (on `ℕ`).
-/
example (i : ℕ) : shortPathNat' i ⊓ shiftedPathNat' i = ⊥ := by
  sorry

/-!
11. Prove that `shortPathNat' i ⊔ shortPathNat' j = shortPathNat' (max i j)`.
-/
example (i j : ℕ) : shortPathNat' i ⊔ shortPathNat' j = shortPathNat' (max i j) := by
  sorry

/-!
12. Show that `pathNat \ shortPathNat' i` is `shiftedPathNat' i`.
-/
example (i : ℕ) : pathNat \ shortPathNat' i = shiftedPathNat' i := by
  sorry

/-!
13. `SimpleGraph` has an *indexed supremum* operation `⨆ i, G i` which is the graph
with edges between `u` and `v` if and only if there exists an index `i` such that `u`
and `v` are adjacent in `G i`. Prove that `pathNat = ⨆ i : ℕ, shortPathNat' i`.
-/
example : pathNat = ⨆ i : ℕ, shortPathNat' i := by
  sorry

/-!
14. Show that the edge set of `pathNat` is `{e | ∃ n, e = s(n, n + 1)}`. (Hint: use
`induction e using Sym2.ind`.)
-/
example : pathNat.edgeSet = {e | ∃ n, e = s(n, n + 1)} := by
  sorry

/-!
15. The darts whose first vertex is `v` are exactly the darts obtained from the
neighbours of `v` by `dartOfNeighborSet`.
-/
#source dartOfNeighborSet

example {G : SimpleGraph V} {v : V} :
    {d : G.Dart | d.fst = v} = Set.range (G.dartOfNeighborSet v) := by
  sorry

/-! SOLUTIONS -/

/-!
1. Show that the complement of the complete graph is the empty graph.
-/
example : (⊤ : SimpleGraph V)ᶜ = ⊥ := by
  simp

/-!
2. Show that `G ≤ H` if and only if `Hᶜ ≤ Gᶜ`.
-/
example (G H : SimpleGraph V) : G ≤ H ↔ Hᶜ ≤ Gᶜ := by
  simp

/-!
3. Show that `pathNat` has support `ℕ`. (Remember `ℕ` is a type not a set so we need
to use `Set.univ` to talk about `ℕ` as a `Set ℕ`.)
-/
example : pathNat.support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  use n + 1
  simp

/-!
4. Show that the neighbours of `n + 1` in `pathNat` are exactly `n` and `n + 2`.
-/
example (n : ℕ) : pathNat.neighborSet (n + 1) = {n, n + 2} := by
  ext a
  simp [or_comm, Eq.comm]

/-!
5. For `i : ℕ`, define the graph `shiftedPathNat i` to be a `SimpleGraph ℕ` with
edges from `n` to `n + 1` iff `i ≤ n`. (Notice we don't need to give proofs of `symm`
and `loopless`, since `aesop_graph` can prove these.)
-/
@[simps]
def shiftedPathNat (i : ℕ) : SimpleGraph ℕ where
  Adj n m := n + 1 = m ∧ i ≤ n ∨ m + 1 = n ∧ i ≤ m

/-!
6. Prove that `shiftedPathNat 0 = pathNat`.
-/
example : shiftedPathNat 0 = pathNat := by
  ext u v
  simp

/-!
7. For `i : ℕ`, define the graph `shortPathNat i` to be a `SimpleGraph ℕ` with edges
from `n` to `n + 1` iff `n < i`.
-/
@[simps]
def shortPathNat (i : ℕ) : SimpleGraph ℕ where
  Adj n m := n + 1 = m ∧ n < i ∨ m + 1 = n ∧ m < i

/-!
8. Prove that `shortPathNat i ⊔ shiftedPathNat i = pathNat`.
-/
example (i : ℕ) : shortPathNat i ⊔ shiftedPathNat i = pathNat := by
  ext u v
  grind [shortPathNat_adj, shiftedPathNat_adj]

/-!
9. Show that the graph `shiftedPathNat j` is a subgraph of `shiftedPathNat i` if
and only if `i ≤ j`.
-/
example (i j : ℕ) : shiftedPathNat j ≤ shiftedPathNat i ↔ i ≤ j := by
  refine ⟨fun h => ?_, fun h a b => by grind [shiftedPathNat_adj]⟩
  have := h (by simp : (shiftedPathNat j).Adj j (j + 1))
  grind [shiftedPathNat_adj]

/-!
10. Prove that `shortPathNat i ⊓ shiftedPathNat i` is the empty graph (on `ℕ`).
-/
example (i : ℕ) : shortPathNat i ⊓ shiftedPathNat i = ⊥ := by
  ext u v
  grind [inf_adj, shortPathNat_adj, shiftedPathNat_adj]

/-!
11. Prove that `shortPathNat i ⊔ shortPathNat j = shortPathNat (max i j)`.
-/
example (i j : ℕ) : shortPathNat i ⊔ shortPathNat j = shortPathNat (max i j) := by
  ext u v
  grind [shortPathNat_adj]


/-!
12. Show that `pathNat \ shortPathNat i` is `shiftedPathNat i`.
-/
example (i : ℕ) : pathNat \ shortPathNat i = shiftedPathNat i := by
  ext u v
  grind [sdiff_adj, shortPathNat_adj, shiftedPathNat_adj]

/-!
13. `SimpleGraph` has an *indexed supremum* operation `⨆ i, G i` which is the graph
with edges between `u` and `v` if and only if there exists an index `i` such that `u`
and `v` are adjacent in `G i`. Prove that `pathNat = ⨆ i : ℕ, shortPathNat i`.
-/
example : pathNat = ⨆ i : ℕ, shortPathNat i := by
  ext u v
  simp only [iSup_adj, shortPathNat_adj]
  constructor
  · rintro (h | h)
    · exact ⟨u + 1, by grind⟩
    · exact ⟨v + 1, by grind⟩
  · grind

/-!
14. Show that the edge set of `pathNat` is `{e | ∃ n, e = s(n, n + 1)}`. (Hint: use
`induction e using Sym2.ind`.)
-/
example : pathNat.edgeSet = {e | ∃ n, e = s(n, n + 1)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y => simp only [mem_edgeSet, Set.mem_ofPred_eq, Sym2.eq_iff]; grind

/-!
15. The darts whose first vertex is `v` are exactly the darts obtained from the
neighbours of `v` by `dartOfNeighborSet`.
-/
example {G : SimpleGraph V} {v : V} :
    {d : G.Dart | d.fst = v} = Set.range (G.dartOfNeighborSet v) := by
  -- we use `ext` to prove set equality by proving mutual inclusion
  ext d
  constructor
  · rintro rfl
    -- the `rintro rfl` uses the hypothesis `d.toProd.1 = v` to replace
    -- `v` by `d.toProd.1` everywhere, so `v` has vanished:
    -- the goal is now `d ∈ Set.range (G.dartOfNeighborSet d.toProd.1)`
    exact ⟨⟨d.snd, by simp⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    -- this time the hypothesis is `G.dartOfNeighborSet v a = d`, so `rfl` replaces
    -- `d` and it is `d` that vanishes:
    -- the goal is now `G.dartOfNeighborSet v a ∈ {d | d.toProd.1 = v}`
    rfl

/-! END SOLUTIONS -/

end SimpleGraph
