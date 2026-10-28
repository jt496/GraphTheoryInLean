/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import GraphTheoryInLean.C03_Constructions.C03_Constructions
namespace SimpleGraph
/-!
# Exercises

1. Show that a Cayley graph defined on a commutative additive group is simply a
circulant graph.
-/
example (G : Type*) [AddCommGroup G] (s : Set G) :
    addCayley s = circulantGraph s := by
  sorry

/-!
2. Show that the Paley graph on 17 vertices is a circulant graph with the following
differences. Hint: first show that the set of squares in `ZMod 17` is
`{0, 1, 2, 4, 8, 9, 13, 15, 16}`. After `ext` the goal mentions a new variable of
type `ZMod 17`, but `decide` only works on statements with no free variables. Instead
use `decide +revert`, which first reverts the variable and then checks the resulting
statement `∀ y : ZMod 17, …` case by case.
-/
lemma paleyGraph₁₇_eq_circulant' :
    paleyGraph (ZMod 17) = circulantGraph {1, 2, 4, 8, 9, 13, 15, 16} := by
  sorry

/-!
3. Prove that in `Q[n + 1]` the vertex `(v, b₁)` is adjacent to `(v, b₂)` if and only
if `b₁ ≠ b₂`.
-/
example {n : ℕ} (v : HypercubeVert n) (b₁ b₂ : Bool) :
    Q[n + 1].Adj (v, b₁) (v, b₂) ↔ b₁ ≠ b₂ := by
  sorry

/-!
4. Prove that the union (i.e. `⊔`) of the complete bipartite graph between `V` and
`W` with the disjoint union `⊕g` (i.e. `sum`) of complete graphs on `V` and `W` is
the complete graph on `V ⊕ W`.
-/
example {V W : Type*} : completeBipartiteGraph V W ⊔ (⊤ ⊕g ⊤) = ⊤ := by
  sorry

/-!
5. Prove that the complete `1`-partite graph with a single class `ℕ` is empty.
-/
example : completeEquipartiteNat 1 = ⊥ := by
  sorry

/-!
6. Prove that the blow-up of a complete graph is a complete multipartite graph.
-/
example {ι : Type*} (V : ι → Type*) :
    (⊤ : SimpleGraph ι).blowUpGraph V = completeMultipartiteGraph V := by
  sorry

/-!
7. Prove that the cycle graph `C[3]` is the complete graph on `Fin 3`. (Mathlib has
this as `cycleGraph_three_eq_top`, but try to prove it directly.)
-/
example : C[3] = K[3] := by
  sorry

/-!
8. Prove that the disjoint union of empty graphs is empty.
-/
example {ι : Type*} {V : ι → Type*} : Σg (fun i => (⊥ : SimpleGraph (V i))) = ⊥ := by
  sorry

/-!
9. Prove that every left copy of a vertex is isolated in the Mycielskian of the
empty graph. (So `mμ[⊥]` is a star on the right copies together with the isolated
left copies.)
-/
example {V : Type*} (u : V) (x : Option (V ⊕ V)) :
    ¬ mμ[(⊥ : SimpleGraph V)].Adj u ₗ x := by
  sorry

/-!
10. Prove that the cycle graph `C[n + 2]` is `circulantGraph {1}`. (Mathlib has
this, for `C[n + 1]`, as `cycleGraph_eq_circulantGraph`, but prove it directly.)
-/
example (n : ℕ) : C[n + 2] = circulantGraph {1} := by
  sorry

/-!
11. Prove that `sigmaCompleteNat` is the complement of the complete multipartite
graph `completeMultipartiteNat`. Hint: after `ext ⟨i, a⟩ ⟨j, b⟩`, consider the cases
`i = j` and `i ≠ j` separately. In the first case `subst` the equation, so that `a`
and `b` have the same type.
-/
example : sigmaCompleteNat = completeMultipartiteNatᶜ := by
  sorry

/-! SOLUTIONS -/

/-!
1. Show that a Cayley graph defined on a commutative additive group is simply a
circulant graph.
-/
example (G : Type*) [AddCommGroup G] (s : Set G) :
    addCayley s = circulantGraph s := by
  ext u v
  rw [addCayley_adj', circulantGraph_adj]
  aesop

/-!
2. Show that the Paley graph on 17 vertices is a circulant graph with the following
differences. Hint: first show that the set of squares in `ZMod 17` is
`{0, 1, 2, 4, 8, 9, 13, 15, 16}`. After `ext` the goal mentions a new variable of
type `ZMod 17`, but `decide` only works on statements with no free variables. Instead
use `decide +revert`, which first reverts the variable and then checks the resulting
statement `∀ y : ZMod 17, …` case by case.
-/
lemma paleyGraph₁₇_eq_circulant :
    paleyGraph (ZMod 17) = circulantGraph {1, 2, 4, 8, 9, 13, 15, 16} := by
  have : {y : ZMod 17 | IsSquare y} = {0, 1, 2, 4, 8, 9, 13, 15, 16} := by
    ext
    constructor <;> decide +revert
  simp [this, circulantGraph_eq_erase_zero]

/-!
3. Prove that in `Q[n + 1]` the vertex `(v, b₁)` is adjacent to `(v, b₂)` if and only
if `b₁ ≠ b₂`.
-/
example {n : ℕ} (v : HypercubeVert n) (b₁ b₂ : Bool) :
    Q[n + 1].Adj (v, b₁) (v, b₂) ↔ b₁ ≠ b₂ := by simp

/-!
4. Prove that the union (i.e. `⊔`) of the complete bipartite graph between `V` and
`W` with the disjoint union `⊕g` (i.e. `sum`) of complete graphs on `V` and `W` is
the complete graph on `V ⊕ W`.
-/
example {V W : Type*} : completeBipartiteGraph V W ⊔ (⊤ ⊕g ⊤) = ⊤ := by
  ext u v
  cases u <;> cases v <;> simp

/-!
5. Prove that the complete `1`-partite graph with a single class `ℕ` is empty.
-/
example : completeEquipartiteNat 1 = ⊥ := by
  ext ⟨i, _⟩ ⟨j, _⟩
  simp [Subsingleton.elim i j]

/-!
6. Prove that the blow-up of a complete graph is a complete multipartite graph.
-/
example {ι : Type*} (V : ι → Type*) :
    (⊤ : SimpleGraph ι).blowUpGraph V = completeMultipartiteGraph V := rfl

/-!
7. Prove that the cycle graph `C[3]` is the complete graph on `Fin 3`. (Mathlib has
this as `cycleGraph_three_eq_top`, but try to prove it directly.)
-/
example : C[3] = K[3] := by
  ext
  decide +revert

/-!
8. Prove that the disjoint union of empty graphs is empty.
-/
example {ι : Type*} {V : ι → Type*} : Σg (fun i => (⊥ : SimpleGraph (V i))) = ⊥ := by
  ext ⟨i, u⟩ ⟨j, v⟩
  simp

/-!
9. Prove that every left copy of a vertex is isolated in the Mycielskian of the
empty graph. (So `mμ[⊥]` is a star on the right copies together with the isolated
left copies.)
-/
example {V : Type*} (u : V) (x : Option (V ⊕ V)) :
    ¬ mμ[(⊥ : SimpleGraph V)].Adj u ₗ x := by
  rcases x with _ | (v | v) <;> simp

/-!
10. Prove that the cycle graph `C[n + 2]` is `circulantGraph {1}`. (Mathlib has
this, for `C[n + 1]`, as `cycleGraph_eq_circulantGraph`, but prove it directly.)
-/
example (n : ℕ) : C[n + 2] = circulantGraph {1} := by
  ext u v
  grind [cycleGraph_adj, circulantGraph_adj]

/-!
11. Prove that `sigmaCompleteNat` is the complement of the complete multipartite
graph `completeMultipartiteNat`. Hint: after `ext ⟨i, a⟩ ⟨j, b⟩`, consider the cases
`i = j` and `i ≠ j` separately. In the first case `subst` the equation, so that `a`
and `b` have the same type.
-/
example : sigmaCompleteNat = completeMultipartiteNatᶜ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-! END SOLUTIONS -/


end SimpleGraph
