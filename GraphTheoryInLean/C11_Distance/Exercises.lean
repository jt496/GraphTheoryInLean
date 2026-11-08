/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import GraphTheoryInLean.C11_Distance.C11_Distance
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
/-!
# Exercises

1. Show that two vertices with a common neighbour are at distance at most `2`.
-/
example {u v w : V} (huw : G.Adj u w) (hwv : G.Adj w v) : G.edist u v ≤ 2 := by
  sorry

/-!
2. Show that in a triangle-free graph two distinct vertices with a common neighbour
are at distance exactly `2`. Hint: `edist_eq_two_iff`.
-/
example (h3 : G.CliqueFree 3) {u v w : V} (huw : G.Adj u w) (hwv : G.Adj w v)
    (huv : u ≠ v) : G.edist u v = 2 := by
  sorry

/-!
3. Deduce from `Hom.edist_le` that adding edges cannot increase distances (this is
Mathlib's `edist_anti`), and that the distance between two vertices of an induced
subgraph is at least their distance in `G`.

Hint: `Hom.ofLE` and `Embedding.induce`.
-/
example {H : SimpleGraph V} (h : G ≤ H) (u v : V) : H.edist u v ≤ G.edist u v := by
  sorry

example (s : Set V) (u v : s) : G.edist u v ≤ (G.induce s).edist u v := by
  sorry

/-!
4. Use `edist_eq_hammingDist` to show that the Hamming distance (between vertices of
the hypercube) satisfies the triangle inequality.

Hint: rewrite the triangle inequality for `edist` in `Q[n]` using
`edist_eq_hammingDist`, and cast the result back to `ℕ`.
-/
example {n : ℕ} (u v w : HypercubeVert n) :
    u.hammingDist w ≤ u.hammingDist v + v.hammingDist w := by
  sorry

/-!
5. Show that the complete bipartite graph `K[s + 2, t + 1]` has diameter `2`.
-/
example (s t : ℕ) : K[s + 2, t + 1].ediam = 2 := by
  sorry

/-!
6. Show that if `G` has diameter at least `3` then its complement has diameter at
most `3`.

Hint: take two vertices `u` and `v` at distance more than `2` in `G`
(`two_lt_edist_iff`), and show that every vertex is adjacent to `u` or to `v` in
`Gᶜ`, or equal to one of them.
-/
example (h : 3 ≤ G.ediam) : Gᶜ.ediam ≤ 3 := by
  sorry

/-!
7. Show that if `v` has a neighbour in `G` then in the Mycielskian `mμ(G)` the two
copies `vˡ` and `vʳ` of `v` are at distance exactly `2`. Hint: `edist_eq_two_iff`.
-/
example {u v : V} (h : G.Adj u v) : mμ(G).edist vˡ vʳ = 2 := by
  sorry

/-!
8. Show that every vertex of the cycle graph `C[n + 3]` has eccentricity
`(n + 3) / 2`.

Hint: `IsVertexTransitive.eccent_eq`, `ediam` and `ediam_cycleGraph`.
-/
example (n : ℕ) (v : Fin (n + 3)) : C[n + 3].eccent v = ((n + 3) / 2 : ℕ) := by
  sorry

/-!
9. Show that the Grötzsch graph `mμ(C[5])` has girth `4`. Hint: use
`egirth_mycielskian_eq_four`.
-/
example : grotzschGraph.egirth = 4 := by
  sorry

/-!
10. Use the Moore bound to show that a `3`-regular graph of diameter at most `2` has
at most `10` vertices. (The Petersen graph shows that this is best possible.)
-/
example [G.LocallyFinite] (h : G.IsRegularOfDegree 3) (hd : G.ediam ≤ 2) :
    ENat.card V ≤ 10 := by
  sorry

/-!
11. Use the cage bound to show that a graph with minimum degree at least `3` and
girth at least `5` has at least `10` vertices. (The Petersen graph shows that this
is best possible.)
-/
example [G.LocallyFinite] [Nonempty V] (h : ∀ v, 3 ≤ G.degree v)
    (hg : 5 ≤ G.egirth) : 10 ≤ ENat.card V := by
  sorry

/-! SOLUTIONS -/

/-!
1. Show that two vertices with a common neighbour are at distance at most `2`.
-/
example {u v w : V} (huw : G.Adj u w) (hwv : G.Adj w v) : G.edist u v ≤ 2 :=
  (edist_le (Walk.cons huw (Walk.cons hwv Walk.nil))).trans (by simp)

/-!
2. Show that in a triangle-free graph two distinct vertices with a common neighbour
are at distance exactly `2`. Hint: `edist_eq_two_iff`.

The vertices `u` and `v` are not adjacent, since otherwise `u`, `v` and `w` would
form a triangle, and `w` is a common neighbour.
-/
example (h3 : G.CliqueFree 3) {u v w : V} (huw : G.Adj u w) (hwv : G.Adj w v)
    (huv : u ≠ v) : G.edist u v = 2 := by
  classical
  exact edist_eq_two_iff.mpr ⟨huv, fun h => h3 _ (is3Clique_triple_iff.2
    ⟨h, huw, hwv.symm⟩), w, G.mem_commonNeighbors.2 ⟨huw, hwv.symm⟩⟩

/-!
3. Deduce from `Hom.edist_le` that adding edges cannot increase distances (this is
Mathlib's `edist_anti`), and that the distance between two vertices of an induced
subgraph is at least their distance in `G`.

Hint: `Hom.ofLE` and `Embedding.induce`.

Both inequalities apply `Hom.edist_le` to a homomorphism that is the identity on
vertices: the inclusion `Hom.ofLE h : G →g H`, and the embedding
`Embedding.induce s : G.induce s ↪g G` of the induced subgraph.
-/
example {H : SimpleGraph V} (h : G ≤ H) (u v : V) : H.edist u v ≤ G.edist u v :=
  (Hom.ofLE h).edist_le u v

example (s : Set V) (u v : s) : G.edist u v ≤ (G.induce s).edist u v :=
  (Embedding.induce s).toHom.edist_le u v

/-!
4. Use `edist_eq_hammingDist` to show that the Hamming distance (between vertices of
the hypercube) satisfies the triangle inequality.

Hint: rewrite the triangle inequality for `edist` in `Q[n]` using
`edist_eq_hammingDist`, and cast the result back to `ℕ`.
-/
example {n : ℕ} (u v w : HypercubeVert n) :
    u.hammingDist w ≤ u.hammingDist v + v.hammingDist w := by
  have := Q[n].edist_triangle (u := u) (v := v) (w := w)
  rw [edist_eq_hammingDist, edist_eq_hammingDist, edist_eq_hammingDist] at this
  exact_mod_cast this

/-!
5. Show that the complete bipartite graph `K[s + 2, t + 1]` has diameter `2`.

In the complete bipartite graph any two vertices on the same side have a common
neighbour on the other side, so the diameter is at most `2`, while two distinct
vertices on the same side are not adjacent, so it is at least `2`.
-/
example (s t : ℕ) : K[s + 2, t + 1].ediam = 2 := by
  refine le_antisymm (ediam_le_of_edist_le fun u v => not_lt.1 fun h => ?_) ?_
  · obtain ⟨-, hadj, hcn⟩ := two_lt_edist_iff.mp h
    rw [Set.eq_empty_iff_forall_notMem] at hcn
    rcases u with a | a <;> rcases v with b | b
    · exact hcn (.inr 0) (by simp [mem_commonNeighbors])
    · simp at hadj
    · simp at hadj
    · exact hcn (.inl 0) (by simp [mem_commonNeighbors])
  · exact (edist_eq_two_iff.mpr ⟨by simp, by simp, .inr 0,
      by simp [mem_commonNeighbors]⟩).ge.trans
      (edist_le_ediam (u := .inl 0) (v := .inl 1))

/-!
6. Show that if `G` has diameter at least `3` then its complement has diameter at
most `3`.

Hint: take two vertices `u` and `v` at distance more than `2` in `G`
(`two_lt_edist_iff`), and show that every vertex is adjacent to `u` or to `v` in
`Gᶜ`, or equal to one of them.
-/
example (h : 3 ≤ G.ediam) : Gᶜ.ediam ≤ 3 := by
  obtain ⟨u, v, huv⟩ : ∃ u v, 2 < G.edist u v := by
    by_contra! hc
    exact absurd (h.trans (ediam_le_of_edist_le hc)) (by decide)
  obtain ⟨hne, hnadj, hcn⟩ := two_lt_edist_iff.mp huv
  -- in `Gᶜ`, every vertex is within distance `1` of `u` or `v`, and `u` and `v` are
  -- within distance `1` of each other
  have hnear : ∀ x, ∃ w ∈ ({u, v} : Set V), Gᶜ.edist x w ≤ 1 := by
    intro x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
      exists_eq_left, edist_le_one_iff_adj_or_eq, compl_adj]
    by_contra! hx
    have : x ∈ G.commonNeighbors u v := by
      simp only [mem_commonNeighbors]
      exact ⟨(hx.1.1 hx.1.2).symm, (hx.2.1 hx.2.2).symm⟩
    simp [hcn] at this
  have huv1 : Gᶜ.edist u v ≤ 1 := edist_le_one_iff_adj_or_eq.mpr (.inl ⟨hne, hnadj⟩)
  have hpair : ∀ a ∈ ({u, v} : Set V), ∀ b ∈ ({u, v} : Set V), Gᶜ.edist a b ≤ 1 := by
    rintro a (rfl | rfl) b (rfl | rfl) <;>
      first | simp | exact huv1 | exact edist_comm.trans_le huv1
  refine ediam_le_of_edist_le fun x y => ?_
  obtain ⟨a, ha, hxa⟩ := hnear x
  obtain ⟨b, hb, hyb⟩ := hnear y
  calc Gᶜ.edist x y ≤ Gᶜ.edist x a + Gᶜ.edist a b + Gᶜ.edist b y :=
        Gᶜ.edist_triangle.trans (add_le_add_left Gᶜ.edist_triangle _)
    _ ≤ 1 + 1 + 1 := by gcongr; exacts [hpair a ha b hb, edist_comm.trans_le hyb]
    _ = 3 := by norm_num

/-!
7. Show that if `v` has a neighbour in `G` then in the Mycielskian `mμ(G)` the two
copies `vˡ` and `vʳ` of `v` are at distance exactly `2`. Hint: `edist_eq_two_iff`.

The two copies of `v` are distinct and not adjacent (`v` is not adjacent to itself
in `G`), and the left copy `uˡ` of any neighbour `u` of `v` is a common neighbour.
-/
example {u v : V} (h : G.Adj u v) : mμ(G).edist vˡ vʳ = 2 := by
  rw [edist_eq_two_iff]
  refine ⟨by simp, by simp, ⟨uˡ, ?_⟩⟩
  simp [mem_commonNeighbors, h.symm]

/-!
8. Show that every vertex of the cycle graph `C[n + 3]` has eccentricity
`(n + 3) / 2`.

Hint: `IsVertexTransitive.eccent_eq`, `ediam` and `ediam_cycleGraph`.
-/
example (n : ℕ) (v : Fin (n + 3)) : C[n + 3].eccent v = ((n + 3) / 2 : ℕ) := by
  rw [← ediam_cycleGraph n, ediam,
    iSup_congr fun u => (isVertexTransitive_cycleGraph _).eccent_eq u v, iSup_const]

/-!
9. Show that the Grötzsch graph `mμ(C[5])` has girth `4`. Hint: use
`egirth_mycielskian_eq_four`.

`C[5]` is triangle-free, and its vertex `0` has the two neighbours `1` and `4`, so
`egirth_mycielskian_eq_four` applies. Both facts are finite checks.
-/
example : grotzschGraph.egirth = 4 := by
  refine egirth_mycielskian_eq_four (by decide) fun h => ?_
  exact absurd (h 0 1 4 (by decide) (by decide)) (by decide)

/-!
10. Use the Moore bound to show that a `3`-regular graph of diameter at most `2` has
at most `10` vertices. (The Petersen graph shows that this is best possible.)
-/
example [G.LocallyFinite] (h : G.IsRegularOfDegree 3) (hd : G.ediam ≤ 2) :
    ENat.card V ≤ 10 := by
  simpa [Finset.sum_range_succ] using moore_bound G 2 2 (fun v => (h v).le) hd

/-!
11. Use the cage bound to show that a graph with minimum degree at least `3` and
girth at least `5` has at least `10` vertices. (The Petersen graph shows that this
is best possible.)
-/
example [G.LocallyFinite] [Nonempty V] (h : ∀ v, 3 ≤ G.degree v)
    (hg : 5 ≤ G.egirth) : 10 ≤ ENat.card V := by
  simpa [Finset.sum_range_succ] using cage_bound_odd G 2 2 h hg

/-! END SOLUTIONS -/

end SimpleGraph
