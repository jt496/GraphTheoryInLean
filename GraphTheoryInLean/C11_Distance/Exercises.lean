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
subgraph is at least their distance in `G`. Hint: `Hom.ofLE` and
`Embedding.induce`.
-/
example {H : SimpleGraph V} (h : G ≤ H) (u v : V) : H.edist u v ≤ G.edist u v := by
  sorry

example (s : Set V) (u v : s) : G.edist u v ≤ (G.induce s).edist u v := by
  sorry

/-!
4. Show that `dist` does not satisfy the triangle inequality in general: find a
graph `G` on `Fin 3` and vertices `u`, `v`, `w` with
`G.dist u v + G.dist v w < G.dist u w`. Hint: an edge plus an isolated vertex, and
`dist_eq_zero_iff_eq_or_not_reachable`.
-/
example : ∃ (G : SimpleGraph (Fin 3)) (u v w : Fin 3),
    G.dist u v + G.dist v w < G.dist u w := by
  sorry

/-!
5. Use `edist_eq_hammingDist` to show that the Hamming distance satisfies the
triangle inequality.
-/
example {n : ℕ} (u v w : HypercubeVert n) :
    u.hammingDist w ≤ u.hammingDist v + v.hammingDist w := by
  sorry

/-!
6. Show that every vertex of the cycle graph `C[n + 3]` has eccentricity
`(n + 3) / 2`. Hint: in a vertex-transitive graph all the eccentricities are equal
(`IsVertexTransitive.eccent_eq`), and the diameter is their supremum (`ediam`).
-/
example (n : ℕ) (v : Fin (n + 3)) : C[n + 3].eccent v = ((n + 3) / 2 : ℕ) := by
  sorry

/-!
7. Show that every vertex of the hypercube `Q[n]` has eccentricity `n`.
-/
example {n : ℕ} (v : HypercubeVert n) : Q[n].eccent v = n := by
  sorry

/-!
8. Show that the complete bipartite graph `K[s + 2, t + 1]` has diameter `2`.
-/
example (s t : ℕ) : K[s + 2, t + 1].ediam = 2 := by
  sorry

/-!
9. Show that if `G` has diameter at least `3` then its complement has diameter at
most `3`. Hint: take two vertices `u` and `v` at distance more than `2` in `G`
(`two_lt_edist_iff`), and show that every vertex is adjacent to `u` or to `v` in
`Gᶜ`, or equal to one of them.
-/
example (h : 3 ≤ G.ediam) : Gᶜ.ediam ≤ 3 := by
  sorry

/-!
10. Show that if `v` has a neighbour in `G` then in the Mycielskian `mμ[G]` the two
copies `v ₗ` and `v ᵣ` of `v` are at distance exactly `2`. Hint: `edist_eq_two_iff`.
-/
example {u v : V} (h : G.Adj u v) : mμ[G].edist (v ₗ) (v ᵣ) = 2 := by
  sorry

/-!
11. Show that the Grötzsch graph `mμ[C[5]]` has girth `4`.
-/
example : grotzschGraph.egirth = 4 := by
  sorry

/-!
12. Use the Moore bound to show that a cubic graph of diameter at most `2` has at
most `10` vertices. (The Petersen graph shows that this is best possible.)
-/
example [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsRegularOfDegree 3) (hd : G.ediam ≤ 2) : Fintype.card V ≤ 10 := by
  sorry

/-!
13. Show that the Moore bound holds with local finiteness as the only finiteness
assumption: a locally finite graph with maximum degree at most `d + 1` and diameter
at most `k` is finite, and has at most `1 + (d + 1) * (1 + d + ⋯ + d ^ (k - 1))`
vertices. Hint: `finite_of_eccent_le` and `moore_bound`.
-/
example (G : SimpleGraph V) [G.LocallyFinite] (d k : ℕ)
    (h_deg : ∀ v, G.degree v ≤ d + 1) (h : G.ediam ≤ k) :
    Finite V ∧ Nat.card V ≤ 1 + (d + 1) * ∑ i ∈ Finset.range k, d ^ i := by
  sorry

/-!
14. Use the cage bound to show that a graph with minimum degree at least `3` and
girth at least `5` has at least `10` vertices. (The Petersen graph shows that this
is best possible.)
-/
example [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ v, 3 ≤ G.degree v) (hg : 5 ≤ G.egirth) : 10 ≤ Fintype.card V := by
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
    ⟨h, huw, hwv.symm⟩), w, (G.mem_commonNeighbors).2 ⟨huw, hwv.symm⟩⟩

/-!
3. Deduce from `Hom.edist_le` that adding edges cannot increase distances (this is
Mathlib's `edist_anti`), and that the distance between two vertices of an induced
subgraph is at least their distance in `G`. Hint: `Hom.ofLE` and
`Embedding.induce`.

Both inequalities apply `Hom.edist_le` to a homomorphism that is the identity on
vertices: the inclusion `Hom.ofLE h : G →g H`, and the embedding
`Embedding.induce s : G.induce s ↪g G` of the induced subgraph.
-/
example {H : SimpleGraph V} (h : G ≤ H) (u v : V) : H.edist u v ≤ G.edist u v :=
  (Hom.ofLE h).edist_le u v

example (s : Set V) (u v : s) : G.edist u v ≤ (G.induce s).edist u v :=
  (Embedding.induce s).toHom.edist_le u v

/-!
4. Show that `dist` does not satisfy the triangle inequality in general: find a
graph `G` on `Fin 3` and vertices `u`, `v`, `w` with
`G.dist u v + G.dist v w < G.dist u w`. Hint: an edge plus an isolated vertex, and
`dist_eq_zero_iff_eq_or_not_reachable`.

Take the edge `0 — 1` and the isolated vertex `2`. No walk leaves `2`, so `2` is
reachable only from itself, and the junk value `0` gives
`G.dist 0 2 + G.dist 2 1 = 0 < 1 = G.dist 0 1`.
-/
example : ∃ (G : SimpleGraph (Fin 3)) (u v w : Fin 3),
    G.dist u v + G.dist v w < G.dist u w := by
  let G := fromRel fun a b : Fin 3 => a = 0 ∧ b = 1
  have h2 (x : Fin 3) (h : G.Reachable 2 x) : x = 2 := by
    obtain ⟨p⟩ := h
    cases p with
    | nil => rfl
    | cons ha _ =>
      rename_i y _
      fin_cases y <;> exact absurd ha (by decide)
  have h01 : G.dist 0 1 = 1 := dist_eq_one_iff_adj.mpr (by decide)
  have h02 : G.dist 0 2 = 0 := dist_eq_zero_iff_eq_or_not_reachable.mpr
    (.inr fun h => absurd (h2 0 h.symm) (by decide))
  have h21 : G.dist 2 1 = 0 := dist_eq_zero_iff_eq_or_not_reachable.mpr
    (.inr fun h => absurd (h2 1 h) (by decide))
  exact ⟨G, 0, 2, 1, by rw [h01, h02, h21]; norm_num⟩

/-!
5. Use `edist_eq_hammingDist` to show that the Hamming distance satisfies the
triangle inequality.

Rewrite the triangle inequality for `edist` in `Q[n]` using
`edist_eq_hammingDist`, and cast the result back to `ℕ`.
-/
example {n : ℕ} (u v w : HypercubeVert n) :
    u.hammingDist w ≤ u.hammingDist v + v.hammingDist w := by
  have := Q[n].edist_triangle (u := u) (v := v) (w := w)
  rw [edist_eq_hammingDist, edist_eq_hammingDist, edist_eq_hammingDist] at this
  exact_mod_cast this

/-!
6. Show that every vertex of the cycle graph `C[n + 3]` has eccentricity
`(n + 3) / 2`. Hint: in a vertex-transitive graph all the eccentricities are equal
(`IsVertexTransitive.eccent_eq`), and the diameter is their supremum (`ediam`).

Since all the eccentricities equal `C[n + 3].eccent v`, so does their supremum, the
diameter, which we computed in `ediam_cycleGraph`.
-/
example (n : ℕ) (v : Fin (n + 3)) : C[n + 3].eccent v = ((n + 3) / 2 : ℕ) := by
  rw [← ediam_cycleGraph n, ediam,
    iSup_congr fun u => (isVertexTransitive_cycleGraph _).eccent_eq u v, iSup_const]

/-!
7. Show that every vertex of the hypercube `Q[n]` has eccentricity `n`.
-/
example {n : ℕ} (v : HypercubeVert n) : Q[n].eccent v = n :=
  le_antisymm (eccent_le_ediam.trans ediam_hypercube.le)
    (radius_hypercube.ge.trans radius_le_eccent)

/-!
8. Show that the complete bipartite graph `K[s + 2, t + 1]` has diameter `2`.

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
9. Show that if `G` has diameter at least `3` then its complement has diameter at
most `3`. Hint: take two vertices `u` and `v` at distance more than `2` in `G`
(`two_lt_edist_iff`), and show that every vertex is adjacent to `u` or to `v` in
`Gᶜ`, or equal to one of them.

In the complement every vertex `x` is adjacent to `u` or to `v` (or equal to one of
them), since otherwise `x` would be a common neighbour of `u` and `v` in `G`; and `u`
is adjacent to `v`. So any two vertices are joined in `Gᶜ` by a walk of length at
most `3` through `u` or `v`.
-/
example (h : 3 ≤ G.ediam) : Gᶜ.ediam ≤ 3 := by
  obtain ⟨u, v, huv⟩ : ∃ u v, 2 < G.edist u v := by
    by_contra! hc
    exact absurd (h.trans (ediam_le_of_edist_le hc)) (by decide)
  obtain ⟨hne, hnadj, hcn⟩ := two_lt_edist_iff.mp huv
  have hnear : ∀ x, Gᶜ.edist x u ≤ 1 ∨ Gᶜ.edist x v ≤ 1 := by
    intro x
    simp only [edist_le_one_iff_adj_or_eq, compl_adj]
    by_contra! hx
    have : x ∈ G.commonNeighbors u v := by
      simp only [mem_commonNeighbors]
      exact ⟨(hx.1.1 hx.1.2).symm, (hx.2.1 hx.2.2).symm⟩
    simp [hcn] at this
  have huv1 : Gᶜ.edist u v ≤ 1 :=
    edist_le_one_iff_adj_or_eq.mpr (Or.inl ⟨hne, hnadj⟩)
  refine ediam_le_of_edist_le fun x y => ?_
  rcases hnear x with hx | hx <;> rcases hnear y with hy | hy
  · calc Gᶜ.edist x y ≤ Gᶜ.edist x u + Gᶜ.edist u y := Gᶜ.edist_triangle
      _ ≤ 1 + 1 := add_le_add hx (by rwa [edist_comm])
      _ ≤ 3 := by norm_num
  · calc Gᶜ.edist x y ≤ Gᶜ.edist x u + Gᶜ.edist u v + Gᶜ.edist v y :=
          Gᶜ.edist_triangle.trans (add_le_add_left Gᶜ.edist_triangle _)
      _ ≤ 1 + 1 + 1 := add_le_add (add_le_add hx huv1) (by rwa [edist_comm])
      _ = 3 := by norm_num
  · calc Gᶜ.edist x y ≤ Gᶜ.edist x v + Gᶜ.edist v u + Gᶜ.edist u y :=
          Gᶜ.edist_triangle.trans (add_le_add_left Gᶜ.edist_triangle _)
      _ ≤ 1 + 1 + 1 :=
          add_le_add (add_le_add hx (by rwa [edist_comm])) (by rwa [edist_comm])
      _ = 3 := by norm_num
  · calc Gᶜ.edist x y ≤ Gᶜ.edist x v + Gᶜ.edist v y := Gᶜ.edist_triangle
      _ ≤ 1 + 1 := add_le_add hx (by rwa [edist_comm])
      _ ≤ 3 := by norm_num

/-!
10. Show that if `v` has a neighbour in `G` then in the Mycielskian `mμ[G]` the two
copies `v ₗ` and `v ᵣ` of `v` are at distance exactly `2`. Hint: `edist_eq_two_iff`.

The two copies of `v` are distinct and not adjacent (`v` is not adjacent to itself
in `G`), and the left copy `u ₗ` of any neighbour `u` of `v` is a common neighbour.
-/
example {u v : V} (h : G.Adj u v) : mμ[G].edist (v ₗ) (v ᵣ) = 2 := by
  rw [edist_eq_two_iff]
  refine ⟨by simp, by simp, ⟨u ₗ, ?_⟩⟩
  rw [mem_commonNeighbors]
  simp [h.symm]

/-!
11. Show that the Grötzsch graph `mμ[C[5]]` has girth `4`.

`C[5]` is triangle-free, and its vertex `0` has the two neighbours `1` and `4`, so
`egirth_mycielskian_eq_four` applies. Both facts are finite checks.
-/
example : grotzschGraph.egirth = 4 := by
  refine egirth_mycielskian_eq_four (by decide) fun h => ?_
  exact absurd (h 0 1 4 (by decide) (by decide)) (by decide)

/-!
12. Use the Moore bound to show that a cubic graph of diameter at most `2` has at
most `10` vertices. (The Petersen graph shows that this is best possible.)
-/
example [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsRegularOfDegree 3) (hd : G.ediam ≤ 2) : Fintype.card V ≤ 10 := by
  simpa [Finset.sum_range_succ] using moore_bound G 2 2 (fun v => (h v).le) hd

/-!
13. Show that the Moore bound holds with local finiteness as the only finiteness
assumption: a locally finite graph with maximum degree at most `d + 1` and diameter
at most `k` is finite, and has at most `1 + (d + 1) * (1 + d + ⋯ + d ^ (k - 1))`
vertices. Hint: `finite_of_eccent_le` and `moore_bound`.
-/
/-!
An empty graph is finite. Otherwise any vertex `r` has eccentricity at most the
diameter, so `V` is finite by `finite_of_eccent_le`, and we can apply `moore_bound`.
-/
example (G : SimpleGraph V) [G.LocallyFinite] (d k : ℕ)
    (h_deg : ∀ v, G.degree v ≤ d + 1) (h : G.ediam ≤ k) :
    Finite V ∧ Nat.card V ≤ 1 + (d + 1) * ∑ i ∈ Finset.range k, d ^ i := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨r⟩⟩
  · exact ⟨inferInstance, by simp⟩
  have hfin : Finite V := finite_of_eccent_le (eccent_le_ediam (u := r) |>.trans h)
  exact ⟨hfin, moore_bound G d k h_deg h⟩

/-!
14. Use the cage bound to show that a graph with minimum degree at least `3` and
girth at least `5` has at least `10` vertices. (The Petersen graph shows that this
is best possible.)
-/
example [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ v, 3 ≤ G.degree v) (hg : 5 ≤ G.egirth) : 10 ≤ Fintype.card V := by
  simpa [Finset.sum_range_succ, Nat.card_eq_fintype_card] using
    cage_bound_odd G 2 2 (fun v => h v) hg

/-! END SOLUTIONS -/

end SimpleGraph
