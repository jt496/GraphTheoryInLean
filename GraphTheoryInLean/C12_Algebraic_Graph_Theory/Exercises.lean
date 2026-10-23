import GraphTheoryInLean.C12_Algebraic_Graph_Theory.C12_Algebraic_Graph_Theory
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
/-!
# Exercises
1. Let `M` be a group. Prove that for any `s : Set M` the Cayley graph
`mulCayley s` is vertex-transitive. (Start by showing that left multiplication by any
`g : M` is an automorphism of `mulCayley s`.)
-/
def autMulLeftCayley' {M : Type*} [Group M] (s : Set M) (g : M) :
    mulCayley s ≃g mulCayley s :=
  sorry

lemma isVertexTransitive_mulCayley' {M : Type*} [Group M] (s : Set M) :
    IsVertexTransitive (mulCayley s) := by
  sorry

/-!
2. Show that the automorphisms of a complete graph are exactly the permutations of
its vertices, i.e. that its automorphism group is the symmetric group
`Equiv.Perm V`, and deduce that `K[n]` has `n!` automorphisms. (Hint: Mathlib's
`Iso.completeGraph` turns a bijection into an isomorphism of complete graphs, and
`Nat.card_perm` counts permutations.)
-/
def autTopMulEquivPerm' (V : Type*) :
    ((⊤ : SimpleGraph V) ≃g (⊤ : SimpleGraph V)) ≃* Equiv.Perm V :=
  sorry

lemma card_aut_completeGraph' (n : ℕ) : Nat.card (K[n] ≃g K[n]) = n.factorial := by
  sorry

/-!
3. Show that a graph and its complement have the same automorphisms. (Hint: for the
inverse map, treat the pairs of vertices `a = b` and `a ≠ b` separately.)
-/
def autComplMulEquiv' (G : SimpleGraph V) : (G ≃g G) ≃* (Gᶜ ≃g Gᶜ) :=
  sorry

/-!
4. Show that every vertex of a vertex-transitive graph with an odd number of vertices
has even degree. (Hint: such a graph is regular by
`IsVertexTransitive.exists_isRegularOfDegree`; now use the handshake lemma in the
form `sum_degrees_eq_twice_card_edges'` of
[The Handshake Lemma](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-the-handshake-lemma).)
-/
lemma even_degree_of_isVertexTransitive' [Fintype V] [G.LocallyFinite]
    (h : G.IsVertexTransitive) (hodd : Odd (Fintype.card V)) (v : V) :
    Even (G.degree v) := by
  sorry

/-!
5. Show that the Kneser graph `Kn[n, k]` is vertex-transitive, and deduce that so is
the Petersen graph. Hint: a permutation `σ` of `Fin n` gives an automorphism
`x ↦ x.map σ`. Given two `k`-subsets `s` and `t`, glue a bijection between `s` and
`t` to one between their complements, using `Fintype.equivOfCardEq` and
`Equiv.subtypeCongr`, to get a permutation sending `s` onto `t`.
-/
lemma isVertexTransitive_kneserGraph' (n k : ℕ) : Kn[n, k].IsVertexTransitive := by
  sorry

example : petersenGraph.IsVertexTransitive := by
  sorry

/-!
6. Show that the cycle `C[n + 3]` has `2 * (n + 3)` automorphisms. (Hint: use
`autCycleGraphMulEquivDihedral` and `DihedralGroup.nat_card`.)
-/
lemma card_aut_cycleGraph' (n : ℕ) :
    Nat.card (C[n + 3] ≃g C[n + 3]) = 2 * (n + 3) := by
  sorry

/-!
7. Show that the trace of the square of the adjacency matrix of a finite graph is
twice the number of edges.
-/
open Finset in
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (G.adjMatrix ℕ ^ 2).trace = 2 * #G.edgeFinset := by
  sorry

/-!
8. The vector `mycielskianLift t x` again has entries summing to zero, so the
construction can be repeated. Show this, and deduce that the Grötzsch graph
`grotzschGraph`, i.e. `mμ[C[5]]`, has eigenvalues `1`, `-φ ^ 2` and `-ψ ^ 2`. (Hint:
`grotzschGraph` is isomorphic to `mμ[mμ[K[2]]]`, by `Iso.mapMycielskian` applied to
`mycielskianCompleteTwoIsoCycleFive`.)
-/
lemma sum_mycielskianLift' [Fintype V] {R : Type*} [CommRing R] (t : R)
    {x : V → R} (hsum : ∑ v, x v = 0) : ∑ w, mycielskianLift t x w = 0 := by
  sorry

open scoped goldenRatio in
example : 1 ∈ spectrum ℝ (grotzschGraph.adjMatrix ℝ) ∧
    -φ ^ 2 ∈ spectrum ℝ (grotzschGraph.adjMatrix ℝ) ∧
    -ψ ^ 2 ∈ spectrum ℝ (grotzschGraph.adjMatrix ℝ) := by
  sorry

/-!
9. Show that the entries in each row of the Laplacian sum to `0`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (i : V) :
    ∑ j, G.lapMatrix ℤ i j = 0 := by
  sorry

/-!
10. Show that if `G` has no isolated vertices, then the kernel of the Laplacian of
the Mycielskian `mμ[G]` is `1`-dimensional.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : ∀ v, ¬ G.IsIsolated v) :
    Module.finrank ℝ (mμ[G].lapMatrix ℝ).toLin'.ker = 1 := by
  sorry

/-!
11. Show that `C[5]` is strongly regular with parameters `(5, 2, 0, 1)`, and deduce
that its diameter is `2`.
-/
example : C[5].IsSRGWith 5 2 0 1 ∧ C[5].ediam = 2 := by
  sorry

/-!
12. Show that there is no strongly regular graph with parameters `(10, 4, 0, 1)`.
-/
example {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ G.IsSRGWith 10 4 0 1 := by
  sorry

/-!
13. Show that the Hamming cube is isomorphic to the third construction of the
hypercube, the Hasse diagram `hypercubeHasse` of the subsets of `Fin n`, by sending a
vertex `x` to the set of coordinates `i` with `x i = true`. (Hint: adding the basis
vector `e i` to `x` removes `i` from this set if it is there, and inserts it
otherwise. Use `hypercubeHamming_adj_iff_exists`, `hasse_adj`,
`Finset.covBy_iff_exists_insert`, `Finset.covBy_insert` and `Finset.erase_covBy`.)
-/
open scoped hypercubeHamming in
def hypercubeHammingIsoHasse' (n : ℕ) : hypercubeHamming n ≃g hypercubeHasse n :=
  sorry

/-!
14. Show that the hypercube is *arc-transitive*: for any two edges `x — y` and
`u — v` there is an automorphism sending `x` to `u` and `y` to `v`. (Hint: if
`y = x + e i` and `v = u + e j`, compose a translation, the coordinate permutation
`Equiv.swap i j` and another translation.)
-/
open scoped hypercubeHamming in
lemma exists_aut_hypercubeHamming_of_adj' {n : ℕ} {x y u v : Fin n → Bool}
    (h : (hypercubeHamming n).Adj x y) (h' : (hypercubeHamming n).Adj u v) :
    ∃ g : hypercubeHamming n ≃g hypercubeHamming n, g x = u ∧ g y = v := by
  sorry

/-!
15. Show that the copies of any graph `A` in a complete graph are just the injective
maps between the vertex types. Deduce that `K[n]` contains
`n.descFactorial (k + 3) = n * (n - 1) * ⋯ * (n - k - 2)` labelled copies of
`C[k + 3]`. (Hint: `Fintype.card_embedding_eq`.)
-/
def copyTopEquiv' {W : Type*} (A : SimpleGraph V) :
    Copy A (⊤ : SimpleGraph W) ≃ (V ↪ W) :=
  sorry

lemma labelledCopyCount_completeGraph_cycleGraph' (n k : ℕ) :
    K[n].labelledCopyCount C[k + 3] = n.descFactorial (k + 3) := by
  sorry

/-!
16. Deduce that `K[n + 3]` contains `(n + 3)! / (2 * (n + 3))` Hamiltonian cycles,
i.e. unlabelled copies of `C[n + 3]`. (Hint: `labelledCopyCount_cycleGraph`.)
-/
lemma copyCount_completeGraph_cycleGraph' (n : ℕ) :
    2 * (n + 3) * K[n + 3].copyCount C[n + 3] = (n + 3).factorial := by
  sorry

/-!
17. Count the `4`-cycles in the hypercube: show that `Q[n]` contains
`2 ^ n * (n * (n - 1))` labelled copies of `C[4]` and, for `2 ≤ n`,
`n.choose 2 * 2 ^ (n - 2)` unlabelled ones. (Hint: transport
`labelledCopyCount_hypercube` and `copyCount_hypercube` along the isomorphism
`hypercubeTwoIsoCycleFour : Q[2] ≃g C[4]`, using `Iso.labelledCopyCount_eq` and
`Iso.copyCount_eq_left`.)
-/
lemma labelledCopyCount_hypercube_cycleGraph_four' (n : ℕ) :
    Q[n].labelledCopyCount C[4] = 2 ^ n * (n * (n - 1)) := by
  sorry

lemma copyCount_hypercube_cycleGraph_four' (n : ℕ) (hn : 2 ≤ n) :
    Q[n].copyCount C[4] = n.choose 2 * 2 ^ (n - 2) := by
  sorry

/-!
18. Show that `C[5]` has `10` labelled copies in itself, using Exercise 6.
-/
lemma labelledCopyCount_cycleGraph_five_self' :
    C[5].labelledCopyCount C[5] = 10 := by
  sorry

/-! SOLUTIONS -/

/-!
1. Let `M` be a group. Prove that for any `s : Set M` the Cayley graph
`mulCayley s` is vertex-transitive. (Start by showing that left multiplication by any
`g : M` is an automorphism of `mulCayley s`.)
-/
/-- Left multiplication by `g` as an automorphism of the Cayley graph
`mulCayley s`. -/
def autMulLeftCayley {M : Type*} [Group M] (s : Set M) (g : M) :
    mulCayley s ≃g mulCayley s :=
  ⟨Equiv.mulLeft g, by simp⟩

lemma isVertexTransitive_mulCayley {M : Type*} [Group M] (s : Set M) :
    IsVertexTransitive (mulCayley s) :=
  fun u v => ⟨autMulLeftCayley s (v * u⁻¹), by simp [autMulLeftCayley]⟩

/-!
2. Show that the automorphisms of a complete graph are exactly the permutations of
its vertices, i.e. that its automorphism group is the symmetric group
`Equiv.Perm V`, and deduce that `K[n]` has `n!` automorphisms. (Hint: Mathlib's
`Iso.completeGraph` turns a bijection into an isomorphism of complete graphs, and
`Nat.card_perm` counts permutations.)

An automorphism of `⊤` is determined by its underlying permutation, and conversely
every permutation `σ` preserves adjacency (`σ a ≠ σ b ↔ a ≠ b`), which is
`Iso.completeGraph σ`. The inverse laws (filled in automatically) and
multiplicativity hold by `rfl`.
-/
/-- The automorphism group of a complete graph is the symmetric group. -/
def autTopMulEquivPerm (V : Type*) :
    ((⊤ : SimpleGraph V) ≃g (⊤ : SimpleGraph V)) ≃* Equiv.Perm V where
  toFun e := e.toEquiv
  invFun σ := Iso.completeGraph σ
  map_mul' _ _ := rfl

lemma card_aut_completeGraph (n : ℕ) : Nat.card (K[n] ≃g K[n]) = n.factorial := by
  rw [Nat.card_congr (autTopMulEquivPerm (Fin n)).toEquiv, Nat.card_perm,
    Nat.card_fin]

/-!
3. Show that a graph and its complement have the same automorphisms. (Hint: for the
inverse map, treat the pairs of vertices `a = b` and `a ≠ b` separately.)

An automorphism `e` of `G` preserves non-adjacency of distinct vertices, so `simp`
shows that it is an automorphism of `Gᶜ`. Conversely, if `e` is an automorphism of
`Gᶜ` then for `a ≠ b` (so `e a ≠ e b`) the two complement adjacencies agree, and
negating gives the adjacencies in `G`; for `a = b` both sides are false.
-/
/-- A graph and its complement have the same automorphisms. -/
def autComplMulEquiv (G : SimpleGraph V) : (G ≃g G) ≃* (Gᶜ ≃g Gᶜ) where
  toFun e := ⟨e.toEquiv, by simp [e.map_adj_iff]⟩
  invFun e := ⟨e.toEquiv, fun {a b} => by
    have h := e.map_adj_iff (v := a) (w := b)
    by_cases hab : a = b
    · subst hab; simp
    · have hab' : e a ≠ e b := e.injective.ne hab
      rw [← not_iff_not]
      simpa [compl_adj, hab, hab'] using h⟩
  map_mul' _ _ := rfl

/-!
4. Show that every vertex of a vertex-transitive graph with an odd number of vertices
has even degree. (Hint: such a graph is regular by
`IsVertexTransitive.exists_isRegularOfDegree`; now use the handshake lemma in the
form `sum_degrees_eq_twice_card_edges'` of
[The Handshake Lemma](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-the-handshake-lemma).)

If `G` is `d`-regular then the handshake lemma says that `|V| * d` is twice the
number of edges, hence even, and since `|V|` is odd `d` must be even.
-/
lemma even_degree_of_isVertexTransitive [Fintype V] [G.LocallyFinite]
    (h : G.IsVertexTransitive) (hodd : Odd (Fintype.card V)) (v : V) :
    Even (G.degree v) := by
  classical
  obtain ⟨d, hd⟩ := IsVertexTransitive.exists_isRegularOfDegree h
  have hsum := G.sum_degrees_eq_twice_card_edges'
  rw [Finset.sum_congr rfl fun v _ => hd v, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hsum
  rw [hd v]
  exact (Nat.even_mul.1 ⟨_, hsum.trans (two_mul _)⟩).resolve_left
    (Nat.not_even_iff_odd.2 hodd)

/-!
5. Show that the Kneser graph `Kn[n, k]` is vertex-transitive, and deduce that so is
the Petersen graph. Hint: a permutation `σ` of `Fin n` gives an automorphism
`x ↦ x.map σ`. Given two `k`-subsets `s` and `t`, glue a bijection between `s` and
`t` to one between their complements, using `Fintype.equivOfCardEq` and
`Equiv.subtypeCongr`, to get a permutation sending `s` onto `t`.
-/
lemma isVertexTransitive_kneserGraph (n k : ℕ) : Kn[n, k].IsVertexTransitive := by
  classical
  -- a permutation `σ` of `Fin n` gives the automorphism `x ↦ x.map σ`
  let aut (σ : Equiv.Perm (Fin n)) : Kn[n, k] ≃g Kn[n, k] :=
    { toFun x := ⟨x.val.map σ.toEmbedding, by simpa using x.prop⟩
      invFun x := ⟨x.val.map σ.symm.toEmbedding, by simpa using x.prop⟩
      left_inv x := by ext; simp
      right_inv x := by ext; simp
      map_rel_iff' := by intro x y; simp [Finset.disjoint_map, Subtype.ext_iff] }
  intro s t
  -- glue bijections `s ≃ t` and `sᶜ ≃ tᶜ` into a permutation sending `s` onto `t`
  have hs : Fintype.card {x // x ∈ s.val} = Fintype.card {x // x ∈ t.val} := by
    simp [s.prop, t.prop]
  have hc : Fintype.card {x // x ∉ s.val} = Fintype.card {x // x ∉ t.val} := by
    simp [Fintype.card_subtype_compl, s.prop, t.prop]
  let σ : Equiv.Perm (Fin n) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq hs) (Fintype.equivOfCardEq hc)
  refine ⟨aut σ, Subtype.ext ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    have h : σ x = ((Fintype.equivOfCardEq hs) ⟨x, hx⟩ : Fin n) := by
      simp [σ, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]
    simp [h]
  · simp [aut, s.prop, t.prop]

example : petersenGraph.IsVertexTransitive := isVertexTransitive_kneserGraph 5 2

/-!
6. Show that the cycle `C[n + 3]` has `2 * (n + 3)` automorphisms. (Hint: use
`autCycleGraphMulEquivDihedral` and `DihedralGroup.nat_card`.)
-/
/-- The cycle `C[n + 3]` has `2 * (n + 3)` automorphisms. -/
lemma card_aut_cycleGraph (n : ℕ) :
    Nat.card (C[n + 3] ≃g C[n + 3]) = 2 * (n + 3) := by
  rw [Nat.card_congr (autCycleGraphMulEquivDihedral n).toEquiv,
    DihedralGroup.nat_card]

/-!
7. Show that the trace of the square of the adjacency matrix of a finite graph is
twice the number of edges.
-/
open Finset in
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (G.adjMatrix ℕ ^ 2).trace = 2 * #G.edgeFinset := by
  simp_rw [Matrix.trace, Matrix.diag, sq, adjMatrix_mul_self_apply_self,
    Nat.cast_id]
  exact sum_degrees_eq_twice_card_edges G

/-!
8. The vector `mycielskianLift t x` again has entries summing to zero, so the
construction can be repeated. Show this, and deduce that the Grötzsch graph
`grotzschGraph`, i.e. `mμ[C[5]]`, has eigenvalues `1`, `-φ ^ 2` and `-ψ ^ 2`. (Hint:
`grotzschGraph` is isomorphic to `mμ[mμ[K[2]]]`, by `Iso.mapMycielskian` applied to
`mycielskianCompleteTwoIsoCycleFive`.)
-/
lemma sum_mycielskianLift [Fintype V] {R : Type*} [CommRing R] (t : R)
    {x : V → R} (hsum : ∑ v, x v = 0) : ∑ w, mycielskianLift t x w = 0 := by
  simp [Fintype.sum_option, Fintype.sum_sum_type, ← Finset.mul_sum, hsum]

/-!
Lifting the eigenvector `![1, -1]` of `K[2]` twice, first with `s` and then with `φ`
or `ψ`, gives the eigenvalues `φ * (s * -1)` and `ψ * (s * -1)` of `mμ[mμ[K[2]]]`,
for `s = φ` and `s = ψ`. Since `φ * ψ = -1`, these are `-φ ^ 2`, `1` and `-ψ ^ 2`.
-/
open Matrix in
open scoped goldenRatio in
example : 1 ∈ spectrum ℝ (grotzschGraph.adjMatrix ℝ) ∧
    -φ ^ 2 ∈ spectrum ℝ (grotzschGraph.adjMatrix ℝ) ∧
    -ψ ^ 2 ∈ spectrum ℝ (grotzschGraph.adjMatrix ℝ) := by
  have hK : K[2].adjMatrix ℝ *ᵥ ![1, -1] = (-1 : ℝ) • ![1, -1] := by
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, adjMatrix_apply]
  have hx0 : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by simp
  have hsum : ∑ i, (![1, -1] : Fin 2 → ℝ) i = 0 := by simp
  have h (s : ℝ) (hs : s ^ 2 = s + 1) :
      φ * (s * -1) ∈ spectrum ℝ (mμ[mμ[K[2]]].adjMatrix ℝ) ∧
        ψ * (s * -1) ∈ spectrum ℝ (mμ[mμ[K[2]]].adjMatrix ℝ) :=
    mem_spectrum_adjMatrix_mycielskian (mycielskianLift_ne_zero s hx0)
      (adjMatrix_mycielskian_mulVec_mycielskianLift hs hK hsum)
      (sum_mycielskianLift s hsum)
  rw [mycielskianCompleteTwoIsoCycleFive.symm.mapMycielskian.spectrum_adjMatrix]
  obtain ⟨h₁, h₂⟩ := h φ Real.goldenRatio_sq
  obtain ⟨h₃, h₄⟩ := h ψ Real.goldenConj_sq
  refine ⟨?_, ?_, ?_⟩
  · norm_num at h₃
    exact h₃
  · convert h₁
    ring
  · convert h₄
    ring

/-!
9. Show that the entries in each row of the Laplacian sum to `0`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (i : V) :
    ∑ j, G.lapMatrix ℤ i j = 0 := by
  simpa [Matrix.mulVec, dotProduct] using
    congr_fun (G.lapMatrix_mulVec_one_eq_zero ℤ) i

/-!
10. Show that if `G` has no isolated vertices, then the kernel of the Laplacian of
the Mycielskian `mμ[G]` is `1`-dimensional.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : ∀ v, ¬ G.IsIsolated v) :
    Module.finrank ℝ (mμ[G].lapMatrix ℝ).toLin'.ker = 1 := by
  rw [← card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix,
    Fintype.card_eq_nat_card]
  exact (connected_mycielskian_iff.2 h).card_connectedComponent

/-!
11. Show that `C[5]` is strongly regular with parameters `(5, 2, 0, 1)`, and deduce
that its diameter is `2`.
-/
example : C[5].IsSRGWith 5 2 0 1 ∧ C[5].ediam = 2 := by
  have h : C[5].IsSRGWith 5 2 0 1 :=
    { card := by decide
      regular := by intro v; decide +revert
      of_adj := by decide
      of_not_adj := by unfold Pairwise; decide }
  refine ⟨h, h.ediam_eq_two (fun h' => ?_) one_ne_zero⟩
  have hne : ¬ C[5].Adj 0 2 := by decide
  exact hne (by rw [h', top_adj]; decide)

/-!
12. Show that there is no strongly regular graph with parameters `(10, 4, 0, 1)`.
-/
example {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ G.IsSRGWith 10 4 0 1 := fun h => by
  have := h.param_eq G (by norm_num)
  norm_num at this

/-!
13. Show that the Hamming cube is isomorphic to the third construction of the
hypercube, the Hasse diagram `hypercubeHasse` of the subsets of `Fin n`, by sending a
vertex `x` to the set of coordinates `i` with `x i = true`. (Hint: adding the basis
vector `e i` to `x` removes `i` from this set if it is there, and inserts it
otherwise. Use `hypercubeHamming_adj_iff_exists`, `hasse_adj`,
`Finset.covBy_iff_exists_insert`, `Finset.covBy_insert` and `Finset.erase_covBy`.)

We first give the bijection and compute the effect of adding a basis vector.
-/
/-- Bool vectors of length `n` correspond to subsets of `Fin n`. -/
def boolVecEquivFinset (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun x := {i | x i = true}
  invFun s i := decide (i ∈ s)
  left_inv x := by ext i; simp
  right_inv s := by ext i; simp

open scoped hypercubeHamming in
lemma boolVecEquivFinset_add_single {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    boolVecEquivFinset n (x + e i) =
      if x i = true then (boolVecEquivFinset n x).erase i
      else insert i (boolVecEquivFinset n x) := by
  ext j
  by_cases hj : j = i <;> split_ifs <;>
    simp_all [boolVecEquivFinset, Bool.add_eq_xor, Bool.zero_eq_false]

/-!
If the set of `x` is covered by the set of `y`, then `y` is `x` with one more
coordinate set to `true`, so `x` and `y` are adjacent. Conversely, adding a basis
vector either inserts or erases an element, giving a covering relation in one
direction or the other.
-/
lemma hypercubeHamming_adj_of_covBy {n : ℕ} {x y : Fin n → Bool}
    (h : boolVecEquivFinset n x ⋖ boolVecEquivFinset n y) :
    (hypercubeHamming n).Adj x y := by
  obtain ⟨a, ha, hS⟩ := Finset.covBy_iff_exists_insert.1 h
  have hxa : x a = false := by simpa [boolVecEquivFinset] using ha
  refine hypercubeHamming_adj_iff_exists.2 ⟨a, (boolVecEquivFinset n).injective ?_⟩
  rw [boolVecEquivFinset_add_single, hxa]
  simpa using hS.symm

/-- The Hamming cube is isomorphic to the Hasse diagram of the subsets of
`Fin n`. -/
def hypercubeHammingIsoHasse (n : ℕ) : hypercubeHamming n ≃g hypercubeHasse n where
  toEquiv := boolVecEquivFinset n
  map_rel_iff' {x y} := by
    rw [hasse_adj]
    refine ⟨fun h => h.elim hypercubeHamming_adj_of_covBy
      fun h => (hypercubeHamming_adj_of_covBy h).symm, fun h => ?_⟩
    obtain ⟨i, rfl⟩ := hypercubeHamming_adj_iff_exists.1 h
    rw [boolVecEquivFinset_add_single]
    split_ifs with hi
    · exact .inr (Finset.erase_covBy (by simpa [boolVecEquivFinset] using hi))
    · exact .inl (Finset.covBy_insert (by simpa [boolVecEquivFinset] using hi))

/-!
14. Show that the hypercube is *arc-transitive*: for any two edges `x — y` and
`u — v` there is an automorphism sending `x` to `u` and `y` to `v`. (Hint: if
`y = x + e i` and `v = u + e j`, compose a translation, the coordinate permutation
`Equiv.swap i j` and another translation.)

Translating by `x` sends `x` to `0` and `y = x + eᵢ` to `eᵢ`; swapping the
coordinates `i` and `j` fixes `0` and sends `eᵢ` to `eⱼ`; and translating by `u`
sends `0` to `u` and `eⱼ` to `v`.
-/
open scoped hypercubeHamming in
lemma exists_aut_hypercubeHamming_of_adj {n : ℕ} {x y u v : Fin n → Bool}
    (h : (hypercubeHamming n).Adj x y) (h' : (hypercubeHamming n).Adj u v) :
    ∃ g : hypercubeHamming n ≃g hypercubeHamming n, g x = u ∧ g y = v := by
  obtain ⟨i, rfl⟩ := hypercubeHamming_adj_iff_exists.1 h
  obtain ⟨j, rfl⟩ := hypercubeHamming_adj_iff_exists.1 h'
  refine ⟨(hypercubeHamming.translate x).trans
    ((hypercubeHamming.permute (Equiv.swap i j)).trans
      (hypercubeHamming.translate u)), ?_, ?_⟩
  · simp [BooleanRing.add_self]
  · have : (e i : Fin n → Bool) ∘ Equiv.swap i j = e j := by
      simpa using Pi.single_comp_equiv (Equiv.swap i j) i true
    simp [this]

/-!
15. Show that the copies of any graph `A` in a complete graph are just the injective
maps between the vertex types. Deduce that `K[n]` contains
`n.descFactorial (k + 3) = n * (n - 1) * ⋯ * (n - k - 2)` labelled copies of
`C[k + 3]`. (Hint: `Fintype.card_embedding_eq`.)

Adjacency in `⊤` is `≠`, so an injective map sends adjacent vertices (which are
distinct) to adjacent vertices: every injective map is a copy.
-/
/-- Copies of `A` in a complete graph are the injective maps of vertices. -/
def copyTopEquiv {W : Type*} (A : SimpleGraph V) :
    Copy A (⊤ : SimpleGraph W) ≃ (V ↪ W) where
  toFun f := f.toEmbedding
  invFun f := ⟨⟨f, fun hab => f.injective.ne hab.ne⟩, f.injective⟩

lemma labelledCopyCount_completeGraph_cycleGraph (n k : ℕ) :
    K[n].labelledCopyCount C[k + 3] = n.descFactorial (k + 3) := by
  rw [labelledCopyCount, Fintype.card_eq_nat_card, Nat.card_congr (copyTopEquiv _),
    Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp

/-!
16. Deduce that `K[n + 3]` contains `(n + 3)! / (2 * (n + 3))` Hamiltonian cycles,
i.e. unlabelled copies of `C[n + 3]`. (Hint: `labelledCopyCount_cycleGraph`.)
-/
lemma copyCount_completeGraph_cycleGraph (n : ℕ) :
    2 * (n + 3) * K[n + 3].copyCount C[n + 3] = (n + 3).factorial := by
  have h := labelledCopyCount_cycleGraph K[n + 3] n
  rw [labelledCopyCount_completeGraph_cycleGraph, Nat.descFactorial_self] at h
  rw [h, mul_comm]

/-!
17. Count the `4`-cycles in the hypercube: show that `Q[n]` contains
`2 ^ n * (n * (n - 1))` labelled copies of `C[4]` and, for `2 ≤ n`,
`n.choose 2 * 2 ^ (n - 2)` unlabelled ones. (Hint: transport
`labelledCopyCount_hypercube` and `copyCount_hypercube` along the isomorphism
`hypercubeTwoIsoCycleFour : Q[2] ≃g C[4]`, using `Iso.labelledCopyCount_eq` and
`Iso.copyCount_eq_left`.)

The labelled count is `labelledCopyCount_hypercube n 2`, since
`n.descFactorial 2 = n * (n - 1)`, and the unlabelled count is
`copyCount_hypercube n 2`.
-/
lemma labelledCopyCount_hypercube_cycleGraph_four (n : ℕ) :
    Q[n].labelledCopyCount C[4] = 2 ^ n * (n * (n - 1)) := by
  rw [← hypercubeTwoIsoCycleFour.labelledCopyCount_eq .refl,
    labelledCopyCount_hypercube]
  simp [Nat.descFactorial, mul_comm]

lemma copyCount_hypercube_cycleGraph_four (n : ℕ) (hn : 2 ≤ n) :
    Q[n].copyCount C[4] = n.choose 2 * 2 ^ (n - 2) := by
  rw [← hypercubeTwoIsoCycleFour.copyCount_eq_left Q[n], copyCount_hypercube n 2 hn]

/-!
18. Show that `C[5]` has `10` labelled copies in itself, using Exercise 6.
-/
lemma labelledCopyCount_cycleGraph_five_self :
    C[5].labelledCopyCount C[5] = 10 := by
  rw [labelledCopyCount, Fintype.card_eq_nat_card, Nat.card_congr (copyEquivAut _),
    card_aut_cycleGraph 2]

/-! END SOLUTIONS -/

end SimpleGraph
