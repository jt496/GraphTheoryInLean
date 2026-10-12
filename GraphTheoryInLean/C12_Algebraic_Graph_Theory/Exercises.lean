import GraphTheoryInLean.C12_Algebraic_Graph_Theory.C12_Algebraic_Graph_Theory
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
/-!
# Exercises
1. Let `M` be a group, prove that for any `s : Set M` the Cayley graph
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
has even degree. (Hint: such a graph is regular by `isRegular_of_isVertexTransitive`;
now use the handshake lemma in the form `sum_degrees_eq_twice_card_edges'` of
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
7. Show that the trace of the square of the adjacency matrix is twice the number of
edges.
-/
open Finset in
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (G.adjMatrix ℕ ^ 2).trace = 2 * #G.edgeFinset := by
  sorry

/-!
8. Show that the entries in each row of the Laplacian sum to `0`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (i : V) :
    ∑ j, G.lapMatrix ℤ i j = 0 := by
  sorry

/-!
9. Show that if `G` has no isolated vertices, then the kernel of the Laplacian of
the Mycielskian `mμ[G]` is `1`-dimensional.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : ∀ v, ¬ G.IsIsolated v) :
    Module.finrank ℝ (mμ[G].lapMatrix ℝ).toLin'.ker = 1 := by
  sorry

/-!
10. Show that `C[5]` is strongly regular with parameters `(5, 2, 0, 1)`, and deduce
that its diameter is `2`.
-/
example : C[5].IsSRGWith 5 2 0 1 ∧ C[5].ediam = 2 := by
  sorry

/-!
11. Show that there is no strongly regular graph with parameters `(10, 4, 0, 1)`.
-/
example {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ G.IsSRGWith 10 4 0 1 := by
  sorry

/-!
12. Show that the Hamming graph is isomorphic to the third construction of the
hypercube from
[Hypercube](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-hypercube),
the Hasse diagram `hypercubeHasse n` of the subsets of `Fin n`, by sending a vertex
`x` to the set of coordinates `i` with `x i = true`. (Hint: adding `Pi.single i true`
to `x` removes `i` from this set if it is there, and inserts it otherwise. Use
`hypercubeHamming_adj_iff_exists`, `hasse_adj`, `Finset.covBy_iff_exists_insert`,
`Finset.covBy_insert` and `Finset.erase_covBy`.)
-/
def hypercubeHammingIsoHasse' (n : ℕ) : hypercubeHamming n ≃g hypercubeHasse n :=
  sorry

/-!
13. Show that the hypercube is *arc-transitive*: for any two edges `x — y` and
`x' — y'` there is an automorphism sending `x` to `x'` and `y` to `y'`. (Hint: if
`y = x + Pi.single i true` and `y' = x' + Pi.single j true`, compose a translation,
the coordinate permutation `Equiv.swap i j` and another translation.)
-/
lemma exists_aut_hypercubeHamming_of_adj' {n : ℕ} {x y x' y' : Fin n → Bool}
    (h : (hypercubeHamming n).Adj x y) (h' : (hypercubeHamming n).Adj x' y') :
    ∃ g : hypercubeHamming n ≃g hypercubeHamming n, g x = x' ∧ g y = y' := by
  sorry

/-!
14. Show that the copies of any graph `A` in a complete graph are just the injective
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
15. Deduce that `K[n + 3]` contains `(n + 3)! / (2 * (n + 3))` Hamiltonian cycles,
i.e. unlabelled copies of `C[n + 3]`. (Hint: `labelledCopyCount_cycleGraph`.)
-/
lemma copyCount_completeGraph_cycleGraph' (n : ℕ) :
    2 * (n + 3) * K[n + 3].copyCount C[n + 3] = (n + 3).factorial := by
  sorry

/-!
16. Count the 4-cycles in the hypercube: show that `Q[n]` contains
`2 ^ n * (n * (n - 1))` labelled copies of `C[4]` and, for `2 ≤ n`,
`n.choose 2 * 2 ^ (n - 2)` unlabelled ones. (Hint: transport
`labelledCopyCount_hypercube` and `copyCount_hypercube` along the isomorphism
`hypercubeTwoIsoCycleFour : Q[2] ≃g C[4]` of
[Exercises](https://jt496.github.io/GraphTheoryInLean/Maps/#section-exercises-maps),
using `Iso.labelledCopyCount_eq` and `Iso.copyCount_eq_left`.)
-/
lemma labelledCopyCount_hypercube_cycleGraph_four' (n : ℕ) :
    Q[n].labelledCopyCount C[4] = 2 ^ n * (n * (n - 1)) := by
  sorry

lemma copyCount_hypercube_cycleGraph_four' (n : ℕ) (hn : 2 ≤ n) :
    Q[n].copyCount C[4] = n.choose 2 * 2 ^ (n - 2) := by
  sorry

/-!
17. Since `mμ[K[2]]` is a 5-cycle, it contains as many labelled copies of `C[5]` as
`C[5]` has automorphisms. Check that the two counts agree: show that `C[5]` has `10`
labelled copies in itself, using exercise 6, and that `mμ[K[2]]` has `10` labelled
copies of `C[5]`, using `labelledCopyCount_mycielskian_cycleGraph_five`. (Hint: for
the second part, `cliqueFree_of_card_lt` shows that `K[2]` is triangle-free, and
`decide` can evaluate the final sum.)
-/
lemma labelledCopyCount_cycleGraph_five_self' :
    C[5].labelledCopyCount C[5] = 10 := by
  sorry

lemma labelledCopyCount_mycielskian_completeGraph_two' :
    mμ[K[2]].labelledCopyCount C[5] = 10 := by
  sorry

/-!
The remaining exercises form a longer, more advanced project. Exercises 19–30 prove
an *edge-isoperimetric inequality* for the hypercube: a set `A` of `2 ^ k` vertices
of `Q[n]` spans at most `k * 2 ^ (k - 1)` edges. Exercises 31 and 32 show that this
is best possible: a `k`-dimensional subcube (as in
[Counting Copies of Subcubes*](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-counting-copies-of-subcubes))
achieves it, so among all sets of this size subcubes span the most edges
(equivalently, they have the smallest edge-boundary).

To count edges we use `SimpleGraph.interedges` from Mathlib: `G.interedges s t`
is the `Finset` of *ordered* pairs `(u, v) ∈ s ×ˢ t` with `G.Adj u v`. Thus
`#(G.interedges A A)` counts every edge inside `A` twice, and our goal is the
bound `#(Q[n].interedges A A) ≤ k * 2 ^ k`. (We `open Finset` for the `#` and
`×ˢ` notation and the many `Finset` lemmas we will need.)

The proof is by induction on `n` using `Q[n + 1] = Q[n] □ K₂`, splitting `A`
over the two copies of `Q[n]`. Since the two halves of `A` need not be powers
of two, the bound `k * 2 ^ k` is not general enough for the induction to
close. Instead we prove the multiplicative form

`2 ^ #(Q[n].interedges A A) ≤ #A ^ #A`

which is the classical bound `e(A) ≤ ½ * |A| * log₂ |A|` with the logarithms
cleared away, so that everything stays in `ℕ`. All the intermediate steps are
stated for the *prism* `G □ (⊤ : SimpleGraph Bool)` over an arbitrary graph
`G`, and are put together for the hypercube result at the very end.
-/
open Finset

/-!
18. Show that the Mycielskian of the hypercube contains `n ^ 3 * 2 ^ (n - 1)`
5-cycles, by proving that `2 * mμ[Q[n]].copyCount C[5] = n ^ 3 * 2 ^ n`. Hint: `Q[n]`
is triangle-free, and has no 5-cycles since it is bipartite, so
`copyCount_mycielskian_cycleGraph_five` applies.
-/
example (n : ℕ) : 2 * mμ[Q[n]].copyCount C[5] = n ^ 3 * 2 ^ n := by
  sorry

/-!
19. Show that any finset of `α × Bool` splits as the union of a *bottom part*
`A₀ ×ˢ {false}` and a *top part* `A₁ ×ˢ {true}`.
-/
lemma exists_bool_split' {α : Type*} [DecidableEq α] (A : Finset (α × Bool)) :
    ∃ A₀ A₁ : Finset α, A = A₀ ×ˢ {false} ∪ A₁ ×ˢ {true} := by
  sorry

/-!
20. Show that bottom and top parts are disjoint, and deduce that the size of a
bottom/top split is the sum of the sizes of its parts.
-/
lemma disjoint_bool_split' {α : Type*} (A₀ A₁ : Finset α) :
    Disjoint (A₀ ×ˢ ({false} : Finset Bool)) (A₁ ×ˢ {true}) := by
  sorry

lemma card_bool_split' {α : Type*} [DecidableEq α] (A₀ A₁ : Finset α) :
    #(A₀ ×ˢ {false} ∪ A₁ ×ˢ {true}) = #A₀ + #A₁ := by
  sorry

/-!
21. Show that `interedges` distributes over unions in either argument.
-/
lemma interedges_union_left' [DecidableEq V] [DecidableRel G.Adj]
    (s₁ s₂ t : Finset V) :
    G.interedges (s₁ ∪ s₂) t = G.interedges s₁ t ∪ G.interedges s₂ t := by
  sorry

lemma interedges_union_right' [DecidableEq V] [DecidableRel G.Adj]
    (s t₁ t₂ : Finset V) :
    G.interedges s (t₁ ∪ t₂) = G.interedges s t₁ ∪ G.interedges s t₂ := by
  sorry

/-!
22. In the prism `G □ K₂` (written `G □ ⊤` with `⊤ : SimpleGraph Bool`) the
vertex `(u, b)` is adjacent to `(w, c)` with `b ≠ c` iff `u = w`, so the edges
between opposite copies of two vertex sets `A₀` and `A₁` form a perfect
matching on `A₀ ∩ A₁`. Prove the resulting count. (Hint: show that the edge
set is the image of `A₀ ∩ A₁` under an injective map.)
-/
lemma card_interedges_bool_ne' [DecidableRel G.Adj] [DecidableEq V] {b c : Bool}
    (hbc : b ≠ c) (A₀ A₁ : Finset V) :
    #((G □ ⊤).interedges (A₀ ×ˢ {b}) (A₁ ×ˢ {c})) = #(A₀ ∩ A₁) := by
  sorry

/-!
23. Show similarly that the edges of the prism within one of the two copies of
`G` correspond to edges of `G` itself.
-/
lemma card_interedges_bool_eq' [DecidableRel G.Adj] [DecidableEq V] (b : Bool)
    (A₀ A₁ : Finset V) :
    #((G □ ⊤).interedges (A₀ ×ˢ {b}) (A₁ ×ˢ {b})) = #(G.interedges A₀ A₁) := by
  sorry

/-!
24. Put exercises 21–23 together: the ordered edge count of a bottom/top split
decomposes into the counts of the two parts plus one matching edge for each
common vertex, in each direction. (Hint: `interedges_disjoint_left` and
`interedges_disjoint_right` provide the disjointness needed to add up the
cards.)
-/
lemma card_interedges_bool_split' [DecidableRel G.Adj] [DecidableEq V]
    (A₀ A₁ : Finset V) :
    #((G □ ⊤).interedges (A₀ ×ˢ {false} ∪ A₁ ×ˢ {true})
        (A₀ ×ˢ {false} ∪ A₁ ×ˢ {true}))
      = #(G.interedges A₀ A₀) + #(G.interedges A₁ A₁) + 2 * #(A₀ ∩ A₁) := by
  sorry

/-!
25. We now turn to the arithmetic. Prove the key binomial estimate: if `a ≤ b`
then `a.choose i * b ^ i ≤ b.choose i * a ^ i`. (Hint: multiplying both sides
by `i !` turns the binomial coefficients into descending factorials
`a * (a - 1) * ⋯ * (a - i + 1)`, by `Nat.descFactorial_eq_factorial_mul_choose`
and `Nat.descFactorial_eq_prod_range`, and the two sides can then be compared
factor by factor: `(a - j) * b ≤ (b - j) * a`.)
-/
lemma choose_mul_pow_le' {a b : ℕ} (i : ℕ) (hab : a ≤ b) :
    a.choose i * b ^ i ≤ b.choose i * a ^ i := by
  sorry

/-!
26. Deduce that for `a ≤ b` we have `2 ^ a * b ^ b ≤ (a + b) ^ b`. This is the
concavity-style estimate `a ≤ b * log₂ (1 + a / b)` in disguise, and it is the
heart of the isoperimetric inequality. (Hint: expand `(a + b) ^ b` with the
binomial theorem `add_pow`, write `2 ^ a = ∑ i ∈ range (a + 1), a.choose i`
using `Nat.sum_range_choose`, and compare the sums term by term using the
previous exercise.)
-/
lemma two_pow_mul_pow_le' {a b : ℕ} (hab : a ≤ b) :
    2 ^ a * b ^ b ≤ (a + b) ^ b := by
  sorry

/-!
27. Combine the previous exercise with some elementary estimates to obtain the
arithmetic form of the inductive step. (Hint: reduce to the case `a ≤ b`, and
in that case bound `2 ^ (x + y + 2 * c)` by `(2 * a) ^ a * (2 ^ a * b ^ b)`.)
-/
lemma two_pow_le_add_pow' {a b c x y : ℕ} (hca : c ≤ a) (hcb : c ≤ b)
    (hx : 2 ^ x ≤ a ^ a) (hy : 2 ^ y ≤ b ^ b) :
    2 ^ (x + y + 2 * c) ≤ (a + b) ^ (a + b) := by
  sorry

/-!
28. Prove the inductive step: if the multiplicative bound holds for all vertex
sets of `G` then it holds for all vertex sets of the prism `G □ K₂`. (Hint:
split `A` using exercise 19 and put exercises 20, 24 and 27 together.)
-/
lemma boxProdTop_two_pow_card_interedges_le' [DecidableRel G.Adj]
    [DecidableEq V] (hG : ∀ B : Finset V, 2 ^ #(G.interedges B B) ≤ #B ^ #B)
    (A : Finset (V × Bool)) :
    2 ^ #((G □ ⊤).interedges A A) ≤ #A ^ #A := by
  sorry

/-!
29. Prove the multiplicative edge-isoperimetric inequality for the hypercube
by induction on `n`. (Hint: for the inductive step recall that `Q[n + 1]` is
*definitionally* `Q[n] □ ⊤`, so the previous exercise applies to it —
`exact` will happily cross this definitional equality.)
-/
lemma two_pow_card_interedges_le' {n : ℕ} : ∀ A : Finset (HypercubeVert n),
    2 ^ #(Q[n].interedges A A) ≤ #A ^ #A := by
  sorry

/-!
30. Deduce the edge-isoperimetric inequality: a set of `2 ^ k` vertices of the
hypercube spans at most `k * 2 ^ (k - 1)` edges, i.e. at most `k * 2 ^ k`
ordered adjacent pairs. (Hint: compare exponents of `2` using
`Nat.pow_le_pow_iff_right`.)
-/
theorem card_interedges_le_of_card_eq_two_pow' {n k : ℕ}
    {A : Finset (HypercubeVert n)} (hA : #A = 2 ^ k) :
    #(Q[n].interedges A A) ≤ k * 2 ^ k := by
  sorry

/-!
31. Show that a graph embedding `f : G ↪g H` preserves the number of ordered
adjacent pairs inside a set, and that the whole vertex set of a finite graph
spans `∑ v, G.degree v` ordered adjacent pairs. (Hint: for the first part, show
that `f.toEmbedding.prodMap f.toEmbedding` maps `G.interedges s t` onto the
ordered adjacent pairs of `s.map f.toEmbedding` and `t.map f.toEmbedding`.)
-/
lemma card_interedges_map' {W : Type*} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (f : G ↪g H) (s t : Finset V) :
    #(H.interedges (s.map f.toEmbedding) (t.map f.toEmbedding)) =
      #(G.interedges s t) := by
  sorry

lemma card_interedges_univ' [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] :
    #(G.interedges univ univ) = ∑ v, G.degree v := by
  sorry

/-!
32. Deduce that the bound of exercise 30 is attained: the copy of `Q[k]` inside
`Q[k + m]` given by the embedding `hypercubeEmbedding k m` of
[Exercises](https://jt496.github.io/GraphTheoryInLean/Maps/#section-exercises-maps)
is a set of `2 ^ k` vertices spanning exactly `k * 2 ^ k` ordered adjacent pairs.
-/
theorem exists_card_interedges_eq' (k m : ℕ) :
    ∃ A : Finset (HypercubeVert (k + m)), #A = 2 ^ k ∧
      #(Q[k + m].interedges A A) = k * 2 ^ k := by
  sorry

/-! SOLUTIONS -/

/-!
1. Let `M` be a group, prove that for any `s : Set M` the Cayley graph
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
-/
/-!
An automorphism of `⊤` is determined by its underlying permutation, and conversely
every permutation `σ` preserves adjacency (`σ a ≠ σ b ↔ a ≠ b`), which is
`Iso.completeGraph σ`. Both maps, and multiplicativity, hold by `rfl`.
-/
/-- The automorphism group of a complete graph is the symmetric group. -/
def autTopMulEquivPerm (V : Type*) :
    ((⊤ : SimpleGraph V) ≃g (⊤ : SimpleGraph V)) ≃* Equiv.Perm V where
  toFun e := e.toEquiv
  invFun σ := Iso.completeGraph σ
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

lemma card_aut_completeGraph (n : ℕ) : Nat.card (K[n] ≃g K[n]) = n.factorial := by
  rw [Nat.card_congr (autTopMulEquivPerm (Fin n)).toEquiv, Nat.card_perm,
    Nat.card_fin]

/-!
3. Show that a graph and its complement have the same automorphisms. (Hint: for the
inverse map, treat the pairs of vertices `a = b` and `a ≠ b` separately.)
-/
/-!
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
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-!
4. Show that every vertex of a vertex-transitive graph with an odd number of vertices
has even degree. (Hint: such a graph is regular by `isRegular_of_isVertexTransitive`;
now use the handshake lemma in the form `sum_degrees_eq_twice_card_edges'` of
[The Handshake Lemma](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-the-handshake-lemma).)
-/
/-!
If `G` is `d`-regular then the handshake lemma says that `|V| * d` is twice the
number of edges, hence even, and since `|V|` is odd `d` must be even.
-/
lemma even_degree_of_isVertexTransitive [Fintype V] [G.LocallyFinite]
    (h : G.IsVertexTransitive) (hodd : Odd (Fintype.card V)) (v : V) :
    Even (G.degree v) := by
  classical
  obtain ⟨d, hd⟩ := isRegular_of_isVertexTransitive h
  have hsum := G.sum_degrees_eq_twice_card_edges'
  rw [Finset.sum_congr rfl fun v _ => hd v, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hsum
  rw [hd v]
  exact (Nat.even_mul.1 ⟨_, hsum.trans (two_mul _)⟩).resolve_left
    (Nat.not_even_iff_odd.2 hodd)

/-!
5. Show that the Kneser graph `Kn[n, k]` is vertex-transitive, and deduce that so is
the Petersen graph.
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
7. Show that the trace of the square of the adjacency matrix is twice the number of
edges.
-/
open Finset in
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (G.adjMatrix ℕ ^ 2).trace = 2 * #G.edgeFinset := by
  simp only [Matrix.trace, Matrix.diag, sq, adjMatrix_mul_self_apply_self,
    Nat.cast_id]
  exact sum_degrees_eq_twice_card_edges G

/-!
8. Show that the entries in each row of the Laplacian sum to `0`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (i : V) :
    ∑ j, G.lapMatrix ℤ i j = 0 := by
  simpa [Matrix.mulVec, dotProduct] using
    congr_fun (G.lapMatrix_mulVec_one_eq_zero ℤ) i

/-!
9. Show that if `G` has no isolated vertices, then the kernel of the Laplacian of
the Mycielskian `mμ[G]` is `1`-dimensional.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : ∀ v, ¬ G.IsIsolated v) :
    Module.finrank ℝ (mμ[G].lapMatrix ℝ).toLin'.ker = 1 := by
  rw [← card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  exact (connected_mycielskian_iff.2 h).card_connectedComponent

/-!
10. Show that `C[5]` is strongly regular with parameters `(5, 2, 0, 1)`, and deduce
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
11. Show that there is no strongly regular graph with parameters `(10, 4, 0, 1)`.
-/
example {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ G.IsSRGWith 10 4 0 1 := fun h => by
  have := h.param_eq G (by norm_num)
  norm_num at this

/-!
12. Show that the Hamming graph is isomorphic to the third construction of the
hypercube from
[Hypercube](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-hypercube),
the Hasse diagram `hypercubeHasse n` of the subsets of `Fin n`, by sending a vertex
`x` to the set of coordinates `i` with `x i = true`. (Hint: adding `Pi.single i true`
to `x` removes `i` from this set if it is there, and inserts it otherwise. Use
`hypercubeHamming_adj_iff_exists`, `hasse_adj`, `Finset.covBy_iff_exists_insert`,
`Finset.covBy_insert` and `Finset.erase_covBy`.)
-/
/-!
We first give the bijection and compute the effect of adding a basis vector.
-/
/-- Bool vectors of length `n` correspond to subsets of `Fin n`. -/
def boolVecEquivFinset (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun x := {i | x i = true}
  invFun s i := decide (i ∈ s)
  left_inv x := by ext i; simp
  right_inv s := by ext i; simp

lemma boolVecEquivFinset_add_single {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    boolVecEquivFinset n (x + Pi.single i true) =
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

/-- The Hamming graph is isomorphic to the Hasse diagram of the subsets of
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
13. Show that the hypercube is *arc-transitive*: for any two edges `x — y` and
`x' — y'` there is an automorphism sending `x` to `x'` and `y` to `y'`. (Hint: if
`y = x + Pi.single i true` and `y' = x' + Pi.single j true`, compose a translation,
the coordinate permutation `Equiv.swap i j` and another translation.)
-/
/-!
Translating by `x` sends `x` to `0` and `y = x + eᵢ` to `eᵢ`; swapping the
coordinates `i` and `j` fixes `0` and sends `eᵢ` to `eⱼ`; and translating by `x'`
sends `0` to `x'` and `eⱼ` to `y'`.
-/
lemma exists_aut_hypercubeHamming_of_adj {n : ℕ} {x y x' y' : Fin n → Bool}
    (h : (hypercubeHamming n).Adj x y) (h' : (hypercubeHamming n).Adj x' y') :
    ∃ g : hypercubeHamming n ≃g hypercubeHamming n, g x = x' ∧ g y = y' := by
  obtain ⟨i, rfl⟩ := hypercubeHamming_adj_iff_exists.1 h
  obtain ⟨j, rfl⟩ := hypercubeHamming_adj_iff_exists.1 h'
  refine ⟨(hammingTranslate x).trans
    ((hammingPermute (Equiv.swap i j)).trans (hammingTranslate x')), ?_, ?_⟩
  · simp
  · have : (Pi.single i true : Fin n → Bool) ∘ Equiv.swap i j =
        Pi.single j true := by
      simpa using Pi.single_comp_equiv (Equiv.swap i j) i true
    simp [this]

/-!
14. Show that the copies of any graph `A` in a complete graph are just the injective
maps between the vertex types. Deduce that `K[n]` contains
`n.descFactorial (k + 3) = n * (n - 1) * ⋯ * (n - k - 2)` labelled copies of
`C[k + 3]`. (Hint: `Fintype.card_embedding_eq`.)
-/
/-!
Adjacency in `⊤` is `≠`, so an injective map sends adjacent vertices (which are
distinct) to adjacent vertices: every injective map is a copy.
-/
/-- Copies of `A` in a complete graph are the injective maps of vertices. -/
def copyTopEquiv {W : Type*} (A : SimpleGraph V) :
    Copy A (⊤ : SimpleGraph W) ≃ (V ↪ W) where
  toFun f := f.toEmbedding
  invFun f := ⟨⟨f, fun hab => f.injective.ne hab.ne⟩, f.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma labelledCopyCount_completeGraph_cycleGraph (n k : ℕ) :
    K[n].labelledCopyCount C[k + 3] = n.descFactorial (k + 3) := by
  rw [labelledCopyCount, Fintype.card_eq_nat_card, Nat.card_congr (copyTopEquiv _),
    Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp

/-!
15. Deduce that `K[n + 3]` contains `(n + 3)! / (2 * (n + 3))` Hamiltonian cycles,
i.e. unlabelled copies of `C[n + 3]`. (Hint: `labelledCopyCount_cycleGraph`.)
-/
lemma copyCount_completeGraph_cycleGraph (n : ℕ) :
    2 * (n + 3) * K[n + 3].copyCount C[n + 3] = (n + 3).factorial := by
  have h := labelledCopyCount_cycleGraph K[n + 3] n
  rw [labelledCopyCount_completeGraph_cycleGraph, Nat.descFactorial_self] at h
  rw [h, mul_comm]

/-!
16. Count the 4-cycles in the hypercube: show that `Q[n]` contains
`2 ^ n * (n * (n - 1))` labelled copies of `C[4]` and, for `2 ≤ n`,
`n.choose 2 * 2 ^ (n - 2)` unlabelled ones. (Hint: transport
`labelledCopyCount_hypercube` and `copyCount_hypercube` along the isomorphism
`hypercubeTwoIsoCycleFour : Q[2] ≃g C[4]` of
[Exercises](https://jt496.github.io/GraphTheoryInLean/Maps/#section-exercises-maps),
using `Iso.labelledCopyCount_eq` and `Iso.copyCount_eq_left`.)
-/
/-!
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
17. Since `mμ[K[2]]` is a 5-cycle, it contains as many labelled copies of `C[5]` as
`C[5]` has automorphisms. Check that the two counts agree: show that `C[5]` has `10`
labelled copies in itself, using exercise 6, and that `mμ[K[2]]` has `10` labelled
copies of `C[5]`, using `labelledCopyCount_mycielskian_cycleGraph_five`. (Hint: for
the second part, `cliqueFree_of_card_lt` shows that `K[2]` is triangle-free, and
`decide` can evaluate the final sum.)
-/
lemma labelledCopyCount_cycleGraph_five_self :
    C[5].labelledCopyCount C[5] = 10 := by
  rw [labelledCopyCount, Fintype.card_eq_nat_card, Nat.card_congr (copyEquivAut _),
    card_aut_cycleGraph 2]

/-!
A copy of `C[5]` in `K[2]` would be an injective map from `Fin 5` to `Fin 2`, so
`K[2]` is `C[5]`-free. In `K[2]` every vertex has degree one, so the double sum is
`2`, and `decide` can compute it.
-/
lemma labelledCopyCount_mycielskian_completeGraph_two :
    mμ[K[2]].labelledCopyCount C[5] = 10 := by
  have h3 : K[2].CliqueFree 3 := cliqueFree_of_card_lt (by simp)
  have h5 : C[5].Free K[2] := fun ⟨f⟩ => by
    simpa using Fintype.card_le_of_injective f f.injective
  rw [labelledCopyCount_mycielskian_cycleGraph_five h3 h5]
  decide

/-!
18. Show that the Mycielskian of the hypercube contains `n ^ 3 * 2 ^ (n - 1)`
5-cycles, by proving that `2 * mμ[Q[n]].copyCount C[5] = n ^ 3 * 2 ^ n`.
-/
example (n : ℕ) : 2 * mμ[Q[n]].copyCount C[5] = n ^ 3 * 2 ^ n := by
  -- `Q[n]` is bipartite, but `C[5]` is not, so `Q[n]` has no 5-cycles
  have h5 : C[5].Free Q[n] := by
    rintro ⟨c⟩
    obtain ⟨col⟩ := hypercube_isBipartite n
    have h : C[5].Colorable 2 := ⟨col.comp c.toHom⟩
    rw [← chromaticNumber_le_iff_colorable,
      chromaticNumber_cycleGraph_of_odd 5 (by decide) (by decide)] at h
    exact absurd h (by decide)
  rw [copyCount_mycielskian_cycleGraph_five (hypercube_cliqueFree_three n) h5]
  have hdeg : ∀ u, Q[n].degree u = n := hypercube_isRegularOfDegree n
  simp only [hdeg, sum_const, card_neighborFinset_eq_degree, card_univ,
    card_hypercubeVert, smul_eq_mul]
  ring

/-!
19. Show that any finset of `α × Bool` splits as the union of a *bottom part*
`A₀ ×ˢ {false}` and a *top part* `A₁ ×ˢ {true}`.
-/
/-- Any finset of `α × Bool` splits as a union of a bottom and a top part. -/
lemma exists_bool_split {α : Type*} [DecidableEq α] (A : Finset (α × Bool)) :
    ∃ A₀ A₁ : Finset α, A = A₀ ×ˢ {false} ∪ A₁ ×ˢ {true} := by
  refine ⟨{p ∈ A | p.2 = false}.image Prod.fst,
          {p ∈ A | p.2 = true}.image Prod.fst, ?_⟩
  ext ⟨v, b⟩
  simp only [mem_union, mem_product, mem_image, mem_filter, mem_singleton]
  cases b <;> aesop

/-!
20. Show that bottom and top parts are disjoint, and deduce that the size of a
bottom/top split is the sum of the sizes of its parts.
-/
lemma disjoint_bool_split {α : Type*} (A₀ A₁ : Finset α) :
    Disjoint (A₀ ×ˢ ({false} : Finset Bool)) (A₁ ×ˢ {true}) :=
  disjoint_product.2 (.inr (by simp))

/-- The size of a bottom/top split is the sum of the sizes of the parts. -/
lemma card_bool_split {α : Type*} [DecidableEq α] (A₀ A₁ : Finset α) :
    #(A₀ ×ˢ {false} ∪ A₁ ×ˢ {true}) = #A₀ + #A₁ := by
  rw [card_union_of_disjoint (disjoint_bool_split A₀ A₁)]
  simp

/-!
21. Show that `interedges` distributes over unions in either argument.

`interedges` is a `filter` of a finset product, so distributivity over unions
follows by rewriting with `Finset.union_product` / `Finset.product_union` and
`Finset.filter_union`.
-/
/-- `interedges` distributes over unions in the first argument. -/
lemma interedges_union_left [DecidableEq V] [DecidableRel G.Adj]
    (s₁ s₂ t : Finset V) :
    G.interedges (s₁ ∪ s₂) t = G.interedges s₁ t ∪ G.interedges s₂ t := by
  simp_rw [interedges_def, union_product, filter_union]

/-- `interedges` distributes over unions in the second argument. -/
lemma interedges_union_right [DecidableEq V] [DecidableRel G.Adj]
    (s t₁ t₂ : Finset V) :
    G.interedges s (t₁ ∪ t₂) = G.interedges s t₁ ∪ G.interedges s t₂ := by
  simp_rw [interedges_def, product_union, filter_union]

/-!
22. In the prism `G □ K₂` (written `G □ ⊤` with `⊤ : SimpleGraph Bool`) the
vertex `(u, b)` is adjacent to `(w, c)` with `b ≠ c` iff `u = w`, so the edges
between opposite copies of two vertex sets `A₀` and `A₁` form a perfect
matching on `A₀ ∩ A₁`. Prove the resulting count. (Hint: show that the edge
set is the image of `A₀ ∩ A₁` under an injective map.)
-/
/-- Edges of the prism `G □ K₂` between opposite copies of two vertex sets
correspond to common vertices of the two sets. -/
lemma card_interedges_bool_ne [DecidableRel G.Adj] [DecidableEq V] {b c : Bool}
    (hbc : b ≠ c) (A₀ A₁ : Finset V) :
    #((G □ ⊤).interedges (A₀ ×ˢ {b}) (A₁ ×ˢ {c})) = #(A₀ ∩ A₁) := by
  have hinj : Function.Injective
      fun v : V => (((v, b), (v, c)) : (V × Bool) × V × Bool) := by
    intro x y hxy
    simpa using congrArg (fun p => p.1.1) hxy
  have himg : (G □ ⊤).interedges (A₀ ×ˢ {b}) (A₁ ×ˢ {c})
      = (A₀ ∩ A₁).image fun v => ((v, b), (v, c)) := by
    ext ⟨⟨u, β⟩, w, γ⟩
    simp only [mem_interedges_iff, mem_product, mem_singleton, mem_image,
      mem_inter, boxProd_adj, top_adj, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hu, rfl⟩, ⟨hw, rfl⟩, ⟨-, h⟩ | ⟨-, rfl⟩⟩
      · exact absurd h hbc
      · exact ⟨u, ⟨hu, hw⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨v, ⟨hv₀, hv₁⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      exact ⟨⟨hv₀, rfl⟩, ⟨hv₁, rfl⟩, Or.inr ⟨hbc, rfl⟩⟩
  rw [himg, card_image_of_injective _ hinj]

/-!
23. Show similarly that the edges of the prism within one of the two copies of
`G` correspond to edges of `G` itself.
-/
/-- Edges of the prism `G □ K₂` within one copy correspond to edges of `G`. -/
lemma card_interedges_bool_eq [DecidableRel G.Adj] [DecidableEq V] (b : Bool)
    (A₀ A₁ : Finset V) :
    #((G □ ⊤).interedges (A₀ ×ˢ {b}) (A₁ ×ˢ {b})) = #(G.interedges A₀ A₁) := by
  have hinj : Function.Injective
      fun e : V × V => (((e.1, b), (e.2, b)) : (V × Bool) × V × Bool) := by
    intro x y hxy
    simp_all [Prod.ext_iff]
  have himg : (G □ ⊤).interedges (A₀ ×ˢ {b}) (A₁ ×ˢ {b})
      = (G.interedges A₀ A₁).image fun e => ((e.1, b), (e.2, b)) := by
    ext ⟨⟨u, β⟩, w, γ⟩
    simp only [mem_interedges_iff, mem_product, mem_singleton, mem_image,
      boxProd_adj, top_adj, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨hu, rfl⟩, ⟨hw, rfl⟩, ⟨h, -⟩ | ⟨h, -⟩⟩
      · exact ⟨u, w, ⟨hu, hw, h⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact absurd rfl h
    · rintro ⟨x, y, ⟨hx, hy, hadj⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      exact ⟨⟨hx, rfl⟩, ⟨hy, rfl⟩, Or.inl ⟨hadj, rfl⟩⟩
  rw [himg, card_image_of_injective _ hinj]

/-!
24. Put exercises 21–23 together: the ordered edge count of a bottom/top split
decomposes into the counts of the two parts plus one matching edge for each
common vertex, in each direction. (Hint: `interedges_disjoint_left` and
`interedges_disjoint_right` provide the disjointness needed to add up the
cards.)
-/
/-- Splitting the ordered edge count of a bottom/top split in `G □ K₂`. -/
lemma card_interedges_bool_split [DecidableRel G.Adj] [DecidableEq V]
    (A₀ A₁ : Finset V) :
    #((G □ ⊤).interedges (A₀ ×ˢ {false} ∪ A₁ ×ˢ {true})
        (A₀ ×ˢ {false} ∪ A₁ ×ˢ {true}))
      = #(G.interedges A₀ A₀) + #(G.interedges A₁ A₁) + 2 * #(A₀ ∩ A₁) := by
  have hd := disjoint_bool_split A₀ A₁
  rw [interedges_union_left,
      card_union_of_disjoint (interedges_disjoint_left _ hd _),
      interedges_union_right, interedges_union_right,
      card_union_of_disjoint (interedges_disjoint_right _ _ hd),
      card_union_of_disjoint (interedges_disjoint_right _ _ hd),
      card_interedges_bool_eq, card_interedges_bool_eq,
      card_interedges_bool_ne (by simp), card_interedges_bool_ne (by simp),
      inter_comm A₁ A₀]
  grind

/-!
25. We now turn to the arithmetic. Prove the key binomial estimate: if `a ≤ b`
then `a.choose i * b ^ i ≤ b.choose i * a ^ i`. (Hint: multiplying both sides
by `i !` turns the binomial coefficients into descending factorials
`a * (a - 1) * ⋯ * (a - i + 1)`, by `Nat.descFactorial_eq_factorial_mul_choose`
and `Nat.descFactorial_eq_prod_range`, and the two sides can then be compared
factor by factor: `(a - j) * b ≤ (b - j) * a`.)
-/
/-!
Multiplying by `i !` turns both binomial coefficients into descending
factorials, which are products of `i` factors, and the padded products
`(a - j) * b` and `(b - j) * a` can be compared factor by factor.
-/
/-- Key binomial estimate: `C(a,i) * b ^ i ≤ C(b,i) * a ^ i` for `a ≤ b`. -/
lemma choose_mul_pow_le {a b : ℕ} (i : ℕ) (hab : a ≤ b) :
    a.choose i * b ^ i ≤ b.choose i * a ^ i := by
  have key : a.descFactorial i * b ^ i ≤ b.descFactorial i * a ^ i := by
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    calc (∏ j ∈ range i, (a - j)) * b ^ i
        = ∏ j ∈ range i, ((a - j) * b) := by
          rw [prod_mul_distrib, prod_const, card_range]
      _ ≤ ∏ j ∈ range i, ((b - j) * a) := by
          apply prod_le_prod
          intro j hj
          rcases le_total a j with h | h
          · simp [Nat.sub_eq_zero_of_le h]
          · calc (a - j) * b = a * b - j * b := by rw [Nat.sub_mul]
              _ ≤ a * b - j * a :=
                  Nat.sub_le_sub_left (Nat.mul_le_mul_left j hab) _
              _ = (b - j) * a := by rw [Nat.sub_mul, mul_comm a b]
      _ = (∏ j ∈ range i, (b - j)) * a ^ i := by
          rw [prod_mul_distrib, prod_const, card_range]
  rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose, mul_assoc, mul_assoc] at key
  exact Nat.le_of_mul_le_mul_left key (Nat.factorial_pos i)

/-!
26. Deduce that for `a ≤ b` we have `2 ^ a * b ^ b ≤ (a + b) ^ b`. This is the
concavity-style estimate `a ≤ b * log₂ (1 + a / b)` in disguise, and it is the
heart of the isoperimetric inequality. (Hint: expand `(a + b) ^ b` with the
binomial theorem `add_pow`, write `2 ^ a = ∑ i ∈ range (a + 1), a.choose i`
using `Nat.sum_range_choose`, and compare the sums term by term using the
previous exercise.)
-/
/-- Key inequality: for `a ≤ b` we have `2 ^ a * b ^ b ≤ (a + b) ^ b`. -/
lemma two_pow_mul_pow_le {a b : ℕ} (hab : a ≤ b) :
    2 ^ a * b ^ b ≤ (a + b) ^ b := by
  rw [add_pow, ← Nat.sum_range_choose a, sum_mul]
  calc ∑ i ∈ range (a + 1), a.choose i * b ^ b
      ≤ ∑ i ∈ range (a + 1), a ^ i * b ^ (b - i) * b.choose i := by
        apply sum_le_sum
        intro i hi
        have hib : i ≤ b := (Nat.lt_succ_iff.1 (mem_range.1 hi)).trans hab
        calc a.choose i * b ^ b = a.choose i * b ^ i * b ^ (b - i) := by
              rw [mul_assoc, pow_mul_pow_sub b hib]
          _ ≤ b.choose i * a ^ i * b ^ (b - i) :=
              Nat.mul_le_mul_right _ (choose_mul_pow_le i hab)
          _ = a ^ i * b ^ (b - i) * b.choose i := by ring
    _ ≤ ∑ i ∈ range (b + 1), a ^ i * b ^ (b - i) * b.choose i :=
        sum_le_sum_of_subset (range_subset_range.2 (by grind))

/-!
27. Combine the previous exercise with some elementary estimates to obtain the
arithmetic form of the inductive step. (Hint: reduce to the case `a ≤ b`, and
in that case bound `2 ^ (x + y + 2 * c)` by `(2 * a) ^ a * (2 ^ a * b ^ b)`.)
-/
/-- The inductive step of the isoperimetric inequality in multiplicative
form. -/
lemma two_pow_le_add_pow {a b c x y : ℕ} (hca : c ≤ a) (hcb : c ≤ b)
    (hx : 2 ^ x ≤ a ^ a) (hy : 2 ^ y ≤ b ^ b) :
    2 ^ (x + y + 2 * c) ≤ (a + b) ^ (a + b) := by
  have key : ∀ a b x y : ℕ, c ≤ a → a ≤ b → 2 ^ x ≤ a ^ a → 2 ^ y ≤ b ^ b →
      2 ^ (x + y + 2 * c) ≤ (a + b) ^ (a + b) := by
    intro a b x y hca hab hx hy
    calc 2 ^ (x + y + 2 * c) = 2 ^ x * 2 ^ y * (2 ^ c * 2 ^ c) := by ring
      _ ≤ a ^ a * b ^ b * (2 ^ a * 2 ^ a) := by
          have h2 : 2 ^ c ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hca
          exact Nat.mul_le_mul (Nat.mul_le_mul hx hy) (Nat.mul_le_mul h2 h2)
      _ = (2 * a) ^ a * (2 ^ a * b ^ b) := by rw [mul_pow]; ring
      _ ≤ (a + b) ^ a * (a + b) ^ b :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by grind) a)
            (two_pow_mul_pow_le hab)
      _ = (a + b) ^ (a + b) := (pow_add _ _ _).symm
  rcases le_total a b with hab | hab
  · exact key a b x y hca hab hx hy
  · have h := key b a y x hcb hab hy hx
    rwa [add_comm y x, add_comm b a] at h

/-!
28. Prove the inductive step: if the multiplicative bound holds for all vertex
sets of `G` then it holds for all vertex sets of the prism `G □ K₂`. (Hint:
split `A` using exercise 19 and put exercises 20, 24 and 27 together.)
-/
/-- The multiplicative bound transfers from `G` to the prism `G □ K₂`. -/
lemma boxProdTop_two_pow_card_interedges_le [DecidableRel G.Adj]
    [DecidableEq V] (hG : ∀ B : Finset V, 2 ^ #(G.interedges B B) ≤ #B ^ #B)
    (A : Finset (V × Bool)) :
    2 ^ #((G □ ⊤).interedges A A) ≤ #A ^ #A := by
  obtain ⟨A₀, A₁, hA⟩ := exists_bool_split A
  rw [hA, card_interedges_bool_split, card_bool_split]
  exact two_pow_le_add_pow (card_le_card inter_subset_left)
    (card_le_card inter_subset_right) (hG A₀) (hG A₁)

/-!
29. Prove the multiplicative edge-isoperimetric inequality for the hypercube
by induction on `n`. (Hint: for the inductive step recall that `Q[n + 1]` is
*definitionally* `Q[n] □  ⊤`, so the previous exercise applies to it —
`exact` will happily cross this definitional equality.)
-/
/-!
In the inductive step the goal is stated for `Q[n + 1]`, while the previous
lemma produces a bound for `Q[n].boxProd ⊤` on the vertex type
`HypercubeVert n × Bool`. These agree *definitionally* (`hypercube_succ` and
`hypercubeVert_succ` are both `rfl`), so `exact` accepts the term as it is: no
rewriting is needed (and `rw`/`simp` would in fact struggle here, since they
match syntactically and do not see through this definitional equality).
-/
/-- The multiplicative edge-isoperimetric inequality for the hypercube. -/
lemma two_pow_card_interedges_le {n : ℕ} : ∀ A : Finset (HypercubeVert n),
    2 ^ #(Q[n].interedges A A) ≤ #A ^ #A := by
  induction n with
  | zero =>
    intro A
    simpa [SimpleGraph.interedges, Rel.interedges, hypercube_zero] using
      Nat.succ_le_of_lt Nat.pow_self_pos
  | succ n ih => exact fun A => boxProdTop_two_pow_card_interedges_le ih A

/-!
30. Deduce the edge-isoperimetric inequality: a set of `2 ^ k` vertices of the
hypercube spans at most `k * 2 ^ (k - 1)` edges, i.e. at most `k * 2 ^ k`
ordered adjacent pairs. (Hint: compare exponents of `2` using
`Nat.pow_le_pow_iff_right`.)
-/
/-- **Edge-isoperimetric inequality** for the hypercube, `2 ^ k` version: a
set of `2 ^ k` vertices of `Q[n]` spans at most `k * 2 ^ (k - 1)` edges
(counted here as `k * 2 ^ k` ordered adjacent pairs), as achieved by
subcubes. -/
theorem card_interedges_le_of_card_eq_two_pow {n k : ℕ}
    {A : Finset (HypercubeVert n)} (hA : #A = 2 ^ k) :
    #(Q[n].interedges A A) ≤ k * 2 ^ k := by
  have h := two_pow_card_interedges_le A
  rw [hA, ← pow_mul] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

/-!
31. Show that a graph embedding `f : G ↪g H` preserves the number of ordered
adjacent pairs inside a set, and that the whole vertex set of a finite graph
spans `∑ v, G.degree v` ordered adjacent pairs. (Hint: for the first part, show
that `f.toEmbedding.prodMap f.toEmbedding` maps `G.interedges s t` onto the
ordered adjacent pairs of `s.map f.toEmbedding` and `t.map f.toEmbedding`.)

An embedding is injective and reflects adjacency, so `f × f` maps the ordered
adjacent pairs in `s ×ˢ t` bijectively onto those in the images. For the second part,
the ordered pairs with first entry `v` correspond to the neighbours of `v`. We take
the `LocallyFinite` instance as an argument, as in
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond),
so that the lemma applies whichever instance the degrees are computed with.
-/
lemma card_interedges_map {W : Type*} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (f : G ↪g H) (s t : Finset V) :
    #(H.interedges (s.map f.toEmbedding) (t.map f.toEmbedding)) =
      #(G.interedges s t) := by
  rw [← card_map (f.toEmbedding.prodMap f.toEmbedding)]
  congr 1
  ext ⟨x, y⟩
  simp only [mem_interedges_iff, mem_map, Prod.exists]
  aesop

lemma card_interedges_univ [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] :
    #(G.interedges univ univ) = ∑ v, G.degree v := by
  rw [interedges_def, card_filter, sum_product]
  refine sum_congr rfl fun v _ => ?_
  rw [← card_neighborFinset_eq_degree, ← card_filter]
  congr 1
  ext w
  simp

/-!
32. Deduce that the bound of exercise 30 is attained: the copy of `Q[k]` inside
`Q[k + m]` given by the embedding `hypercubeEmbedding k m` of
[Exercises](https://jt496.github.io/GraphTheoryInLean/Maps/#section-exercises-maps)
is a set of `2 ^ k` vertices spanning exactly `k * 2 ^ k` ordered adjacent pairs.

By exercise 31 the image of the vertex set of `Q[k]` spans as many ordered
adjacent pairs as `Q[k]` itself, namely the degree sum of a `k`-regular graph on
`2 ^ k` vertices.
-/
theorem exists_card_interedges_eq (k m : ℕ) :
    ∃ A : Finset (HypercubeVert (k + m)), #A = 2 ^ k ∧
      #(Q[k + m].interedges A A) = k * 2 ^ k := by
  refine ⟨univ.map (hypercubeEmbedding k m).toEmbedding,
    by simp [card_hypercubeVert], ?_⟩
  rw [card_interedges_map, card_interedges_univ,
    sum_congr rfl fun v _ => hypercube_isRegularOfDegree k v]
  simp [card_hypercubeVert, mul_comm]

/-! END SOLUTIONS -/

end SimpleGraph
