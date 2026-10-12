import GraphTheoryInLean.C05_Maps.C05_Maps
namespace SimpleGraph
variable {V W X : Type*}
/-!
# Exercises
1. Show that there is no graph homomorphism from `K[n + 1]` to `K[n]` (i.e.
`K[n + 1]` is not `n`-colourable).
-/
example (n : ℕ) : IsEmpty (K[n + 1] →g K[n]) := by
  sorry

/-!
2. Define an embedding of `P[n]` into `P[n + k]` so that the image is exactly the
last `n` vertices.
-/
example (n k : ℕ) : (P[n]) ↪g (P[n + k]) where
  toFun i := i.addNat k
  inj' := sorry
  map_rel_iff' := sorry

/-!
3. Show that any `G ↪g H` gives rise to an embedding of `G` into any blow-up of `H`
with nonempty parts.
-/
def Embedding.mapBlowUp' {G : SimpleGraph V} {ι : Type*} {H : SimpleGraph ι}
    (e : G ↪g H) (W : ι → Type*) (f : ∀ (i : ι), W i) :
    G ↪g H.blowUpGraph W := by
  sorry

/-!
4. Show that if `G ≤ H` are graphs on the same vertex type then `G ⊑ H`.
-/
example {G H : SimpleGraph V} (h : G ≤ H) : G ⊑ H := by
  sorry

/-!
5. Show that if `G ≃g H` then `Gᶜ ≃g Hᶜ`.
-/
example (G : SimpleGraph V) (H : SimpleGraph W) (f : G ≃g H) : Gᶜ ≃g Hᶜ := by
  sorry

/-!
6. Show that a graph isomorphic to `⊥` is itself `⊥`.
-/
example (G : SimpleGraph V) (f : G ≃g (⊥ : SimpleGraph W)) : G = ⊥ := by
  sorry

/-!
7. Show that the path graph `P[4]` is *self-complementary*, i.e. isomorphic to its
own complement. (Hint: find a suitable permutation of the vertices; you can define it
and its inverse using `Matrix` vector notation `![_, _, _, _]`.)
-/
example : P[4] ≃g (P[4])ᶜ := by
  sorry

/-!
8. Show that the cycle `C[5]` is also self-complementary. (Hint: try `i ↦ 2 * i`.)
-/
example : C[5] ≃g (C[5])ᶜ := by
  sorry

/-!
9. We saw that for an embedding `f : V ↪ W` we have `(G.map f).comap f = G`, but
only `(H.comap f).map f ≤ H`. Show that this inequality can be strict.
-/
example : ∃ (f : Fin 1 ↪ Fin 2) (H : SimpleGraph (Fin 2)),
    (H.comap f).map f ≠ H := by
  sorry

/-!
10. Define an embedding of `Q[n]` into `Q[n + k]` by iterating
`hypercube.embedFalse`.
-/
def hypercubeEmbedding' (n : ℕ) : (k : ℕ) → Q[n] ↪g Q[n + k] := sorry

/-!
The next question asks for an isomorphism `Q[2] ≃g C[4]`. In
[Algebraic Graph Theory](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#chapter-algebraic-graph-theory)
we use it to identify the automorphism group of the 2-dimensional hypercube.

11. Show that `Q[2]` is isomorphic to the cycle `C[4]`. Both graphs are concrete
finite graphs with decidable adjacency (`DecidableRel Q[n].Adj` was established in
[Decidability, Finiteness and Degrees](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#chapter-decidability-finiteness-and-degrees),
and Mathlib provides `instDecidableRelFinAdjCycleGraph` for `C[n]`), so every proof
obligation can be checked by `decide`. Recall also that `v[i, j]` where
`i, j ∈ {0, 1}` is scoped notation for the vertices of `Q[2]`. (The stub is marked
`noncomputable` only so that its `sorry` does not cause problems when this guide is
built; you can remove the keyword once you have filled in the solution.)
-/
open HypercubeVert
noncomputable def hypercubeTwoIsoCycleFour' : Q[2] ≃g C[4] := sorry

/-!
Exercises 12–16 are about the indexed tensor product `⨂g i, G i` from the starred
section
[Tensor Products*](https://jt496.github.io/GraphTheoryInLean/Maps/#section-tensor-products).

12. Show that for each index `j` the projection out of the indexed tensor product
`⨂g i, G i` is a graph homomorphism to `G j`.
-/
example {ι : Type*} {V : ι → Type*} (G : ∀ i, SimpleGraph (V i)) (j : ι) :
    ⨂g i, G i →g G j := sorry

/-!
13. The universal property of the indexed tensor product.
Given graph homomorphisms from `K` to each `G i`, there is a homomorphism from `K` to
the indexed tensor product `⨂g i, G i` (provided `ι` is nonempty, which here follows
from the existence of `i₀`; the next exercise looks at the case when `ι` is empty).
-/
example {ι : Type*} {V : ι → Type*} (i₀ : ι) {K : SimpleGraph X}
    (G : ∀ i, SimpleGraph (V i)) (f : ∀ i, K →g G i) : K →g ⨂g i, G i := sorry

/-!
14. Prove that if `ι` is empty then there is a graph homomorphism from a graph `K`
to the indexed tensor product `⨂g i, G i` iff `K` is the empty graph `⊥`.
-/
example {ι : Type*} [IsEmpty ι] {V : ι → Type*} {K : SimpleGraph X}
    (G : ∀ i, SimpleGraph (V i)) : Nonempty (K →g ⨂g i, G i) ↔ K = ⊥ := by
  sorry

/-!
15. The degree of `f` in the indexed tensor product is the product of the degrees of
its components. The neighbour set is the `Fintype.piFinset` of the componentwise
neighbour sets, and (using `[Nonempty ι]`) the `≠` condition in the adjacency is
automatic.
-/
example {ι : Type*} {V : ι → Type*} {G : (i : ι) → SimpleGraph (V i)}
    {f : (i : ι) → V i} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [∀ i, Fintype ((G i).neighborSet (f i))] :
    (⨂g i, G i).degree f = ∏ i, (G i).degree (f i) := by
  sorry

/-!
16. Given graph homomorphisms from `K` to each `G i`, one of which, `f i₀`, is a
graph embedding, we have a graph embedding of `K` into the indexed tensor product.
(We say that `f i₀` is a graph embedding by giving both additional properties that
allow the original homomorphism to be upgraded: injectivity and adjacency
reflection.)
-/
example {ι : Type*} {V : ι → Type*} (i₀ : ι) {K : SimpleGraph X}
    (G : ∀ i, SimpleGraph (V i)) (f : ∀ i, K →g G i)
    (inj : Function.Injective (f i₀))
    (reflect : ∀ {x y}, (G i₀).Adj (f i₀ x) (f i₀ y) → K.Adj x y) :
    K ↪g ⨂g i, G i where
  toFun x i := sorry
  inj' := sorry
  map_rel_iff' := sorry

/-!
The next two exercises are about the starred section
[Vertex-Transitivity](https://jt496.github.io/GraphTheoryInLean/Maps/#section-vertex-transitivity).

17. Show that if `G` is vertex-transitive then so is its complement `Gᶜ`, and deduce
that the empty graph `⊥` is vertex-transitive. (Hint: as in exercise 5, an
automorphism of `G` is also an automorphism of `Gᶜ`; and `compl_top` says
`⊤ᶜ = ⊥`.)
-/
lemma IsVertexTransitive.compl' {G : SimpleGraph V} (h : G.IsVertexTransitive) :
    Gᶜ.IsVertexTransitive := by
  sorry

lemma isVertexTransitive_bot' : (⊥ : SimpleGraph V).IsVertexTransitive := by
  sorry

/-!
18. Our characterization `isVertexTransitive_mycielskian_iff` of the
vertex-transitive Mycielskians assumes that `V` is nonempty. Show that this
assumption is needed: if `V` is empty then the Mycielskian of any graph on `V` is
vertex-transitive, but the graph is not isomorphic to `K[2]`.

If `V` is empty then the Mycielskian has the single vertex `none`, so the identity
sends any vertex to any other; and an isomorphism to `K[2]` would give an element
`e.symm 0` of `V`.
-/
lemma isVertexTransitive_mycielskian_of_isEmpty' [IsEmpty V] (G : SimpleGraph V) :
    mμ[G].IsVertexTransitive :=
  sorry

lemma isEmpty_iso_completeGraph_two_of_isEmpty' [IsEmpty V] (G : SimpleGraph V) :
    IsEmpty (G ≃g K[2]) :=
  sorry

/-!
The last exercise is about the starred section
[Claw-Free Graphs*](https://jt496.github.io/GraphTheoryInLean/Maps/#section-claw-free-graphs).

19. Show that `K[4]` is claw-free, but contains a non-induced copy of the claw
`K[1, 3]`.
-/
example : K[4].ClawFree ∧ K[1, 3] ⊑ K[4] := by
  sorry

/-! SOLUTIONS -/

/-!
1. Show that there is no graph homomorphism from `K[n + 1]` to `K[n]` (i.e.
`K[n + 1]` is not `n`-colourable).
-/
example (n : ℕ) : IsEmpty (K[n + 1] →g K[n]) :=
  ⟨fun f => by simpa using Fintype.card_le_of_injective f f.injective_of_top_hom⟩

/-!
2. Define an embedding of `P[n]` into `P[n + k]` so that the image is exactly the
last `n` vertices.
-/
/-- The embedding of `P[n]` into `P[n + k]` as the last `n` vertices. -/
@[simps]
def pathGraphEmbedding (n k : ℕ) : (P[n]) ↪g (P[n + k]) where
  toFun i := i.addNat k
  inj' := (Fin.addNatEmb k).injective
  map_rel_iff' := by
    intro i j
    grind [Function.Embedding.coeFn_mk, pathGraph_adj]

#check pathGraphEmbedding_apply

/-!
3. Show that any `G ↪g H` gives rise to an embedding of `G` into any blow-up of `H`
with nonempty parts.
-/
/-- An embedding `e : G ↪g H` gives an embedding of `G` into any blow-up of `H` with
nonempty parts: compose `e` with `Embedding.blowUp`. -/
def Embedding.mapBlowUp {G : SimpleGraph V} {ι : Type*} {H : SimpleGraph ι}
    (e : G ↪g H) (W : ι → Type*) (f : ∀ (i : ι), W i) :
    G ↪g H.blowUpGraph W :=
  (Embedding.blowUp H W f).comp e

/-!
4. Show that if `G ≤ H` are graphs on the same vertex type then `G ⊑ H`.
(The homomorphism `Hom.ofLE h` is the identity on vertices, so it is injective.
Mathlib calls this result `IsContained.of_le`.)
-/
example {G H : SimpleGraph V} (h : G ≤ H) : G ⊑ H :=
  ⟨(Hom.ofLE h).toCopy Function.injective_id⟩

/-!
5. Show that if `G ≃g H` then `Gᶜ ≃g Hᶜ`.
-/
example (G : SimpleGraph V) (H : SimpleGraph W) (f : G ≃g H) : Gᶜ ≃g Hᶜ :=
    ⟨f, by simp [f.map_adj_iff, f.injective.eq_iff]⟩

/-!
6. Show that a graph isomorphic to `⊥` is itself `⊥`.
-/
example (G : SimpleGraph V) (f : G ≃g (⊥ : SimpleGraph W)) : G = ⊥ := by
  ext
  simp [← f.map_adj_iff]

/-!
7. Show that the path graph `P[4]` is *self-complementary*, i.e. isomorphic to its
own complement. (Hint: find a suitable permutation of the vertices; you can define it
and its inverse using `Matrix` vector notation `![_, _, _, _]`.)
-/
example : P[4] ≃g (P[4])ᶜ where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

/-!
8. Show that the cycle `C[5]` is also self-complementary. (Hint: try `i ↦ 2 * i`.)
(Multiplication by `2` sends the edges `{i, i + 1}` of `C[5]` to the pairs
`{2 * i, 2 * i + 2}`, which are exactly the edges of the complement; its inverse is
multiplication by `3`.)
-/
example : C[5] ≃g (C[5])ᶜ where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

/-!
9. We saw that for an embedding `f : V ↪ W` we have `(G.map f).comap f = G`, but
only `(H.comap f).map f ≤ H`. Show that this inequality can be strict.
(It is not an equality because any edge of `H` touching a vertex outside the range of
`f` is lost by the comap. Here we embed `Fin 1` into `Fin 2` and lose the only edge
of `⊤`.)
-/
example : ∃ (f : Fin 1 ↪ Fin 2) (H : SimpleGraph (Fin 2)),
    (H.comap f).map f ≠ H := by
  refine ⟨Fin.castSuccEmb, ⊤, fun h => ?_⟩
  have h01 : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by decide
  rw [← h, map_adj] at h01
  -- an edge of the comap is an edge of a graph on `Fin 1`, which has no edges
  obtain ⟨u, v, huv, -⟩ := h01
  exact huv.ne (Subsingleton.elim u v)

/-!
10. Define an embedding of `Q[n]` into `Q[n + k]` by iterating
`hypercube.embedFalse`.
-/
/-- The embedding `Q[n] ↪g Q[n + k]` obtained by iterating `hypercube.embedFalse`. -/
def hypercubeEmbedding (n : ℕ) : (k : ℕ) → Q[n] ↪g Q[n + k]
  | 0 => Embedding.refl
  | k + 1 => (hypercube.embedFalse (n + k)).comp (hypercubeEmbedding n k)

/-!
The next question asks for an isomorphism `Q[2] ≃g C[4]`. In
[Algebraic Graph Theory](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#chapter-algebraic-graph-theory)
we use it to identify the automorphism group of the 2-dimensional hypercube.

11. Show that `Q[2]` is isomorphic to the cycle `C[4]`. Both graphs are concrete
finite graphs with decidable adjacency (`DecidableRel Q[n].Adj` was established in
[Decidability, Finiteness and Degrees](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#chapter-decidability-finiteness-and-degrees),
and Mathlib provides `instDecidableRelFinAdjCycleGraph` for `C[n]`), so every proof
obligation can be checked by `decide`. Recall also that `v[i, j]` where
`i, j ∈ {0, 1}` is scoped notation for the vertices of `Q[2]`.
-/

/-- The Gray-code isomorphism `Q[2] ≃g C[4]`, sending the vertices
`00, 10, 11, 01` to `0, 1, 2, 3`. -/
def hypercubeTwoIsoCycleFour : Q[2] ≃g C[4] where
  toFun v := match v with
    | v[0, 0] => 0
    | v[1, 0] => 1
    | v[1, 1] => 2
    | v[0, 1] => 3
  invFun := ![v[0, 0], v[1, 0], v[1, 1], v[0, 1]]
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

/-!
Exercises 12–16 are about the indexed tensor product `⨂g i, G i` from the starred
section
[Tensor Products*](https://jt496.github.io/GraphTheoryInLean/Maps/#section-tensor-products).

12. The projection out of the indexed tensor product is a graph homomorphism.
-/
example {ι : Type*} {V : ι → Type*} (G : ∀ i, SimpleGraph (V i)) (j : ι) :
    ⨂g i, G i →g G j where
  toFun f := f j
  map_rel' h := (piTensorProd_adj.1 h).1 j

/-!
13. The universal property of the indexed tensor product.
Given graph homomorphisms from `K` to each `G i`, there is a homomorphism from `K` to
the indexed tensor product `⨂g i, G i` (provided `ι` is nonempty, which here follows
from the existence of `i₀`; the next exercise looks at the case when `ι` is empty).
-/
example {ι : Type*} {V : ι → Type*} (i₀ : ι) {K : SimpleGraph X}
    (G : ∀ i, SimpleGraph (V i)) (f : ∀ i, K →g G i) : K →g ⨂g i, G i where
  toFun x i := f i x
  map_rel' h := by
    have : Nonempty ι := ⟨i₀⟩
    rw [piTensorProd_adj_of_nonempty]
    exact fun i => (f i).map_adj h

/-!
14. Prove that if `ι` is empty then there is a graph homomorphism from a graph `K`
to the indexed tensor product `⨂g i, G i` iff `K` is the empty graph `⊥`.
-/
lemma piTensorProd_hom_iff_of_isEmpty {ι : Type*} [IsEmpty ι] {V : ι → Type*}
    {K : SimpleGraph X} (G : ∀ i, SimpleGraph (V i)) :
    Nonempty (K →g ⨂g i, G i) ↔ K = ⊥ := by
  constructor
  · rintro ⟨f⟩
    ext a b
    simp only [bot_adj, iff_false]
    intro h
    apply (f.map_adj h).ne
    -- The goal is now `⊢ f a = f b`
    -- Note that `f.toFun` is a map from `X` to the vertex type
    -- of the indexed tensor product
    have _ : X → (i : ι) → V i := f.toFun
    -- So `f a` and `f b` are both elements of `(i : ι) → V i`.
    have _ : (i : ι) → V i := f a
    have _ : (i : ι) → V i := f b
    -- Since `ι` is empty, `(i : ι) → V i` contains a unique element
    -- (you can define it by `fun i => isEmptyElim i`)
    have : Unique ((i : ι) → V i) := inferInstance
    -- Lean has the `Subsingleton` typeclass for types with at most one element.
    have : Subsingleton ((i : ι) → V i) := inferInstance
    -- So `f a = f b` since they are both elements of a Subsingleton type.
    apply Subsingleton.elim
    -- Note, none of the `have` statements above are needed, they are for exposition.
  · rintro rfl
    -- We need to show that there is a graph homomorphism from `⊥` to the indexed
    -- tensor product. Since `ι` is empty there is only one choice for the
    -- `toFun`. Since `⊥` has no edges, the proof of map_rel' is trivial.
    exact ⟨{ toFun := fun _ i => isEmptyElim i, map_rel' := fun h => h.elim }⟩

/-!
15. The degree of `f` in the indexed tensor product is the product of the degrees of
its components. The neighbour set is the `Fintype.piFinset` of the componentwise
neighbour sets, and (using `[Nonempty ι]`) the `≠` condition in the adjacency is
automatic.
-/
example {ι : Type*} {V : ι → Type*} {G : (i : ι) → SimpleGraph (V i)}
    {f : (i : ι) → V i} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [∀ i, Fintype ((G i).neighborSet (f i))] :
    (⨂g i, G i).degree f = ∏ i, (G i).degree (f i) := by
  simp_rw [← card_neighborFinset_eq_degree, ← Fintype.card_piFinset]
  congr 1
  ext g
  simp
/-!
16. Given graph homomorphisms from `K` to each `G i`, one of which, `f i₀`, is a
graph embedding, we have a graph embedding of `K` into the indexed tensor product.
(We say that `f i₀` is a graph embedding by giving both additional properties that
allow the original homomorphism to be upgraded: `inj` injectivity and `reflect`
reflection of adjacency.)
-/
example {ι : Type*} {V : ι → Type*} (i₀ : ι) {K : SimpleGraph X}
    (G : ∀ i, SimpleGraph (V i)) (f : ∀ i, K →g G i)
    (inj : Function.Injective (f i₀))
    (reflect : ∀ {x y}, (G i₀).Adj (f i₀ x) (f i₀ y) → K.Adj x y) :
    K ↪g ⨂g i, G i where
  toFun x i := f i x
  inj' _ _ h := inj (congrFun h i₀)
  map_rel_iff' := by
    have : Nonempty ι := ⟨i₀⟩
    intro x y
    rw [piTensorProd_adj_of_nonempty]
    exact ⟨fun h => reflect (h i₀), fun hk i => (f i).map_adj hk⟩

/-!
The next two exercises are about the starred section
[Vertex-Transitivity](https://jt496.github.io/GraphTheoryInLean/Maps/#section-vertex-transitivity).

17. Show that if `G` is vertex-transitive then so is its complement `Gᶜ`, and deduce
that the empty graph `⊥` is vertex-transitive.
-/
lemma IsVertexTransitive.compl {G : SimpleGraph V} (h : G.IsVertexTransitive) :
    Gᶜ.IsVertexTransitive := by
  intro u v
  obtain ⟨f, hf⟩ := h u v
  -- `f` preserves adjacency and distinctness, so it also preserves non-adjacency
  exact ⟨⟨f, by simp [f.map_adj_iff, f.injective.eq_iff]⟩, hf⟩

lemma isVertexTransitive_bot : (⊥ : SimpleGraph V).IsVertexTransitive := by
  simpa using (isVertexTransitive_top (V := V)).compl

/-!
18. Our characterization `isVertexTransitive_mycielskian_iff` of the
vertex-transitive Mycielskians assumes that `V` is nonempty. Show that this
assumption is needed: if `V` is empty then the Mycielskian of any graph on `V` is
vertex-transitive, but the graph is not isomorphic to `K[2]`.

If `V` is empty then the Mycielskian has the single vertex `none`, so the identity
sends any vertex to any other; and an isomorphism to `K[2]` would give an element
`e.symm 0` of `V`.
-/
lemma isVertexTransitive_mycielskian_of_isEmpty [IsEmpty V] (G : SimpleGraph V) :
    mμ[G].IsVertexTransitive :=
  fun _ _ => ⟨.refl, Subsingleton.elim _ _⟩

lemma isEmpty_iso_completeGraph_two_of_isEmpty [IsEmpty V] (G : SimpleGraph V) :
    IsEmpty (G ≃g K[2]) :=
  ⟨fun e => isEmptyElim (e.symm 0)⟩

/-!
The last exercise is about the starred section
[Claw-Free Graphs*](https://jt496.github.io/GraphTheoryInLean/Maps/#section-claw-free-graphs).

19. Show that `K[4]` is claw-free, but contains a non-induced copy of the claw
`K[1, 3]`.
(An induced claw would need two of its leaves to be non-adjacent, but any two
distinct vertices of `K[4]` are adjacent. On the other hand vertex `0` and its three
neighbours `1, 2, 3` give a copy of the claw.)
-/
example : K[4].ClawFree ∧ K[1, 3] ⊑ K[4] := by
  refine ⟨fun ⟨f⟩ => ?_, ?_⟩
  · -- the images of two leaves are distinct, hence adjacent in `K[4]`
    have h : K[4].Adj (f (.inr 0)) (f (.inr 1)) := by simp
    -- but `f` reflects adjacency, and the two leaves are not adjacent in the claw
    simp [f.map_adj_iff] at h
  · exact claw_isContained (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! END SOLUTIONS -/

end SimpleGraph
