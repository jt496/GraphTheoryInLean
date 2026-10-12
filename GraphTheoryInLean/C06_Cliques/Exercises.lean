import GraphTheoryInLean.C05_Maps.Exercises
import GraphTheoryInLean.C06_Cliques.C06_Cliques

namespace SimpleGraph
open Finset
variable {V : Type*} {G : SimpleGraph V}

/-!
# Exercises

1. Show that any finite subset `t` of a clique `s` is a `#t`-clique.
-/
example {s : Set V} {t : Finset V} (hc : G.IsClique s) (h : ↑t ⊆ s) :
    G.IsNClique #t t := by
  sorry

/-!
2. Show that `{0, 1, 2}` is a triangle in the Paley graph on `17` vertices.
-/
example : (paleyGraph (ZMod 17)).IsNClique 3 {0, 1, 2} := by
  sorry

/-!
3. Show that the Paley graph on `17` vertices is `4`-clique free. (Although `decide`
should be able to prove this it will probably time-out; you may want to use
`native_decide` instead.)
-/
lemma paleyGraph_seventeen_cliqueFree_four' :
    (paleyGraph (ZMod 17)).CliqueFree 4 := by
  sorry

/-!
4. Show that a set of vertices is a clique in `G` if and only if it is an independent
set in the complement of `G`. (Mathlib has this as `isIndepSet_compl`, but prove it
directly from the definitions, using `compl_adj`.)
-/
example {s : Set V} : G.IsClique s ↔ Gᶜ.IsIndepSet s := by
  sorry

/-!
5. Show that if `G` is `m`-clique-free and `m ≤ n` then `G` is also `n`-clique-free.
-/
example {m n : ℕ} (h : G.CliqueFree m) (hmn : m ≤ n) : G.CliqueFree n := by
  sorry

/-!
6. Show that the clique number is monotone: if `G ≤ H` then `ω G ≤ ω H`. (There is
a one-line proof using a lemma from the chapter, and a direct proof using
`exists_isNClique_cliqueNum`.)
-/
lemma cliqueNum_mono' [Finite V] {H : SimpleGraph V} (h : G ≤ H) : ω G ≤ ω H := by
  sorry

/-!
7. Show that the clique number of the Paley graph on `17` vertices is `3`.
(Recall we have: `IsNClique.cliqueNum_eq_of_cliqueFree` so we just need to give an
example of a `3`-clique and show that the graph is `4`-clique free.)
-/
example : ω (paleyGraph (ZMod 17)) = 3 := by
  sorry

/-!
In the next few exercises we look at the clique number of graph products starting
with the tensor product `G ⊗g H`. Recall that two vertices `(v₁, w₁), (v₂, w₂)` of
the tensor product are adjacent if and only if `G.Adj v₁ v₂` and `H.Adj w₁ w₂`.
-/
/-!
8. Unlike the junk value `⍺ pathNat₁ = 0` of
[Independence Number of the Infinite Path on ℕ](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-independence-number-of-the-infinite-path-on),
the clique number of the infinite path is an honest value. Show that
`ω pathNat₁ = 2`. Hint: `pathNat₁` is triangle-free, since adjacent vertices have
different parity. The lemma `IsNClique.le_cliqueNum` needs `[Finite V]`, so for the
lower bound unfold `cliqueNum` as a supremum and use `le_csSup`.
-/
example : ω pathNat₁ = 2 := by
  sorry

/-!
9. The first projection of a clique in the tensor product `G ⊗g H` is a clique in
`G`.
-/
example {W : Type*} {H : SimpleGraph W} {s : Set (V × W)}
    (h : (G ⊗g H).IsClique s) : G.IsClique (Prod.fst '' s) := by
  sorry

/-!
10. If `G` is `n`-clique-free then so is its tensor product `G ⊗g H` with any graph
`H`.
-/
lemma CliqueFree.tensorProd_left' {W : Type*} {H : SimpleGraph W} {n : ℕ}
    (h : G.CliqueFree n) : (G ⊗g H).CliqueFree n := by
  sorry

/-!
11. The `j`-th projection of a clique in the indexed tensor product `⨂g i, G i` is a
clique in `G j`.
-/
example {ι : Type*} {V : ι → Type*} {G : (i : ι) → SimpleGraph (V i)} (j : ι)
    {s : Set ((i : ι) → V i)} (h : (⨂g i, G i).IsClique s) :
    (G j).IsClique ((· j) '' s) := by
  sorry

/-!
12. The clique number of `G ⊗g H` is `min (ω G) (ω H)`. (Hint: for the lower bound,
let `m = min (ω G) (ω H)` and use `not_cliqueFree_iff_top_isContained` to find
copies of `K[m]` in both `G` and `H`. Pair them with `tensorProd.prod` to get a
homomorphism `K[m] →g G ⊗g H`.)
-/
lemma cliqueNum_tensorProd' {W : Type*} [Finite V] [Finite W] {H : SimpleGraph W} :
    ω (G ⊗g H) = min (ω G) (ω H) := by
  sorry

/-!
We now turn to the box product `G □ H`. Recall that two vertices `(v₁, w₁), (v₂, w₂)`
of the box product are adjacent if and only if either `G.Adj v₁ v₂` and `w₁ = w₂`, or
`v₁ = v₂` and `H.Adj w₁ w₂`. This implies that cliques are always constant in one
coordinate.
-/
/-!
13. A clique `s` in `G` gives a "row" clique in the box product `G □ H` (so long as
there is a vertex `h₀` in `H` to fix the second coordinate).
-/
example {W : Type*} {H : SimpleGraph W} {s : Set V} (h₀ : W) (h : G.IsClique s) :
    (G □ H).IsClique ((·, h₀) '' s) := by
  sorry

/-!
14. In any box product `G □ H` with nonempty second factor we have `ω G ≤ ω (G □ H)`:
the embedding `boxProdLeft` can transport a maximum clique of `G` to a clique of the
same size in `G □ H`.
-/
lemma cliqueNum_boxProd_le_left' {W : Type*} [Finite V] [Finite W] [Nonempty W]
    {H : SimpleGraph W} : ω G ≤ ω (G □ H) := by
  sorry

/-!
15. A clique of `G □ H` containing a "horizontal" edge (two vertices sharing their
second coordinate) is constant in the second coordinate.
-/
lemma IsClique.boxProd_snd_eq' {W : Type*} {H : SimpleGraph W} {s : Set (V × W)}
    {x y : V × W} (ht : (G □ H).IsClique s) (hx : x ∈ s) (hy : y ∈ s)
    (hG : G.Adj x.1 y.1) (hsnd : x.2 = y.2) : ∀ z ∈ s, z.2 = x.2 := by
  sorry

/-!
16. `Prod.fst` is injective on a clique of `G □ H` whose vertices all share the same
second coordinate, so such a clique projects to a clique of `G` of the same size.
-/
lemma IsNClique.boxProd_image_fst' {W : Type*} [DecidableEq V] {H : SimpleGraph W}
    {m : ℕ} {t : Finset (V × W)} {w : W} (ht : (G □ H).IsNClique m t)
    (hconst : ∀ z ∈ t, z.2 = w) : G.IsNClique m (t.image Prod.fst) := by
  sorry

/-!
17. A clique of `G □ H` containing a "horizontal" edge has size at most `ω G`.
-/
lemma boxProd_card_le_left' {W : Type*} [Finite V] {H : SimpleGraph W} {m : ℕ}
    {t : Finset (V × W)} {x y : V × W} (ht : (G □ H).IsNClique m t) (hx : x ∈ t)
    (hy : y ∈ t) (hG : G.Adj x.1 y.1) (hsnd : x.2 = y.2) : m ≤ ω G := by
  sorry

/-!
18. The clique number of `G □ H` is `max (ω G) (ω H)` (for finite nonempty graphs).
-/
lemma cliqueNum_boxProd' {W : Type*} [Finite V] [Finite W] [Nonempty V]
    [Nonempty W] {H : SimpleGraph W} :
    ω (G □ H) = max (ω G) (ω H) := by
  sorry

/-!
19. The clique number of the hypercube `Q[n]` is `1` for `n = 0` and `2`
otherwise. (There are easier ways to prove this, for instance once we have colourings
we could use a two-colouring to prove `ω Q[n] ≤ 2`, but we can also use the result of
the previous exercise.)
-/
lemma cliqueNum_hypercube' {n : ℕ} : ω Q[n] = if n = 0 then 1 else 2 := by
  sorry

/-!
The next few exercises are on independent sets, Ramsey numbers, Kneser graphs and
Mycielskians.
-/
/-!
20. Show that the Paley graph on `17` vertices has independence number `3`. (As in
the chapter, rewrite with `cliqueFree_compl` before using `decide` or
`native_decide`.) Together with exercise 3 this shows that there is a graph on `17`
vertices with no `4`-clique and no independent set of size `4`, so the Ramsey number
`R(4, 4)` is at least `18`. (In fact `R(4, 4) = 18`.)
-/
example : ⍺ (paleyGraph (ZMod 17)) = 3 := by
  sorry

/-!
21. Show that a clique and an independent set share at most one vertex, and deduce
that `ω G + ⍺ G ≤ Nat.card V + 1` in any finite graph.
-/
lemma cliqueNum_add_indepNum_le' [Finite V] : ω G + ⍺ G ≤ Nat.card V + 1 := by
  sorry

/-!
22. Show that any graph on at least `6` vertices contains a triangle or an
independent set of size `3`, so that `R(3, 3) = 6`. (Hint: suppose not, and apply
`degree_le_indepNum_of_triangleFree` to both `G` and `Gᶜ`, bounding both
independence numbers with `CliqueFree.cliqueNum_le`. Mathlib's `degree_compl`
relates the degrees of a vertex in `G` and `Gᶜ`.)
-/
theorem not_cliqueFree_three_and_indepSetFree_three' [Fintype V]
    (h : 6 ≤ Fintype.card V) : ¬ (G.CliqueFree 3 ∧ G.IndepSetFree 3) := by
  sorry

/-!
23. Show that the Kneser graph `Kn[n, 1]` is isomorphic to the complete graph `K[n]`.
(Its vertices are the singletons `{a}`, and distinct singletons are disjoint.)
-/
example (n : ℕ) : Nonempty (Kn[n, 1] ≃g K[n]) := by
  sorry

/-!
24. Compute the clique number of the Mycielskian of the edgeless graph `⊥`. The
answer depends on whether `V` is empty. If `V` is empty then `mμ[⊥]` has only the
vertex `none`, so its clique number is `1`. If `V` is nonempty then `none` and `v ᵣ`
are adjacent and `mμ[⊥]` is triangle-free, so its clique number is `2`.
-/
lemma cliqueNum_mycielskian_bot_of_isEmpty' [IsEmpty V] :
    ω mμ[(⊥ : SimpleGraph V)] = 1 := by
  sorry

lemma cliqueNum_mycielskian_bot' [Finite V] [Nonempty V] :
    ω mμ[(⊥ : SimpleGraph V)] = 2 := by
  sorry

/-!
The last few exercises are on independent sets in complete bipartite graphs (and
their Mycielskians).
-/
/-!
25. In a complete bipartite graph the non-neighbours of a left vertex are precisely
the left part, and similarly for right vertices.
-/
lemma completeBipartiteGraph.not_adj_inl' {V W : Type*} {v : V} {x : V ⊕ W} :
    ¬ (completeBipartiteGraph V W).Adj (Sum.inl v) x ↔
      x ∈ Set.range (Sum.inl : V → V ⊕ W) := by
  sorry

lemma completeBipartiteGraph.not_adj_inr' {V W : Type*} {w : W} {x : V ⊕ W} :
    ¬ (completeBipartiteGraph V W).Adj (Sum.inr w) x ↔
      x ∈ Set.range (Sum.inr : W → V ⊕ W) := by
  sorry

/-!
26. An independent set of a complete bipartite graph is contained entirely in the
left part or entirely in the right part: if it contains a left vertex then all its
vertices are non-neighbours of that vertex, so all lie in the left part.
-/
lemma completeBipartiteGraph.isIndepSet_subset_left_or_right' {V W : Type*}
    {s : Set (V ⊕ W)} (hs : (completeBipartiteGraph V W).IsIndepSet s) :
    s ⊆ Set.range Sum.inl ∨ s ⊆ Set.range Sum.inr := by
  sorry

/-!
27. Any `Finset` contained in the range of a function `f : α → β` with finite
domain has at most `Nat.card α` elements. In particular a `Finset (V ⊕ W)` contained
in the left part has at most `Nat.card V` elements (and similarly on the right),
since the left part is the range of `Sum.inl`.
-/
lemma card_le_of_subset_range' {α β : Type*} [Finite α] {f : α → β} {s : Finset β}
    (h : ↑s ⊆ Set.range f) : #s ≤ Nat.card α := by
  sorry

/-!
28. Any set of vertices contained in one part of a complete bipartite graph is
independent, since a part contains no edges (we only need this for the right part).
-/
lemma completeBipartiteGraph.isIndepSet_of_subset_range_inr' {V W : Type*}
    {s : Set (V ⊕ W)} (h : s ⊆ Set.range (Sum.inr : W → V ⊕ W)) :
    (completeBipartiteGraph V W).IsIndepSet s := by
  sorry

/-!
29. The independence number of a complete bipartite graph is the size of the larger
part; we state this as `⍺ K[a, b] = b` when `a ≤ b`. The right part is a `b`-element
independent set, and by exercises 26 and 27 no independent set is larger.
-/
theorem completeBipartiteGraph.indepNum_eq' {a b : ℕ} (h : a ≤ b) :
    ⍺ K[a, b] = b := by
  sorry

/-!
If we want to bound the independence number of the Mycielskian of a complete
bipartite graph we need a bound on the size of any independent set `s` of `K[a, b]`
plus the size of the complement of its open neighbourhood `N(s)ᶜ`. We give this bound
in the next exercise. The last two exercises use `le_indepNum_mycielskian` and
`mycielskian_indepSet_card_le` from the starred section
[Independence Number of the Mycielskian*](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-independence-number-of-the-mycielskian).
-/
/-!
30. Any independent set `s` of `K[a, b]` (with `a ≤ b`) satisfies
`#s + #N(s)ᶜ ≤ 2 * b`. We state this with an abstract Finset `t` in place of
`N(s)ᶜ`, characterized by its membership property, so that the lemma applies
whatever decidability instances `N(s)ᶜ` is written with. If `s` is empty then `t`
is all `a + b` vertices; otherwise `s` lies in a single part (exercise 26) and
`t` lies in the same part (every vertex of the other part is a neighbour of any
vertex of `s`), so each has size at most that of the part.
-/
lemma completeBipartiteGraph.indepSet_card_add_le' {a b : ℕ} (hab : a ≤ b)
    {s t : Finset (Fin a ⊕ Fin b)} (hs : K[a, b].IsIndepSet ↑s)
    (ht : ∀ x, x ∈ t ↔ ∀ y ∈ s, ¬ K[a, b].Adj y x) :
    #s + #t ≤ 2 * b := by
  sorry

/-!
31. The independence number of the Mycielskian of `K[a, b]` is `2 * b` whenever
`a ≤ b` and `b ≠ 0`: the right part `B` is an independent set with `B ⊆ N(B)ᶜ`,
so it contributes at least `2 * b`, and no independent set does better by the
previous lemma. (Note that `b ≠ 0` is needed: `mμ[K[0, 0]]` still has the vertex
`none`, so its independence number is `1`.)
-/
theorem indepNum_mycielskian_completeBipartite' {a b : ℕ} [NeZero b] (h : a ≤ b) :
    ⍺ mμ[K[a, b]] = 2 * b := by
  sorry

/-! SOLUTIONS -/

/-!
1. Show that any finite subset `t` of a clique `s` is a `#t`-clique.
-/
example {s : Set V} {t : Finset V} (hc : G.IsClique s) (h : ↑t ⊆ s) :
    G.IsNClique #t t :=
  ⟨hc.subset h, rfl⟩

/-!
2. Show that `{0, 1, 2}` is a triangle in the Paley graph on `17` vertices.
-/
example : (paleyGraph (ZMod 17)).IsNClique 3 {0, 1, 2} := by
  decide

/-!
3. Show that the Paley graph on `17` vertices is `4`-clique free. (Although `decide`
should be able to prove this it will probably time-out; you may want to use
`native_decide` instead.)
-/
lemma paleyGraph_seventeen_cliqueFree_four :
    (paleyGraph (ZMod 17)).CliqueFree 4 := by
  native_decide

/-!
4. Show that a set of vertices is a clique in `G` if and only if it is an independent
set in the complement of `G`. (Mathlib has this as `isIndepSet_compl`, but prove it
directly from the definitions, using `compl_adj`.)
-/
example {s : Set V} : G.IsClique s ↔ Gᶜ.IsIndepSet s := by
  constructor
  · -- distinct vertices of a clique are adjacent in `G`, so not adjacent in `Gᶜ`
    intro h x hx y hy hne hadj
    exact ((compl_adj G x y).mp hadj).2 (h hx hy hne)
  · -- if distinct `x`, `y` were not adjacent in `G` they would be adjacent in `Gᶜ`
    intro h x hx y hy hne
    by_contra hnadj
    exact h hx hy hne ((compl_adj G x y).mpr ⟨hne, hnadj⟩)

/-!
5. Show that if `G` is `m`-clique-free and `m ≤ n` then `G` is also `n`-clique-free.
-/
example {m n : ℕ} (h : G.CliqueFree m) (hmn : m ≤ n) : G.CliqueFree n :=
  h.mono hmn

/-!
6. Show that the clique number is monotone: if `G ≤ H` then `ω G ≤ ω H`. (There is
a one-line proof using a lemma from the chapter, and a direct proof using
`exists_isNClique_cliqueNum`.)
-/
lemma cliqueNum_mono [Finite V] {H : SimpleGraph V} (h : G ≤ H) : ω G ≤ ω H :=
  -- `G ≤ H` gives a homomorphism `Hom.ofLE h : G →g H`, so this is a special case of
  -- `Hom.cliqueNum_le`. Alternatively, directly: a clique `s` in `G` achieving the
  -- clique number of `G` is also a clique in `H`, so its size is at most `ω H`:
  -- `obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum; exact (hs.mono h).le_cliqueNum`
  (Hom.ofLE h).cliqueNum_le

/-!
7. Show that the clique number of the Paley graph on `17` vertices is `3`.
(Recall we have: `IsNClique.cliqueNum_eq_of_cliqueFree` so we just need to give an
example of a `3`-clique and show that the graph is `4`-clique free.)
-/
example : ω (paleyGraph (ZMod 17)) = 3 := by
  -- the Paley graph on 17 vertices is 4-cliquefree (exercise 3)
  have h4 : (paleyGraph (ZMod 17)).CliqueFree 4 :=
    paleyGraph_seventeen_cliqueFree_four
  -- and it contains a triangle (exercise 2)
  have h3 : (paleyGraph (ZMod 17)).IsNClique 3 {0, 1, 2} := by decide
  exact h3.cliqueNum_eq_of_cliqueFree h4

/-!
In the next few exercises we look at the clique number of graph products starting
with the tensor product `G ⊗g H`. Recall that two vertices `(v₁, w₁), (v₂, w₂)` of
the tensor product are adjacent if and only if `G.Adj v₁ v₂` and `H.Adj w₁ w₂`.
-/
/-!
8. Unlike the junk value `⍺ pathNat₁ = 0` of
[Independence Number of the Infinite Path on ℕ](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-independence-number-of-the-infinite-path-on),
the clique number of the infinite path is an honest value. Show that
`ω pathNat₁ = 2`.
-/
example : ω pathNat₁ = 2 := by
  -- `pathNat₁` is triangle-free: adjacent vertices have different parity
  have h3 : pathNat₁.CliqueFree 3 := by
    intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht.card_eq
    have h1 : pathNat₁.Adj a b := ht.isClique (by grind) (by grind) hab
    have h2 : pathNat₁.Adj a c := ht.isClique (by grind) (by grind) hac
    have h3 : pathNat₁.Adj b c := ht.isClique (by grind) (by grind) hbc
    grind
  -- the edge `{0, 1}` is a `2`-clique, and `IsNClique.cliqueNum_eq_of_cliqueFree`
  -- needs no finiteness: `h3` bounds the size of every clique
  have h2 : pathNat₁.IsNClique 2 {0, 1} := is2Clique_pair_iff.mpr (by decide)
  exact h2.cliqueNum_eq_of_cliqueFree h3

/-!
9. The first projection of a clique in the tensor product `G ⊗g H` is a clique in
`G`.
-/
example {W : Type*} {H : SimpleGraph W} {s : Set (V × W)}
    (h : (G ⊗g H).IsClique s) : G.IsClique (Prod.fst '' s) := by
  -- take two distinct vertices in the image, lifted to `(v₁, w₁), (v₂, w₂) ∈ s`
  rintro _ ⟨⟨v₁, w₁⟩, hp, rfl⟩ _ ⟨⟨v₂, w₂⟩, hq, rfl⟩ hne
  -- the lifts are distinct, so adjacent; adjacency in `G ⊗g H` gives `G.Adj v₁ v₂`
  exact (h hp hq (fun he => hne (congrArg Prod.fst he))).1

/-!
10. If `G` is `n`-clique-free then so is its tensor product `G ⊗g H` with any graph
`H`.
-/
lemma CliqueFree.tensorProd_left {W : Type*} {H : SimpleGraph W} {n : ℕ}
    (h : G.CliqueFree n) : (G ⊗g H).CliqueFree n :=
  -- unlike the box product, the first projection is a homomorphism `G ⊗g H →g G`
  -- (`tensorProd.fstHom`), so it maps any `n`-clique to an `n`-clique of `G`
  h.of_hom tensorProd.fstHom

/-!
11. The `j`-th projection of a clique in the indexed tensor product `⨂g i, G i` is a
clique in `G j`.
-/
example {ι : Type*} {V : ι → Type*} {G : (i : ι) → SimpleGraph (V i)} (j : ι)
    {s : Set ((i : ι) → V i)} (h : (⨂g i, G i).IsClique s) :
    (G j).IsClique ((· j) '' s) := by
  rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩ hne
  -- `f` and `g` differ at `j`, so are distinct, hence adjacent in every coordinate
  have hadj := h hf hg (fun he => hne (congrFun he j))
  rw [piTensorProd_adj] at hadj
  exact hadj.1 j

/-!
12. The clique number of `G ⊗g H` is `min (ω G) (ω H)`. (Hint: for the lower bound,
let `m = min (ω G) (ω H)` and use `not_cliqueFree_iff_top_isContained` to find
copies of `K[m]` in both `G` and `H`. Pair them with `tensorProd.prod` to get a
homomorphism `K[m] →g G ⊗g H`.)
-/
lemma cliqueNum_tensorProd {W : Type*} [Finite V] [Finite W] {H : SimpleGraph W} :
    ω (G ⊗g H) = min (ω G) (ω H) := by
  classical
  apply le_antisymm
  · -- upper bound: both projections `tensorProd.fstHom`, `tensorProd.sndHom` are
    -- homomorphisms, so the clique number cannot exceed either factor's
    exact le_min tensorProd.fstHom.cliqueNum_le tensorProd.sndHom.cliqueNum_le
  · -- lower bound: with `m := min (ω G) (ω H)`, neither `G` nor `H` is
    -- `m`-clique-free (each has a clique of size at least `m`)
    set m := min (ω G) (ω H)
    obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    obtain ⟨t, ht⟩ := H.exists_isNClique_cliqueNum
    have hG : ¬ G.CliqueFree m := fun hf => hf.mono (min_le_left ..) s hs
    have hH : ¬ H.CliqueFree m := fun hf => hf.mono (min_le_right ..) t ht
    -- so both contain a copy of the complete graph on `Fin m`
    rw [not_cliqueFree_iff_top_isContained] at hG hH
    obtain ⟨f⟩ := hG
    obtain ⟨g⟩ := hH
    -- pairing the two copies gives a homomorphism from `⊤` into `G ⊗g H`
    simpa using (tensorProd.prod f.toHom g.toHom).cliqueNum_le

/-!
We now turn to the box product `G □ H`. Recall that two vertices `(v₁, w₁), (v₂, w₂)`
of the box product are adjacent if and only if either `G.Adj v₁ v₂` and `w₁ = w₂`, or
`v₁ = v₂` and `H.Adj w₁ w₂`. This implies that cliques are always constant in one
coordinate.
-/
/-!
13. A clique `s` in `G` gives a "row" clique in the box product `G □ H` (so long as
there is a vertex `h₀` in `H` to fix the second coordinate).
-/
example {W : Type*} {H : SimpleGraph W} {s : Set V} (h₀ : W) (h : G.IsClique s) :
    (G □ H).IsClique ((·, h₀) '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
  -- both vertices share the second coordinate `h₀`, so they are adjacent in `G □ H`
  -- precisely because `a` and `b` are adjacent in `G`.
  rw [boxProd_adj]
  exact Or.inl ⟨h ha hb (fun he => hne (by rw [he])), rfl⟩

/-!
14. In any box product `G □ H` with nonempty second factor we have `ω G ≤ ω (G □ H)`:
the embedding `boxProdLeft` can transport a maximum clique of `G` to a clique of the
same size in `G □ H`.
-/
lemma cliqueNum_boxProd_le_left {W : Type*} [Finite V] [Finite W] [Nonempty W]
    {H : SimpleGraph W} : ω G ≤ ω (G □ H) :=
  (boxProdLeft G H (Classical.arbitrary W)).toHom.cliqueNum_le

/-!
15. A clique of `G □ H` containing a "horizontal" edge (two vertices sharing their
second coordinate) is constant in the second coordinate.
-/
lemma IsClique.boxProd_snd_eq {W : Type*} {H : SimpleGraph W} {s : Set (V × W)}
    {x y : V × W} (ht : (G □ H).IsClique s) (hx : x ∈ s) (hy : y ∈ s)
    (hG : G.Adj x.1 y.1) (hsnd : x.2 = y.2) : ∀ z ∈ s, z.2 = x.2 := by
  intro z hz
  -- `z` is equal or adjacent to both `x` and `y`; if `z` differed from `x` in the
  -- second coordinate it would share its first coordinate with both, forcing
  -- `x.1 = y.1`, which contradicts `G.Adj x.1 y.1`
  have h1 := ht hz hx
  have h2 := ht hz hy
  grind [boxProd_adj]

/-!
16. `Prod.fst` is injective on a clique of `G □ H` whose vertices all share the same
second coordinate, so such a clique projects to a clique of `G` of the same size.
-/
lemma IsNClique.boxProd_image_fst {W : Type*} [DecidableEq V] {H : SimpleGraph W}
    {m : ℕ} {t : Finset (V × W)} {w : W} (ht : (G □ H).IsNClique m t)
    (hconst : ∀ z ∈ t, z.2 = w) : G.IsNClique m (t.image Prod.fst) := by
  -- it suffices to show that `Prod.fst` preserves adjacency on `t` (injectivity on
  -- the clique `t` is then automatic); an edge of `t` cannot be vertical, since the
  -- vertices of `t` agree in the second coordinate
  refine ht.image_of_adj fun p hp q hq h => ?_
  grind [boxProd_adj]

/-!
17. A clique of `G □ H` containing a "horizontal" edge has size at most `ω G`.
-/
lemma boxProd_card_le_left {W : Type*} [Finite V] {H : SimpleGraph W} {m : ℕ}
    {t : Finset (V × W)} {x y : V × W} (ht : (G □ H).IsNClique m t) (hx : x ∈ t)
    (hy : y ∈ t) (hG : G.Adj x.1 y.1) (hsnd : x.2 = y.2) : m ≤ ω G := by
  classical
  -- every vertex of `t` shares the second coordinate `x.2`
  have hconst : ∀ z ∈ t, z.2 = x.2 :=
    fun z hz => ht.isClique.boxProd_snd_eq hx hy hG hsnd z hz
  exact (ht.boxProd_image_fst hconst).le_cliqueNum

/-!
18. The clique number of `G □ H` is `max (ω G) (ω H)` (for finite nonempty graphs).
-/
lemma cliqueNum_boxProd {W : Type*} [Finite V] [Finite W] [Nonempty V]
    [Nonempty W] {H : SimpleGraph W} :
    ω (G □ H) = max (ω G) (ω H) := by
  classical
  apply le_antisymm
  · -- upper bound: a maximum clique has an edge, horizontal or vertical
    obtain ⟨t, ht⟩ := (G □ H).exists_isNClique_cliqueNum
    rcases Nat.lt_or_ge t.card 2 with hsmall | hbig
    · -- a clique of size at most one is bounded since `ω G ≥ 1`
      grind [ht.card_eq, one_le_cliqueNum]
    · -- pick two distinct adjacent vertices `x`, `y`
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hbig
      have hadj := ht.isClique hx hy hxy
      rw [boxProd_adj] at hadj
      rcases hadj with ⟨hG, hsnd⟩ | ⟨hH, hfst⟩
      · -- horizontal edge: bound the clique directly by `ω G`
        exact (boxProd_card_le_left ht hx hy hG hsnd).trans (le_max_left _ _)
      · -- vertical edge: swap the factors with `boxProdComm` to turn it into a
        -- horizontal edge of `H □ G`, then reuse the same bound, now giving `ω H`
        have htH := ht.mapHom (boxProdComm ..).toHom
        exact (boxProd_card_le_left htH (Finset.mem_image_of_mem _ hx)
          (Finset.mem_image_of_mem _ hy) hH hfst).trans (le_max_right _ _)
  · -- lower bound: a row realizes `ω G` (`boxProdLeft`) and a column realizes `ω H`
    -- (`boxProdRight`); both are graph embeddings into `G □ H`
    exact max_le cliqueNum_boxProd_le_left
      (boxProdRight G H (Classical.arbitrary V)).toHom.cliqueNum_le

/-!
19. The clique number of the hypercube `Q[n]` is `1` for `n = 0` and `2`
otherwise. (There are easier ways to prove this, for instance once we have colourings
we could use a two-colouring to prove `ω Q[n] ≤ 2`, but we can also use the result of
the previous exercise.)
-/
lemma cliqueNum_hypercube {n : ℕ} : ω Q[n] = if n = 0 then 1 else 2 := by
  induction n with
  | zero =>
    apply one_le_cliqueNum.antisymm' (by simp)
  | succ n ih =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    have := cliqueNum_boxProd (G := Q[n]) (H := (⊤ : SimpleGraph Bool))
    rw [ih, cliqueNum_top] at this
    cases n <;> simpa

/-!
The next few exercises are on independent sets, Ramsey numbers, Kneser graphs and
Mycielskians.
-/
/-!
20. Show that the Paley graph on `17` vertices has independence number `3`. (As in
the chapter, rewrite with `cliqueFree_compl` before using `decide` or
`native_decide`.) Together with exercise 3 this shows that there is a graph on `17`
vertices with no `4`-clique and no independent set of size `4`, so the Ramsey number
`R(4, 4)` is at least `18`. (In fact `R(4, 4) = 18`.)
-/
example : ⍺ (paleyGraph (ZMod 17)) = 3 := by
  -- `{0, 3, 6}` is independent since `3` is not a square mod `17`
  have h3 : (paleyGraph (ZMod 17)).IsNIndepSet 3 {0, 3, 6} := by decide
  exact h3.indepNum_eq_of_indepSetFree (by rw [← cliqueFree_compl]; native_decide)

/-!
21. Show that a clique and an independent set share at most one vertex, and deduce
that `ω G + ⍺ G ≤ Nat.card V + 1` in any finite graph.
-/
lemma cliqueNum_add_indepNum_le [Finite V] : ω G + ⍺ G ≤ Nat.card V + 1 := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨t, ht⟩ := G.exists_isNIndepSet_indepNum
  -- two distinct common vertices would be both adjacent and non-adjacent
  have hst : #(s ∩ t) ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    by_contra hne
    simp only [Finset.mem_inter] at hx hy
    exact ht.isIndepSet hx.2 hy.2 hne (hs.isClique hx.1 hy.1 hne)
  -- inclusion-exclusion, and `s ∪ t` has at most `Nat.card V` elements
  have := Finset.card_union_add_card_inter s t
  have := (s ∪ t).card_le_univ
  rw [← hs.card_eq, ← ht.card_eq, Nat.card_eq_fintype_card]
  grind

/-!
22. Show that any graph on at least `6` vertices contains a triangle or an
independent set of size `3`, so that `R(3, 3) = 6`. (Hint: suppose not, and apply
`degree_le_indepNum_of_triangleFree` to both `G` and `Gᶜ`, bounding both
independence numbers with `CliqueFree.cliqueNum_le`. Mathlib's `degree_compl`
relates the degrees of a vertex in `G` and `Gᶜ`.)
-/
theorem not_cliqueFree_three_and_indepSetFree_three [Fintype V]
    (h : 6 ≤ Fintype.card V) : ¬ (G.CliqueFree 3 ∧ G.IndepSetFree 3) := by
  classical
  rintro ⟨h3, hi3⟩
  -- `Gᶜ` is also triangle-free, since `G` has no independent set of size `3`
  have hc3 : Gᶜ.CliqueFree 3 := (G.cliqueFree_compl).mpr hi3
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by grind)
  -- so `v` has degree at most `⍺ G` in `G` and at most `⍺ Gᶜ` in `Gᶜ`
  have h1 := degree_le_indepNum_of_triangleFree h3 v
  have h2 := degree_le_indepNum_of_triangleFree hc3 v
  -- and both independence numbers are at most `2`
  have hα : ⍺ G ≤ 2 := by simpa using hc3.cliqueNum_le
  have hαc : ⍺ Gᶜ ≤ 2 := by simpa using h3.cliqueNum_le
  -- but the two degrees add up to `Fintype.card V - 1 ≥ 5`
  have := G.degree_compl v
  grind

/-!
23. Show that the Kneser graph `Kn[n, 1]` is isomorphic to the complete graph `K[n]`.
(Its vertices are the singletons `{a}`, and distinct singletons are disjoint.)
-/
example (n : ℕ) : Nonempty (Kn[n, 1] ≃g K[n]) := by
  -- the map `a ↦ {a}` is a bijection from `Fin n` to the vertices of `Kn[n, 1]`
  let f : Fin n → {s : Finset (Fin n) // #s = 1} := fun a => ⟨{a}, card_singleton a⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => by simpa [f] using congrArg Subtype.val h, fun s => ?_⟩
    obtain ⟨a, ha⟩ := card_eq_one.mp s.2
    exact ⟨a, Subtype.ext ha.symm⟩
  refine ⟨⟨(Equiv.ofBijective f hf).symm, ?_⟩⟩
  -- it remains to check that adjacency is preserved
  intro a b
  obtain ⟨a, rfl⟩ := hf.2 a
  obtain ⟨b, rfl⟩ := hf.2 b
  simp [f]

/-!
24. Compute the clique number of the Mycielskian of the edgeless graph `⊥`. The
answer depends on whether `V` is empty. If `V` is empty then `mμ[⊥]` has only the
vertex `none`, so its clique number is `1`. If `V` is nonempty then `none` and `v ᵣ`
are adjacent and `mμ[⊥]` is triangle-free, so its clique number is `2`.
-/
lemma cliqueNum_mycielskian_bot_of_isEmpty [IsEmpty V] :
    ω mμ[(⊥ : SimpleGraph V)] = 1 :=
  -- `mμ[⊥]` has exactly one vertex, `none`
  one_le_cliqueNum.antisymm'
    (by simpa using mμ[(⊥ : SimpleGraph V)].cliqueNum_le_natCard)

lemma cliqueNum_mycielskian_bot [Finite V] [Nonempty V] :
    ω mμ[(⊥ : SimpleGraph V)] = 2 := by
  classical
  -- `none` and `v ᵣ` are adjacent, giving a `2`-clique
  obtain ⟨v⟩ := ‹Nonempty V›
  have h2 : mμ[(⊥ : SimpleGraph V)].IsNClique 2 {none, v ᵣ} :=
    is2Clique_pair_iff.mpr (by simp)
  -- moreover `mμ[⊥]` is `3`-clique-free since `⊥` is trivially triangle-free
  exact h2.cliqueNum_eq_of_cliqueFree (cliqueFree_bot (by norm_num)).mycielskian

/-!
The last few exercises are on independent sets in complete bipartite graphs (and
their Mycielskians).
-/
/-!
25. In a complete bipartite graph the non-neighbours of a left vertex are precisely
the left part, and similarly for right vertices.
-/
lemma completeBipartiteGraph.not_adj_inl {V W : Type*} {v : V} {x : V ⊕ W} :
    ¬ (completeBipartiteGraph V W).Adj (Sum.inl v) x ↔
      x ∈ Set.range (Sum.inl : V → V ⊕ W) := by
  cases x <;> simp

lemma completeBipartiteGraph.not_adj_inr {V W : Type*} {w : W} {x : V ⊕ W} :
    ¬ (completeBipartiteGraph V W).Adj (Sum.inr w) x ↔
      x ∈ Set.range (Sum.inr : W → V ⊕ W) := by
  cases x <;> simp

/-!
26. An independent set of a complete bipartite graph is contained entirely in the
left part or entirely in the right part: if it contains a left vertex then all its
vertices are non-neighbours of that vertex, so all lie in the left part.
-/
lemma completeBipartiteGraph.isIndepSet_subset_left_or_right {V W : Type*}
    {s : Set (V ⊕ W)} (hs : (completeBipartiteGraph V W).IsIndepSet s) :
    s ⊆ Set.range Sum.inl ∨ s ⊆ Set.range Sum.inr := by
  by_cases h : ∃ v, Sum.inl v ∈ s
  · obtain ⟨v, hv⟩ := h
    exact Or.inl fun x hx => not_adj_inl.mp fun hadj => hs hv hx hadj.ne hadj
  · refine Or.inr fun x hx => ?_
    rcases x with x | x
    · exact absurd ⟨x, hx⟩ h
    · exact Set.mem_range_self x

/-!
27. Any `Finset` contained in the range of a function `f : α → β` with finite
domain has at most `Nat.card α` elements. In particular a `Finset (V ⊕ W)` contained
in the left part has at most `Nat.card V` elements (and similarly on the right),
since the left part is the range of `Sum.inl`.
-/
lemma card_le_of_subset_range {α β : Type*} [Finite α] {f : α → β} {s : Finset β}
    (h : ↑s ⊆ Set.range f) : #s ≤ Nat.card α := by
  classical
  have := Fintype.ofFinite α
  -- `s` is contained in the image of `univ` under `f`, which has at most `#univ`
  -- elements
  have hsub : s ⊆ univ.image f := fun x hx => by simpa using h hx
  simpa using (card_le_card hsub).trans card_image_le

/-!
28. Any set of vertices contained in one part of a complete bipartite graph is
independent, since a part contains no edges (we only need this for the right part).
-/
lemma completeBipartiteGraph.isIndepSet_of_subset_range_inr {V W : Type*}
    {s : Set (V ⊕ W)} (h : s ⊆ Set.range (Sum.inr : W → V ⊕ W)) :
    (completeBipartiteGraph V W).IsIndepSet s := by
  intro u hu v hv hne hadj
  obtain ⟨x, rfl⟩ := h hu
  obtain ⟨y, rfl⟩ := h hv
  simp at hadj

/-!
29. The independence number of a complete bipartite graph is the size of the larger
part; we state this as `⍺ K[a, b] = b` when `a ≤ b`. The right part is a `b`-element
independent set, and by exercises 26 and 27 no independent set is larger.
-/
theorem completeBipartiteGraph.indepNum_eq {a b : ℕ} (h : a ≤ b) :
    ⍺ K[a, b] = b := by
  apply IsNIndepSet.indepNum_eq_of_indepSetFree (s := univ.map .inr)
  · exact ⟨completeBipartiteGraph.isIndepSet_of_subset_range_inr (by simp), by simp⟩
  · intro s hs
    rcases completeBipartiteGraph.isIndepSet_subset_left_or_right hs.isIndepSet
      with h | h <;> grind [hs.card_eq, card_le_of_subset_range h, Nat.card_fin]

/-!
If we want to bound the independence number of the Mycielskian of a complete
bipartite graph we need a bound on the size of any independent set `s` of `K[a, b]`
plus the size of the complement of its open neighbourhood `N(s)ᶜ`. We give this bound
in the next exercise. The last two exercises use `le_indepNum_mycielskian` and
`mycielskian_indepSet_card_le` from the starred section
[Independence Number of the Mycielskian*](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-independence-number-of-the-mycielskian).
-/
/-!
30. Any independent set `s` of `K[a, b]` (with `a ≤ b`) satisfies
`#s + #N(s)ᶜ ≤ 2 * b`. We state this with an abstract Finset `t` in place of
`N(s)ᶜ`, characterized by its membership property, so that the lemma applies
whatever decidability instances `N(s)ᶜ` is written with. If `s` is empty then `t`
is all `a + b` vertices; otherwise `s` lies in a single part (exercise 26) and
`t` lies in the same part (every vertex of the other part is a neighbour of any
vertex of `s`), so each has size at most that of the part.
-/
lemma completeBipartiteGraph.indepSet_card_add_le {a b : ℕ} (hab : a ≤ b)
    {s t : Finset (Fin a ⊕ Fin b)} (hs : K[a, b].IsIndepSet ↑s)
    (ht : ∀ x, x ∈ t ↔ ∀ y ∈ s, ¬ K[a, b].Adj y x) :
    #s + #t ≤ 2 * b := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · -- `s = ∅` : `t` has at most `a + b ≤ 2 * b` vertices
    grind [Fintype.card_sum, Fintype.card_fin, t.card_le_univ]
  rcases completeBipartiteGraph.isIndepSet_subset_left_or_right hs with hL | hR
  · -- `s` lies in the left part, and so does `t`
    obtain ⟨y, rfl⟩ := hL (mem_coe.mpr hx)
    have h1 : #s ≤ a := by simpa using card_le_of_subset_range hL
    have h2 : #t ≤ a := by
      simpa using card_le_of_subset_range fun z hz =>
        completeBipartiteGraph.not_adj_inl.mp ((ht z).mp (mem_coe.mp hz) _ hx)
    grind
  · -- `s` lies in the right part, and so does `t`
    obtain ⟨y, rfl⟩ := hR (mem_coe.mpr hx)
    have h1 : #s ≤ b := by simpa using card_le_of_subset_range hR
    have h2 : #t ≤ b := by
      simpa using card_le_of_subset_range fun z hz =>
        completeBipartiteGraph.not_adj_inr.mp ((ht z).mp (mem_coe.mp hz) _ hx)
    grind

/-!
31. The independence number of the Mycielskian of `K[a, b]` is `2 * b` whenever
`a ≤ b` and `b ≠ 0`: the right part `B` is an independent set with `B ⊆ N(B)ᶜ`,
so it contributes at least `2 * b`, and no independent set does better by the
previous lemma. (Note that `b ≠ 0` is needed: `mμ[K[0, 0]]` still has the vertex
`none`, so its independence number is `1`.)
-/
theorem indepNum_mycielskian_completeBipartite {a b : ℕ} [NeZero b] (h : a ≤ b) :
    ⍺ mμ[K[a, b]] = 2 * b := by
  refine le_antisymm ?_ ?_
  · -- `≤` : a maximum independent set `T` of `mμ[K[a, b]]` satisfies
    -- `#T ≤ #A + #N(A)ᶜ ≤ 2 * b`, where `A` is the left part of `T`
    obtain ⟨T, hT⟩ := (mμ[K[a, b]]).exists_isNIndepSet_indepNum
    rw [← hT.card_eq]
    exact le_trans (mycielskian_indepSet_card_le hT.isIndepSet)
      (completeBipartiteGraph.indepSet_card_add_le h
        (isIndepSet_preimage_left_finset hT.isIndepSet)
        fun _ => by simp)
  · -- `≥` : the right part is an independent set `s` with `#s = b` and `s ⊆ N(s)ᶜ`
    have hind : K[a, b].IsIndepSet (↑(univ.map .inr : Finset (Fin a ⊕ Fin b))) :=
      completeBipartiteGraph.isIndepSet_of_subset_range_inr (by simp)
    refine le_trans ?_ (le_indepNum_mycielskian hind)
    have h1 : #(univ.map .inr : Finset (Fin a ⊕ Fin b)) = b := by simp
    have h2 := card_le_card (subset_compl_openNeighborhoodFinset hind)
    grind

/-! END SOLUTIONS -/

end SimpleGraph
