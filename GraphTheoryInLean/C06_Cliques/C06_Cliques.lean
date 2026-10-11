import GraphTheoryInLean.C04_Decidability_Finiteness_and_Degrees.C04_Decidability_Finiteness_and_Degrees
import GraphTheoryInLean.C05_Maps.Exercises
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SetFamily.KruskalKatona

namespace SimpleGraph
open scoped SimpleGraph
section cliques
variable {V : Type*} {G : SimpleGraph V}

/-!
Cliques (sets of pairwise adjacent vertices) and independent sets (sets of pairwise
non-adjacent vertices) are among the most basic substructures of a graph, and the
sizes of the largest ones, the *clique number* and the *independence number*, are two
of the most studied graph parameters. The archetypal question in extremal graph
theory asks how many edges a graph can have without containing a large clique, and,
as we will see in the next chapter, the clique number is a natural lower bound for
the chromatic number. The Mycielskian is important precisely because it shows how
bad this bound can be: it raises the chromatic number while leaving the clique
number unchanged.

In this chapter we introduce Mathlib's cliques (`IsClique`, `IsNClique`) and
clique-free graphs (`CliqueFree`), and show that graph homomorphisms map cliques to
cliques. Mathlib has no `Decidable` instance for `CliqueFree`, so we build one from
the finset of all `n`-cliques. We then introduce the clique number (`cliqueNum`),
independent sets (`IsIndepSet`) and the independence number (`indepNum`), and compute
the independence number of the Kneser graph using the Erdős–Ko–Rado theorem. Finally
we prove the well-known result that the Mycielskian preserves the clique number, and
give a formula for the independence number of the Mycielskian.

# Cliques

A *clique* in a graph is a (not necessarily finite) set of vertices that are pairwise
adjacent.
-/
#source IsClique -- abbrev IsClique (s : Set α) : Prop := s.Pairwise G.Adj

#source Pairwise -- def Pairwise (r : α → α → Prop) := ∀ ⦃i j⦄, i ≠ j → r i j

/-!
If `G ≤ H` and `s` is a clique in `G` then `s` is also a clique in `H`.
-/
#check IsClique.mono
/-!
If `s` is a clique in `G` then `s` is also a clique in the graph `G ⊔ H` (where `H`
is any other graph on the same vertex set).
-/
example {s : Set V} (h : G.IsClique s) {H : SimpleGraph V} : (G ⊔ H).IsClique s :=
  h.mono le_sup_left

/-!
If `s` is a clique in `G` then any subset of `s` is also a clique in `G`.
-/
#check IsClique.subset

example {s t : Set V} (h : G.IsClique (s ∪ t)) : G.IsClique t := by
  apply h.subset
  exact Set.subset_union_right

/-!
If `s : Set V` and `a : V` then `insert a s` is the set `{a} ∪ s`.
-/
example (s : Set V) (a : V) : insert a s = {a} ∪ s := rfl

/-!
If `s` is a clique in `G` and `a` is a vertex adjacent to every vertex in `s` that is
not equal to `a` then `insert a s` is also a clique in `G`.
-/
#check IsClique.insert

/-!
Recall that if `u ≠ v` then `edge u v` is the `SimpleGraph V` with the single edge
`s(u, v)` and so `G ⊔ edge u v` is the graph obtained by adding this edge to `G`.

If `u ≠ v` then any set of vertices `s` is a clique in `G ⊔ edge u v` if and only if
`s \ {u}` and `s \ {v}` are both cliques in `G`.
-/
#check isClique_sup_edge_of_ne_iff

/-!
# Finite Cliques

[Figure: Examples of cliques](https://jt496.github.io/GraphTheoryInLean/figures/cliques.svg)

If `s : Finset V` is a clique with `n` vertices then we call it an `n`-clique. This
is `IsNClique` in Lean, which is a structure that bundles a proof that `s` is a
clique together with a proof that `s` has cardinality `n`.

Notice that `IsClique` takes a `Set V` while `IsNClique` takes a `Finset V`. A clique
may be infinite, so `IsClique` works with sets. But an `n`-clique needs a size in
`ℕ`, and `#s` is a natural number for a finset (and computable, so `decide` and
`#eval` can use it). The field `isClique : G.IsClique s` silently coerces the finset
`s` to a set. This coercion is written `↑s` (or `(s : Set V)`), and we will see it
in many statements below, such as `G.IsIndepSet ↑s`.
-/
#source IsNClique -- structure IsNClique (n : ℕ) (s : Finset α) : Prop where
                  --                 isClique : G.IsClique s
                  --                 card_eq : #s = n
/-!
The `Finset` `{a, b}` is a 2-clique if and only if `G.Adj a b` holds.
-/
lemma is2Clique_pair_iff {a b : V} [DecidableEq V] :
    G.IsNClique 2 {a, b} ↔ G.Adj a b := by
  constructor <;> intro h
  · apply h.isClique (by grind) (by grind)
    rintro rfl
    grind [h.card_eq]
  · constructor
    · simp [h]
    · grind [h.ne]

/-!
The `Finset` `{a, b, c}` is a 3-clique if and only if `a`, `b`, and `c` are pairwise
adjacent. Notice in this and the previous lemma we need to give Lean a
`DecidableEq V` instance to be able to form the `Finset` `{a, b}` and `{a, b, c}`.
Also we don't need to assume that the vertices in the cliques are distinct because
pairwise adjacency trivially implies that they are distinct.
-/
example {a b c : V} [DecidableEq V] :
    G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c :=
  is3Clique_triple_iff

/-!
If we insert a vertex `a` into an `n`-clique `s` and `a` is adjacent to every vertex
in `s` then `insert a s` is an `(n + 1)`-clique.
-/
#check IsNClique.insert
/-!
For concrete finite graphs `decide` can check small examples directly.
-/
example : K[9].IsNClique 5 {0, 1, 3, 5, 7} := by decide

/-!
Famously the Mycielskian of any triangle-free graph is also triangle-free, so in
particular any iterated Mycielskian of the 5-cycle is triangle-free. (We will prove
this and a more general result later.)

For now we just check that a particular set of 3 vertices in `mμ^3 C[5]` is not a
3-clique.
-/
example :
    ¬ (mμ^3 C[5]).IsNClique 3 {(0 : Fin 5)ᵣᵣᵣ, (1 : Fin 5)ₗₗₗ, (2 : Fin 5)ₗᵣₗ} := by
  decide

/-!
A graph homomorphism `G →g H` is injective on any clique: distinct vertices of a
clique are adjacent, so their images are adjacent, hence distinct (since `H` is
loopless). This generalizes `Hom.injective_of_top_hom` (the case where the graph is a
clique).
-/
lemma Hom.injOn_of_isClique {W : Type*} {H : SimpleGraph W} (f : G →g H)
    {s : Set V} (hs : G.IsClique s) : Set.InjOn f s := by
  intro x hx y hy hxy
  by_contra hne
  exact H.irrefl (hxy ▸ f.map_adj (hs hx hy hne))

/-!
Next, if a map `f : V → W` is injective on an `n`-clique `s` of `G` and
sends adjacent vertices of `s` to adjacent vertices of `H` then the image of `s` is
an `n`-clique of `H`. (We will use this several times, with `f` a graph homomorphism
or a projection.)
-/
lemma IsNClique.image_of_adj {W : Type*} {H : SimpleGraph W} [DecidableEq W]
    {n : ℕ} {s : Finset V} (hs : G.IsNClique n s) {f : V → W} (hinj : Set.InjOn f s)
    (hadj : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → G.Adj x y → H.Adj (f x) (f y)) :
    H.IsNClique n (s.image f) := by
  refine ⟨?_, by rw [Finset.card_image_of_injOn hinj, hs.card_eq]⟩
  rintro _ ha _ hb hne
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  exact hadj hx hy (hs.isClique hx hy fun h => hne (by rw [h]))

/-!
Using `Hom.injOn_of_isClique` we can show that the image of an `n`-clique under a
graph homomorphism is an `n`-clique.
-/
protected lemma IsNClique.mapHom {W : Type*} {H : SimpleGraph W} [DecidableEq W]
    {n : ℕ} {s : Finset V} (hs : G.IsNClique n s) (f : G →g H) :
    H.IsNClique n (s.image f) :=
  hs.image_of_adj (f.injOn_of_isClique hs.isClique) fun _ _ _ _ h => f.map_adj h

/-!
# Clique-Free

Much of extremal graph theory is concerned with properties of graphs that do not
contain cliques of a certain size. For example, Mantel's theorem says that a
triangle-free graph on `n` vertices has at most `n ^ 2 / 4` edges.

We say that a graph `G` is *n-clique-free* if it contains no `n`-cliques.
-/
#source CliqueFree -- def CliqueFree (n : ℕ) : Prop := ∀ t, ¬G.IsNClique n t
/-!
So `¬ G.CliqueFree n` holds if and only if `G` contains an `n`-clique.
-/
example (n : ℕ) : ¬ G.CliqueFree n ↔ ∃ t, G.IsNClique n t := by
  simp [CliqueFree]

/-!
If `G ≤ H` and `H` is `n`-clique-free then so is `G`, so the property of being
`n`-clique-free is monotone downwards (in Mathlib, `Antitone`).
-/
#check CliqueFree.anti      -- G ≤ H → CliqueFree n H → CliqueFree n G
/-!
More generally, Mathlib's `CliqueFree.comap` says that if `H` contains a copy of `G`
(`G ⊑ H`, see
[Copies](https://jt496.github.io/GraphTheoryInLean/Maps/#section-copies)) and `H` is
`n`-clique-free then so is `G`. Since a copy is just an injective homomorphism, we
can ask whether injectivity is needed. It is not: a homomorphism `G →g H` is enough,
since by `IsNClique.mapHom` it maps any `n`-clique of `G` to an `n`-clique of `H`.
-/
#check CliqueFree.comap     -- G ⊑ H → CliqueFree n H → CliqueFree n G

lemma CliqueFree.of_hom {W : Type*} {H : SimpleGraph W} {n : ℕ} (f : G →g H)
    (h : H.CliqueFree n) : G.CliqueFree n :=
  fun t ht => by classical exact h _ (ht.mapHom f)

/-!
An `n`-clique is the same thing as a copy of the complete graph `K[n]`, so `G` is
`n`-clique-free exactly when it contains no copy of `K[n]`, i.e. when `G` is
`K[n]`-free in the sense of
[Copies](https://jt496.github.io/GraphTheoryInLean/Maps/#section-copies).
-/
#check not_cliqueFree_iff_top_isContained -- ¬G.CliqueFree n ↔ K[n] ⊑ G
#check cliqueFree_iff_free_top_fin        -- G.CliqueFree n ↔ K[n].Free G
end cliques

/-!
If we take any complete-multipartite graph with nonempty parts indexed by a type `ι`
then it will contain an `n`-clique if and only if the index type has cardinality at
least `n`. Notice that this result makes sense for `ι` an infinite type, so we need a
way to say that `n ≤ #ι` without assuming that `ι` is finite.

In this situation we can use `ENat.card` which is the cardinality of a type as an
extended natural number `ENat` or `ℕ∞`. (See
[Cardinality](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-cardinality)
for more details on the different ways to talk about cardinality.)
-/
#check completeMultipartiteGraph.not_cliqueFree_of_le_enatCard
/-!
Notice how this lemma requires the parts to be nonempty. Instead of a hypothesis
`∀ i, Nonempty (W i)` it takes a function `f : ∀ i, W i` choosing a vertex in each
part. Having such a choice function is equivalent to all parts being nonempty, and
it is often easier to work with. We do the same in `blowUpGraph_cliqueFree_iff`
below.

Conversely, if `ι` is finite with less than `n` elements then the graph is
`n`-clique-free. (Mathlib states this direction for a `Fintype` index.)
-/
#check cliqueFree_completeMultipartiteGraph

/-!
The blow-up of a graph `G` with nonempty parts is `n`-clique-free if and only if `G`
is `n`-clique-free.
-/
lemma blowUpGraph_cliqueFree_iff {n : ℕ} {ι : Type*} (G : SimpleGraph ι)
    (W : ι → Type*) (f : ∀ i, W i) :
    (G.blowUpGraph W).CliqueFree n ↔ G.CliqueFree n := by
  constructor <;> intro h
  · exact h.comap ⟨(Embedding.blowUp _ _ f).toCopy⟩
  · -- the projection `Sigma.fst` to the index of the part is a homomorphism
    exact h.of_hom ⟨Sigma.fst, id⟩

/-!
Note that `CliqueFree` does not have a `Decidable` instance in Mathlib, so we cannot
use `decide` or `#eval` to check if a graph is `n`-clique-free. However, there is a
computable way to enumerate all `n`-cliques in a finite graph, and this will allow us
to provide such an instance.

# The Finset of n-Cliques

If `G` is a finite graph then we can form the `Finset` of all `n`-cliques in `G`.
-/
#source cliqueFinset -- def cliqueFinset (n : ℕ) : Finset (Finset α) :=
                     --                       {s | G.IsNClique n s}

/-!
Recall our discussion of
[Set-Builder Notation](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-set-builder-notation).
The finset `G.cliqueFinset n` is `univ : Finset (Finset V)`, i.e. the powerset of
`V`, filtered for those `Finset`s that are `n`-cliques in `G`.
-/
example {V : Type*} [Fintype V] (n : ℕ) {G : SimpleGraph V} [DecidableRel G.Adj]
  [DecidableEq V] : G.cliqueFinset n =
     (Finset.univ : Finset (Finset V)).filter (G.IsNClique n · ) := rfl

/-!
This is computable so we can use `#eval` to compute the `Finset (Finset V)` of all
`n`-cliques in a finite graph `G : SimpleGraph V`.
-/
#eval C[5].cliqueFinset 2     -- {{0, 1}, {1, 2}, {2, 3}, {0, 4}, {3, 4}}
#eval mμ[K[4]].cliqueFinset 3 -- {{0ₗ, 1ₗ, 2ₗ}, {0ₗ, 1ₗ, 3ₗ},..., {1ₗ, 2ₗ, 3ᵣ}}
#eval mμ[K[4]].cliqueFinset 5 -- ∅
/-!
The `cliqueFinset` of `n`-cliques in a finite graph is empty if and only if the graph
is `n`-clique-free.
-/
#check cliqueFinset_eq_empty_iff -- G.cliqueFinset n = ∅ ↔ G.CliqueFree n
/-!
Hence we can decide if a finite graph is `n`-clique-free by checking if
`G.cliqueFinset n = ∅`.
-/
instance decidableCliqueFree {V : Type*} [Fintype V] (n : ℕ) {G : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableEq V] : Decidable (G.CliqueFree n) :=
  decidable_of_iff _ cliqueFinset_eq_empty_iff

#eval C[5].CliqueFree 3     -- true
#eval mμ[C[5]].CliqueFree 3 -- true
#eval Q[4].CliqueFree 3     -- true

section indset
variable {V : Type*} {G : SimpleGraph V}

/-!
# Clique Number

The *clique number* of a graph is the size of the largest clique in the graph. In
Mathlib this is defined as the `sSup` of the set of `n` such that there exists an
`n`-clique in the graph.
-/
#source cliqueNum -- noncomputable def cliqueNum (G : SimpleGraph α) : ℕ :=
                  --                      sSup {n | ∃ s, G.IsNClique n s}
@[inherit_doc]
scoped notation "ω" => SimpleGraph.cliqueNum
/-!
Since this is our first time seeing `sSup` we will take a moment to explain what it
is. The name `sSup` stands for *set supremum*, for `ℕ` this is the largest element of
a nonempty bounded `Set ℕ`, or `0` if the set is empty or unbounded.
-/
#check Nat.sSup_def
#check Nat.sSup_of_not_bddAbove
/-!
What this means for our definition of `cliqueNum` is that:

1. If there is no bound on the size of cliques in `G` then `G.cliqueNum = 0`. This is
   the same lossy `0`-convention we met with `Nat.card` in
   [Cardinality](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-cardinality):
   `sSup` on `ℕ` returns the genuine largest element only when its argument is
   nonempty and bounded above, and falls back to `0` otherwise.
2. If `G` has no vertices then `G.cliqueNum = 0`, but this time for a genuine reason:
   the empty set is a `0`-clique, so `0` really is the largest clique size. (So in
   particular `G.cliqueNum = 0` can hold for very different reasons.)
3. It is noncomputable. This is the trade-off for being able to define it for
   arbitrary graphs. (Although since computing clique numbers is NP-hard, a
   computable version would only go so far.)
4. Because it doesn't rely on `Fintype V`, when we prove theorems about it for finite
   graphs we can use `Finite V` as our finiteness assumption.

For example, the complete graph on `ℕ` has cliques of every size, so its clique
number is the junk value `0`, while the complete graph on `Fin 3` has clique number
`3`. (In the next chapter we will see that Mathlib makes a different choice for the
chromatic number, which takes values in `ℕ∞`, so that an infinite chromatic number
is recorded as `⊤` rather than `0`.)
-/
example : ω (⊤ : SimpleGraph ℕ) = 0 := by simp

example : ω (⊤ : SimpleGraph (Fin 3)) = 3 := by simp

/-!
In a finite graph any clique has size at most the `cliqueNum`:
-/
#check IsClique.card_le_cliqueNum

/-!
We will often apply this to an `n`-clique, so we record that version too.
-/
lemma IsNClique.le_cliqueNum [Finite V] {n : ℕ} {s : Finset V}
    (h : G.IsNClique n s) : n ≤ ω G :=
  h.card_eq ▸ h.isClique.card_le_cliqueNum

/-!
In a finite graph the clique number is at most the number of vertices, since any
clique is a subset of the vertex set.
-/
#check cliqueNum_le_natCard -- ω G ≤ Nat.card V

/-!
The clique number of the complete graph on a type is its cardinality measured using
`Nat.card`. It needs no finiteness assumption: on an infinite type both sides are the
junk value `0`.
-/
#check cliqueNum_top -- (⊤ : SimpleGraph α).cliqueNum = Nat.card α

/-!
Any nonempty finite graph has clique number at least 1 (a single vertex is a
`1`-clique). Mathlib states this as `cliqueNum_ne_zero_of_finite`.
-/
lemma one_le_cliqueNum [Finite V] [Nonempty V] : 1 ≤ ω G :=
  (G.cliqueNum_ne_zero_of_finite).bot_lt

/-!
Every graph has a clique whose size is the clique number. This needs no finiteness
at all: if the clique sizes are unbounded then `ω G = 0`, and `∅` is a `0`-clique!
-/
#check exists_isNClique_cliqueNum -- ∃ s, G.IsNClique (ω G) s

/-!
A graph homomorphism into a finite graph cannot decrease the clique number: by
`exists_isNClique_cliqueNum` there is a clique of size `ω G`, and it maps to a clique
of the same size in `H`. The hypothesis `[Finite W]` cannot be dropped. For example,
`K[3]` maps into the complete graph on `ℕ` (any injective map will do), but the
complete graph on `ℕ` has clique number `0 < 3`.
-/
lemma Hom.cliqueNum_le {W : Type*} [Finite W] {H : SimpleGraph W} (f : G →g H) :
    ω G ≤ ω H := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  exact (hs.mapHom f).le_cliqueNum

/-!
By contrast, the clique number is invariant under graph isomorphism with no
finiteness assumptions at all. An isomorphism matches up the cliques of the two
graphs, so the two sets of clique sizes are equal, and hence so are their `sSup`s
(junk values included).
-/
lemma Iso.cliqueNum_eq {W : Type*} {H : SimpleGraph W} (e : G ≃g H) : ω G = ω H := by
  classical
  simp only [cliqueNum]
  congr 1
  ext n
  exact ⟨fun ⟨_, hs⟩ => ⟨_, hs.mapHom e.toHom⟩,
    fun ⟨_, hs⟩ => ⟨_, hs.mapHom e.symm.toHom⟩⟩

/-!
If `G` is `(n + 1)`-clique-free then `ω G ≤ n`. Once again no finiteness is needed,
since the clique given by `exists_isNClique_cliqueNum` always exists.
-/
lemma CliqueFree.cliqueNum_le {n : ℕ} (h : G.CliqueFree (n + 1)) : ω G ≤ n := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  by_contra! hlt
  exact h.mono hlt _ hs

/-!
So to compute a clique number it is enough to find an `n`-clique and show that the
graph is `(n + 1)`-clique-free.
-/
theorem IsNClique.cliqueNum_eq_of_cliqueFree [Finite V] {s : Finset V}
    {n : ℕ} (hs : G.IsNClique n s) (h : G.CliqueFree (n + 1)) :
    ω G = n :=
  h.cliqueNum_le.antisymm hs.le_cliqueNum

/-!
For example, the `5`-cycle has clique number `2`: `{0, 1}` is an edge and the cycle
is triangle-free.
-/
example : ω C[5] = 2 := by
  have h2 : C[5].IsNClique 2 {0, 1} := by decide
  exact h2.cliqueNum_eq_of_cliqueFree (by decide)

/-!
Graph theorists distinguish a *maximum* clique (one of the largest possible size)
from a *maximal* clique (one that is not contained in any larger clique). Every
maximum clique is maximal but not conversely: an edge hanging off a triangle is a
maximal clique of size `2`. Mathlib expresses maximality with the general
order-theoretic predicate `Maximal G.IsClique s`, while `IsMaximumClique` (for finite
graphs) says that a finset is a clique of size `ω G`.
-/
#check IsMaximumClique.isMaximalClique -- G.IsMaximumClique s → Maximal G.IsClique ↑s
#check maximumClique_exists            -- ∃ s, G.IsMaximumClique s

/-!
# Independent Sets

An *independent set* in a graph is a set of vertices that are pairwise non-adjacent.
This is defined analogously to `IsClique`.
-/
#source IsIndepSet -- abbrev IsIndepSet (s : Set α) : Prop :=
                   --                    s.Pairwise (fun v w ↦ ¬G.Adj v w)
/-!
Since a `SimpleGraph` is loopless `s : Set V` is an independent set iff every pair of
vertices in `s` is non-adjacent (irrespective of whether or not they are distinct).
-/
lemma isIndepSet_iff_forall_not_adj {s : Set V} :
    G.IsIndepSet s ↔ ∀ ⦃v w⦄, v ∈ s → w ∈ s → ¬G.Adj v w := by
  rw [isIndepSet_iff, Set.Pairwise]
  grind [SimpleGraph.irrefl]

/-!
If `s` is an independent set in `G` then its complement meets every edge of `G`. (In
other words, the complement of an independent set is a *vertex cover*.)
-/
#check IsIndepSet.nonempty_mem_compl_mem_edge

/-!
The independent sets of `G` are exactly the cliques of its complement `Gᶜ`, so each
notion for cliques has an independent-set counterpart. The analogues of `IsNClique`
and `CliqueFree` are `IsNIndepSet` and `IndepSetFree`.
-/
#source IsNIndepSet -- structure IsNIndepSet (n : ℕ) (s : Finset α) : Prop where
                    --                 isIndepSet : G.IsIndepSet s
                    --                 card_eq : s.card = n
#source IndepSetFree -- def IndepSetFree (n : ℕ) : Prop := ∀ t, ¬G.IsNIndepSet n t
/-!
Mathlib's simp lemmas `isNClique_compl` and `cliqueFree_compl` translate between the
two. Mathlib has a `Decidable` instance for `IsNIndepSet` but not for
`IndepSetFree`, so to check the latter with `decide` we first rewrite it as a
statement about cliques in `Gᶜ`, where our `decidableCliqueFree` instance applies.
-/
#check isNClique_compl  -- Gᶜ.IsNClique n s ↔ G.IsNIndepSet n s
#check cliqueFree_compl -- Gᶜ.CliqueFree n ↔ G.IndepSetFree n

/-!
There is an analogous definition of the *independence number* of a graph, as the size
of the largest independent set.
-/
#source indepNum -- noncomputable def indepNum (G : SimpleGraph α) : ℕ :=
                 --                     sSup {n | ∃ s, G.IsNIndepSet n s}

/--
The maximal number of vertices of an independent set in a graph `G`.
Denoted `⍺ G`. The symbol is the APL alpha `⍺` (Unicode `U+237A`, typed as `\apla`)
rather than the Greek `α` (`\a`), to avoid clashes with generic type variables.
-/
scoped notation "⍺" => SimpleGraph.indepNum

/-!
The independence number of `G` is the clique number of `Gᶜ`, and the analogues of
the clique-number lemmas above hold, such as `IsIndepSet.card_le_indepNum` and
`exists_isNIndepSet_indepNum`.
-/
#check cliqueNum_compl -- ω Gᶜ = ⍺ G
#check IsIndepSet.card_le_indepNum
#check exists_isNIndepSet_indepNum
/-!
The analogue of `IsNClique.cliqueNum_eq_of_cliqueFree` for independent sets: if `s`
is an `n`-independent set in `G` and `G` has no `(n + 1)`-independent set then
`⍺ G = n`. Rather than repeating the argument we pass to the complement.
-/
theorem IsNIndepSet.indepNum_eq_of_indepSetFree [Finite V] {s : Finset V}
    {n : ℕ} (hs : G.IsNIndepSet n s) (h : G.IndepSetFree (n + 1)) :
    ⍺ G = n := by
  rw [← cliqueNum_compl]
  exact (G.isNClique_compl.mpr hs).cliqueNum_eq_of_cliqueFree
    fun t ht => h t (G.isNClique_compl.mp ht)

/-!
Any finite edgeless graph has independence number equal to the number of vertices.
This is the complement of `cliqueNum_top`, since `⊥ᶜ = ⊤`. (The proof still works
for `V` infinite, so we omit the finiteness assumption.)
-/
@[simp]
lemma indepNum_bot : ⍺ (⊥ : SimpleGraph V) = Nat.card V := by
  simp [← cliqueNum_compl]

/-!
## Triangles and Independent Sets

In a triangle-free graph the neighbourhood of any vertex is an independent set, since
two adjacent neighbours of `v` would form a triangle with `v`.
-/
#check isIndepSet_neighborSet_of_triangleFree
/-!
Hence in a finite triangle-free graph every vertex has degree at most `⍺ G`.
-/
lemma degree_le_indepNum_of_triangleFree [Finite V] [G.LocallyFinite]
    (h : G.CliqueFree 3) (v : V) : G.degree v ≤ ⍺ G := by
  rw [← card_neighborFinset_eq_degree]
  exact IsIndepSet.card_le_indepNum
    (by simpa using G.isIndepSet_neighborSet_of_triangleFree h v)

/-!
So in a triangle-free graph with no large independent sets every vertex has small
degree. Applying this to both a graph and its complement is the idea behind the
simplest case of Ramsey's theorem. The *Ramsey number* `R(3, 3)` is the least `n`
such that every graph on `n` vertices contains a triangle or an independent set of
size `3`. Mathlib has no graph Ramsey numbers, but we can still prove the classical
value `R(3, 3) = 6`.

The `5`-cycle shows that `R(3, 3) > 5`: it is triangle-free and has no independent
set of size `3`. As explained above, we rewrite `IndepSetFree` in terms of the
complement before calling `decide`.
-/
example : C[5].CliqueFree 3 ∧ C[5].IndepSetFree 3 :=
  ⟨by decide, by rw [← cliqueFree_compl]; decide⟩

example : ⍺ C[5] = 2 := by
  have h2 : C[5].IsNIndepSet 2 {0, 2} := by decide
  exact h2.indepNum_eq_of_indepSetFree (by rw [← cliqueFree_compl]; decide)

/-!
The upper bound `R(3, 3) ≤ 6` is left as an exercise: applying
`degree_le_indepNum_of_triangleFree` to both `G` and `Gᶜ` does most of the work.

The `5`-cycle also shows that the product of the clique and independence numbers
can be smaller than the number of vertices: `ω C[5] * ⍺ C[5] = 4 < 5`.
Contrast this with the bound `|V| ≤ χ G * ⍺ G` that we will prove in the
next chapter. On the other hand the sum satisfies `ω G + ⍺ G ≤ |V| + 1` for every
finite graph, since a clique and an independent set share at most one vertex (see the
exercises).
-/

/-!
## Independence Number of the Infinite Path on ℕ

The infinite path graph on `ℕ` (`pathNat₁`) has unbounded independent sets, so what
is its independence number? Due to the `sSup` definition, it is `0`!

Adjacent vertices of `pathNat₁` differ by one, so they have different parities. Hence
any set of natural numbers that all have the same parity is independent.
-/
lemma pathNat₁_isIndepSet_of_mod_two_eq {s : Set ℕ}
    (h : ∀ ⦃a b⦄, a ∈ s → b ∈ s → a % 2 = b % 2) : pathNat₁.IsIndepSet s := by
  rw [isIndepSet_iff_forall_not_adj]
  rintro a b ha hb (rfl | rfl) <;> grind [h ha hb]

/-!
In particular, for every `n` the first `n` even numbers form an `n`-independent set.
So the set of sizes of independent sets is not bounded above, and
`Nat.sSup_of_not_bddAbove` gives `⍺ pathNat₁ = 0`.
-/
lemma indepNum_pathNat₁ : ⍺ pathNat₁ = 0 := by
  apply Nat.sSup_of_not_bddAbove
  rintro ⟨N, hN⟩
  have hs : pathNat₁.IsNIndepSet (N + 1)
      ((Finset.range (N + 1)).map ⟨(2 * ·), mul_right_injective₀ two_ne_zero⟩) := by
    refine ⟨pathNat₁_isIndepSet_of_mod_two_eq ?_, by simp⟩
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image]
    grind
  exact N.not_succ_le_self (hN ⟨_, hs⟩)

/-!
## Independence Number of the Kneser Graph *

Recall that the Kneser graph `kneserGraph β k` is the graph whose vertices are the
`k`-element subsets of a type `β`, and in which two vertices are adjacent iff the
subsets are disjoint and distinct. When `β` is `Fin n`, we have the notation
`Kn[n, k]`.

So an independent set in `Kn[n, k]` is a family of `k`-element subsets of `Fin n` in
which no two members are disjoint: an *intersecting family*. The Erdős–Ko–Rado
theorem says that if `2 * k ≤ n` then an intersecting family of `k`-element subsets
of an `n`-element set has at most `(n - 1).choose (k - 1)` members. This is in
Mathlib, and it is essentially the computation of the independence number of
`Kn[n, k]`.
-/
#check Finset.erdos_ko_rado
/-!
Mathlib states the theorem for a `Finset` `𝒜` of `Finset (Fin n)`s with three
hypotheses:
* `Set.Intersecting`: no two members of `𝒜` are disjoint. Note that this quantifies
  over *all* pairs `a, b ∈ 𝒜`, including `a = b`. So a family containing `∅` is never
  intersecting, since `∅` is disjoint from itself.
* `Set.Sized r`: every member of `𝒜` has exactly `r` elements.
* `r ≤ n / 2`: here `/` is natural-number (floor) division, so this is equivalent to
  `2 * r ≤ n`.
-/
section kneser
variable {k : ℕ} {β : Type*}
open Finset
/-!
The vertices of `kneserGraph β k` have type `{s : Finset β // #s = k}` which is a
bit of a pain to write, so we introduce a local notation for it.
-/

/-- The type of `k`-element subsets of `β`: `{s : Finset β // #s = k}`, the
vertices of `kneserGraph β k` -/
local notation "βₖ" => {s : Finset β // #s = k}

/-!
For any `i : β`, the set of all vertices containing `i` (the *star* at `i`) is an
independent set in `kneserGraph β k`: any two such vertices share `i`, so they are
not disjoint. When `1 ≤ k` and `2 * k ≤ #β` this is a largest independent set: we
will see below that the Erdős–Ko–Rado theorem gives the matching upper bound. (For
larger `k` the graph has no edges at all.)
-/
lemma kneserGraph_isIndepSet_of_mem (i : β) :
    (kneserGraph β k).IsIndepSet {b | i ∈ b.val} := by
  intro a ha b hb hne hf
  rw [kneserGraph_adj, ne_eq] at hf
  exact Finset.disjoint_left.mp hf.1 ha hb

/-!
We now want to start using the `Finset.powersetCard` API to compute sizes of families
of `k`-element subsets of a fintype `β`. Due to our choice of vertex type for the
Kneser graph we need the following book-keeping lemma which has zero mathematical
content.

Given any predicate `p : Finset β → Prop`, the number of `k`-element subsets of `β`
satisfying `p` can be counted in two different but equivalent ways: as vertices of
the Kneser graph, or as members of `Finset.powersetCard k univ`. (The bijection
between the two is `Subtype.val`.)
-/
lemma card_filter_val_eq_card_filter_powersetCard [Fintype β] (p : Finset β → Prop)
    [DecidablePred p] : #{b ∈ (Finset.univ : Finset βₖ) | p b.val} =
    #(((Finset.univ : Finset β).powersetCard k).filter p) := by
  classical
  refine card_bij (fun b _ => b.val) (by simp_all)
    (by simp [Subtype.ext_iff]) ?_
  simp only [mem_filter, mem_powersetCard]
  exact fun t ht => ⟨⟨t, ht.1.2⟩, by simpa using ht.2, rfl⟩

/-!
To compute the independence number we need the size of the star at `i`: the number
of `k`-element subsets of a finite type `β` containing `i` is
`(Fintype.card β - 1).choose (k - 1)`. We get this from Mathlib's
`card_filter_powersetCard_subset`, which counts the `k`-element subsets containing a
given finset `s` (here `s = {i}`).

The hypothesis `[NeZero k]` is needed. For `k = 0` the only `0`-element subset of
`β` is `∅`, which does not contain `i`, so the count is `0`. But natural-number
subtraction gives `k - 1 = 0`, so the formula evaluates to `1`. (`NeZero k` is a
typeclass recording that `k ≠ 0`; as an instance argument it can be found
automatically, for example when `k` is `n + 1`.)
-/
lemma card_filter_mem_eq_choose_sub_one [Fintype β] [DecidableEq β]
    (i : β) [NeZero k] : #{b ∈ (Finset.univ : Finset βₖ) | i ∈ b.val} =
    (Fintype.card β - 1).choose (k - 1) := by
  rw [card_filter_val_eq_card_filter_powersetCard (i ∈ ·)]
  simpa [singleton_subset_iff] using card_filter_powersetCard_subset {i} univ k
    (subset_univ _) (by simpa using NeZero.one_le)

/-!
As well as stars, the Kneser graph also contains independent sets determined by size:
if we take less than `2 * k` elements of `β` then the set of all `k`-element subsets
of this set is an independent set in `kneserGraph β k`.
-/
lemma kneserGraph_isIndepSet_of_card_lt {s : Finset β} (h : #s < 2 * k) :
    (kneserGraph β k).IsIndepSet {b | b.val ⊆ s} := by
  classical
  intro a ha b hb hne hf
  rw [kneserGraph_adj, ne_eq] at hf
  have hcard : (a.val ∪ b.val).card = 2 * k := by
    rw [card_union_of_disjoint hf.1, a.2, b.2, two_mul]
  grind [card_le_card (union_subset ha hb)]

/-!
Taking `s = univ` in `kneserGraph_isIndepSet_of_card_lt`: if `β` has less than
`2 * k` elements then `kneserGraph β k` is the edgeless graph, since any distinct
pair of `k`-element subsets of `β` must intersect.
-/
lemma kneserGraph_eq_bot_of_card_lt [Finite β] (h : Nat.card β < 2 * k) :
    kneserGraph β k = ⊥ := by
  have := Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card] at h
  have := kneserGraph_isIndepSet_of_card_lt (k := k) (s := Finset.univ)
    (by simpa using h)
  ext u v
  simpa using fun huv => this (by simp) (by simp) huv.2 huv

/-!
To apply the Erdős–Ko–Rado theorem we must transport an independent set of
`kneserGraph β k`, which is a finset of subtypes, to a family of `Finset β`s. The
image under `Subtype.val` of an independent set is an intersecting family, provided
`k ≠ 0`. Since Mathlib's `Intersecting` also requires each member to meet itself,
this is where `[NeZero k]` is needed: the only `0`-element subset is `∅`.
-/
lemma kneserGraph_isIndepSet_image_intersecting [DecidableEq β] [NeZero k]
    {t : Finset βₖ} (ht : (kneserGraph β k).IsIndepSet (t : Set _)) :
    ((t.image Subtype.val : Finset (Finset β)) : Set (Finset β)).Intersecting := by
  simp only [Finset.coe_image]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hdisj
  obtain rfl | hne := eq_or_ne x y
  · -- we use the fact that `k ≠ 0` to prove that `x` is not disjoint from itself
    exact NeZero.ne k (by simpa [disjoint_self.mp hdisj] using x.prop.symm)
  · exact ht hx hy hne ⟨hdisj, hne⟩

/-!
The image under `Subtype.val` of any finset of `k`-element subsets of `β` is a
family of `k`-element sized subsets of `β`.
-/
lemma sized_image_val [DecidableEq β] (t : Finset βₖ) :
    ((t.image Subtype.val : Finset (Finset β)) : Set (Finset β)).Sized k := by
  simp +contextual [Set.Sized]

/-!
Since the version of the Erdős–Ko–Rado theorem in Mathlib is stated in terms of
intersecting families of `k`-element subsets of `Fin n` we now take `β := Fin n` and
work in `Kn[n, k]`.

If `k ≤ n / 2` and `k ≠ 0` then the independence number of `Kn[n, k]` is achieved
by the star at `0`, with the upper bound given by the Erdős–Ko–Rado theorem. If
instead `n / 2 < k` then the Kneser graph is the edgeless graph and its independence
number is the size of its vertex set.
-/
theorem indepNum_kneserGraph {n : ℕ} [NeZero k] :
    ⍺ Kn[n, k] = if k ≤ n / 2 then (n - 1).choose (k - 1) else n.choose k := by
  by_cases hk : k ≤ n / 2
  · rw [ite_eq_left hk]
    have : NeZero n := NeZero.of_pos (by grind [NeZero.pos k])
    classical
    apply IsNIndepSet.indepNum_eq_of_indepSetFree
      (s := {b ∈ (Finset.univ : Finset {s : Finset (Fin n) // #s = k}) |
        (0 : Fin n) ∈ b.val})
    · constructor
      · simp [kneserGraph_isIndepSet_of_mem (0 : Fin n)]
      · simp [card_filter_mem_eq_choose_sub_one]
    · intro t ht
      have hAcard : (t.image Subtype.val).card = t.card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      have hInt := kneserGraph_isIndepSet_image_intersecting ht.isIndepSet
      have hSized := sized_image_val t
      have hbound := Finset.erdos_ko_rado hInt hSized hk
      grind [ht.card_eq]
  · have hn : Nat.card (Fin n) < 2 * k := by grind [Nat.card_fin]
    simp [hk, kneserGraph_eq_bot_of_card_lt hn]

/-!
For example, the Petersen graph `Kn[5, 2]` has independence number
`(5 - 1).choose (2 - 1) = 4`. Combined with the bound `|V| ≤ χ G * ⍺ G` from the next
chapter, this shows that the Petersen graph is not `2`-colourable, since it has
`10 > 2 * 4` vertices.
-/
example : ⍺ Kn[5, 2] = 4 := by simp [indepNum_kneserGraph]

end kneser
end indset
section mycielskian_cliquenum
variable {V : Type*} {G : SimpleGraph V}

/-!
# Clique and Independence Number of the Mycielskian

Recall from
[Mycielskian](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-mycielskian)
Mycielski's two facts: if `G` is triangle-free then so is `mμ[G]`, and if `G` has
chromatic number `k` then `mμ[G]` has chromatic number `k + 1`. In this section we
prove the first fact, and more generally that the Mycielskian preserves the clique
number. The second fact is `chromaticNumber_mycielskian` in the next chapter.
Together they show that the clique number can be a very poor lower bound for the
chromatic number. We finish by computing the independence number of `mμ[G]`.

## Triangle-Free Mycielskians

We start with the promised proof that the Mycielskian of a triangle-free graph is
triangle-free, before moving on to the more general result that the Mycielskian
preserves the clique number (of any finite graph with at least one edge).
-/
theorem CliqueFree.mycielskian (h : G.CliqueFree 3) : mμ[G].CliqueFree 3 := by
  intro t ht
  -- we use `classical` to avoid the need for a `DecidableEq V` instance here
  classical
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := ht
  rcases a with _ | (a₁ | a₂) <;>
  rcases b with _ | (b₁ | b₂) <;>
  rcases c with _ | (c₁ | c₂) <;>
  -- 27 goals, but 23 are easily dispatched by `simp only` since they either assert
  -- the existence of loops; edges inside the "right" copy of `V`; or edges from the
  -- "left" copy of `V` to `none`, all of which do not exist in `mμ[G]`.
  simp only [mycielskian_adj] at hab hac hbc <;>
    -- only 4 goals remain!
    -- In each goal the local context contains three adjacency hypotheses
    -- that assert the existence of a triangle in `G`, contradicting our
    -- assumption that `G` is triangle-free.
    exact h _ <| is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩

/-!
Hence the iterated Mycielskian of any triangle-free graph is also triangle-free.
-/
theorem CliqueFree.iterMycielskian (n : ℕ) (h : G.CliqueFree 3) :
    (mμ^n G).CliqueFree 3 := by
  induction n with
  | zero => exact h
  | succ _ ih => exact ih.mycielskian

/-!
In particular the iterated Mycielskian of the 5-cycle is triangle-free.
-/
theorem cliqueFree_three_iterMycielskian_cycleGraph (n : ℕ) :
    (mμ^n C[5]).CliqueFree 3 :=
  CliqueFree.iterMycielskian n (by decide)

/-!
## Clique Number of the Mycielskian

We now turn to the clique number of the Mycielskian.

On paper this is easy: any clique in `G` also appears in `mμ[G]` via the obvious
embedding. Conversely any clique of size at least `3` in `mμ[G]` cannot use the
vertex `none` since `none` is only adjacent to the vertices in the right-copy of `V`,
and the right-copy of `V` is an independent set. Moreover no clique in `mμ[G]` can
contain `v ₗ` and `v ᵣ` for any `v ∈ V`. (Since this would imply that `G.Adj v v`
which is impossible.) Hence any clique of size at least `3` in `mμ[G]` can be mapped
to a clique of the same size in `G` using the projection we will define below.

We first prove that the Mycielskian embedding mapping `G` into its Mycielskian sends
`k`-cliques in `G` to `k`-cliques in `mμ[G]`.
-/
lemma IsNClique.mycielskian {k : ℕ} {s : Finset V} (h : G.IsNClique k s) :
    (mμ[G]).IsNClique k (s.map (Embedding.mycielskianLeft G).toEmbedding) := by
  classical
  simpa [Finset.map_eq_image] using h.mapHom (Embedding.mycielskianLeft G).toHom

/-!
Next we want to show that the vertex `none` cannot belong to any `k`-clique in
`mμ[G]` when `3 ≤ k`, because `none` is only adjacent to right-vertices, and no two
right-vertices are adjacent.
-/
lemma mycielskian_none_notMem_clique {k : ℕ} (h3 : 3 ≤ k)
    {t : Finset (Option (V ⊕ V))} (ht : mμ[G].IsNClique k t) : none ∉ t := by
  classical -- needed to use `Finset.erase` below since it requires `DecidableEq V`
  intro hmem
  -- since `t` is a `k`-clique with `3 ≤ k`, `t.erase none` has at least 2 elements.
  have hcard : 2 ≤ (t.erase none).card := by
    grind [Finset.card_erase_of_mem hmem, ht.card_eq]
  -- so we can find two distinct vertices `a, b` in `t.erase none`, and they are
  -- adjacent since `t` is a clique.
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  -- both `a` and `b` are adjacent to `none` in `mμ[G]`
  have h_na := ht.isClique hmem (Finset.mem_of_mem_erase ha) (by grind)
  have h_nb := ht.isClique hmem (Finset.mem_of_mem_erase hb) (by grind)
  -- so they must be "right" vertices
  -- below `try tac` runs `tac`, but if `tac` fails it
  -- does nothing instead of raising an error
  rcases a with _ | ⟨va | va⟩ <;> rcases b with _ | ⟨vb | vb⟩
    <;> try simp only [mycielskian_adj] at h_na h_nb
  -- but no two "right" vertices are adjacent, so we have a contradiction.
  exact ht.isClique (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab


/-!
If `s` is a clique in the Mycielskian then `s` cannot contain both `v ₗ` and `v ᵣ`
for any `v ∈ V` (since `mμ[G].Adj v ₗ v ᵣ` would imply `G.Adj v v` which is
impossible). Moreover we just proved that any `k`-clique with `3 ≤ k` cannot contain
`none`. This means that if we define a projection map from the vertices of `mμ[G]` to
the vertices of `G` by "forgetting" which side (left or right) vertices came from
(and sending `none` to an arbitrary vertex in `V`) then it will be injective on any
clique in `mμ[G]` of size at least `3` and also preserve adjacency.
-/

/-- Projection from the vertex set of `mμ[G]` to that of `G` (will preserve
`k`-cliques for `k ≥ 3`) -/
def mycielskianProj (v₀ : V) : Option (V ⊕ V) → V
  | some (Sum.inl v) => v
  | some (Sum.inr v) => v
  | none             => v₀

/-!
We need some simple definitional lemmas about `mycielskianProj`.
-/
@[simp]
lemma mycielskianProj_left (v₀ v : V) :
    mycielskianProj v₀ (some (Sum.inl v)) = v := rfl

@[simp]
lemma mycielskianProj_right (v₀ v : V) :
    mycielskianProj v₀ (some (Sum.inr v)) = v := rfl

@[simp]
lemma mycielskianProj_none (v₀ : V) : mycielskianProj v₀ none = v₀ := rfl

/-!
The projection map is injective on any clique `t` in `mμ[G]` that doesn't contain
`none`, since if two vertices in `t` had the same projection then they would be the
images of some `v ₗ` and `v ᵣ` and in particular `v ₗ` would be adjacent to `v ᵣ` in
`mμ[G]` which implies `G.Adj v v`, a contradiction.
-/
lemma mycielskianProj_injOn_clique (v₀ : V) {k : ℕ}
    {t : Finset (Option (V ⊕ V))} (hn : none ∉ t) (ht : mμ[G].IsNClique k t) :
    Set.InjOn (mycielskianProj v₀) (t : Set (Option (V ⊕ V))) := by
  intro a ha b hb hxy
  by_contra hne
  have := ht.isClique ha hb hne
  rcases a with _ | ⟨v | v⟩ <;> rcases b with _ | ⟨w | w⟩ <;> simp_all

/-!
Any `k`-clique in `mμ[G]` (with `3 ≤ k`) maps to a `k`-clique in `G` under
`mycielskianProj`.
-/
lemma IsNClique.of_mycielskian [DecidableEq V] (v₀ : V) {k : ℕ} (h3 : 3 ≤ k)
    {t : Finset (Option (V ⊕ V))} (ht : mμ[G].IsNClique k t) :
    G.IsNClique k (t.image (mycielskianProj v₀)) := by
  -- any clique of size at least `3` in `mμ[G]` cannot contain `none`
  have hnone := mycielskian_none_notMem_clique h3 ht
  -- hence the projection is injective on `t`
  have hinj := mycielskianProj_injOn_clique v₀ hnone ht
  -- so it remains to show that the projection preserves adjacency on `t`
  refine ht.image_of_adj hinj fun x hx y hy hadj => ?_
  -- `first | t₁ | t₂ | …` tries the tactics in turn, until one succeeds
  rcases x with _ | ⟨_ | _⟩ <;> rcases y with _ | ⟨_ | _⟩ <;> -- 9 goals
    first | exact absurd hx hnone | exact absurd hy hnone | exact hadj | simp at hadj

/-!
Any finite graph with at least one edge has the same clique number as its
Mycielskian. (For the edgeless graph `⊥` the answer depends on whether `V` is empty;
see the exercises.)
-/
theorem cliqueNum_mycielskian_of_ne_bot [Finite V] (h : G ≠ ⊥) :
    ω mμ[G] = ω G := by
  classical -- to infer `DecidableEq V`
  -- `G ≠ ⊥` gives an edge, i.e. a `2`-clique, so `2 ≤ ω G`
  obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp h
  have h2 : 2 ≤ ω G := (G.is2Clique_pair_iff.mpr hab).le_cliqueNum
  -- a maximum clique of `G` maps to an `ω G`-clique in `mμ[G]`, so it only remains
  -- to show that `mμ[G]` is `(ω G + 1)`-clique-free
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  apply hs.mycielskian.cliqueNum_eq_of_cliqueFree
  intro t ht
  -- any `(ω G + 1)`-clique in `mμ[G]` projects to an `(ω G + 1)`-clique in `G`
  -- (note `3 ≤ ω G + 1` since `2 ≤ ω G`), contradicting `card_le_cliqueNum`
  exact absurd (ht.of_mycielskian a (by grind)).le_cliqueNum (by grind)

/-!
Applying this repeatedly to the `5`-cycle, we see that every iterated Mycielskian of
`C[5]` has clique number `2`. Each `mμ^n C[5]` has an edge because its clique number
is `2`, while the edgeless graph `⊥` is `2`-clique-free.
-/
theorem cliqueNum_iterMycielskian_cycleGraph (n : ℕ) : ω (mμ^n C[5]) = 2 := by
  induction n with
  | zero =>
    have h2 : C[5].IsNClique 2 {0, 1} := by decide
    exact h2.cliqueNum_eq_of_cliqueFree (by decide)
  | succ n ih =>
    have hne : mμ^n C[5] ≠ ⊥ := by
      intro h
      obtain ⟨s, hs⟩ := (mμ^n C[5]).exists_isNClique_cliqueNum
      rw [ih, h] at hs
      exact cliqueFree_bot le_rfl s hs
    rw [← ih]
    exact cliqueNum_mycielskian_of_ne_bot hne

/-!
In
[Colouring Mycielskians](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-colouring-mycielskians)
we show that `mμ^n C[5]` has chromatic number `n + 3`. So these graphs all have
clique number `2` but have arbitrarily large chromatic number.
-/

end mycielskian_cliquenum
section open_neighborhoods
variable {V : Type*}
/-!
## Independence Number of the Mycielskian *

We now derive a formula for the independence number of the Mycielskian of a finite
graph. To state it we need the *open neighbourhood* of a set of vertices `s` in `G`:
the set of vertices adjacent to at least one vertex of `s`. It is called *open* to
distinguish it from the *closed neighbourhood*, which also contains `s` itself. (Some
texts instead define the neighbourhood of `s` to exclude `s`. The definitions agree
when `s` is independent, which is the only case we will use.) Mathlib has no
definition of the neighbourhood of a set of vertices, so we make our own.
-/

/-- The open neighbourhood of a set of vertices in a graph `G` is the union of the
neighbourhoods of each vertex in the set. -/
def openNeighborhoodSet (G : SimpleGraph V) (s : Set V) : Set V :=
  ⋃ v ∈ s, G.neighborSet v
/-!
The bounded union `⋃ v ∈ s, _` is notation for a nested `Set.iUnion`, indexed
first by `v : V` and then by proofs of `v ∈ s`.
-/
#check Set.iUnion
/-!
Membership in the open neighbourhood and in its complement (the vertices with no
neighbour in `s`) unfold as expected.
-/
@[simp]
lemma mem_openNeighborhoodSet {G : SimpleGraph V} {s : Set V} {x : V} :
    x ∈ G.openNeighborhoodSet s ↔ ∃ a ∈ s, G.Adj a x := by
  simp [openNeighborhoodSet]

lemma mem_compl_openNeighborhoodSet {G : SimpleGraph V} {s : Set V} {x : V} :
    x ∈ (G.openNeighborhoodSet s)ᶜ ↔ ∀ a ∈ s, ¬ G.Adj a x := by
  simp

/-!
We need a `Finset` version of the open neighbourhood, which can only be defined for
locally finite graphs (so that each vertex `v` has a `neighborFinset`). The bounded
union `⋃ v ∈ s, _` that we used to define `openNeighborhoodSet` has a direct `Finset`
counterpart: `s.biUnion f` is the union of the finsets `f v` over `v ∈ s`. Note that
it requires `DecidableEq` on the target type, since building a `Finset` union means
deciding which elements are duplicates.
-/
#check Finset.biUnion -- [DecidableEq β] (s : Finset α) (t : α → Finset β) : Finset β
#check Finset.coe_biUnion -- ↑(s.biUnion t) = ⋃ x ∈ s, ↑(t x)

/-- The open neighbourhood of a Finset `s` in a graph `G` is the finset of vertices
that are adjacent to at least one vertex in `s`. -/
def openNeighborhoodFinset (G : SimpleGraph V) [G.LocallyFinite] [DecidableEq V]
    (s : Finset V) : Finset V := s.biUnion (fun v ↦ G.neighborFinset v)

/-!
It will be convenient to write `N(s)` for the open neighbourhood of a `s : Finset V`,
as is standard in graph theory, so that (in a finite graph) the vertices with no
neighbours in `s` form the finset `N(s)ᶜ`. We want to do this with a fixed `G` here
so we use `local notation` whose expansion mentions the ambient section variable `G`
explicitly, so `N(s)` always refers to the current graph `G`.
-/
variable (G : SimpleGraph V)
@[inherit_doc]
local notation:max "N(" s ")" => openNeighborhoodFinset G s
variable {G}
/-!
Membership in `N(s)` and its complement, and the coercion of `N(s)` to a `Set`,
unfold as expected.
-/
@[simp]
lemma mem_openNeighborhoodFinset [G.LocallyFinite] [DecidableEq V] {s : Finset V}
    {x : V} : x ∈ N(s) ↔ ∃ a ∈ s, G.Adj a x := by
  simp [openNeighborhoodFinset]

@[simp]
lemma coe_openNeighborhoodFinset [G.LocallyFinite] [DecidableEq V] (s : Finset V) :
    (N(s) : Set V) = G.openNeighborhoodSet ↑s := by
  ext x
  simp

lemma mem_compl_openNeighborhoodFinset [Fintype V] [G.LocallyFinite] [DecidableEq V]
    {s : Finset V} {x : V} : x ∈ N(s)ᶜ ↔ ∀ a ∈ s, ¬ G.Adj a x := by
  simp

/-!
Now for independent sets in the Mycielskian. Any independent set `s` in `G` gives
rise to an independent set in `mμ[G]` consisting of the left copy of `s` together
with the right copy of every vertex having no neighbour in `s`, i.e. `sₗ ∪ N(s)ᶜᵣ`.
-/
lemma IsIndepSet.mycielskian {s : Set V} (h : G.IsIndepSet s) :
    mμ[G].IsIndepSet (s.image (·ₗ) ∪ (G.openNeighborhoodSet s)ᶜ.image (·ᵣ)) := by
  rintro a ha b hb hne hf
  -- `a` and `b` are each either a left copy of a vertex of `s` or a right copy
  --  of a vertex with no neighbour in `s`; we split on both. The right-right case
  -- has no edge, so `simp` closes it, leaving the three cases below.
  obtain (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) := ha
    <;> obtain (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) := hb
      <;> simp only [mycielskian_adj] at hf
  -- Now have `G.Adj x y` and at least one of `x` or `y` is in `s`
  · exact h hx hy hf.ne hf -- both in `sₗ`: contradicts independence of `s`
  -- `y` has no neighbour in `s`, yet `x ∈ s` and `G.Adj x y`
  · exact mem_compl_openNeighborhoodSet.mp hy _ hx hf
  -- symmetric to the previous case
  · exact mem_compl_openNeighborhoodSet.mp hx _ hy hf.symm

open Finset mycielskian
/-!
The following simple lemma will help us to compute the size of independent sets in
`mμ[G]`. The left and right images of any two finsets are disjoint (they lie in
different summands) and both maps are injective, so the union of the images has size
`#s + #t`.
-/
lemma card_image_left_union_image_right [DecidableEq V] (s t : Finset V) :
    #(s.image (·ₗ) ∪ t.image (·ᵣ)) = #s + #t := by
  rw [Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ left_injective,
    Finset.card_image_of_injective _ right_injective]
  exact Finset.disjoint_left.mpr fun a ha hb => by
    rw [mem_image] at ha hb
    obtain ⟨x, -, rfl⟩ := ha
    obtain ⟨y, -, hy⟩ := hb
    simp at hy

/-!
We will show that the independence number of `mμ[G]` is the maximum, over all
independent sets `s` of `G`, of `#s + #N(s)ᶜ`. The lower bound comes straight from
`IsIndepSet.mycielskian`.
-/
lemma le_indepNum_mycielskian [Fintype V] [DecidableEq V] [G.LocallyFinite]
    {s : Finset V} (h : G.IsIndepSet ↑s) : #s + #N(s)ᶜ ≤ mμ[G].indepNum := by
  have hSindep : mμ[G].IsIndepSet ↑(s.image (·ₗ) ∪ N(s)ᶜ.image (·ᵣ)) := by
    simpa using h.mycielskian
  rw [← card_image_left_union_image_right s (N(s)ᶜ)]
  exact hSindep.card_le_indepNum

/-!
The left preimage of an independent set of `mμ[G]` is an independent set of `G` (the
left copy is a copy of `G`).
-/
lemma isIndepSet_preimage_left {t : Set (Option (V ⊕ V))}
    (h : mμ[G].IsIndepSet t) : G.IsIndepSet ((·ₗ) ⁻¹' t) := by
  intro x hx y hy hne
  simpa using h hx hy (by simp [hne])

/-!
The `Finset` version of the previous lemma uses `Finset.preimage`. Unlike
`Set.preimage`, it takes an extra argument: a proof that the map is injective on the
preimage. This guarantees that the preimage of a finset is finite. Here the map
`(·ₗ)` is injective, so we can always supply `left_injective.injOn`.
-/
#check Finset.preimage -- (s : Finset β) (f : α → β) (hf : Set.InjOn f (f ⁻¹' ↑s))
lemma isIndepSet_preimage_left_finset {T : Finset (Option (V ⊕ V))}
    (hT : mμ[G].IsIndepSet ↑T) :
    G.IsIndepSet ↑(T.preimage (·ₗ) left_injective.injOn) := by
  simpa using G.isIndepSet_preimage_left hT

/-!
An independent set `s` has no neighbours in itself, i.e. `s ⊆ N(s)ᶜ`: adjacent
vertices are distinct, so if `a, z ∈ s` were adjacent this would contradict
independence.
-/
lemma subset_compl_openNeighborhoodFinset [Fintype V] [DecidableEq V]
    [G.LocallyFinite] {s : Finset V}
    (h : G.IsIndepSet ↑s) : s ⊆ N(s)ᶜ :=
  fun z hz => by simpa using fun a ha hadj => h ha hz hadj.ne hadj

/-!
In a nonempty finite graph the finset of non-neighbours of an independent set `s` is
nonempty: it contains `s` itself, unless `s` is empty in which case it is all of `V`.
-/
lemma compl_openNeighborhoodFinset_nonempty [Fintype V] [Nonempty V] [DecidableEq V]
    [G.LocallyFinite] {s : Finset V}
    (h : G.IsIndepSet ↑s) : N(s)ᶜ.Nonempty := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · simp [openNeighborhoodFinset]
  · exact ⟨z, subset_compl_openNeighborhoodFinset h hz⟩

/-!
If an independent set `T` of `mμ[G]` contains `none` then, since `none` is adjacent
to every right-vertex, `T` contains no right-vertices. Hence `T` is contained in
`none` together with the left copies of its left part.
-/
lemma mycielskian_indepSet_subset_insert_none [DecidableEq V]
    {T : Finset (Option (V ⊕ V))} (hT : mμ[G].IsIndepSet ↑T) (hnone : none ∈ T) :
    T ⊆ insert none
      ((T.preimage (·ₗ) left_injective.injOn).image (·ₗ)) := by
  intro v hv
  rcases v with _ | (x | x)
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_image.mpr ⟨x, Finset.mem_preimage.mpr hv, rfl⟩)
  -- `x ᵣ` cannot lie in `T` since it is adjacent to `none ∈ T`
  · exact (hT (mem_coe.mpr hnone) (mem_coe.mpr hv) (by simp) (by simp)).elim

/-!
No vertex in the right part of an independent finset `T` of `mμ[G]` has a neighbour
in its left part (there are no `left`–`right` edges within `T`).
-/
lemma mycielskian_indepSet_preimage_right_subset [Fintype V] [DecidableEq V]
    [G.LocallyFinite]
    {T : Finset (Option (V ⊕ V))} (hT : mμ[G].IsIndepSet ↑T) :
    T.preimage (·ᵣ) right_injective.injOn ⊆
      N(T.preimage (·ₗ) left_injective.injOn)ᶜ := by
  intro y hy
  refine mem_compl_openNeighborhoodFinset.mpr fun a ha => ?_
  simpa using hT (Finset.mem_preimage.mp ha) (Finset.mem_preimage.mp hy) (by simp)

/-!
Any Finset `T` of vertices of `mμ[G]` not containing `none` is covered by the left
copies of its left part together with the right copies of its right part. (This is
just bookkeeping, no graph is involved: every vertex of `mμ[G]` is `none`, a left
copy, or a right copy.)
-/
lemma subset_image_preimage_left_union_right [DecidableEq V]
    {T : Finset (Option (V ⊕ V))} (hnone : none ∉ T) :
    T ⊆ (T.preimage (·ₗ) left_injective.injOn).image (·ₗ) ∪
      (T.preimage (·ᵣ) right_injective.injOn).image (·ᵣ) := by
  intro v hv
  rcases v with _ | (x | x)
  · exact absurd hv hnone
  · exact mem_union_left _ (mem_image.mpr ⟨x, Finset.mem_preimage.mpr hv, rfl⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨x, Finset.mem_preimage.mpr hv, rfl⟩)

/-!
Key calculation for the upper bound: an independent set `T` of `mμ[G]` is no larger
than `#A + #N(A)ᶜ`, where `A` is the set of vertices of `G` whose left copy lies
in `T`.
-/
lemma mycielskian_indepSet_card_le [Fintype V] [Nonempty V] [DecidableEq V]
    [G.LocallyFinite]
    {T : Finset (Option (V ⊕ V))} (hT : mμ[G].IsIndepSet ↑T) :
    #T ≤ #(T.preimage (·ₗ) left_injective.injOn) +
      #N(T.preimage (·ₗ) left_injective.injOn)ᶜ := by
  -- `A` (resp. `B`) is the set of vertices of `G` whose
  --  left (resp. right) copy lies in `T`.
  let A : Finset V := T.preimage (·ₗ) left_injective.injOn
  let B : Finset V := T.preimage (·ᵣ) right_injective.injOn
  -- `A` is an independent set of `G`, so `N(A)ᶜ` is nonempty (previous lemmas).
  have hNne : N(A)ᶜ.Nonempty :=
    compl_openNeighborhoodFinset_nonempty (isIndepSet_preimage_left_finset hT)
  by_cases hnone : none ∈ T
  · -- `none ∈ T` : `T` is covered by `none` and the left copies of `A`, and
    -- `N(A)ᶜ` contributes at least `1` since it is nonempty.
    calc #T ≤ #(insert none (A.image (·ₗ))) :=
          Finset.card_le_card (mycielskian_indepSet_subset_insert_none hT hnone)
      _ ≤ #(A.image (·ₗ)) + 1 := Finset.card_insert_le _ _
      _ = #A + 1 := by
            rw [Finset.card_image_of_injective _ left_injective]
      _ ≤ #A + #N(A)ᶜ := Nat.add_le_add_left hNne.card_pos _
  · -- `none ∉ T` : `T` is covered by the left and right images of `A` and `B`,
    -- and `B ⊆ N(A)ᶜ` since there are no `left`–`right` edges in `T`.
    calc #T ≤ #(A.image (·ₗ) ∪ B.image (·ᵣ)) :=
          Finset.card_le_card (subset_image_preimage_left_union_right hnone)
      _ = #A + #B := card_image_left_union_image_right A B
      _ ≤ #A + #N(A)ᶜ := Nat.add_le_add_left
          (Finset.card_le_card (mycielskian_indepSet_preimage_right_subset hT)) _

/-!
Putting the two bounds together we obtain a formula for the independence number of
the Mycielskian: `⍺ mμ[G]` is the maximum of `#s + #N(s)ᶜ` over all independent
sets `s` of `G`, and this maximum is realized by the independent set
`sₗ ∪ N(s)ᶜᵣ`. In particular there is always a maximum independent set of `mμ[G]`
avoiding `none` (although other maximum independent sets may contain `none`, as
happens for `G = ⊥` on a single vertex).

We write the maximum using `Finset.sup`: for an `ℕ`-valued function `f`, `t.sup f`
is the largest value of `f` on the finset `t` (and `0` if `t` is empty). The
hypothesis `[Nonempty V]` is needed: if `V` is empty then `mμ[G]` still has the
vertex `none`, so `⍺ mμ[G] = 1`, but the only independent set of `G` is `∅` and the
formula gives `0`.
-/
theorem indepNum_mycielskian [Fintype V] [Nonempty V] [DecidableEq V]
    [DecidableRel G.Adj] :
    ⍺ mμ[G] = ({s | G.IsIndepSet ↑s} : Finset (Finset V)).sup
    (fun s => #s + #N(s)ᶜ) := by
  apply le_antisymm
  · -- `≤` : a maximum independent set `T` of `mμ[G]` is dominated by the value
    -- of the sup at its left part `A`.
    obtain ⟨T, hT⟩ := (mμ[G]).exists_isNIndepSet_indepNum
    rw [← hT.card_eq]
    have hAF : T.preimage (·ₗ) left_injective.injOn ∈
        univ.filter fun s : Finset V => G.IsIndepSet ↑s :=
      mem_filter.mpr ⟨mem_univ _, isIndepSet_preimage_left_finset hT.isIndepSet⟩
    exact (G.mycielskian_indepSet_card_le hT.isIndepSet).trans
      (Finset.le_sup (f := fun s => #s + #N(s)ᶜ) hAF)
  · -- `≥` : each independent `s` achieves its value in the sup.
    exact Finset.sup_le fun s hs => le_indepNum_mycielskian (mem_filter.mp hs).2

/-!
Taking `s = ∅` in the formula gives `⍺ mμ[G] ≥ Nat.card V`, and taking `s` to be a
maximum independent set gives `⍺ mμ[G] ≥ 2 * ⍺ G` (since `s ⊆ N(s)ᶜ` for an
independent set `s`). But there are examples where neither is sharp: add an isolated
vertex to `C[5]` then the graph has `6` vertices and independence number `3`, so both
bounds give `6`, but `s = {w}` gives `1 + 6 = 7`.

For the `5`-cycle the only maximizer is `s = ∅`, with `#∅ + #N(∅)ᶜ = 0 + 5 = 5`,
while every nonempty independent `s` gives at most `4 = 2 * ⍺ C[5]`.

The Mycielskian of the `5`-cycle is the *Grötzsch graph*, so we can use the previous
result to compute its independence number. After rewriting with
`indepNum_mycielskian`, `decide` evaluates the maximum over the `11` independent sets
of `C[5]` (by checking all `2 ^ 5 = 32` subsets of `Fin 5`).
-/
example : ⍺ grotzschGraph = 5 := by
  rw [indepNum_mycielskian]
  decide

end open_neighborhoods
end SimpleGraph
