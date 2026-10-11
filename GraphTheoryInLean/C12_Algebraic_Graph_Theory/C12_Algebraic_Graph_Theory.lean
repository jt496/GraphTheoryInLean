import GraphTheoryInLean.C11_Distance.C11_Distance
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
variable {V : Type*} {G : SimpleGraph V}
namespace SimpleGraph

/-!
*Algebraic graph theory* studies a graph via algebraic objects attached to it: its
group of automorphisms, and matrices indexed by its vertices, above all the adjacency
matrix. In this chapter we look at both, and at how they interact.

The *automorphisms* of a graph `G`, i.e. the isomorphisms `G ≃g G`, form a group that
measures how symmetric `G` is. In
[Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#chapter-maps) we met
automorphisms and *vertex-transitive* graphs, in which any vertex can be sent to any
other by an automorphism, and showed that cycle graphs and hypercubes are
vertex-transitive. In
[Distance Invariants under Isomorphism](https://jt496.github.io/GraphTheoryInLean/Distance/#section-distance-invariants-under-isomorphism)
we saw that all the vertices of a vertex-transitive graph have the same eccentricity,
so its radius equals its diameter.

We first note that `G ≃g G` is a group and that isomorphic graphs have isomorphic
automorphism groups, and then compute the automorphism groups of some of our running
examples. We start with a graph with no symmetry: the infinite path `pathNat₁`, whose
automorphism group is trivial. Next we identify the automorphism group of the cycle
graph `C[n]` as a dihedral group.

We then turn to matrices. The adjacency matrix `A` of a finite graph determines the
graph and its powers count walks. A permutation of the vertices is an automorphism
iff it preserves `A`, so isomorphic graphs have the same eigenvalues, and in a
vertex-transitive graph every vertex lies on the same number of closed walks of each
length. We also survey Mathlib's results on the Laplacian, including the theorem
that the number of connected components of a graph is the dimension of the kernel
of its Laplacian, and on strongly regular graphs such as the Petersen graph.

Next we return to the hypercube: we show that two of the constructions of `Q[n]` from
[Hypercube](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-hypercube)
give isomorphic graphs, and use the Hamming-graph model to prove that the
automorphism group of `Q[n]` is the hyperoctahedral group `ℤ/2 ≀ Sₙ`, of order
`2ⁿ · n!`.

Automorphisms also let us count copies of one graph in another: the number of
labelled copies is the number of unlabelled copies times the number of automorphisms.
We apply this to count the cycles in a graph and the 5-cycles in the Mycielskian of a
graph with no triangles and no 5-cycles. Finally, combining this counting identity
with the automorphism group of the hypercube, we show that every copy of `Q[k]` in
`Q[n]` is an induced subcube, and count these copies.

# Automorphism Groups

Mathlib provides a `Group` instance on the automorphisms `G ≃g G` of any graph, with
multiplication given by composition: `(e * f) v = e (f v)`. (Recall that
`SimpleGraph.Iso` is an abbrev for `RelIso`, which has a `Group` instance.)
-/
#synth Group (C[5] ≃g C[5]) -- RelIso.instGroup

/-!
An isomorphism `e : G ≃g H` transports automorphisms of `G` to automorphisms of `H`
by conjugation, `f ↦ e ∘ f ∘ e⁻¹`, and this is an isomorphism of automorphism
groups. So isomorphic graphs have isomorphic automorphism groups, and we may compute
an automorphism group using whichever model of a graph is most convenient.

The underlying bijection is Mathlib's `RelIso.relIsoCongr e e`, which transports
isomorphisms along isomorphisms by pre- and post-composition, so we only need to
check that it is multiplicative. We follow Mathlib's naming for such maps (compare
`MulAut.congr`, which does the same for automorphisms of groups).
-/
#check RelIso.relIsoCongr -- (r₁ ≃r r₂) → (s₁ ≃r s₂) → ((r₁ ≃r s₁) ≃ (r₂ ≃r s₂))

/-- Transport of the automorphism group of a graph along an isomorphism
`e : G ≃g H`, by conjugation: `f ↦ e ∘ f ∘ e.symm`. -/
@[simps!]
def Iso.autCongr {W : Type*} {H : SimpleGraph W} (e : G ≃g H) :
    (G ≃g G) ≃* (H ≃g H) :=
  { RelIso.relIsoCongr e e with
    map_mul' f g := by ext v; simp [RelIso.relIsoCongr_apply] }

/-!
## Automorphisms of the Infinite Path

At the opposite extreme from vertex-transitive graphs are graphs with no symmetry at
all: a graph is *asymmetric* if its only automorphism is the identity, i.e. its
automorphism group is trivial. A simple example is the infinite path `pathNat₁`. This
may seem surprising since, as we saw in
[Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#chapter-maps), `pathNat₁` has
many embeddings into itself: for each `j : ℕ` the embedding `pathNat₁Translate j`
sends `i` to `i + j`. However, none of these is surjective, except for the identity
`pathNat₁Translate 0`.

The key observation is that `0` is the only vertex of `pathNat₁` of degree one (all
the other vertices have degree two), and isomorphisms preserve degrees. So every
automorphism of `pathNat₁` fixes `0`.
-/
#check degree_pathNat₁ -- pathNat₁.degree n = if n = 0 then 1 else 2
#check Iso.degree_eq   -- (f : G ≃g G') (x : V) : G'.degree (f x) = G.degree x

lemma aut_pathNat₁_apply_zero (e : pathNat₁ ≃g pathNat₁) : e 0 = 0 := by
  have h := e.degree_eq 0
  rw [degree_pathNat₁, degree_pathNat₁] at h
  grind

/-!
We can now walk along the path, showing that an automorphism `e` fixes every vertex
by induction using `Nat.twoStepInduction` (a similar argument will identify the
automorphisms of cycle graphs in the next section). Since `1` is the only neighbour
of `e 0 = 0`, `e` fixes `1`. If `e` fixes `k` and `k + 1` then `e (k + 2)` is a
neighbour of `e (k + 1) = k + 1`, so it is either `k` or `k + 2`. It cannot be
`k = e k` since `e` is injective, so `e` fixes `k + 2`.
-/
lemma aut_pathNat₁_apply (e : pathNat₁ ≃g pathNat₁) (k : ℕ) : e k = k := by
  induction k using Nat.twoStepInduction with
  | zero => exact aut_pathNat₁_apply_zero e
  | one =>
    have h : pathNat₁.Adj (e 0) (e 1) := e.map_adj_iff.2 (by simp)
    grind [aut_pathNat₁_apply_zero]
  | more k ih₀ ih₁ =>
    have h : pathNat₁.Adj (e (k + 1)) (e (k + 2)) := e.map_adj_iff.2 (by simp)
    have hne : e (k + 2) ≠ e k := fun h => by simpa using e.injective h
    grind

/-!
So the automorphism group of `pathNat₁` is trivial: every automorphism is the
identity `1`, and there is exactly one of them.
-/
lemma aut_pathNat₁_eq_one (e : pathNat₁ ≃g pathNat₁) : e = 1 := by
  ext k
  exact aut_pathNat₁_apply e k

lemma card_aut_pathNat₁ : Nat.card (pathNat₁ ≃g pathNat₁) = 1 :=
  Nat.card_eq_one_iff_exists.2 ⟨1, aut_pathNat₁_eq_one⟩

/-!
In particular `pathNat₁` is not vertex-transitive.
-/
lemma not_isVertexTransitive_pathNat₁ : ¬ pathNat₁.IsVertexTransitive := by
  intro h
  obtain ⟨e, he⟩ := h 0 1
  simp [aut_pathNat₁_apply_zero] at he

/-!
What makes `pathNat₁` asymmetric is that it has a single endpoint (a vertex of degree
one), `0`. A finite path with at least two vertices has two endpoints, and reversing
it is a non-trivial automorphism; likewise the two-way infinite path on `ℤ` has the
reflection `i ↦ -i` and the translations `i ↦ i + j` as automorphisms.
-/

/-!
## Automorphisms of Cycle Graphs

In
[Vertex-Transitivity](https://jt496.github.io/GraphTheoryInLean/Maps/#section-vertex-transitivity)
we showed that the cycle graph `C[n]` is vertex-transitive, using the rotations
`cycleGraphRotate d`, which send the vertex `d` to `0`. We now determine its whole
automorphism group. Besides the rotations there is an automorphism given by
reflecting the vertices, i.e. sending `k` to `-k` modulo `n`.
-/
/--
The automorphism of the cycle graph `C[n]` given by reflecting the vertices.
-/
@[simps]
def cycleGraphReflect {n : ℕ} : C[n] ≃g C[n] where
  toFun k := -k
  invFun k := -k
  left_inv k := by simp
  right_inv k := by simp
  map_rel_iff' := by
    match n with
    | 0 | 1 => simp
    | n + 2 =>
      intro a b
      change -a - -b = 1 ∨ -b - -a = 1 ↔ a - b = 1 ∨ b - a = 1
      simp [sub_eq_add_neg, add_comm, or_comm]

/-!
If `e : C[n + 2] ≃g C[n + 2]` is an automorphism of the cycle graph and
`e 1 - e 0 = 1` then `e` is a rotation, namely the one sending the vertex `e.symm 0`
to `0`. (We work with `C[n + 2]` throughout since `cycleGraph_adj` only
describes adjacency in `C[n + 2]`. The statements would remain (trivially) true for
`C[n + 1]`, but the classification of automorphisms below is *false* for `C[0]`:
the empty map is an automorphism, yet `Fin 0` has no element to witness the
existential.)
-/
lemma aut_cycleGraph_eq_rotate {n : ℕ} (e : C[n + 2] ≃g C[n + 2])
    (h : e 1 - e 0 = 1) : e = cycleGraphRotate (e.symm 0) := by
  let i := e 0
  have hstep : e 1 = 1 + i := by grind
  have hall : ∀ (j : ℕ) (hj : j < n + 2),
      e ⟨j, hj⟩ = ⟨j, hj⟩ + i := by
    intro j
    induction j using Nat.twoStepInduction with
    | zero => simp [i]
    | one  =>  simpa [add_comm] using hstep
    | more j ihj ihj1 =>
      intro hj2
      have hadj : C[n + 2].Adj (e ⟨j + 2, hj2⟩) (e ⟨j + 1, by grind⟩) :=
        e.toHom.map_adj (by
          rw [cycleGraph_adj]
          exact Or.inl (Fin.ext (by rw [Fin.sub_val_of_le (by simp)]; simp)))
      have hs : (⟨j + 1, by grind⟩ : Fin (n + 2)) = 1 + ⟨j, by grind⟩ := by
        apply Fin.ext
        change j + 1 = (1 + j) % (n + 2)
        rw [Nat.mod_eq_of_lt (by grind), add_comm]
      have hnext : (⟨j + 2, hj2⟩ : Fin (n + 2)) = 1 + ⟨j + 1, by grind⟩ := by
        apply Fin.ext
        change j + 2 = (1 + (j + 1)) % (n + 2)
        rw [Nat.mod_eq_of_lt (by grind), add_comm 1]
      rcases hadj with hadj | hadj
      · grind
      · have heq : e ⟨j + 2, hj2⟩ = e ⟨j, by grind⟩ := by grind
        have : j + 2 = j := Fin.mk.inj (e.toEquiv.injective heq)
        grind
  have h0 : e (-i) = 0 := by
    simpa [i] using hall (-i).val (-i).isLt
  have hsymm : e.symm 0 = -i := e.symm_apply_eq.2 h0.symm
  rw [hsymm]
  ext k
  simpa [i, sub_neg_eq_add] using congrArg Fin.val (hall k.val k.isLt)

/-!
If instead `e 0 - e 1 = 1` then `e` is a rotation followed by the reflection. To
see this note that `f = cycleGraphReflect ∘ e` satisfies `f 1 - f 0 = 1`, so `f` is
a rotation by the previous lemma, and hence `e = cycleGraphReflect ∘ f` is as
claimed (the reflection is an involution).
-/
lemma aut_cycleGraph_eq_rotate_trans_reflect {n : ℕ} (e : C[n + 2] ≃g C[n + 2])
    (h : e 0 - e 1 = 1) :
    e = (cycleGraphRotate (e.symm 0)).trans cycleGraphReflect := by
  let f := e.trans cycleGraphReflect
  have hf : f 1 - f 0 = 1 := by
    simpa [f, sub_eq_add_neg, add_comm] using h
  have hsymm : e.symm 0 = f.symm 0 := e.symm_apply_eq.2 (by simp [f])
  rw [hsymm, ← aut_cycleGraph_eq_rotate f hf]
  ext k
  simp [f]

/-!
Hence any automorphism of the cycle graph `C[n + 2]` is either a rotation or a
rotation followed by reflection.
-/
lemma aut_cycleGraph {n : ℕ} (e : C[n + 2] ≃g C[n + 2]) : ∃ i : Fin (n + 2),
    e = cycleGraphRotate i ∨ e = (cycleGraphRotate i).trans cycleGraphReflect := by
  have h0 : C[n + 2].Adj (e 0) (e 1) :=
    e.toHom.map_adj (by grind [cycleGraph_adj])
  rcases h0 with h | h
  · exact ⟨_, Or.inr (aut_cycleGraph_eq_rotate_trans_reflect e h)⟩
  · exact ⟨_, Or.inl (aut_cycleGraph_eq_rotate e h)⟩

/-!
For `n ≥ 3` the automorphism group of `C[n]` is the dihedral group
`DihedralGroup n`, which is why we state the result for `C[n + 3]`. For `n < 3` it
fails for trivial reasons:
* `C[0]` has vertex type `Fin 0`, hence exactly one automorphism, while
  `DihedralGroup 0` is infinite;
* `C[1]` has one vertex, hence one automorphism, while `DihedralGroup 1` has two
  elements;
* `C[2]` is a single edge, with two automorphisms, while `DihedralGroup 2` has four
  elements.

Our rotations match Mathlib's conventions for `DihedralGroup` exactly: `r i`
corresponds to `cycleGraphRotate i` and, since `sr i = sr 0 * r i`, the reflection
`sr i` corresponds to `cycleGraphRotate i` followed by the reflection. In both cases
the index `i` is the vertex sent to `0`, i.e. `e.symm 0`.
-/
#source DihedralGroup
/-!
Multiplicativity is easiest to check in the direction from `DihedralGroup (n + 3)`,
where it amounts to four short computations with rotations and reflections, so we
build the isomorphism in that direction and then take its inverse.
-/
/-- The automorphism group of the cycle graph `C[n + 3]` is isomorphic to the
dihedral group of order `2(n + 3)`. -/
def autCycleGraphMulEquivDihedral (n : ℕ) :
    (C[n + 3] ≃g C[n + 3]) ≃* DihedralGroup (n + 3) :=
  MulEquiv.symm
    { toFun := fun d => match d with
        | .r i => cycleGraphRotate ((ZMod.finEquiv (n + 3)).symm i)
        | .sr i => (cycleGraphRotate ((ZMod.finEquiv (n + 3)).symm i)).trans
            cycleGraphReflect
      invFun e := if e 1 - e 0 = 1 then .r (ZMod.finEquiv (n + 3) (e.symm 0))
        else .sr (ZMod.finEquiv (n + 3) (e.symm 0))
      left_inv d := by
        have hneg : (-1 : Fin (n + 3)) ≠ 1 := by simp [Fin.ext_iff]
        rcases d with i | i <;> simp [hneg]
      right_inv e := by
        by_cases h : e 1 - e 0 = 1
        · simpa [h] using (aut_cycleGraph_eq_rotate e h).symm
        · have h0 : C[n + 3].Adj (e 0) (e 1) :=
            e.toHom.map_adj (by grind [cycleGraph_adj])
          rw [cycleGraph_adj] at h0
          simpa [h] using
            (aut_cycleGraph_eq_rotate_trans_reflect e (h0.resolve_right h)).symm
      map_mul' := by
        rintro (i | i) (j | j) <;>
        · ext k
          simp [map_add, map_sub]
          abel_nf }

/-!
Combining this with the isomorphism `hypercubeTwoIsoCycleFour : Q[2] ≃g C[4]` from
the exercises of
[Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#chapter-maps), the
automorphism group of the square `Q[2]` is the dihedral group of order `8`. (We
identify the automorphism group of every hypercube in
[The Automorphism Group of the Hypercube*](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-the-automorphism-group-of-the-hypercube).)
-/
/-- The automorphism group of the square `Q[2]` is the dihedral group of
order 8. -/
abbrev autHypercubeTwoMulEquivDihedral : (Q[2] ≃g Q[2]) ≃* DihedralGroup 4 :=
  hypercubeTwoIsoCycleFour.autCongr.trans (autCycleGraphMulEquivDihedral 1)

/-!
# The Adjacency Matrix

A finite graph can also be studied via matrices indexed by its vertices. Mathlib's
`Matrix V V R` is the type of functions `V → V → R`, so no ordering of the vertices
is needed.

The *adjacency matrix* `G.adjMatrix R` has `(u, v)` entry `1` if `u` and `v` are
adjacent and `0` otherwise. It is symmetric with zero diagonal.

[Figure: A graph $G$ and its adjacency matrix $A(G)$](https://jt496.github.io/GraphTheoryInLean/figures/adjmatrix.svg)
-/
#source adjMatrix

#eval C[4].adjMatrix ℕ -- !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

#check isSymm_adjMatrix -- (G.adjMatrix R).IsSymm

/-!
The `(u, v)` entry of the `n`-th power of the adjacency matrix counts the walks of
length `n` from `u` to `v`
([Walks](https://jt496.github.io/GraphTheoryInLean/Walks/#chapter-walks)). The walks
of a given length between two vertices form a `Finset`, `finsetWalkLength`, so both
sides can be computed.

[Figure: Two length-2 walks from vertex 1 to vertex 3 and the entry $(A^2)_{1,3}=2$](https://jt496.github.io/GraphTheoryInLean/figures/walkcount.svg)
-/
#check adjMatrix_pow_apply_eq_card_walk
-- (G.adjMatrix R ^ n) u v = Fintype.card {p : G.Walk u v // p.length = n}

#eval (C[5].adjMatrix ℕ ^ 5) 0 0 -- 2
#eval (C[5].finsetWalkLength 5 0 0).card -- 2

/-!
The two closed walks of length `5` from `0` in `C[5]` go once round the cycle in
either direction. Walks of length `2` from `u` to `v` correspond to common
neighbours of `u` and `v`; in particular the diagonal entries of `A²` are the
degrees.
-/
#check walkLengthTwoEquivCommonNeighbors
-- {p : G.Walk u v // p.length = 2} ≃ G.commonNeighbors u v

#check adjMatrix_mul_self_apply_self -- (A * A) i i = G.degree i

/-!
The adjacency matrix determines the graph, and a bijection of the vertices is an
automorphism exactly when it preserves the adjacency matrix: relabelling the rows and
columns of `A` by `σ` leaves `A` unchanged. In matrix language, the permutation
matrix `P` of `σ` satisfies `P A Pᵀ = A`, i.e. `P` commutes with `A`. In Lean we
relabel with `Matrix.submatrix`, which composes the row and column indices with `σ`.

A permutation `σ` of the vertices is an automorphism, i.e. preserves adjacency, iff
it preserves the adjacency matrix.
-/
theorem adjMatrix_submatrix_eq_iff [DecidableRel G.Adj] {R : Type*} [Semiring R]
    [Nontrivial R] (σ : V ≃ V) :
    (G.adjMatrix R).submatrix σ σ = G.adjMatrix R ↔
      ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v := by
  constructor
  · intro h u v
    have := congrFun (congrFun h u) v
    by_cases h₁ : G.Adj (σ u) (σ v) <;> by_cases h₂ : G.Adj u v <;>
      simp_all [adjMatrix_apply]
  · intro h
    ext u v
    simp [adjMatrix_apply, h]

/-!
For an automorphism `f`, Mathlib's `Embedding.submatrix_adjMatrix` already gives
`(G.adjMatrix R).submatrix f f = G.adjMatrix R`, and so do its powers, since
relabelling rows and columns is a ring isomorphism (`Matrix.reindexRingEquiv`).
Combined with the walk-counting formula, this shows that automorphisms preserve the
number of walks of each length between two vertices. In a vertex-transitive graph it
follows that every vertex lies in the same number of closed walks of length `k`.

In a vertex-transitive graph the diagonal entries of each power of the adjacency
matrix are all equal.
-/
theorem IsVertexTransitive.adjMatrix_pow_apply_self [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {R : Type*} [Semiring R] (h : G.IsVertexTransitive)
    (k : ℕ) (u v : V) :
    (G.adjMatrix R ^ k) u u = (G.adjMatrix R ^ k) v v := by
  obtain ⟨f, rfl⟩ := h u v
  have hA : (G.adjMatrix R).reindex f f = G.adjMatrix R := f.reindex_adjMatrix R
  have hk : (G.adjMatrix R ^ k).reindex f f = G.adjMatrix R ^ k := by
    rw [← Matrix.coe_reindexRingEquiv, map_pow, Matrix.coe_reindexRingEquiv, hA]
  simpa using congrFun (congrFun hk (f u)) (f u)

/-!
Summing over the vertices, the trace of `Aᵏ` is the number of vertices times any one
diagonal entry.
-/
theorem IsVertexTransitive.trace_adjMatrix_pow [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {R : Type*} [Semiring R] (h : G.IsVertexTransitive)
    (k : ℕ) (v : V) :
    (G.adjMatrix R ^ k).trace = Fintype.card V • (G.adjMatrix R ^ k) v v := by
  rw [Matrix.trace, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun u _ => h.adjMatrix_pow_apply_self k u v

/-!
So in a vertex-transitive graph on `n` vertices each vertex lies on `tr(Aᵏ) / n`
closed walks of length `k`. (We write the walks as `{p : G.Walk v v | p.length = k}`,
the form used by `adjMatrix_pow_apply_eq_card_walk`.)

In a vertex-transitive graph on `n` vertices each vertex lies in `tr(Aᵏ) / n` closed
walks of length `k`.
-/
theorem IsVertexTransitive.card_walk_self_eq_trace_div [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (h : G.IsVertexTransitive) (k : ℕ) (v : V) :
    Fintype.card {p : G.Walk v v | p.length = k} =
      (G.adjMatrix ℕ ^ k).trace / Fintype.card V := by
  rw [h.trace_adjMatrix_pow k v, smul_eq_mul,
    Nat.mul_div_cancel_left _ (Fintype.card_pos_iff.2 ⟨v⟩),
    adjMatrix_pow_apply_eq_card_walk, Nat.cast_id]

/-!
For example, the cycle `C[5]` is vertex-transitive (`isVertexTransitive_cycleGraph`)
and has `10` closed walks of length `5`, so each of its `5` vertices lies on two of
them: the two directions round the cycle.
-/
#eval (C[5].adjMatrix ℕ ^ 5).trace -- 10

example (v : Fin 5) : Fintype.card {p : C[5].Walk v v | p.length = 5} = 2 := by
  rw [(isVertexTransitive_cycleGraph 5).card_walk_self_eq_trace_div]
  decide

/-!
The eigenvalues of the adjacency matrix make up the *spectrum* of `G`, a central
object of algebraic graph theory. (Mathlib's `spectrum R M` is the set of `r : R` for
which `r • 1 - M` is not invertible; for a matrix over a field these are its
eigenvalues.) Mathlib has little about it so far: for example, a `d`-regular graph
has eigenvalue `d`, with the all-ones eigenvector. (In
[The Laplacian](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-the-laplacian)
we show that its multiplicity is the number of connected components.)
-/
#check IsRegularOfDegree.mem_spectrum_adjMatrix
-- G.IsRegularOfDegree d → (d : R) ∈ spectrum R (G.adjMatrix R)

/-!
Isomorphic graphs have the same adjacency matrix up to relabelling, so they have the
same characteristic polynomial, and hence the same eigenvalues with the same
multiplicities.

Isomorphic graphs have adjacency matrices with the same characteristic polynomial.
-/
theorem Iso.charpoly_adjMatrix [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : Type*} [CommRing R] (f : G ≃g H) :
    (G.adjMatrix R).charpoly = (H.adjMatrix R).charpoly := by
  rw [← f.reindex_adjMatrix R, Matrix.charpoly_reindex]

/-!
The converse fails: the star `K[4, 1]` and the disjoint union `C[4] ⊕g K[1]` of a
`4`-cycle and a single vertex are two graphs on the same vertex type `Fin 4 ⊕ Fin 1`,
with the same characteristic polynomial `x⁵ - 4x³`, but are not isomorphic. Mathlib's
polynomials are not computable, so neither `#eval` nor `decide` can help: `#eval`
refuses because `Matrix.charpoly` is `noncomputable`, and `decide` cannot evaluate
polynomial arithmetic. But we can still prove them.

We relabel the vertices by `Fin 5` (using `finSumFinEquiv`) and use `decide` only to
check the resulting integer matrix, a finite computation. We then expand the
determinant along its rows with `Matrix.det_succ_row_zero`, and finish with `ring`.
-/
open Polynomial in
example : (K[4, 1].adjMatrix ℤ).charpoly = X ^ 5 - 4 * X ^ 3 := by
  rw [← Matrix.charpoly_reindex finSumFinEquiv]
  have hM : (K[4, 1].adjMatrix ℤ).reindex finSumFinEquiv finSumFinEquiv =
      !![0, 0, 0, 0, 1; 0, 0, 0, 0, 1; 0, 0, 0, 0, 1;
        0, 0, 0, 0, 1; 1, 1, 1, 1, 0] := by
    decide
  rw [hM, Matrix.charpoly, Matrix.det_succ_row_zero]
  -- expanding the determinant along its rows leaves a polynomial identity
  suffices X * (X * (X * (X * X + -1) + -X) + (-1) ^ 3 * (X * X)) +
      -((-1) ^ 4 * (X * (X * X))) = X ^ 5 - 4 * X ^ 3 by
    simpa [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.charmatrix_apply,
      Matrix.submatrix_apply, Fin.succAbove]
  ring

open Polynomial in
example : ((C[4] ⊕g K[1]).adjMatrix ℤ).charpoly = X ^ 5 - 4 * X ^ 3 := by
  rw [← Matrix.charpoly_reindex finSumFinEquiv]
  have hM : ((C[4] ⊕g K[1]).adjMatrix ℤ).reindex finSumFinEquiv finSumFinEquiv =
      !![0, 1, 0, 1, 0; 1, 0, 1, 0, 0; 0, 1, 0, 1, 0;
        1, 0, 1, 0, 0; 0, 0, 0, 0, 0] := by
    decide
  rw [hM, Matrix.charpoly, Matrix.det_succ_row_zero]
  -- expanding the determinant along its rows leaves a polynomial identity
  suffices X * (X * (X * (X * X) + -X) + -(X * X)) +
      (-(X * (X * X)) + (-1) ^ 3 * (X * (X * X))) = X ^ 5 - 4 * X ^ 3 by
    simpa [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.charmatrix_apply,
      Matrix.submatrix_apply, Fin.succAbove]
  ring
#check IsIsolated
/-!
Graphs with the same eigenvalues cannot be told apart by counting edges or triangles.
The eigenvalues determine the trace of every power `Aᵏ`, i.e. the number of closed
walks of each length, and `tr(A²)` is twice the number of edges while `tr(A³)` is six
times the number of triangles. (Both of our graphs have `4` edges and no triangles.)
But `K[4, 1]` has no isolated vertices, while `C[4] ⊕g K[1]` obviously does.
-/
example : IsEmpty (K[4, 1] ≃g C[4] ⊕g K[1]) := ⟨fun e => by
  have h₁ : ∀ v, ∃ w, K[4, 1].Adj v w := by decide
  have h₂ : ∀ w, ¬ (C[4] ⊕g K[1]).Adj (.inr 0) w := by decide
  obtain ⟨w, hw⟩ := h₁ (e.symm (.inr 0))
  exact h₂ (e w) (by simpa using e.map_adj_iff.2 hw)⟩

/-!
# The Laplacian

The *degree matrix* `G.degMatrix R` is the diagonal matrix of degrees, and the
*Laplacian* is `G.lapMatrix R = G.degMatrix R - G.adjMatrix R`. The diagonal entries
of the degree matrix, which are also its eigenvalues, form the `degreeMultiset` of
[Degree Sequences*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-degree-sequences),
and listing them in non-increasing order gives the `degreeSequence`.

[Figure: A graph $G$ together with $D$, $A$, and the Laplacian $L = D - A$](https://jt496.github.io/GraphTheoryInLean/figures/laplacian.svg)
-/
#source degMatrix -- Matrix V V R := Matrix.diagonal (G.degree ·)
#source lapMatrix -- Matrix V V R := G.degMatrix R - G.adjMatrix R

#eval C[4].lapMatrix ℤ -- !![2, -1, 0, -1; -1, 2, -1, 0; 0, -1, 2, -1; -1, 0, -1, 2]

/-!
The key property of the Laplacian is its quadratic form: for `x : V → R` we have
`xᵀ L x = ∑ (x u - x v)²`, summed over the edges `u — v`. (Mathlib sums over ordered
pairs of adjacent vertices and divides by `2`.)
-/
#check lapMatrix_toLinearMap₂'
-- xᵀ L x = (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2

/-!
Over `ℝ`, this form is a sum of squares, so the Laplacian is positive semidefinite.
It vanishes iff `x` is constant along every edge, and hence on every connected
component. Mathlib writes `M *ᵥ x` (`Matrix.mulVec`) for the product of a matrix
`M` and a vector `x`, i.e. the column vector `M x`, whose entry at `i` is
`∑ j, M i j * x j`. For the Laplacian the entry at a vertex `v` works out to
`∑ (x v - x w)`, summed over the neighbours `w` of `v` (`lapMatrix_mulVec_apply'`).
If `L *ᵥ x = 0` then `xᵀ L x = 0`, and conversely if `x` is constant along every
edge then every entry of `L *ᵥ x` is `0`. So the *kernel* of `L`, the set of vectors
`x` with `L *ᵥ x = 0`, consists of the functions that are constant on components.
-/
#check lapMatrix_mulVec_apply'
-- (G.lapMatrix R *ᵥ x) v = ∑ u ∈ G.neighborFinset v, (x v - x u)

#check posSemidef_lapMatrix -- (G.lapMatrix R).PosSemidef

#check lapMatrix_mulVec_eq_zero_iff_forall_reachable
-- G.lapMatrix ℝ *ᵥ x = 0 ↔ ∀ i j, G.Reachable i j → x i = x j

/-!
Counting dimensions gives the first theorem of spectral graph theory: the number of
connected components of `G` is the dimension of the kernel of its Laplacian, i.e.
the multiplicity of the eigenvalue `0`. In Lean, `M.toLin'` is the matrix `M` viewed
as a linear map `(V → ℝ) → (V → ℝ)`, `.ker` is its kernel, and `Module.finrank ℝ`
gives the dimension of a subspace.
-/
#check card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix
-- Fintype.card G.ConnectedComponent = Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker

example : Module.finrank ℝ ((C[3]⊕g C[4]).lapMatrix ℝ).toLin'.ker = 2 := by
  rw [← card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  decide

/-!
For a `d`-regular graph the degree matrix is `d • 1`, so `L = d • 1 - A`, and the
kernel of `L` is the eigenspace of `A` for the eigenvalue `d`. So the multiplicity of
`d` as an eigenvalue of `A` is the number of connected components. This sharpens
`IsRegularOfDegree.mem_spectrum_adjMatrix` above. In Lean, `End.eigenspace f μ` is
the kernel of `f - μ • 1`.
-/
/-- In a `d`-regular graph the multiplicity of the eigenvalue `d` of the adjacency
matrix is the number of connected components. -/
theorem IsRegularOfDegree.finrank_eigenspace_adjMatrix [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {d : ℕ} (hd : G.IsRegularOfDegree d) :
    Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).toLin' d) =
      Fintype.card G.ConnectedComponent := by
  rw [card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix,
    Module.End.eigenspace_def, lapMatrix, hd.degMatrix_eq ℝ]
  have : (G.adjMatrix ℝ).toLin' - (d : ℝ) • 1 =
      -((d : Matrix V V ℝ) - G.adjMatrix ℝ).toLin' := by
    ext i j
    simp [Matrix.toLin'_apply, Pi.single_apply, Matrix.natCast_apply, eq_comm]
  rw [this, LinearMap.ker_neg]

/-!
For example, the hypercube `Q[n]` is `n`-regular and connected, so `n` is a simple
eigenvalue of its adjacency matrix. As in
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond),
we first put the filtering `LocallyFinite` instance in scope, since the adjacency
matrix is built from `DecidableRel Q[n].Adj`.
-/
example (n : ℕ) :
    Module.finrank ℝ (Module.End.eigenspace (Q[n].adjMatrix ℝ).toLin' n) = 1 := by
  -- put the filtering instance in scope, so that
  -- `hypercube_isRegularOfDegree` uses it
  let : Q[n].LocallyFinite := fun v => Subtype.fintype _
  rw [(hypercube_isRegularOfDegree n).finrank_eigenspace_adjMatrix]
  -- `Q[n]` is connected, so it has exactly one connected component
  exact (hypercube_connected n).card_connectedComponent

/-!
The *incidence matrix* `G.incMatrix R` has rows indexed by vertices and columns by
`Sym2 V`, with `(v, e)` entry `1` iff `v` is an endpoint of the edge `e`. The product
of the incidence matrix and its transpose is `D + A`, the *signless* Laplacian.
-/
#check incMatrix_mul_transpose
-- B * Bᵀ has the degrees on the diagonal and the adjacency matrix elsewhere

/-!
Kirchhoff's matrix-tree theorem (the number of spanning trees is any cofactor of the
Laplacian) is not yet in Mathlib.

# Strongly Regular Graphs

A graph is *strongly regular* with parameters `(n, k, ℓ, μ)` if it has `n` vertices,
is `k`-regular, any two adjacent vertices have exactly `ℓ` common neighbours, and any
two distinct non-adjacent vertices have exactly `μ` common neighbours.
-/
#source IsSRGWith

/-!
The Petersen graph
([Kneser Graphs*](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-kneser-graphs))
is strongly regular with parameters `(10, 3, 0, 1)`: it has girth `5`, so adjacent
vertices have no common neighbours and non-adjacent vertices have at most one, and
its diameter is `2`, so they have at least one. We can check each field with
`decide`, but two need an initial `intro` since `decide` needs a `Decidable` instance
for the exact statement and neither `IsRegularOfDegree` nor `Pairwise` has one.
-/
lemma petersenGraph_isSRGWith : petersenGraph.IsSRGWith 10 3 0 1 where
  card := by decide
  regular := by intro v; decide +revert
  of_adj := by decide
  of_not_adj := by intro u v; decide +revert

/-!
Counting the paths of length `2` from a fixed vertex in two ways shows that the
parameters satisfy `k(k − ℓ − 1) = (n − k − 1)μ`. For the Petersen graph this is
`3 · 2 = 6 · 1`.
-/
#check IsSRGWith.param_eq
-- G.IsSRGWith n k ℓ μ → 0 < n → k * (k - ℓ - 1) = (n - k - 1) * μ

/-!
The diameter of a strongly regular graph with `μ ≠ 0` that is not complete is `2`.
This recovers `ediam_petersenGraph`, which we proved by hand in
[Moore Graphs](https://jt496.github.io/GraphTheoryInLean/Distance/#section-moore-graphs).
-/
#check IsSRGWith.ediam_eq_two -- G.IsSRGWith n k ℓ μ → G ≠ ⊤ → μ ≠ 0 → G.ediam = 2

example : petersenGraph.ediam = 2 := by
  have : Nontrivial {s : Finset (Fin 5) // s.card = 2} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by decide)
  have hne : ¬ petersenGraph.Adj ⟨{0, 1}, rfl⟩ ⟨{0, 2}, rfl⟩ := by decide
  refine petersenGraph_isSRGWith.ediam_eq_two (fun h => hne ?_) one_ne_zero
  rw [h, top_adj]
  decide

/-!
The complement of a strongly regular graph is strongly regular. The complement of the
Petersen graph is the line graph of `K[5]`, with parameters `(10, 6, 3, 4)`.
-/
example : petersenGraphᶜ.IsSRGWith 10 6 3 4 :=
  petersenGraph_isSRGWith.compl

/-!
In terms of the adjacency matrix `A`, the definition says exactly that
`A² = kI + ℓA + μ(J − I − A)`, where `J − I − A` is the adjacency matrix of the
complement. This quadratic equation forces `A` to have at most three distinct
eigenvalues. It is the starting point of the Hoffman–Singleton theorem: a Moore graph
of diameter `2`
([Moore Graphs](https://jt496.github.io/GraphTheoryInLean/Distance/#section-moore-graphs))
is strongly regular with `ℓ = 0` and `μ = 1`, and the multiplicities of its
eigenvalues must be integers, which forces its degrees to be `2`, `3`, `7` or `57`.
-/
#check IsSRGWith.matrix_eq
-- A ^ 2 = k • 1 + ℓ • A + μ • Gᶜ.adjMatrix α, where A = G.adjMatrix α

/-!
# The Hypercube and the Hamming Graph

When we first introduced the hypercube in
[Hypercube](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-hypercube)
we gave two other constructions. One of these was the Hamming graph
`hypercubeHamming n`: the graph on `Fin n → Bool` in which two vertices are adjacent
iff their Hamming distance, computed by Mathlib's `hammingDist` for Pi-types, is one.
Having identified the graph distance in `Q[n]` with the Hamming distance in
[Distance in the Hypercube](https://jt496.github.io/GraphTheoryInLean/Distance/#section-distance-in-the-hypercube),
we are now in a position to prove that this construction agrees with the one we
adopted, i.e. `Q[n] ≃g hypercubeHamming n`.

First we need to identify the two vertex types, i.e. give an equiv
`HypercubeVert n ≃ (Fin n → Bool)`. We build this by recursion on `n`. The base case
holds since both types have exactly one element. In the inductive step we send
`(v, b)` to the function whose first `n` coordinates are those of `v` and whose last
coordinate is `b`. Mathlib's `Fin.snoc`, which appends an element at the end of a
tuple, does exactly this (and `Fin.snocEquiv` is `Fin.snoc` as an equiv).
-/
#check @Fin.snoc      -- append an element at the end of an `n`-tuple
#check Fin.snocEquiv  -- `Fin.snoc` as an equiv

/-- The equiv between the two vertex types of the hypercube, `HypercubeVert n` and
`Fin n → Bool`, sending `(v, b)` to `Fin.snoc v b`, so `b` is the last coordinate. -/
def HypercubeVert.equivPi : (n : ℕ) → HypercubeVert n ≃ (Fin n → Bool)
  | 0 => Equiv.ofUnique Unit _
  | n + 1 => ((equivPi n).prodCongr (Equiv.refl Bool)).trans <|
      (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => Bool)

/-!
Unfolding the equiv one step is definitionally `Fin.snoc`, and marking this as
`@[simp]` lets `simp` compute with `equivPi` recursively.
-/
@[simp]
lemma HypercubeVert.equivPi_succ_apply {n : ℕ} (v : HypercubeVert n) (b : Bool) :
    equivPi (n + 1) (v, b) = Fin.snoc (equivPi n v) b := rfl

/-!
To transfer distances along the equiv we need to know how Mathlib's `hammingDist`
interacts with `Fin.snoc`: appending a coordinate to each of two vertices increases
their Hamming distance by one exactly when the appended coordinates differ. (Note how
this mirrors the recursion in `HypercubeVert.hammingDist`.) To prove this we write
the Hamming distance as a sum of indicators, using `Finset.card_filter`, and split
off the last coordinate with `Fin.sum_univ_castSucc`.
-/
lemma hammingDist_snoc {n : ℕ} {β : Type*} [DecidableEq β] (x y : Fin n → β)
    (a b : β) :
    hammingDist (Fin.snoc x a : Fin (n + 1) → β) (Fin.snoc y b) =
      hammingDist x y + if a = b then 0 else 1 := by
  simp only [hammingDist, Finset.card_filter, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, ne_eq, ite_not]

/-!
The Hamming distance of `HypercubeVert n` vertices agrees with the Hamming distance
of the corresponding functions `Fin n → Bool`, by induction on `n`.
-/
@[simp]
lemma HypercubeVert.hammingDist_equivPi {n : ℕ} (u v : HypercubeVert n) :
    _root_.hammingDist (equivPi n u) (equivPi n v) = u.hammingDist v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨u, b⟩ := u
    obtain ⟨v, c⟩ := v
    simp [hammingDist_snoc, ih]

/-!
Adjacency in the Hamming graph is Hamming distance one, by definition.
-/
@[simp]
lemma hypercubeHamming_adj {n : ℕ} {x y : Fin n → Bool} :
    (hypercubeHamming n).Adj x y ↔ hammingDist x y = 1 := Iff.rfl

/-!
We can now give the graph isomorphism: the underlying equiv is
`HypercubeVert.equivPi`, and it respects adjacency since both adjacency relations say
exactly "Hamming distance one".
-/

/-- The hypercube `Q[n]` (the box product construction) is isomorphic to the Hamming
graph construction `hypercubeHamming n` on `Fin n → Bool`. -/
def hypercubeIsoHamming (n : ℕ) : Q[n] ≃g hypercubeHamming n where
  toEquiv := HypercubeVert.equivPi n
  map_rel_iff' := by
    simp [hypercube_adj_iff_hammingDist_eq_one]

/-!
This isomorphism is a bridge between the two constructions: results proved for
`Q[n]` by induction transport to `hypercubeHamming n`, while statements that need
the coordinates of a vertex, such as identifying the automorphism group of the
hypercube, are more naturally proved for `hypercubeHamming n` and transported back.

Transporting `edist_eq_hammingDist` along `hypercubeIsoHamming` shows that the graph
distance in the Hamming graph is exactly the Hamming distance.
-/
lemma hypercubeHamming_edist_eq {n : ℕ} (x y : Fin n → Bool) :
    (hypercubeHamming n).edist x y = hammingDist x y := by
  obtain ⟨u, rfl⟩ := (HypercubeVert.equivPi n).surjective x
  obtain ⟨v, rfl⟩ := (HypercubeVert.equivPi n).surjective y
  exact ((hypercubeIsoHamming n).edist_eq u v).trans (by simp [edist_eq_hammingDist])

/-!
# The Automorphism Group of the Hypercube *

As a substantial application of the bridge we identify the automorphism group of the
hypercube: it is the *hyperoctahedral group*, the wreath product `ℤ/2 ≀ Sₙ` of order
`2ⁿ · n!`. Concretely every automorphism of the hypercube is uniquely a composition
of a *translation* (`xor` by a fixed vertex) and a *coordinate permutation*, and the
wreath product is the semidirect product `(ℤ/2)ⁿ ⋊ Sₙ` that records how coordinate
permutations act on translations.

We work in the Hamming model and transport the result to `Q[n]` at the end. The
proof has four steps.
1. Translations and coordinate permutations are automorphisms of the Hamming graph.
2. Together they give a group homomorphism from `(ℤ/2)ⁿ ⋊ Sₙ` to its automorphism
   group.
3. This homomorphism is injective: evaluate at `0` and at the basis vectors `eᵢ`.
4. It is surjective. After composing with a translation, an automorphism fixes `0`.
   It then preserves Hamming weight, so it permutes the basis vectors, which gives a
   permutation `σ`. Undoing `σ` leaves an automorphism fixing `0` and every `eᵢ`,
   which is the identity by a rigidity argument: the coordinates of a vertex can be
   read off from its distances to `0` and to the `eᵢ`.

The key to making this precise in Lean is that Mathlib makes `Bool` a `BooleanRing`,
with `0 = false`, `1 = true` and addition given by `xor`. Consequently the vertex
type `Fin n → Bool` of the Hamming graph is an additive group, namely `(ℤ/2)ⁿ`, with
pointwise `xor` (`^^`) as addition: translations are simply `(t + ·)`.
-/
example {n : ℕ} : AddCommGroup (Fin n → Bool) := inferInstance
example (a b : Bool) : a + b = (a ^^ b) := rfl

/-!
Since addition on `Bool` vectors has characteristic two, negation is the identity
and adding the same vector twice gives `0`; we record three `simp` lemmas.
-/
@[simp]
lemma boolVec_neg {n : ℕ} (x : Fin n → Bool) : -x = x := rfl

@[simp]
lemma boolVec_add_self {n : ℕ} (x : Fin n → Bool) : x + x = 0 :=
  funext fun j => Bool.xor_self (x j)

@[simp]
lemma boolVec_add_add_cancel {n : ℕ} (x y : Fin n → Bool) : x + (x + y) = y := by
  rw [← add_assoc, boolVec_add_self, zero_add]

/-!
The vectors of Hamming weight one are exactly the standard basis vectors
`Pi.single i true` (all coordinates `false` except the `i`-th).
-/
@[simp]
lemma hammingNorm_single {n : ℕ} (i : Fin n) :
    hammingNorm (Pi.single i true : Fin n → Bool) = 1 := by
  simp [hammingNorm, Pi.single_apply, Finset.filter_eq']

lemma hammingNorm_eq_one_iff {n : ℕ} {x : Fin n → Bool} :
    hammingNorm x = 1 ↔ ∃ i, x = Pi.single i true := by
  rw [hammingNorm, Finset.card_eq_one]
  refine exists_congr fun i => ?_
  simp only [Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, funext_iff, Pi.single_apply]
  refine forall_congr' fun j => ?_
  split_ifs <;> simp_all [Bool.zero_eq_false]

/-!
Adjacency in the Hamming graph has a clean algebraic description: `x` and `y` are
adjacent iff they differ by a basis vector.
-/
lemma hypercubeHamming_adj_iff_exists {n : ℕ} {x y : Fin n → Bool} :
    (hypercubeHamming n).Adj x y ↔ ∃ i, y = x + Pi.single i true := by
  rw [hypercubeHamming_adj, hammingDist_eq_hammingNorm,
    boolVec_neg, hammingNorm_eq_one_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← hi, boolVec_add_add_cancel]
  · rintro ⟨i, rfl⟩
    exact ⟨i, boolVec_add_add_cancel _ _⟩

/-!
## Translations and Coordinate Permutations

Translation by a fixed vector `t` is an automorphism of the Hamming graph: it
preserves the Hamming distance since `(t + x) - (t + y) = x - y`. Under the
isomorphism `hypercubeIsoHamming`, this corresponds to the automorphism
`hypercubeTranslate` of `Q[n]` from
[Vertex-Transitivity of Hypercubes](https://jt496.github.io/GraphTheoryInLean/Maps/#section-vertex-transitivity-of-hypercubes).
There we had to define `xor` on `HypercubeVert n` and prove its basic properties
(such as `HypercubeVert.xor_xor`) by hand. On `Fin n → Bool`, addition is pointwise
`xor`, and the group structure (associativity, `0`, negation) comes for free from
Mathlib. Only the characteristic-two `simp` lemmas above (`x + x = 0` and its
consequences) needed proofs, each a line or two, since Mathlib has no `BooleanRing`
instance on `Fin n → Bool`.
-/
/-- Translation by `t` (pointwise `xor`) as an automorphism of the Hamming graph. -/
def hammingTranslate {n : ℕ} (t : Fin n → Bool) :
    hypercubeHamming n ≃g hypercubeHamming n where
  toEquiv := Equiv.addLeft t
  map_rel_iff' := by
    intro x y
    grind [Equiv.coe_addLeft, hypercubeHamming_adj, hammingDist_eq_hammingNorm]

@[simp]
lemma hammingTranslate_apply {n : ℕ} (t x : Fin n → Bool) :
    hammingTranslate t x = t + x := rfl

/-!
Permuting the coordinates by `σ : Equiv.Perm (Fin n)` also preserves the Hamming
distance, and hence is an automorphism of the Hamming graph.
-/
lemma hammingDist_comp_perm {ι : Type*} [Fintype ι] {β : Type*}
    [DecidableEq β] (σ : Equiv.Perm ι) (x y : ι → β) :
    hammingDist (x ∘ σ) (y ∘ σ) = hammingDist x y := Finset.card_equiv σ (by simp)

/-- Permutation of coordinates by `σ` as an automorphism of the Hamming graph;
`x` is sent to `x ∘ σ.symm` so that the `i`-th coordinate of the image is the
`σ⁻¹ i`-th coordinate of `x`. -/
def hammingPermute {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    hypercubeHamming n ≃g hypercubeHamming n where
  toEquiv := σ.arrowCongr (Equiv.refl Bool)
  map_rel_iff' {x y} := by
    rw [hypercubeHamming_adj, hypercubeHamming_adj,
      ← hammingDist_comp_perm σ.symm x y]
    rfl

@[simp]
lemma hammingPermute_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    hammingPermute σ x = x ∘ σ.symm := rfl

/-!
In the automorphism group the inverses of translations and coordinate permutations
are computed by `symm`; in particular translation is an involution (characteristic
two again!).
-/
@[simp]
lemma hammingTranslate_inv_apply {n : ℕ} (t x : Fin n → Bool) :
    (hammingTranslate t)⁻¹ x = t + x := rfl

@[simp]
lemma hammingPermute_inv_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    (hammingPermute σ)⁻¹ x = x ∘ σ := rfl

/-!
## The Hyperoctahedral Group

We can now describe the translations and coordinate permutations as a single group:
the semidirect product of `(ℤ/2)ⁿ` (as `Fin n → Bool` under pointwise `xor`) by the
symmetric group `Sₙ`, where a permutation acts on a translation vector by permuting
its coordinates. This is exactly the wreath product `ℤ/2 ≀ Sₙ`, known as the
*hyperoctahedral group*.

Mathlib's `SemidirectProduct N G φ` (notation `N ⋊[φ] G`) is stated for
multiplicative groups, so we need to wrap our additive group `Fin n → Bool` in
`Multiplicative`. (This is a type synonym: `Multiplicative α` has the same
elements as `α`, but its group operation `*` is the `+` of `α`. We pass between the
two with the identity maps `Multiplicative.ofAdd` and `Multiplicative.toAdd`, and
turn an additive automorphism into a multiplicative one with
`AddEquiv.toMultiplicative`.) The action `φ` sends `σ` to the group
automorphism `t ↦ t ∘ σ.symm` of `Fin n → Bool`, which Mathlib provides as
`AddEquiv.arrowCongr σ (AddEquiv.refl Bool)`.
-/
/-- The action of `Equiv.Perm (Fin n)` on translation vectors by permuting
coordinates, as a `MonoidHom` into the automorphisms of
`Multiplicative (Fin n → Bool)`. -/
def hammingPhi (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (Multiplicative (Fin n → Bool)) where
  toFun σ := AddEquiv.toMultiplicative (AddEquiv.arrowCongr σ (AddEquiv.refl Bool))
  map_one' := by ext t; rfl
  map_mul' σ ρ  := by ext t; rfl

/-- The hyperoctahedral group `(ℤ/2)ⁿ ⋊ Sₙ`, i.e. the wreath product `ℤ/2 ≀ Sₙ`,
realized as a semidirect product with `(ℤ/2)ⁿ` as `Fin n → Bool` under pointwise
`xor`. -/
abbrev hyperoctahedralGroup (n : ℕ) : Type :=
  Multiplicative (Fin n → Bool) ⋊[hammingPhi n] Equiv.Perm (Fin n)

/-!
Translations and coordinate permutations give monoid homomorphisms into the
automorphism group of the Hamming graph. (Recall that multiplication of automorphisms
is composition, `(f * g) x = f (g x)`.)
-/
/-- Translations as a monoid homomorphism into the automorphism group of the Hamming
graph. -/
@[simps]
def hammingTranslateHom (n : ℕ) :
    Multiplicative (Fin n → Bool) →* (hypercubeHamming n ≃g hypercubeHamming n) where
  toFun t := hammingTranslate t.toAdd
  map_one' := by ext x; simp
  map_mul' t s := by ext x; simp [add_assoc]

/-- Coordinate permutations as a monoid homomorphism into the automorphism group of
the Hamming graph. -/
@[simps]
def hammingPermuteHom (n : ℕ) :
    Equiv.Perm (Fin n) →* (hypercubeHamming n ≃g hypercubeHamming n) where
  toFun := hammingPermute
  map_one' := by ext x; rfl
  map_mul' σ ρ := by ext x; rfl

/-!
These two homomorphisms are compatible with the action `hammingPhi`: conjugating a
translation by a coordinate permutation is the translation by the permuted vector.
`SemidirectProduct.lift` combines them into a monoid homomorphism from the
hyperoctahedral group to the automorphism group.
-/
/-- The homomorphism from the hyperoctahedral group to the automorphisms of the
Hamming graph, sending `(t, σ)` to the automorphism `x ↦ t + x ∘ σ.symm`, i.e.
coordinate permutation by `σ` followed by translation by `t`. -/
def hyperoctahedralToAut (n : ℕ) :
    hyperoctahedralGroup n →* (hypercubeHamming n ≃g hypercubeHamming n) :=
  SemidirectProduct.lift (hammingTranslateHom n) (hammingPermuteHom n) (by
    intro σ
    ext t x i
    change t (σ.symm i) + x i = t (σ.symm i) + x (σ (σ.symm i))
    rw [Equiv.apply_symm_apply])

@[simp]
lemma hyperoctahedralToAut_apply {n : ℕ} (t : Multiplicative (Fin n → Bool))
    (σ : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    hyperoctahedralToAut n ⟨t, σ⟩ x = t.toAdd + x ∘ σ.symm := rfl

/-!
## Injectivity

The homomorphism into the automorphism group is injective: if permuting coordinates
by `σ` and then translating by `t` fixes every vertex, then evaluating at `0` shows
`t = 0`, and evaluating at the basis vectors shows `σ = 1`. First a small helper: the
map `i ↦ Pi.single i true` is injective.
-/
lemma single_true_left_inj {n : ℕ} {i j : Fin n}
    (h : (Pi.single i true : Fin n → Bool) = Pi.single j true) : i = j := by
  simpa [Pi.single_apply] using congrFun h i

lemma hyperoctahedralToAut_injective (n : ℕ) :
    Function.Injective (hyperoctahedralToAut n) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨t, σ⟩ h
  have happ (x : Fin n → Bool) : t.toAdd + x ∘ σ.symm = x := DFunLike.congr_fun h x
  obtain rfl : t = 1 := by simpa using happ 0
  obtain rfl : σ = 1 := Equiv.ext fun j => Eq.symm <| by
    simpa [Pi.single_apply, Equiv.symm_apply_eq] using
      congrFun (happ (Pi.single j true)) j
  rfl

/-!
## Rigidity

The key step towards surjectivity is a rigidity lemma: an automorphism `g` fixing `0`
and all the basis vectors is the identity. The point is that the coordinates of a
vertex can be read off from distances, which automorphisms preserve. Since the graph
distance in the Hamming graph is the Hamming distance (`hypercubeHamming_edist_eq`),
every automorphism preserves the Hamming distance, and (if it fixes `0`) the Hamming
*weight* `hammingNorm`, i.e. the number of `true` coordinates, which is the Hamming
distance to `0`.
-/
lemma hammingDist_aut {n : ℕ} (g : hypercubeHamming n ≃g hypercubeHamming n)
    (x y : Fin n → Bool) : hammingDist (g x) (g y) = hammingDist x y := by
  have h := g.edist_eq x y
  rw [hypercubeHamming_edist_eq, hypercubeHamming_edist_eq] at h
  exact_mod_cast h

lemma hammingNorm_aut {n : ℕ} {g : hypercubeHamming n ≃g hypercubeHamming n}
    (hg : g 0 = 0) (x : Fin n → Bool) : hammingNorm (g x) = hammingNorm x := by
  rw [← hammingDist_zero_right, ← hg, hammingDist_aut, hammingDist_zero_right]

/-!
Adding a basis vector `Pi.single i true` flips the `i`-th coordinate; if that
coordinate was `true` this decreases the weight by one.
-/
lemma hammingNorm_add_single {n : ℕ} {x : Fin n → Bool} {i : Fin n}
    (h : x i = true) :
    hammingNorm (x + Pi.single i true) + 1 = hammingNorm x := by
  have hset : ({k | (x + Pi.single i true : Fin n → Bool) k ≠ 0} : Finset _) =
      ({k | x k ≠ 0} : Finset _).erase i := by
    ext j
    by_cases hj : j = i
    · simp [hj, h, Bool.zero_eq_false, Bool.add_eq_xor]
    · simp [hj]
  rw [hammingNorm, hset, Finset.card_erase_add_one (by simp [h, Bool.zero_eq_false])]
  rfl

/-!
The vertex `x + eₖ` differs from `x` only in coordinate `k`, so its weight is one
less than that of `x` if `x k = true`, and one more otherwise. Since the distance
from `x` to `eₖ` is the weight of `x + eₖ`, we see that `x k = true` exactly when `x`
is closer to `eₖ` than to `0`.
-/
lemma apply_eq_true_iff_hammingDist_lt {n : ℕ} (x : Fin n → Bool) (k : Fin n) :
    x k = true ↔ hammingDist x (Pi.single k true) < hammingDist x 0 := by
  rw [hammingDist_zero_right, hammingDist_eq_hammingNorm, boolVec_neg]
  cases hk : x k
  · have h : (x + Pi.single k true : Fin n → Bool) k = true := by
      simp [hk, Bool.add_eq_xor]
    have := hammingNorm_add_single h
    rw [add_assoc, boolVec_add_self, add_zero] at this
    grind
  · have := hammingNorm_add_single hk
    grind

/-!
An automorphism `g` fixing `0` and `eₖ` preserves the distances from any `x` to `0`
and to `eₖ`, so by the previous lemma `g x` and `x` agree in coordinate `k`.
-/
lemma aut_eq_id_of_fix_zero_and_singles {n : ℕ}
    {g : hypercubeHamming n ≃g hypercubeHamming n} (h0 : g 0 = 0)
    (h1 : ∀ i, g (Pi.single i true) = Pi.single i true) (x : Fin n → Bool) :
    g x = x := by
  funext k
  rw [Bool.eq_iff_iff, apply_eq_true_iff_hammingDist_lt,
    apply_eq_true_iff_hammingDist_lt, ← h1 k, ← h0, hammingDist_aut, hammingDist_aut,
    h1 k, h0]

/-!
## Surjectivity

Given an arbitrary automorphism `f` we first compose with a translation to obtain an
automorphism `g` fixing `0`. Since `g` preserves weights it permutes the basis
vectors, which yields a permutation `σ` of the coordinates; composing with `σ⁻¹`
gives an automorphism fixing `0` and all basis vectors, which by rigidity is the
identity. Hence `f` is the image of `(f 0, σ)`: permutation of the coordinates by
`σ` followed by translation by `f 0`.
-/
lemma hyperoctahedralToAut_surjective (n : ℕ) :
    Function.Surjective (hyperoctahedralToAut n) := by
  intro f
  set g := (hammingTranslateHom n (Multiplicative.ofAdd (f 0)))⁻¹ * f with hgdef
  have hg0 : g 0 = 0 := by
    simp [hgdef]
  have hsingle : ∀ i : Fin n, ∃ j, g (Pi.single i true) = Pi.single j true := by
    intro i
    exact hammingNorm_eq_one_iff.mp (by rw [hammingNorm_aut hg0, hammingNorm_single])
  choose p hp using hsingle
  have hpinj : Function.Injective p := by
    intro i j hij
    have h' : g (Pi.single i true) = g (Pi.single j true) := by
      rw [hp i, hp j, hij]
    exact single_true_left_inj (g.injective h')
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective p (Finite.injective_iff_bijective.mp hpinj)
  have hh0 : ((hammingPermuteHom n σ)⁻¹ * g) 0 = 0 := by
    simp [hg0]
  have hhsingle : ∀ i,
      ((hammingPermuteHom n σ)⁻¹ * g) (Pi.single i true) = Pi.single i true := by
    intro i
    ext k; simp [hp i, σ, Pi.single_apply, hpinj.eq_iff]
  have hone : (hammingPermuteHom n σ)⁻¹ * g = 1 := by
    ext x : 1
    simpa using aut_eq_id_of_fix_zero_and_singles hh0 hhsingle x
  exact ⟨⟨Multiplicative.ofAdd (f 0), σ⟩,
    (inv_mul_eq_iff_eq_mul.mp (inv_mul_eq_one.mp hone).symm).symm⟩

/-!
## The Characterization of the Automorphism Group

Converting the bijective homomorphism into a group isomorphism, and transporting it
along `hypercubeIsoHamming` (using `Iso.autCongr` from
[Automorphism Groups](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-automorphism-groups)),
we obtain the promised characterization: the automorphism group of the
`n`-dimensional hypercube is the hyperoctahedral group `ℤ/2 ≀ Sₙ`.
-/
/-- The automorphism group of the Hamming graph is the hyperoctahedral group
`ℤ/2 ≀ Sₙ`. -/
noncomputable def hyperoctahedralMulEquivAutHamming (n : ℕ) :
    hyperoctahedralGroup n ≃* (hypercubeHamming n ≃g hypercubeHamming n) :=
  MulEquiv.ofBijective (hyperoctahedralToAut n)
    ⟨hyperoctahedralToAut_injective n, hyperoctahedralToAut_surjective n⟩

/-- The automorphism group of the hypercube `Q[n]` is the hyperoctahedral group
`ℤ/2 ≀ Sₙ`. -/
noncomputable def autHypercubeMulEquivHyperoctahedral (n : ℕ) :
    (Q[n] ≃g Q[n]) ≃* hyperoctahedralGroup n :=
  (hypercubeIsoHamming n).autCongr.trans
    (hyperoctahedralMulEquivAutHamming n).symm

/-!
In particular the hypercube `Q[n]` has exactly `2ⁿ · n!` automorphisms.
-/
lemma card_aut_hypercube (n : ℕ) :
    Nat.card (Q[n] ≃g Q[n]) = 2 ^ n * Nat.factorial n := by
  rw [Nat.card_congr (autHypercubeMulEquivHyperoctahedral n).toEquiv,
    Nat.card_congr (SemidirectProduct.equivProd), Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

/-!
# Counting Copies *

Automorphisms explain the difference between the *labelled* and *unlabelled* copies
of a graph that we met in
[Copies](https://jt496.github.io/GraphTheoryInLean/Maps/#section-copies). In this
section we derive the basic fact that (for finite graphs) the number of labelled
copies of a graph `A` in a graph `B` is equal to the number of unlabelled copies of
`A` in `B`, multiplied by the number of automorphisms of `A`. (Mathlib has the
inequality `copyCount_le_labelledCopyCount`, but not this identity.) We then apply it
to count cycles, and 5-cycles in Mycielskians.

Recall that `Copy A B` is the type of injective graph homomorphisms from `A` to `B`,
and that the following maps
([Which Notion of Subgraph?](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-which-notion-of-subgraph))
pass between copies of `A` in `B` and subgraphs of `B` isomorphic to `A`.
-/
section copies
variable {W : Type*}
open Subgraph

#check Copy.toSubgraph     -- (f : Copy A B) : B.Subgraph
#check Copy.isoToSubgraph  -- (f : Copy A B) : A ≃g f.toSubgraph.coe
#check Subgraph.coeCopy    -- (C : B.Subgraph) : Copy C.coe B

/-!
The counting result follows from a general equivalence: `A.Copy B` is equivalent to
the product of the subtype of subgraphs of `B` that are isomorphic to `A` with the
automorphisms of `A`.

This is obvious informally: labelled copies of `A` in `B` are the same as unlabelled
copies of `A` in `B` together with a choice of labelling, and the labellings of a
fixed unlabelled copy of `A` are equivalent to automorphisms of `A`.

Rather than bundle the definition of this equivalence into a single definition we
break it down into steps to show how the pieces fit together.

For `C` in the subtype `{C : B.Subgraph | Nonempty (A ≃g C.coe)}` the membership
proof `Nonempty (A ≃g C.coe)` is a proposition: it says that a labelling of `C`
exists, but does not provide any particular one. To identify the labellings of `C`
with the automorphisms of `A` we must therefore first fix, using `Classical.choice`,
a *reference* labelling `A ≃g C.coe` for each `C` in the subtype: this is
`chosenSubgraphIso` below. (Since the membership proof is a proposition, an element
of the subtype is determined by its subgraph alone, so `chosenSubgraphIso C` depends
only on `C`.)
-/
/-- Fix, using choice, a reference isomorphism `A ≃g C.coe` for each subgraph `C` of
`B` that is isomorphic to `A`. -/
noncomputable
def chosenSubgraphIso {A : SimpleGraph V} {B : SimpleGraph W}
    (C : {C : B.Subgraph | Nonempty (A ≃g C.coe)}) : A ≃g (C : B.Subgraph).coe :=
  C.property.some

/-!
We then give the equivalence between labellings and automorphisms
`subgraphIsoEquivAut`: a labelling corresponds to the automorphism of `A` recording
how it differs from the reference labelling.
-/
/-- Given a subgraph `C` of `B` that is isomorphic to `A`, the isomorphisms
`A ≃g C.coe` are equivalent to the automorphisms of `A`, by comparison with the
reference isomorphism `chosenSubgraphIso C`. -/
@[simps]
noncomputable
def subgraphIsoEquivAut {A : SimpleGraph V} {B : SimpleGraph W}
    (C : {C : B.Subgraph | Nonempty (A ≃g C.coe)}) :
    (A ≃g (C : B.Subgraph).coe) ≃ (A ≃g A) where
  toFun f := f.trans (chosenSubgraphIso C).symm
  invFun σ := σ.trans (chosenSubgraphIso C)
  left_inv f := by ext b; simp
  right_inv σ := by ext b; simp

/-!
Next, `copyEquivSigmaIso` shows that a copy of `A` in `B` is the same as a subgraph
`C` together with a labelling `A ≃g C.coe`, packaged as a `Sigma` type. No reference
labelling is needed for this step, since the copy itself provides one. The work in
the proof is in `right_inv`: starting from a pair `(C, f)` on the right-hand side,
the subgraph recovered after the round trip is *provably* equal to `C`, but not
*definitionally* equal
([Definitional and Propositional Equalities](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/#section-definitional-and-propositional-equalities)),
so Lean does not identify their coercions as the same type, and the two labellings
have distinct types. One remedy would be to compare the labellings across their
provably-equal types using heterogeneous equality (`HEq`, via `Sigma.ext`). Instead
we sidestep the dependent comparison entirely: we prove that the *inverse* map is
injective (`coeCopy_comp_toCopy_injective` below) and obtain `right_inv` from
`left_inv` using `Function.LeftInverse.rightInverse_of_injective`.
-/
#check Function.LeftInverse.rightInverse_of_injective
/-!
In the injectivity proof the two subgraphs `C` and `D` are local variables, so once
we know `C = D` we can substitute one for the other, after which the labellings have
the *same* type and ordinary `ext` applies. (This type mismatch problem is
essentially the same difficulty we met for walks in
[Copy](https://jt496.github.io/GraphTheoryInLean/Walks/#section-copy). There the type
`G.Walk u v` encodes the endpoints of a walk, so a walk whose endpoints were provably
(but not definitionally) equal to `u` and `v` needed `Walk.copy` to adjust its type.
Here the type of a labelling encodes the subgraph it labels, and a similar mismatch
arises.)
-/
/-- The map sending a subgraph `C` of `B` isomorphic to `A`, together with a
labelling `A ≃g C.coe`, to the corresponding copy of `A` in `B` is injective. -/
theorem coeCopy_comp_toCopy_injective (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Injective
      (fun y : Σ C : {C : B.Subgraph | Nonempty (A ≃g C.coe)}, A ≃g
        (C : B.Subgraph).coe => (y.1 : B.Subgraph).coeCopy.comp y.2.toCopy) := by
  rintro ⟨⟨C, hC⟩, f⟩ ⟨⟨D, hD⟩, g⟩ h
  -- The images agree, and `C` and `D` are local variables, so we
  -- can substitute `C = D`.
  obtain rfl : C = D := by
    simpa only [Copy.toSubgraph, Copy.comp, coeCopy, map_comp, map_iso_top,
      map_hom_top] using congrArg Copy.toSubgraph h
  -- Now `f` and `g` are labellings of the same subgraph, so `ext` applies.
  obtain rfl : f = g := by ext a; exact DFunLike.congr_fun h a
  rfl

/-- `A.Copy B` is equivalent to the Sigma type of subgraphs of `B` that are
isomorphic to `A` with their isomorphisms. -/
@[simps]
noncomputable
def copyEquivSigmaIso (A : SimpleGraph V) (B : SimpleGraph W) :
    A.Copy B ≃
      Σ C : {C : B.Subgraph | Nonempty (A ≃g C.coe)}, A ≃g (C : B.Subgraph).coe where
  toFun c := ⟨⟨c.toSubgraph, ⟨c.isoToSubgraph⟩⟩, c.isoToSubgraph⟩
  invFun y := (y.1 : B.Subgraph).coeCopy.comp y.2.toCopy
  left_inv c := by ext b; rfl
  right_inv :=
    Function.LeftInverse.rightInverse_of_injective (fun c => by ext b; rfl)
      (coeCopy_comp_toCopy_injective A B)

/-!
Finally, `copyEquivSubgraphIsoProdAut` puts the pieces together: applying
`subgraphIsoEquivAut` fibrewise (`Equiv.sigmaCongrRight`) turns each labelling into
an automorphism, and since the fibres are then constant the `Sigma` type collapses to
a product (`Equiv.sigmaEquivProd`).
-/
#check Equiv.sigmaCongrRight
#check Equiv.sigmaEquivProd

/-- `A.Copy B` is equivalent to the product of the subtype of subgraphs of `B` that
are isomorphic to `A` with the automorphisms of `A`. -/
noncomputable
def copyEquivSubgraphIsoProdAut (A : SimpleGraph V) (B : SimpleGraph W) :
    A.Copy B ≃ {C : B.Subgraph | Nonempty (A ≃g C.coe)} × A ≃g A :=
  ((copyEquivSigmaIso A B).trans
    (Equiv.sigmaCongrRight subgraphIsoEquivAut)).trans (Equiv.sigmaEquivProd _ _)

/-!
We can now deduce the promised counting identity. The number of labelled copies of
`A` in `B` (`B.labelledCopyCount A`) equals the number of unlabelled copies
(`B.copyCount A`) multiplied by the number of automorphisms of `A`. (Beware
`A.Copy B` is the type of copies of `A` in `B`, while `B.labelledCopyCount A` is its
cardinality. (The order of `A` and `B` is reversed in the two notations, which can be
confusing.))
-/
#source labelledCopyCount -- classical exact Fintype.card (Copy H G)
#source copyCount -- classical exact #{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}
/-!

Rather than state this in terms of `Fintype.card (A ≃g A)`, which would require a
`Fintype` instance on `A ≃g A`, we use the fact that for finite graphs `A ≃g A` is
equivalent to `Copy A A`, for which Mathlib already provides a `Fintype` instance.
So we already have a name for the number of automorphisms of `A`: it is
`A.labelledCopyCount A`. In fact given any isomorphism `A ≃g B`, with `A` a finite
graph, we can identify `Copy A B` with `A ≃g B`.
-/
/-- For finite graphs, an isomorphism `A ≃g B` witnesses that copies of `A` in `B`
are the same as isomorphisms `A ≃g B`. -/
noncomputable def Iso.copyEquivIso {A : SimpleGraph V} {B : SimpleGraph W}
    (e : A ≃g B) [Finite V] : (Copy A B) ≃ (A ≃g B) where
  toFun f :=
    { Equiv.ofBijective f.toHom ⟨f.injective,
        (Finite.injective_iff_surjective_of_equiv e.toEquiv).1 f.injective⟩ with
      map_rel_iff' {a b} := by
        refine ⟨fun h => ?_, f.toHom.map_rel⟩
        -- `f.mapEdgeSet` is an injection between finite sets of the same size,
        -- hence a surjection, so the edge `s(f a, f b)` of `B` is the image of an
        -- edge of `A`.
        obtain ⟨⟨e', he'⟩, heq⟩ :=
          (Finite.injective_iff_surjective_of_equiv e.mapEdgeSet).1
            f.mapEdgeSet.injective ⟨s(f a, f b), h⟩
        obtain rfl : e' = s(a, b) :=
          Sym2.map.injective f.injective (congrArg Subtype.val heq)
        exact he' }
  invFun φ := φ.toCopy
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- Copies of a finite graph in itself are equivalent to automorphisms of the
graph. -/
noncomputable def copyEquivAut (A : SimpleGraph V) [Finite V] :
    (Copy A A) ≃ (A ≃g A) := Iso.copyEquivIso .refl

/-- For `A` a finite graph, `A.Copy B` is equivalent to the product of the subtype of
subgraphs of `B` that are isomorphic to `A` with copies of `A` in itself. -/
noncomputable
def copyEquivSubgraphIsoProdCopy (A : SimpleGraph V) (B : SimpleGraph W) [Finite V] :
    A.Copy B ≃ {C : B.Subgraph | Nonempty (A ≃g C.coe)} × A.Copy A :=
  (copyEquivSubgraphIsoProdAut A B).trans
    (.prodCongr (Equiv.refl _) (copyEquivAut A).symm)

/-!
Hence, for `A` and `B` finite graphs, the number of labelled copies of `A` in `B` is
equal to the number of unlabelled copies of `A` in `B` multiplied by the number of
labelled copies of `A` in itself (i.e. the number of automorphisms of `A`).
-/
theorem labelledCopyCount_eq_copyCount_mul_labelledCopyCount [Fintype V] [Fintype W]
    (A : SimpleGraph V) (B : SimpleGraph W) :
    B.labelledCopyCount A = B.copyCount A * A.labelledCopyCount A := by
  classical
  rw [labelledCopyCount, Fintype.card_congr (A.copyEquivSubgraphIsoProdCopy B),
      Fintype.card_prod, copyCount, Fintype.card_subtype]
  rfl

end copies

/-!
Isomorphisms `A ≃g A'` and `B ≃g B'` identify the copies of `A` in `B` with the
copies of `A'` in `B'`, by composing on both sides. So isomorphic graphs have the
same copy counts. This lets us count copies in whichever model of a graph is most
convenient.
-/
/-- Isomorphisms `A ≃g A'` and `B ≃g B'` identify the copies of `A` in `B` with the
copies of `A'` in `B'`. -/
def Iso.copyCongr {V' W W' : Type*} {A : SimpleGraph V} {A' : SimpleGraph V'}
    {B : SimpleGraph W} {B' : SimpleGraph W'} (eA : A ≃g A') (eB : B ≃g B') :
    Copy A B ≃ Copy A' B' where
  toFun f := (eB.toCopy.comp f).comp eA.symm.toCopy
  invFun f := (eB.symm.toCopy.comp f).comp eA.toCopy
  left_inv f := by ext; simp
  right_inv f := by ext; simp

lemma Iso.labelledCopyCount_eq {V' W W' : Type*} [Fintype V] [Fintype V'] [Fintype W]
    [Fintype W'] {A : SimpleGraph V} {A' : SimpleGraph V'} {B : SimpleGraph W}
    {B' : SimpleGraph W'} (eA : A ≃g A') (eB : B ≃g B') :
    B.labelledCopyCount A = B'.labelledCopyCount A' := by
  simp only [labelledCopyCount, Fintype.card_eq_nat_card]
  exact Nat.card_congr (eA.copyCongr eB)

/-!
## Counting Copies of Cycles

By `labelledCopyCount_eq_copyCount_mul_labelledCopyCount`, the number of labelled
copies of a finite graph `A` in a graph `B` is the number of unlabelled copies times
the number of automorphisms of `A`. Since the automorphism group of `C[n + 3]` is the
dihedral group of order `2 * (n + 3)`
([Automorphisms of Cycle Graphs](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-automorphisms-of-cycle-graphs)),
this expresses the number of labelled copies of a cycle in a graph in terms of the
number of unlabelled copies.
-/
theorem labelledCopyCount_cycleGraph [Fintype V] (G : SimpleGraph V) (n : ℕ) :
    G.labelledCopyCount C[n + 3] = G.copyCount C[n + 3] * (2 * (n + 3)) := by
  -- `Fintype.card_congr` won't work here because `labelledCopyCount` unfolds to
  -- `Fintype.card` with classical decidability instances, which are not defeq to the
  -- ones `Fintype.card_congr` synthesizes. We avoid this by using `Nat.card`.
  rw [labelledCopyCount_eq_copyCount_mul_labelledCopyCount, labelledCopyCount,
    ← DihedralGroup.card, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    Nat.card_congr ((copyEquivAut C[n + 3]).trans
      (autCycleGraphMulEquivDihedral n).toEquiv)]

/-!
## Counting 5-Cycles in Mycielskians

Since `mμ[K[2]]` is a 5-cycle, every edge of `G` gives a 5-cycle in `mμ[G]` (see
`isCycle_mycielskianClosed_of_adj` in
[Walks](https://jt496.github.io/GraphTheoryInLean/Walks/#chapter-walks)). More
generally, an edge `u — v` of `G`, together with a neighbour `x` of `u` and a
neighbour `y` of `v` with `x ≠ y`, gives the 5-cycle `u ₗ, v ₗ, y ᵣ, none, x ᵣ` in
`mμ[G]`. (Taking `x = v` and `y = u` gives the 5-cycle through the edge `u — v`
alone.)

[Figure: $C_5$ in $mμ(G)$ from an edge and two distinct neighbours](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian_C5.svg)
-/
/-- The copy of `C[5]` in `mμ[G]` through `u ₗ, v ₗ, y ᵣ, none, x ᵣ`, built from an
edge `u — v` of `G` and neighbours `x` of `u` and `y` of `v` with `x ≠ y`. See the
figure `mycielskian_C5`. -/
def mycielskianCopyC5OfNeighbors {u v : V} (h : G.Adj u v) (x : G.neighborSet u)
    (y : G.neighborSet v) (hxy : (x : V) ≠ (y : V)) : Copy C[5] mμ[G] where
  toHom := ⟨![u ₗ, v ₗ, (y : V) ᵣ, none, (x : V) ᵣ], by
    have hx : G.Adj u x := x.2
    have hy : G.Adj v y := y.2
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all +decide [adj_comm]⟩
  injective' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm, h.ne]

/-!
If `G` has no triangles and no 5-cycles then every 5-cycle in `mμ[G]` arises in this
way, and this lets us count them. The argument has two steps.

1. Every copy of `C[5]` in `mμ[G]` passes through `none`. Otherwise, projecting it to
   `G` would give a homomorphism from `C[5]` to `G`, which (as `G` is triangle-free)
   is injective, i.e. a 5-cycle in `G`.
2. The rotations of `C[5]` act on its copies, and can move the vertex sent to `none`
   to any position. So it is enough to count the copies `c` with `c 3 = none`, and
   each of these comes from a unique choice of `(u, v, x, y)` as above.

For the first step, recall the projection from
[Clique Number of the Mycielskian](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-clique-number-of-the-mycielskian),
which sends `v ₗ` and `v ᵣ` to `v`, and `none` to a chosen vertex `v₀`.
-/
#source mycielskianProj
/-!
A homomorphism from `C[2k + 1]` to a graph with no odd cycles of length less than
`2k + 1` is injective. We only need the case `k = 2`: a homomorphism `f` from `C[5]`
to a triangle-free graph is injective. (If `f a = f b` for `a ≠ b` then `a` and `b`
are not adjacent, since `G` has no loops, so they split `C[5]` into arcs of lengths
`2` and `3`, and the arc of length `3` maps to a triangle in `G`.)
-/
lemma hom_cycleGraph_five_injective (h3 : G.CliqueFree 3) (f : C[5] →g G) :
    Function.Injective f := by
  classical
  intro a b hab
  by_contra hne
  obtain h | ⟨k, l, hak, hkl, hlb⟩ := (by decide : ∀ a b : Fin 5, a ≠ b →
    C[5].Adj a b ∨ ∃ k l, C[5].Adj a k ∧ C[5].Adj k l ∧ C[5].Adj l b) a b hne
  · exact (f.map_adj h).ne hab
  · exact h3 {f a, f k, f l} (is3Clique_triple_iff.2
      ⟨f.map_adj hak, (hab ▸ f.map_adj hlb).symm, f.map_adj hkl⟩)

/-!
So if `G` has no triangles and no 5-cycles, every copy of `C[5]` in `mμ[G]` passes
through `none`. (To define the projection we need a vertex `v₀` of `G`; we can take
the projection of any vertex of the copy.)
-/
lemma mycielskianCopyC5_exists_eq_none (h3 : G.CliqueFree 3) (h5 : C[5].Free G)
    (c : Copy C[5] mμ[G]) : ∃ i : Fin 5, c i = none := by
  by_contra! h_ne
  obtain ⟨v₀⟩ : Nonempty V := by
    rcases hc : c 0 with _ | v | v
    exacts [absurd hc (h_ne 0), ⟨v⟩, ⟨v⟩]
  -- away from `none`, the projection maps edges of `mμ[G]` to edges of `G`
  let f : C[5] →g G := ⟨fun i => mycielskianProj v₀ (c i), fun {i j} hij => by
    have := c.toHom.map_adj hij
    have := h_ne i; have := h_ne j
    rcases hi : c i with _ | u | u <;> rcases hj : c j with _ | w | w <;> simp_all⟩
  exact h5 ⟨⟨f, hom_cycleGraph_five_injective h3 f⟩⟩

/-!
For the second step we work with copies of any cycle `C[n]` in any graph `H`.
Precomposing a copy `c` with the rotation `cycleGraphRotate d` gives the copy
`k ↦ c (k - d)`. Suppose every copy passes through a vertex `w` of `H` (exactly once,
since copies are injective). Then a copy is determined by the vertex `i` of `C[n]`
sent to `w`, together with its rotation sending a fixed vertex `j` to `w`. So there
are `n` times as many copies as there are copies sending `j` to `w`.
-/
theorem card_copy_cycleGraph_eq_mul {W : Type*} {H : SimpleGraph W} {n : ℕ}
    [NeZero n] (w : W) (j : Fin n) (hw : ∀ c : Copy C[n] H, ∃ i, c i = w) :
    Nat.card (Copy C[n] H) = n * Nat.card {c : Copy C[n] H // c j = w} := by
  -- `Φ (i, c)` is the rotation of `c` sending `i` to `w`
  let Φ : Fin n × {c : Copy C[n] H // c j = w} → Copy C[n] H :=
    fun p => p.2.1.comp (cycleGraphRotate (p.1 - j)).toCopy
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨i, c, hc⟩ ⟨i', c', hc'⟩ h
      have h' (k : Fin n) : c (k - (i - j)) = c' (k - (i' - j)) :=
        DFunLike.congr_fun h k
      -- at `i'`: `c` sends `i' - (i - j)` to `w`, as it does `j`
      obtain rfl : i = i' := by
        have := c.injective ((h' i').trans (by simpa using hc'.trans hc.symm))
        grind
      obtain rfl : c = c' := Copy.ext fun k => by simpa using h' (k + (i - j))
      rfl
    · intro c
      obtain ⟨i, hi⟩ := hw c
      refine ⟨⟨i, c.comp (cycleGraphRotate (j - i)).toCopy, by simpa using hi⟩, ?_⟩
      ext k
      change c (k - (i - j) - (j - i)) = c k
      congr 1
      abel
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Nat.card_prod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-!
It remains to count the copies `c` with `c 3 = none`. Since `none` is adjacent only
to right vertices, its neighbours `c 2` and `c 4` are right vertices, `y ᵣ` and `x ᵣ`
say. Their other neighbours `c 1` and `c 0` are not `none` (as `c` is injective), so
they are left vertices, `v ₗ` and `u ₗ` say. Reading off the remaining adjacencies,
`c` is the copy built from `(u, v, x, y)`. (Here `x ≠ y` comes for free, since `c` is
injective.)
-/
lemma mycielskianCopyC5_eq_ofNeighbors {c : Copy C[5] mμ[G]} (hc : c 3 = none) :
    ∃ (u : V) (v : G.neighborSet u) (x : G.neighborSet u) (y : G.neighborSet v)
      (hxy : (x : V) ≠ y), c = mycielskianCopyC5OfNeighbors v.2 x y hxy := by
  have hadj (i : Fin 5) : mμ[G].Adj (c i) (c (i + 1)) :=
    c.toHom.map_adj (by fin_cases i <;> decide)
  have hne (i : Fin 5) (hi : i ≠ 3) : c i ≠ none :=
    fun h => hi (c.injective (h.trans hc.symm))
  -- the neighbours `c 2` and `c 4` of `none` are right vertices
  obtain ⟨y, hc2⟩ : ∃ y, c 2 = y ᵣ := by
    have := hadj 2; rcases h : c 2 with _ | y | y <;> simp_all
  obtain ⟨x, hc4⟩ : ∃ x, c 4 = x ᵣ := by
    have := hadj 3; rcases h : c 4 with _ | x | x <;> simp_all
  -- their other neighbours `c 1` and `c 0` are left vertices
  obtain ⟨v, hc1, hvy⟩ : ∃ v, c 1 = v ₗ ∧ G.Adj v y := by
    have := hadj 1; have := hne 1 (by decide)
    rcases h : c 1 with _ | v | v <;> simp_all
  obtain ⟨u, hc0, hxu⟩ : ∃ u, c 0 = u ₗ ∧ G.Adj x u := by
    have := hadj 4; have := hne 0 (by decide)
    rcases h : c 0 with _ | u | u <;> simp_all
  have huv : G.Adj u v := by simpa [hc0, hc1] using hadj 0
  have hxy : x ≠ y := by
    rintro rfl
    exact c.injective.ne (show (4 : Fin 5) ≠ 2 by decide) (by simpa [hc2] using hc4)
  refine ⟨u, ⟨v, huv⟩, ⟨x, hxu.symm⟩, ⟨y, hvy⟩, hxy, Copy.ext fun i => ?_⟩
  fin_cases i
  exacts [hc0, hc1, hc2, hc, hc4]

/-!
Conversely, in a triangle-free graph the neighbourhoods of adjacent vertices are
disjoint, so the condition `x ≠ y` holds automatically.
-/
lemma ne_of_adj_of_cliqueFree_three (h3 : G.CliqueFree 3) {u v x y : V}
    (huv : G.Adj u v) (hx : G.Adj u x) (hy : G.Adj v y) : x ≠ y := by
  classical
  rintro rfl
  exact h3 {u, v, x} (is3Clique_triple_iff.2 ⟨huv, hx, hy⟩)

/-!
So for triangle-free `G` the copies with `c 3 = none` correspond exactly to the
tuples `(u, v, x, y)` with `v` and `x` neighbours of `u`, and `y` a neighbour of `v`,
which we package as a `Sigma` type. Rather than writing down the inverse map, we
show that the map `(u, v, x, y) ↦ mycielskianCopyC5OfNeighbors …` is bijective:
injectivity is read off from the values at `0, 1, 2, 4`, and surjectivity is
`mycielskianCopyC5_eq_ofNeighbors`.

Here, and in the two counts that follow, we assume `[G.LocallyFinite]`, the instance
that the degrees on the right-hand side actually mention (see
[Instance Arguments in Statements](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-instance-arguments-in-statements)),
so that the results apply whichever instance a graph's neighbourhoods carry.
-/
lemma card_copy_mycielskian_apply_three_eq_none [Fintype V] [G.LocallyFinite]
    (h3 : G.CliqueFree 3) :
    Nat.card {c : Copy C[5] mμ[G] // c 3 = none} =
      ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v := by
  let Φ : (Σ u : V, Σ v : G.neighborSet u, G.neighborSet u × G.neighborSet v) →
      {c : Copy C[5] mμ[G] // c 3 = none} := fun ⟨_, v, x, y⟩ =>
    ⟨mycielskianCopyC5OfNeighbors v.2 x y
      (ne_of_adj_of_cliqueFree_three h3 v.2 x.2 y.2), rfl⟩
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨u, ⟨v, hv⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨u', ⟨v', hv'⟩, ⟨x', hx'⟩, ⟨y', hy'⟩⟩ h
      have h' (i : Fin 5) := DFunLike.congr_fun (congrArg Subtype.val h) i
      obtain rfl : u = u' := mycielskian.left_injective (h' 0 : u ₗ = u' ₗ)
      obtain rfl : v = v' := mycielskian.left_injective (h' 1 : v ₗ = v' ₗ)
      obtain rfl : y = y' := mycielskian.right_injective (h' 2 : y ᵣ = y' ᵣ)
      obtain rfl : x = x' := mycielskian.right_injective (h' 4 : x ᵣ = x' ᵣ)
      rfl
    · rintro ⟨c, hc⟩
      obtain ⟨u, v, x, y, -, rfl⟩ := mycielskianCopyC5_eq_ofNeighbors hc
      exact ⟨⟨u, v, x, y⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Nat.card_eq_fintype_card]
  simp_rw [Fintype.card_sigma, Fintype.card_prod, card_neighborSet_eq_degree]
  congr 1 with u
  simp [← Finset.sum_subtype (G.neighborFinset u) _
    (fun v => G.degree u * G.degree v)]

/-!
Putting the two steps together gives the number of labelled copies of `C[5]` in
`mμ[G]`. In the double sum each edge `u — v` of `G` appears twice, as `(u, v)` and as
`(v, u)`.
-/
theorem labelledCopyCount_mycielskian_cycleGraph_five [Fintype V] [G.LocallyFinite]
    (h3 : G.CliqueFree 3) (h5 : C[5].Free G) :
    mμ[G].labelledCopyCount C[5] =
      5 * ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v := by
  rw [labelledCopyCount, Fintype.card_eq_nat_card,
    card_copy_cycleGraph_eq_mul none 3 (mycielskianCopyC5_exists_eq_none h3 h5),
    card_copy_mycielskian_apply_three_eq_none h3]

/-!
Since `C[5]` has `10` automorphisms, `labelledCopyCount_cycleGraph` converts this
into the number of 5-cycles in `mμ[G]`: it is the sum of `d(u) * d(v)` over the edges
`u — v` of `G`. For example, for `G = K[2]` the sum is `1`, and indeed `mμ[K[2]]` is
a single 5-cycle.
-/
theorem copyCount_mycielskian_cycleGraph_five [Fintype V] [G.LocallyFinite]
    (h3 : G.CliqueFree 3) (h5 : C[5].Free G) :
    2 * mμ[G].copyCount C[5] =
      ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v := by
  have h := labelledCopyCount_cycleGraph mμ[G] 2
  rw [labelledCopyCount_mycielskian_cycleGraph_five h3 h5] at h
  grind

/-!
## Induced 5-Cycles

A copy of `C[5]` is only an injective homomorphism, so its image may have chords. In
a triangle-free graph it cannot: if `c a` and `c b` were adjacent for non-adjacent
`a` and `b`, then `a` and `b` would have a common neighbour `k` in `C[5]`, and `c a`,
`c b` and `c k` would form a triangle. So in a triangle-free graph every copy of
`C[5]` is *induced*: it reflects adjacency as well as preserving it.
-/
lemma copy_cycleGraph_five_adj_iff {W : Type*} {H : SimpleGraph W}
    (h3 : H.CliqueFree 3) (c : Copy C[5] H) {a b : Fin 5} :
    H.Adj (c a) (c b) ↔ C[5].Adj a b := by
  classical
  refine ⟨fun hab => ?_, c.toHom.map_adj⟩
  by_contra hnab
  obtain ⟨k, hak, hkb⟩ := (by decide : ∀ a b : Fin 5, ¬ C[5].Adj a b →
    ∃ k, C[5].Adj a k ∧ C[5].Adj k b) a b hnab
  exact h3 {c a, c b, c k}
    (is3Clique_triple_iff.mpr ⟨hab, c.toHom.map_adj hak, (c.toHom.map_adj hkb).symm⟩)

/-!
A copy that reflects adjacency is a graph embedding `A ↪g B`
([Graph Embeddings](https://jt496.github.io/GraphTheoryInLean/Maps/#section-graph-embeddings)),
and Mathlib writes `A ⊴ B` (`IsIndContained`) for the existence of one. So if every
copy of `A` in `B` reflects adjacency, then the copies of `A` in `B` and the
embeddings `A ↪g B` are the same thing. (Mathlib has no induced analogue of
`labelledCopyCount`: "Count induced copies of a graph inside another" is on the TODO
list in Mathlib's `Copy.lean`.)
-/
/-- If every copy of `A` in `B` reflects adjacency, then copies of `A` in `B` are the
same as graph embeddings `A ↪g B`. -/
def copyEquivEmbedding {W X : Type*} {A : SimpleGraph W} {B : SimpleGraph X}
    (h : ∀ (f : Copy A B) {a b : W}, B.Adj (f a) (f b) → A.Adj a b) :
    Copy A B ≃ (A ↪g B) where
  toFun f := ⟨f.toEmbedding, ⟨h f, f.toHom.map_adj⟩⟩
  invFun := Embedding.toCopy
  left_inv _ := rfl
  right_inv _ := rfl

/-!
Since `mμ[G]` is triangle-free when `G` is
([Triangle-Free Mycielskians](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-triangle-free-mycielskians)),
the formula above also counts the embeddings of `C[5]` in `mμ[G]`, i.e. its labelled
induced 5-cycles.
-/
theorem card_embedding_mycielskian_cycleGraph_five [Fintype V] [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (h5 : C[5].Free G) :
    Nat.card (C[5] ↪g mμ[G]) =
      5 * ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v := by
  rw [← Nat.card_congr (copyEquivEmbedding fun c _ _ =>
      (copy_cycleGraph_five_adj_iff h3.mycielskian c).1), ← Fintype.card_eq_nat_card]
  exact labelledCopyCount_mycielskian_cycleGraph_five h3 h5

/-!
# Counting Copies of Subcubes *

As a second application of the Hamming-graph model we count the labelled and
unlabelled copies
([Counting Copies*](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-counting-copies))
of a small cube `Q[k]` inside `Q[n]`. We will show that

* `Q[n].labelledCopyCount Q[k] = 2 ^ n * n.descFactorial k`, and
* `Q[n].copyCount Q[k] = n.choose k * 2 ^ (n - k)` (when `k ≤ n`).

The second is the familiar answer "choose the `k` free coordinates and fix the
others"; the first refines it by the `2 ^ k * k!` automorphisms of `Q[k]`. As for the
automorphism group, we work with the Hamming graphs and transport the results to
`Q[n]` at the end.

The argument is another rigidity theorem: every copy of `Q[k]` in `Q[n]` is
*canonical*. That is, for some choice of `k` distinct coordinates of `Q[n]` and a
vertex `b` of `Q[n]`, it sends each vertex `x` of `Q[k]` to `b + y`, where `y` is
obtained by placing the coordinates of `x` in the chosen positions, with `false`
elsewhere. (In particular `b` is the image of `0`.) So its image is a *subcube*, a
translate of a coordinate subspace. We prove this by induction on the Hamming weight,
using a "parallelogram lemma" about the 4-cycles of the Hamming graph. Finally we
show that every copy of `Q[k]` in `Q[n]` is induced.

## The Parallelogram Lemma

If `x u y v` is a four-cycle in the Hamming graph (i.e. `u ≠ v` are common
neighbours of `x ≠ y`), then `u + v = x + y`; equivalently the cycle is a
two-dimensional "face" `x, x + eᵢ, x + eᵢ + eⱼ, x + eⱼ`.
-/
/-- The parallelogram lemma: if `u ≠ v` are common neighbours of `x ≠ y` in the
Hamming graph then `u + v = x + y`. -/
lemma hypercubeHamming_parallelogram {n : ℕ} {x y u v : Fin n → Bool}
    (hxu : (hypercubeHamming n).Adj x u) (huy : (hypercubeHamming n).Adj u y)
    (hxv : (hypercubeHamming n).Adj x v) (hvy : (hypercubeHamming n).Adj v y)
    (hxy : x ≠ y) (huv : u ≠ v) : u + v = x + y := by
  obtain ⟨i, rfl⟩ := hypercubeHamming_adj_iff_exists.1 hxu
  obtain ⟨j, rfl⟩ := hypercubeHamming_adj_iff_exists.1 huy
  obtain ⟨p, rfl⟩ := hypercubeHamming_adj_iff_exists.1 hxv
  obtain ⟨q, hq⟩ := hypercubeHamming_adj_iff_exists.1 hvy
  -- cancel the common `x`: `eᵢ + eⱼ = eₚ + e_q`
  rw [add_assoc, add_assoc] at hq
  have hkey : Pi.single i true + Pi.single j true =
      (Pi.single p true + Pi.single q true : Fin n → Bool) := add_left_cancel hq
  -- Mathlib classifies the solutions of `eᵢ + eⱼ = eₚ + e_q`: either `i = p` and
  -- `j = q`, or `i = q` and `j = p`, or `i = j` and `p = q` (as `true + true = 0`)
  rcases (Pi.single_add_single_eq_single_add_single (by decide) (by decide)).1
    hkey with ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩
  · exact absurd rfl huv
  · abel
  · exact absurd (by simp [add_assoc]) hxy

/-!
## Canonical Subcube Copies

A canonical copy of `Q[k]` inside `Q[n]` is determined by a base point
`b : Fin n → Bool` and an injection `d : Fin k ↪ Fin n` selecting the `k` free
directions: the vertex `x` of `Q[k]` is sent to `b + extendEmb d x`, where
`extendEmb d x` places the coordinates of `x` in the positions selected by `d`
and is `false` elsewhere.
-/

/-- Extend a `k`-vector to an `n`-vector along an embedding `d : Fin k ↪ Fin n`,
placing `x i` in position `d i` and `false` elsewhere. This is Mathlib's
`Function.extend d x e`, which agrees with `x` along `d` and with the default
function `e` off the image of `d`; here `e` is the zero vector `0 : Fin n → Bool`,
i.e. constantly `false`. -/
noncomputable def extendEmb {n k : ℕ} (d : Fin k ↪ Fin n) (x : Fin k → Bool) :
    Fin n → Bool :=
  Function.extend d x 0

@[simp]
lemma extendEmb_apply {n k : ℕ} (d : Fin k ↪ Fin n) (x : Fin k → Bool) (i : Fin k) :
    extendEmb d x (d i) = x i :=
  d.injective.extend_apply x 0 i

lemma extendEmb_apply_of_not_exists {n k : ℕ} {d : Fin k ↪ Fin n} (x : Fin k → Bool)
    {j : Fin n} (hj : ¬∃ i, d i = j) : extendEmb d x j = false :=
  Function.extend_apply' x (0 : Fin n → Bool) j hj

@[simp]
lemma extendEmb_zero {n k : ℕ} (d : Fin k ↪ Fin n) : extendEmb d 0 = 0 :=
  Function.extend_zero d

lemma extendEmb_add {n k : ℕ} (d : Fin k ↪ Fin n) (x y : Fin k → Bool) :
    extendEmb d (x + y) = extendEmb d x + extendEmb d y := by
  simpa [extendEmb] using Function.extend_add d x y 0 0

lemma extendEmb_single {n k : ℕ} (d : Fin k ↪ Fin n) (i : Fin k) (b : Bool) :
    extendEmb d (Pi.single i b) = Pi.single (d i) b := by
  funext j
  by_cases hj : ∃ i', d i' = j
  · obtain ⟨i', rfl⟩ := hj
    simp [Pi.single_apply, d.injective.eq_iff]
  · have hji : j ≠ d i := fun h => hj ⟨i, h.symm⟩
    simp [extendEmb_apply_of_not_exists _ hj, Bool.zero_eq_false, hji]

lemma extendEmb_injective {n k : ℕ} (d : Fin k ↪ Fin n) :
    Function.Injective (extendEmb d) :=
  Function.extend_injective d.injective 0

/-- The homomorphism `hypercubeHamming k →g hypercubeHamming n` induced by an
embedding of directions. -/
@[simps]
noncomputable def extendHom {n k : ℕ} (d : Fin k ↪ Fin n) :
    hypercubeHamming k →g hypercubeHamming n where
  toFun := extendEmb d
  map_rel' := by
    intro x y hxy
    obtain ⟨i, rfl⟩ := hypercubeHamming_adj_iff_exists.1 hxy
    exact hypercubeHamming_adj_iff_exists.2
      ⟨d i, by rw [extendEmb_add, extendEmb_single]⟩

/-- The canonical copy of `Q[k]` in `Q[n]` with base point `b` and free directions
selected by `d`: the subcube `{ b + extendEmb d x | x : Fin k → Bool }`. -/
noncomputable def subCubeCopy {n k : ℕ} (b : Fin n → Bool) (d : Fin k ↪ Fin n) :
    Copy (hypercubeHamming k) (hypercubeHamming n) where
  toHom := (hammingTranslate b).toHom.comp (extendHom d)
  injective' := fun _ _ h => extendEmb_injective d (add_left_cancel h)

@[simp]
lemma subCubeCopy_apply {n k : ℕ} (b : Fin n → Bool) (d : Fin k ↪ Fin n)
    (x : Fin k → Bool) : subCubeCopy b d x = b + extendEmb d x := rfl

/-!
The base point and direction embedding are recoverable from the copy:
`subCubeCopy` is injective in `(b, d)`.
-/
lemma subCubeCopy_injective {n k : ℕ} :
    Function.Injective fun bd : (Fin n → Bool) × (Fin k ↪ Fin n) =>
      subCubeCopy bd.1 bd.2 := by
  rintro ⟨b, d⟩ ⟨b', d'⟩ h
  have happ : ∀ x, b + extendEmb d x = b' + extendEmb d' x := by
    intro x
    simpa using DFunLike.congr_fun h x
  have hb : b = b' := by simpa using happ 0
  subst hb
  have hd : d = d' := by
    apply DFunLike.ext
    intro i
    have hx := add_left_cancel (happ (Pi.single i true))
    rw [extendEmb_single, extendEmb_single] at hx
    exact single_true_left_inj hx
  rw [hd]

/-!
## Rigidity: Every Copy is a Canonical Subcube Copy

Every copy of `Q[k]` in `Q[n]` is of the form `subCubeCopy b d`. Note that a copy is
only an *injective homomorphism*: it preserves adjacency in the forward direction
only, so, unlike for automorphisms, no distance or weight preservation is available.
The parallelogram lemma substitutes for it: the proof is by strong induction on the
Hamming weight, computing `f y` for `y` of weight `m + 2` from the images of the
three vertices `y + eᵢ`, `y + eⱼ`, `y + eᵢ + eⱼ` below it in the four-cycle through
`y`.

First we prove a small helper lemma: a vector of Hamming weight at least two has two
distinct `true` coordinates.
-/
lemma exists_ne_true_true_of_one_lt_hammingNorm {n : ℕ} {y : Fin n → Bool}
    (hy : 1 < hammingNorm y) : ∃ i j, i ≠ j ∧ y i = true ∧ y j = true := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hy
  use i, j, hij
  simp_all [Bool.zero_eq_false]

/-!
A copy maps each square `y, y + eᵢ, y + eᵢ + eⱼ, y + eⱼ` of `Q[k]` to a four-cycle
in `Q[n]`, so by the parallelogram lemma the image of any corner is the sum of the
images of the other three.
-/
lemma copy_apply_eq_add_add {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) (y : Fin k → Bool)
    {i j : Fin k} (hij : i ≠ j) :
    f y = f (y + Pi.single i true + Pi.single j true) + f (y + Pi.single i true)
      + f (y + Pi.single j true) := by
  have hadj : ∀ (x : Fin k → Bool) (a : Fin k),
      (hypercubeHamming n).Adj (f x) (f (x + Pi.single a true)) :=
    fun x a => f.toHom.map_adj (hypercubeHamming_adj_iff_exists.2 ⟨a, rfl⟩)
  have hpar := hypercubeHamming_parallelogram (hadj y i) (hadj _ j) (hadj y j)
    (by rw [add_right_comm]; exact hadj _ i)
    (fun h => by simpa [Pi.single_apply, hij] using congrFun (f.injective h) i)
    (fun h => hij (single_true_left_inj (add_left_cancel (f.injective h))))
  rw [add_assoc, hpar, add_comm (f y), boolVec_add_add_cancel]

lemma copy_exists_extendEmb {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) :
    ∃ d : Fin k ↪ Fin n, ∀ x, f x = f 0 + extendEmb d x := by
  -- each basis vector is mapped to a neighbour of `f 0`, defining the
  -- direction map `δ`
  have hD : ∀ i : Fin k, ∃ p : Fin n,
      f (Pi.single i true) = f 0 + Pi.single p true := by
    intro i
    have hadj : (hypercubeHamming n).Adj (f 0) (f (Pi.single i true)) :=
      f.toHom.map_adj (hypercubeHamming_adj_iff_exists.2 ⟨i, (zero_add _).symm⟩)
    exact hypercubeHamming_adj_iff_exists.1 hadj
  choose δ hδ using hD
  have hδinj : Function.Injective δ := by
    intro i j hδij
    have h : f (Pi.single i true) = f (Pi.single j true) := by
      rw [hδ i, hδ j, hδij]
    exact single_true_left_inj (f.injective h)
  refine ⟨⟨δ, hδinj⟩, ?_⟩
  suffices H : ∀ (m : ℕ) (y : Fin k → Bool), hammingNorm y = m →
      f y = f 0 + extendEmb ⟨δ, hδinj⟩ y from fun x => H _ x rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · -- weight zero: `y = 0`
      intro y hy
      rw [hammingNorm_eq_zero] at hy
      simp [hy]
    rcases m with _ | m
    · -- weight one: `y` is a basis vector, handled by the direction map
      intro y hy
      obtain ⟨i, rfl⟩ := hammingNorm_eq_one_iff.mp hy
      rw [hδ i, extendEmb_single]
      rfl
    -- weight `m + 2`: `y` has two distinct `true` coordinates `i ≠ j`
    intro y hy
    obtain ⟨i, j, hij, hyi, hyj⟩ :=
      exists_ne_true_true_of_one_lt_hammingNorm (by grind : 1 < hammingNorm y)
    -- the three vertices below `y` in the four-cycle have smaller weight
    have hn₁ : hammingNorm (y + Pi.single i true) = m + 1 := by
      have := hammingNorm_add_single hyi; grind
    have hn₂ : hammingNorm (y + Pi.single j true) = m + 1 := by
      have := hammingNorm_add_single hyj; grind
    have h2j : (y + Pi.single i true : Fin k → Bool) j = true := by
      simp [hij.symm, hyj]
    have hn₃ : hammingNorm (y + Pi.single i true + Pi.single j true) = m := by
      have := hammingNorm_add_single h2j; grind
    have hf₁ := ih (m + 1) (by grind) _ hn₁
    have hf₂ := ih (m + 1) (by grind) _ hn₂
    have hf₃ := ih m (by grind) _ hn₃
    -- `f y` is determined by the three smaller corners of the square
    rw [copy_apply_eq_add_add f y hij, hf₁, hf₂, hf₃]
    simp only [extendEmb_add]
    simp [add_assoc, add_comm, add_left_comm]

/-!
Every copy of `Q[k]` in `Q[n]` *is* a canonical subcube copy.
-/
lemma copy_eq_subCubeCopy {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) :
    ∃ (b : Fin n → Bool) (d : Fin k ↪ Fin n), f = subCubeCopy b d := by
  obtain ⟨d, hd⟩ := copy_exists_extendEmb f
  exact ⟨f 0, d, Copy.ext fun x => by simpa using hd x⟩

/-!
## The Labelled Count

Rigidity and `subCubeCopy_injective` combine into a classification of the copies
of `Q[k]` in `Q[n]`: they correspond exactly to pairs of a base point and a
direction embedding. The labelled copy count follows by counting the pairs.

Sanity checks: for `k = n` the count is `2 ^ n * n!`, the order of the
automorphism group `card_aut_hypercube` (every copy of `Q[n]` in itself is an
automorphism); for `k = 0` it is `2 ^ n`, the number of vertices; for `k = 1` it
is `2 ^ n * n`, the number of edges counted with direction.
-/
noncomputable def copyEquivProd (n k : ℕ) :
    Copy (hypercubeHamming k) (hypercubeHamming n) ≃
      (Fin n → Bool) × (Fin k ↪ Fin n) :=
  (Equiv.ofBijective (fun bd => subCubeCopy bd.1 bd.2)
    ⟨subCubeCopy_injective, fun f => by
      obtain ⟨b, d, hf⟩ := copy_eq_subCubeCopy f
      exact ⟨(b, d), hf.symm⟩⟩).symm

theorem labelledCopyCount_hypercubeHamming (n k : ℕ) :
    (hypercubeHamming n).labelledCopyCount (hypercubeHamming k) =
      2 ^ n * n.descFactorial k := by
  rw [labelledCopyCount, Fintype.card_eq_nat_card,
    Nat.card_congr (copyEquivProd n k), Nat.card_prod,
    ← Fintype.card_eq_nat_card, ← Fintype.card_eq_nat_card,
    Fintype.card_embedding_eq, Fintype.card_fun]
  simp

/-!
To transport this to `Q[n]` we use `Iso.labelledCopyCount_eq` from
[Counting Copies*](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-counting-copies):
isomorphic graphs have the same copy counts.
-/
theorem labelledCopyCount_hypercube (n k : ℕ) :
    Q[n].labelledCopyCount Q[k] = 2 ^ n * n.descFactorial k :=
  ((hypercubeIsoHamming k).labelledCopyCount_eq (hypercubeIsoHamming n)).trans
    (labelledCopyCount_hypercubeHamming n k)

/-!
## The Unlabelled Count

Taking `n = k`, the cube `Q[k]` has `2 ^ k * k!` automorphisms (as we already knew
from `card_aut_hypercube`), and dividing the labelled count by this number gives the
unlabelled count.
-/
/-- The number of subgraphs of `Q[n]` isomorphic to `Q[k]`: choose the `k` free
coordinates, then fix the remaining `n - k` coordinates arbitrarily. -/
theorem copyCount_hypercube (n k : ℕ) (h : k ≤ n) :
    Q[n].copyCount Q[k] = n.choose k * 2 ^ (n - k) := by
  have hcopy : Q[k].labelledCopyCount Q[k] = 2 ^ k * k.factorial := by
    rw [labelledCopyCount_hypercube, Nat.descFactorial_self]
  have hlabel := labelledCopyCount_hypercube n k
  rw [labelledCopyCount_eq_copyCount_mul_labelledCopyCount,
    Nat.descFactorial_eq_factorial_mul_choose, hcopy] at hlabel
  have h2 : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  rw [h2] at hlabel
  refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ k * k.factorial) ?_
  rw [hlabel]
  ring

/-!
## Every Copy is Induced

A canonical subcube copy preserves Hamming distances: translation is an automorphism,
and `extendEmb d` preserves the Hamming weight since the coordinates outside the
image of `d` are all `false`. So a canonical copy preserves graph distances, i.e. it
is an *isometric* embedding.
-/
lemma hammingNorm_extendEmb {n k : ℕ} (d : Fin k ↪ Fin n) (z : Fin k → Bool) :
    hammingNorm (extendEmb d z) = hammingNorm z := by
  simp only [hammingNorm]
  rw [← Finset.card_map d]
  congr 1
  ext j
  by_cases hj : ∃ i, d i = j
  · obtain ⟨i, rfl⟩ := hj
    simp
  · simp_all [extendEmb_apply_of_not_exists _ hj, Bool.zero_eq_false]

lemma hammingDist_extendEmb {n k : ℕ} (d : Fin k ↪ Fin n) (x y : Fin k → Bool) :
    hammingDist (extendEmb d x) (extendEmb d y) = hammingDist x y := by
  rw [hammingDist_eq_hammingNorm, hammingDist_eq_hammingNorm,
    boolVec_neg, boolVec_neg, ← extendEmb_add, hammingNorm_extendEmb]

lemma subCubeCopy_edist {n k : ℕ} (b : Fin n → Bool) (d : Fin k ↪ Fin n)
    (x y : Fin k → Bool) :
    (hypercubeHamming n).edist (subCubeCopy b d x) (subCubeCopy b d y) =
      (hypercubeHamming k).edist x y := by
  have h := hammingDist_aut (hammingTranslate b) (extendEmb d x) (extendEmb d y)
  simp only [hammingTranslate_apply] at h
  rw [hypercubeHamming_edist_eq, hypercubeHamming_edist_eq, subCubeCopy_apply,
    subCubeCopy_apply, h, hammingDist_extendEmb]

/-!
Since adjacency is distance one, a canonical copy reflects adjacency as well as
preserving it, and by rigidity every copy is canonical. So every copy of `Q[k]` in
`Q[n]` is *induced*, and, as for the 5-cycles of
[Induced 5-Cycles](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-induced-5-cycles),
the labelled count also counts the embeddings. We state both facts in the Hamming
model, i.e. for `hypercubeHamming k` in `hypercubeHamming n`.
-/
lemma copy_hypercubeHamming_adj_iff {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) {x y : Fin k → Bool} :
    (hypercubeHamming n).Adj (f x) (f y) ↔ (hypercubeHamming k).Adj x y := by
  obtain ⟨b, d, rfl⟩ := copy_eq_subCubeCopy f
  rw [← edist_eq_one_iff_adj, ← edist_eq_one_iff_adj, subCubeCopy_edist]

theorem card_embedding_hypercubeHamming (n k : ℕ) :
    Nat.card (hypercubeHamming k ↪g hypercubeHamming n) =
      2 ^ n * n.descFactorial k := by
  rw [← Nat.card_congr (copyEquivEmbedding fun f _ _ =>
      (copy_hypercubeHamming_adj_iff f).1), ← Fintype.card_eq_nat_card]
  exact labelledCopyCount_hypercubeHamming n k

end SimpleGraph
