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
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Real.GoldenRatio
namespace SimpleGraph
/-!
*Algebraic graph theory* studies a graph via algebraic objects attached to it, above
all its *automorphism group*, which measures how symmetric the graph is, and its
*adjacency matrix*, whose powers count walks. The two interact: a permutation of the
vertices is an automorphism iff it preserves the adjacency matrix.

In this chapter we start from Mathlib's group structure on the automorphisms `G ≃g G`
of a graph, show that isomorphic graphs have isomorphic automorphism groups, and
compute the automorphism groups of the infinite path `pathNat₁` (trivial) and of the
cycle graph `C[n]` (dihedral). We then introduce the adjacency matrix, and show that
every vertex of a vertex-transitive graph lies on the same number of closed walks of
each length, and that isomorphic graphs have the same eigenvalues, though not
conversely. We also find eigenvalues of Mycielskians, where the golden ratio appears.
We survey Mathlib's results on the Laplacian, whose kernel has dimension equal to the
number of connected components, and on strongly regular graphs such as the Petersen
graph. We then show that the Hamming cube model `hypercubeHamming` of the hypercube
is isomorphic to our recursive box product construction.

The final three sections are more advanced. Using the Hamming cube model of `Q[n]`,
we prove that its automorphism group is the hyperoctahedral group `ℤ/2 ≀ Sₙ`, of
order `2 ^ n * n!`. We then count copies of one graph in another: the unlabelled
copies of `K[s]` are the `s`-cliques, and in general the number of labelled copies is
the number of unlabelled copies times the number of automorphisms, which we apply to
cycles. Finally we show that every copy of `Q[k]` in `Q[n]` is an induced subcube,
and count these copies.

# Automorphism Groups

Mathlib provides a `Group` instance on the automorphisms `G ≃g G` of any graph, with
multiplication given by composition: `(e * f) v = e (f v)`. (Recall that
`SimpleGraph.Iso` is an abbrev for `RelIso`, which has a `Group` instance.)
-/

#synth Group (C[5] ≃g C[5]) -- RelIso.instGroup

/-!
An isomorphism `e : G ≃g H` transports automorphisms of `G` to automorphisms of `H`
by conjugation, `f ↦ e ∘ f ∘ e.symm`, and this is an isomorphism of automorphism
groups. So isomorphic graphs have isomorphic automorphism groups, and we may compute
an automorphism group using whichever model of a graph is most convenient.

The underlying bijection is Mathlib's `RelIso.relIsoCongr e e`, which transports
isomorphisms along isomorphisms by pre- and post-composition, so we only need to
check that it is multiplicative. We follow Mathlib's naming for such maps (compare
`MulAut.congr`, which does the same for automorphisms of groups). Mathlib writes `≃*`
(`MulEquiv`) for an isomorphism of groups, and `→*` (`MonoidHom`) for a homomorphism.
-/
#check RelIso.relIsoCongr -- (r₁ ≃r r₂) → (s₁ ≃r s₂) → ((r₁ ≃r s₁) ≃ (r₂ ≃r s₂))

/-- Transport of the automorphism group of a graph along an isomorphism
`e : G ≃g H`, by conjugation: `f ↦ e ∘ f ∘ e.symm`. -/
@[simps!]
def Iso.autCongr {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
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
many embeddings into itself: for each `j : ℕ` the embedding `pathNat₁.translate j`
sends `i` to `i + j`. However, none of these is surjective, except for the identity
`pathNat₁.translate 0`.

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
it is a nontrivial automorphism; likewise the two-way infinite path on `ℤ` has the
reflection `i ↦ -i` and the translations `i ↦ i + j` as automorphisms.

## Automorphisms of Cycle Graphs

In `isVertexTransitive_cycleGraph` we showed that the cycle graph `C[n]` is
vertex-transitive, using the rotations `cycleGraph.rotate d`, which send the vertex
`d` to `0`. We now determine its whole automorphism group. Besides the rotations
there is an automorphism given by reflecting the vertices, i.e. sending `k` to `-k`
modulo `n`.
-/
/--
The automorphism of the cycle graph `C[n]` given by reflecting the vertices.
-/
@[simps]
def cycleGraph.reflect {n : ℕ} : C[n] ≃g C[n] where
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
    (h : e 1 - e 0 = 1) : e = cycleGraph.rotate (e.symm 0) := by
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
see this note that `f = cycleGraph.reflect ∘ e` satisfies `f 1 - f 0 = 1`, so `f` is
a rotation by the previous lemma, and hence `e = cycleGraph.reflect ∘ f` is as
claimed (the reflection is an involution).
-/
lemma aut_cycleGraph_eq_rotate_trans_reflect {n : ℕ} (e : C[n + 2] ≃g C[n + 2])
    (h : e 0 - e 1 = 1) :
    e = (cycleGraph.rotate (e.symm 0)).trans cycleGraph.reflect := by
  let f := e.trans cycleGraph.reflect
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
    e = cycleGraph.rotate i ∨
      e = (cycleGraph.rotate i).trans cycleGraph.reflect := by
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
corresponds to `cycleGraph.rotate i` and, since `sr i = sr 0 * r i`, the reflection
`sr i` corresponds to `cycleGraph.rotate i` followed by the reflection. In both cases
the index `i` is the vertex sent to `0`, i.e. `e.symm 0`.
-/
#source DihedralGroup
/-!
Multiplicativity is easiest to check in the direction from `DihedralGroup (n + 3)`,
where it amounts to four short computations with rotations and reflections, so we
build the isomorphism in that direction and then take its inverse.
-/
/-- The automorphism group of the cycle graph `C[n + 3]` is isomorphic to the
dihedral group of order `2 * (n + 3)`. -/
def autCycleGraphMulEquivDihedral (n : ℕ) :
    (C[n + 3] ≃g C[n + 3]) ≃* DihedralGroup (n + 3) :=
  MulEquiv.symm
    { toFun := fun d => match d with
        | .r i => cycleGraph.rotate ((ZMod.finEquiv (n + 3)).symm i)
        | .sr i => (cycleGraph.rotate ((ZMod.finEquiv (n + 3)).symm i)).trans
            cycleGraph.reflect
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
        rintro (i | i) (j | j) <;> ext k <;>
          simp [map_add, map_sub, sub_sub, sub_sub_eq_add_sub, add_comm] }

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
def autHypercubeTwoMulEquivDihedral : (Q[2] ≃g Q[2]) ≃* DihedralGroup 4 :=
  hypercubeTwoIsoCycleFour.autCongr.trans (autCycleGraphMulEquivDihedral 1)

/-!
# The Adjacency Matrix

A graph can also be studied via matrices indexed by its vertices. Mathlib's
`Matrix V V R` is the type of functions `V → V → R`, so no ordering of the vertices
is needed.

The *adjacency matrix* `G.adjMatrix R`, which we also write `A`, has `(u, v)` entry
`1` if `u` and `v` are adjacent and `0` otherwise. (`!![a, b; c, d]` is Mathlib's
notation for a matrix written row by row.)

[Figure: A graph $G$ and its adjacency matrix $A(G)$](https://jt496.github.io/GraphTheoryInLean/figures/adjmatrix.svg)
-/
section adjmatrix
variable {V : Type*} {G : SimpleGraph V}

#source adjMatrix
#eval C[4].adjMatrix ℕ -- !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

/-!
Since a `SimpleGraph` is symmetric and loopless, its adjacency matrix is symmetric
with zero diagonal.
-/
#check isSymm_adjMatrix
#check diag_adjMatrix

/-!
The `(u, v)` entry of the `n`-th power of the adjacency matrix counts the walks of
length `n` from `u` to `v`
([Walks](https://jt496.github.io/GraphTheoryInLean/Walks/#chapter-walks)). The walks
of a given length between two vertices form a `Finset`, `finsetWalkLength`, so both
sides can be computed. (Defining `G.adjMatrix R` only needs `DecidableRel G.Adj`, but
a matrix product sums over all of `V`, so from here on we assume `[Fintype V]`.
`[G.LocallyFinite]` is not enough: the entries of powers of the adjacency matrix
count walks and so are finite, but Mathlib's matrix product needs a finite index
type.)

[Figure: The two length-2 walks from vertex 1 to vertex 3 and the entry $(A^2)_{1,3}=2$](https://jt496.github.io/GraphTheoryInLean/figures/walkcount.svg)
-/
#source finsetWalkLength
#check adjMatrix_pow_apply_eq_card_walk

#eval (C[5].adjMatrix ℕ ^ 5) 0 0                    -- 2
#eval (C[5].finsetWalkLength 5 0 0).card            -- 2
#eval (K[5].finsetWalkLength 2 0 1).card            -- 3
#eval (K[2, 4].adjMatrix ℕ ^ 2) (.inl 0) (.inl 0)   -- 4

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
Summing the diagonal entries, the trace of `Aᵏ` is the total number of closed walks
of length `k`. We count the walks with `finsetWalkLength` rather than the set used by
`adjMatrix_pow_apply_eq_card_walk`: `card_set_walk_length_eq` relates the two, and
`simp` rewrites the set form into the `Finset` form using `Fintype.card_ofFinset`.
-/
open Finset in
theorem trace_adjMatrix_pow_eq_sum_card_walk [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {R : Type*} [Semiring R] (k : ℕ) :
    (G.adjMatrix R ^ k).trace = ∑ v, (#(G.finsetWalkLength k v v) : R) := by
  simp [Matrix.trace, adjMatrix_pow_apply_eq_card_walk]

/-!
The adjacency matrix determines the graph, and a bijection of the vertices
`σ : V ≃ V` is an automorphism exactly when it preserves the adjacency matrix:
relabelling the rows and columns of `A` by `σ` leaves `A` unchanged. In matrix
language, the permutation matrix `P` of `σ` satisfies `P A Pᵀ = A`, i.e. `P` commutes
with `A`. In Lean we relabel with `Matrix.submatrix`, which composes the row and
column indices with `σ`.

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
For an automorphism `f`, Mathlib's `Iso.reindex_adjMatrix` already gives
`(G.adjMatrix R).reindex f f = G.adjMatrix R`, and so do its powers, since
relabelling rows and columns is a ring isomorphism (`Matrix.reindexRingEquiv`).
Combined with the walk-counting formula, this shows that automorphisms preserve the
number of walks of each length between two vertices. In a vertex-transitive graph it
follows that every vertex lies on the same number of closed walks of length `k`.

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
So, in a vertex-transitive graph, the `tr(Aᵏ)` closed walks of length `k` are shared
equally among its vertices.
-/
open Finset in
theorem IsVertexTransitive.card_walk_self_eq_trace_div [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (h : G.IsVertexTransitive) (k : ℕ) (v : V) :
    #(G.finsetWalkLength k v v) = (G.adjMatrix ℕ ^ k).trace / Fintype.card V := by
  -- every vertex lies in as many closed walks of length `k` as `v`
  have hu (u : V) : #(G.finsetWalkLength k u u) = #(G.finsetWalkLength k v v) := by
    simpa [adjMatrix_pow_apply_eq_card_walk] using
      h.adjMatrix_pow_apply_self (R := ℕ) k u v
  simp only [trace_adjMatrix_pow_eq_sum_card_walk, Nat.cast_id]
  rw [Finset.sum_eq_card_nsmul fun u _ => hu u, Finset.card_univ, smul_eq_mul,
    Nat.mul_div_cancel_left _ (Fintype.card_pos_iff.2 ⟨v⟩)]

/-!
For example, the cycle `C[5]` is vertex-transitive (`isVertexTransitive_cycleGraph`)
and has `10` closed walks of length `5`, so each of its `5` vertices lies on two of
them: the two directions round the cycle.
-/
#eval (C[5].adjMatrix ℕ ^ 5).trace -- 10

open Finset in
example (v : Fin 5) : #(C[5].finsetWalkLength 5 v v) = 2 := by
  rw [(isVertexTransitive_cycleGraph 5).card_walk_self_eq_trace_div]
  decide

/-!
## Eigenvalues

The eigenvalues of the adjacency matrix make up the *spectrum* of `G`, a central
object of algebraic graph theory. (Mathlib's `spectrum R M` is the set of `ξ : R` for
which `ξ • 1 - M` is not invertible; for a matrix over a field these are its
eigenvalues.)

A `d`-regular graph has eigenvalue `d`, with the all-ones eigenvector. (In
[The Laplacian](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-the-laplacian)
we show that its multiplicity is the number of connected components.)
-/
#check IsRegularOfDegree.mem_spectrum_adjMatrix

/-!
Isomorphic graphs have the same adjacency matrix up to relabelling, so they have the
same characteristic polynomial, i.e. the same eigenvalues with the same
multiplicities.
-/
theorem Iso.charpoly_adjMatrix [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : Type*} [CommRing R] (f : G ≃g H) :
    (G.adjMatrix R).charpoly = (H.adjMatrix R).charpoly := by
  rw [← f.reindex_adjMatrix R, Matrix.charpoly_reindex]

/-!
In particular, isomorphic graphs have the same spectrum. Mathlib's `spectrum` is a
set, so it forgets the multiplicities, and the spectrum of a matrix is determined by
its characteristic polynomial (`Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly`).
-/
theorem Iso.spectrum_adjMatrix [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : Type*} [CommRing R] (f : G ≃g H) :
    spectrum R (G.adjMatrix R) = spectrum R (H.adjMatrix R) := by
  ext ξ
  rw [Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly,
    Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly, f.charpoly_adjMatrix]

/-!
The converse fails: the star `K[4, 1]` and the disjoint union `C[4] ⊕g K[1]` of a
`4`-cycle and a single vertex are two graphs on the same vertex type `Fin 4 ⊕ Fin 1`,
with the same characteristic polynomial `X ^ 5 - 4 * X ^ 3`, but are not isomorphic.
Mathlib's polynomials are not computable, and neither `#eval` nor `decide` can help
directly with proving this.

We relabel the vertices by `Fin 5` (using `finSumFinEquiv`) and use `decide` only to
check the resulting integer matrix, a finite computation. We then expand the
determinant along its rows with `Matrix.det_succ_row_zero`, and finish the proof
with `ring`.

[Figure: Left: the star $K_{4,1}$. Right: the disjoint union of $C_4$ and $K_1$. Vertices are numbered by `finSumFinEquiv` as in the matrices below. Both graphs have characteristic polynomial $x^5 -4x^3$](https://jt496.github.io/GraphTheoryInLean/figures/cospectral.svg)
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

/-!
Graphs with the same eigenvalues, counted with multiplicity, cannot be told apart by
counting edges or triangles. The eigenvalues determine the trace of every power `Aᵏ`,
and hence the number of closed walks of each length
(`trace_adjMatrix_pow_eq_sum_card_walk`), and `tr(A²)` is twice the number of edges
while `tr(A³)` is six times the number of triangles. (Both of our graphs have `4`
edges and no triangles.)

But `K[4, 1]` has no isolated vertices, while `C[4] ⊕g K[1]` obviously does.
-/
example : IsEmpty (K[4, 1] ≃g C[4] ⊕g K[1]) := ⟨fun e => by
  have h₁ : ∀ v, ∃ w, K[4, 1].Adj v w := by decide
  have h₂ : ∀ w, ¬ (C[4] ⊕g K[1]).Adj (.inr 0) w := by decide
  obtain ⟨w, hw⟩ := h₁ (e.symm (.inr 0))
  exact h₂ (e w) (by simpa using e.map_adj_iff.2 hw)⟩

/-!
## Eigenvalues of Mycielskians

Apart from the eigenvalue `d` of a `d`-regular graph (and the Laplacian eigenvalue
`0`), Mathlib has no eigenvalues of particular graphs. But we can often find them by
exhibiting eigenvectors, as Mathlib does for `d`. As an example we show that
eigenvalues of `G` give eigenvalues of its Mycielskian `mμ[G]`, scaled by the golden
ratio.

Mathlib writes `M *ᵥ x` (`Matrix.mulVec`) for the product of a matrix `M` and a
vector `x`, whose entry at `i` is `∑ j, M i j * x j`. So a nonzero vector `x` is an
eigenvector of `M` with eigenvalue `ξ` iff `M *ᵥ x = ξ • x`.

We list the vertices of `mμ[G]` in the order given by their type `Option (V ⊕ V)`:
first the apex `none`, then the left copies `v ₗ`, then the right copies `v ᵣ`. Let
`A` be the adjacency matrix of `G`, and write `1` for the all-ones vector. A left
copy `v ₗ` is adjacent to both copies of each neighbour of `v`, and a right copy
`v ᵣ` is adjacent to the left copies of the neighbours of `v` and to the apex. So the
adjacency matrix of `mμ[G]` has the block form shown in the figure.

 `             apex  left  right                              `
 `   apex   [  0     0     1ᵀ ]   [ 0   ]   [ 1ᵀ x        ]   `
 `   left   [  0     A     A  ] * [ t x ] = [ (t + 1) A x ]   `
 `   right  [  1     A     0  ]   [ x   ]   [ t A x       ]   `

[Figure: The adjacency matrix of the Mycielskian, applied to a vector with blocks $0$, $tx$ and $x$](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian_adjmatrix.svg)

Now let `x` be an eigenvector of `A` with eigenvalue `ξ` whose entries sum to zero,
i.e. `x` is orthogonal to `1`. By the above figure, with `A x = ξ x` and `1ᵀ x = 0`,
the vector `y` with blocks `0`, `t • x` and `x` is sent to the vector with blocks
`0`, `(t + 1) • ξ • x` and `t • ξ • x`. So `y` is an eigenvector with eigenvalue
`t * ξ` provided `t + 1 = t ^ 2`. The roots of this quadratic are the golden ratio
`φ = (1 + √5) / 2` and its conjugate `ψ = (1 - √5) / 2`. In Mathlib these are
`Real.goldenRatio` and `Real.goldenConj`, with notation `φ` and `ψ` in the
`goldenRatio` scope, and `Real.goldenRatio_sq` and `Real.goldenConj_sq` say that they
are these roots. (An eigenvalue `ξ` of `G` need not have an eigenvector whose
entries sum to zero, and then the construction says nothing about `φ * ξ` and
`ψ * ξ`. For example, the only eigenvectors of `K[2]` with eigenvalue `1` are the
constant vectors, and neither `φ` nor `ψ` is an eigenvalue of `mμ[K[2]]`, which is
the `5`-cycle (see below). In a `d`-regular graph, however, every eigenvalue other
than `d` has such an eigenvector: eigenvectors of a symmetric matrix with distinct
eigenvalues are orthogonal, and `1` is an eigenvector with eigenvalue `d`.)

In Lean, if we define `y` by pattern matching on the three kinds of vertex and mark
the definition `@[simp]`, then `simp` evaluates `y` at `none`, `v ₗ` and `v ᵣ`
but leaves `y` alone when it isn't applied to a vertex.
-/
/-- The vector on the vertices of `mμ[G]` with value `0` at `none`, `t * x v` at
`v ₗ` and `x v` at `v ᵣ`. -/
@[simp]
def mycielskianLift {R : Type*} [Zero R] [Mul R] (t : R) (x : V → R) :
    Option (V ⊕ V) → R
  | none => 0
  | v ₗ => t * x v
  | v ᵣ => x v

/-!
The proof is the computation in the figure, with one case for each kind of vertex.
Sums over `Option (V ⊕ V)` split in the same order: `Fintype.sum_option` separates
the term at `none`, and `Fintype.sum_sum_type` splits the rest into the left and
right copies. We work over any commutative ring, and with any root `t` of
`t ^ 2 = t + 1`.

If `A *ᵥ x = ξ • x`, the entries of `x` sum to zero and `t ^ 2 = t + 1`, then
`mycielskianLift t x` satisfies the corresponding equation for `mμ[G]`, with
eigenvalue `t * ξ`.
-/
open Matrix in
theorem adjMatrix_mycielskian_mulVec_mycielskianLift [Fintype V]
    [DecidableRel G.Adj] {R : Type*} [CommRing R] {t ξ : R} (ht : t ^ 2 = t + 1)
    {x : V → R} (hx : G.adjMatrix R *ᵥ x = ξ • x) (hsum : ∑ v, x v = 0) :
    mμ[G].adjMatrix R *ᵥ mycielskianLift t x = (t * ξ) • mycielskianLift t x := by
  -- the entries of `A *ᵥ x` and of `A *ᵥ (t • x)`
  have hv (v : V) : ∑ u, (if G.Adj v u then x u else 0) = ξ * x v := by
    simpa [mulVec, dotProduct, adjMatrix_apply] using congrFun hx v
  have htv (v : V) :
      ∑ u, (if G.Adj v u then t * x u else 0) = t * (ξ * x v) := by
    simp_rw [← hv, Finset.mul_sum, mul_ite, mul_zero]
  -- at a left copy we need `t ^ 2 = t + 1`
  have hleft (v : V) : t * (ξ * x v) + ξ * x v = t * ξ * (t * x v) := by
    -- `linear_combination e` closes the goal if `ring` shows it is `e` rearranged
    linear_combination (-(ξ * x v)) * ht
  ext (_ | v | v) <;> simp_all [mulVec, dotProduct, mul_assoc]

/-!
Since `mycielskianLift t x` takes the value `x v` at `v ᵣ`, it is nonzero whenever
`x` is.
-/
lemma mycielskianLift_ne_zero {R : Type*} [Zero R] [Mul R] (t : R) {x : V → R}
    (hx : x ≠ 0) : mycielskianLift t x ≠ 0 := by
  contrapose hx
  ext v
  simpa using congrFun hx (v ᵣ)

/-!
An eigenvector gives an element of the spectrum. As in Mathlib's proof of
`IsRegularOfDegree.mem_spectrum_adjMatrix`, we pass from the matrix to the linear map
`Matrix.toLin'` it defines, which has the same spectrum (`Matrix.spectrum_toLin'`),
and use the fact that eigenvalues of a linear map lie in its spectrum
(`Module.End.HasEigenvalue.mem_spectrum`). Taking `t = φ` and `t = ψ` gives the
following.

If `x ≠ 0` is an eigenvector of `A` with eigenvalue `ξ` whose entries sum to zero,
then `φ * ξ` and `ψ * ξ` are eigenvalues of `mμ[G]`.
-/
open Matrix in
open scoped goldenRatio in
theorem mem_spectrum_adjMatrix_mycielskian [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {ξ : ℝ} {x : V → ℝ} (hx0 : x ≠ 0)
    (hx : G.adjMatrix ℝ *ᵥ x = ξ • x) (hsum : ∑ v, x v = 0) :
    φ * ξ ∈ spectrum ℝ (mμ[G].adjMatrix ℝ) ∧
      ψ * ξ ∈ spectrum ℝ (mμ[G].adjMatrix ℝ) := by
  have key {t : ℝ} (ht : t ^ 2 = t + 1) :
      t * ξ ∈ spectrum ℝ (mμ[G].adjMatrix ℝ) := by
    rw [← spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_genEigenspace_one.2 (by
        simpa using adjMatrix_mycielskian_mulVec_mycielskianLift ht hx hsum),
       mycielskianLift_ne_zero t hx0⟩
  exact ⟨key Real.goldenRatio_sq, key Real.goldenConj_sq⟩

/-!
For example, `K[2]` has the eigenvector `![1, -1]` with eigenvalue `-1`, and its
entries sum to zero. Since `mμ[K[2]]` is isomorphic to `C[5]`
(`mycielskianCompleteTwoIsoCycleFive`), the `5`-cycle has eigenvalues `-φ` and
`-ψ`.
-/
open Matrix in
open scoped goldenRatio in
example :
    -φ ∈ spectrum ℝ (C[5].adjMatrix ℝ) ∧ -ψ ∈ spectrum ℝ (C[5].adjMatrix ℝ) := by
  have hK : K[2].adjMatrix ℝ *ᵥ ![1, -1] = (-1 : ℝ) • ![1, -1] := by
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, adjMatrix_apply]
  rw [← mycielskianCompleteTwoIsoCycleFive.spectrum_adjMatrix]
  simpa using mem_spectrum_adjMatrix_mycielskian (by simp) hK (by simp)

/-!
Mathlib's `spectrum` is a set, so it does not record multiplicities. But for a
`d`-regular graph `G` on `n` vertices this construction accounts for most of the
spectrum of `mμ[G]`, with multiplicities. The adjacency matrix of `G` is symmetric,
so it has an orthogonal basis of eigenvectors that contains `1`, and the other
`n - 1` basis vectors are orthogonal to `1`. They give `2 * (n - 1)` independent
eigenvectors of `mμ[G]`. The remaining three eigenvectors are constant on the left
copies and on the right copies, and their eigenvalues are the roots of
`X ^ 3 - d * X ^ 2 - (d ^ 2 + n) * X + d * n`. For `G = K[2]` we have `d = 1` and
`n = 2` so this cubic is `(X - 2) * (X ^ 2 + X - 1)`, whose quadratic factor gives
`-φ` and `-ψ` a second time, so the eigenvalues of `C[5]` are `2`, and `-φ` and `-ψ`
each with multiplicity two. (This is a coincidence: for a `d`-regular `G` on `n`
vertices this happens only when `n = 2 * d ^ 2`.)

# The Laplacian

The *degree matrix* (`degMatrix`) is the diagonal matrix of degrees, so its diagonal
entries form the `degreeMultiset`, and listing them in non-increasing order gives the
`degreeSequence`.

The *Laplacian* (`lapMatrix`) is given by
`G.lapMatrix R = G.degMatrix R - G.adjMatrix R`.

[Figure: A graph $G$ and its Laplacian $L = D - A$](https://jt496.github.io/GraphTheoryInLean/figures/laplacian.svg)
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
component. For a positive semidefinite matrix the form vanishes exactly on the
*kernel*, the set of vectors `x` with `L *ᵥ x = 0`, so the kernel of `L` consists of
the functions that are constant on components.
-/
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

example : Module.finrank ℝ ((C[3] ⊕g C[4]).lapMatrix ℝ).toLin'.ker = 2 := by
  rw [← card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  decide

/-!
For a `d`-regular graph the degree matrix is `d • 1`, so `L = d • 1 - A`, and the
kernel of `L` is the eigenspace of `A` for the eigenvalue `d`. So the multiplicity of
`d` as an eigenvalue of `A` is the number of connected components. This sharpens
`IsRegularOfDegree.mem_spectrum_adjMatrix` above. In Lean,
`Module.End.eigenspace f ξ` is the kernel of `f - ξ • 1`.
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


end adjmatrix

/-!
For example, the hypercube `Q[n]` is `n`-regular and connected, so `n` is a simple
eigenvalue of its adjacency matrix. (As in
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond),
we first put the filtering `LocallyFinite` instance in scope, since the adjacency
matrix is built from `DecidableRel Q[n].Adj`.)
-/
example (n : ℕ) :
    Module.finrank ℝ (Module.End.eigenspace (Q[n].adjMatrix ℝ).toLin' n) = 1 := by
  -- put the filtering instance in scope, so that
  -- `IsRegularOfDegree.hypercube` uses it
  let : Q[n].LocallyFinite := fun v => Subtype.fintype _
  rw [(IsRegularOfDegree.hypercube n).finrank_eigenspace_adjMatrix]
  -- `Q[n]` is connected, so it has exactly one connected component
  rw [Fintype.card_eq_nat_card]
  exact (connected_hypercube n).card_connectedComponent

/-!
The *incidence matrix* (`incMatrix`) has rows indexed by vertices and columns by
`Sym2 V`, with `(v, e)` entry `1` iff `v` is an endpoint of the edge `e`. The product
of the incidence matrix and its transpose is `D + A`, the *signless* Laplacian.
-/
#check incMatrix_mul_transpose

/-!

# Strongly Regular Graphs

A graph is *strongly regular* (`IsSRGWith`) with parameters `(n, k, ℓ, μ)` if it has
`n` vertices, is `k`-regular, any two adjacent vertices have exactly `ℓ` common
neighbours, and any two distinct non-adjacent vertices have exactly `μ` common
neighbours.
-/
#source IsSRGWith

/-!
The Petersen graph (`petersenGraph`) is strongly regular with parameters
`(10, 3, 0, 1)`: it has girth `5`, so adjacent vertices have no common neighbours and
non-adjacent vertices have at most one, and its diameter is `2`, so they have at
least one. We can check each field with `decide`, but two need an initial `intro`
since `decide` needs a `Decidable` instance for the exact statement and neither
`IsRegularOfDegree` nor `Pairwise` has one.
-/
lemma IsSRGWith.petersenGraph : petersenGraph.IsSRGWith 10 3 0 1 where
  card := by decide
  regular := by intro v; decide +revert
  of_adj := by decide
  of_not_adj := by intro u v; decide +revert

/-!
Counting the paths of length `2` from a fixed vertex `v` to a vertex that is not
adjacent to `v` in two different ways shows that the parameters satisfy
`k * (k - ℓ - 1) = (n - k - 1) * μ`. For the Petersen graph this is
`3 * 2 = 6 * 1`.
-/
#check IsSRGWith.param_eq
-- G.IsSRGWith n k ℓ μ → 0 < n → k * (k - ℓ - 1) = (n - k - 1) * μ

/-!
The diameter of a strongly regular graph with `μ ≠ 0` that is not complete is `2`.
This recovers `ediam_petersenGraph`, which we proved by hand.
-/
#check IsSRGWith.ediam_eq_two -- G.IsSRGWith n k ℓ μ → G ≠ ⊤ → μ ≠ 0 → G.ediam = 2

example : petersenGraph.ediam = 2 := by
  have : Nontrivial {s : Finset (Fin 5) // s.card = 2} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by decide)
  have hne : ¬ petersenGraph.Adj ⟨{0, 1}, rfl⟩ ⟨{0, 2}, rfl⟩ := by decide
  refine IsSRGWith.petersenGraph.ediam_eq_two (fun h => hne ?_) one_ne_zero
  rw [h, top_adj]
  decide

/-!
The complement of a strongly regular graph is strongly regular. The complement of the
Petersen graph is the line graph of `K[5]`, with parameters `(10, 6, 3, 4)`.
-/
example : petersenGraphᶜ.IsSRGWith 10 6 3 4 :=
  IsSRGWith.petersenGraph.compl

/-!
More generally, the line graph `L[K[n]]` is strongly regular with parameters
`(n * (n - 1) / 2, 2 * (n - 2), n - 2, 4)`. Its vertices are the edges of `K[n]`. Two
edges `{a, b}` and `{a, c}` that share an endpoint have the `n - 2` common neighbours
`{b, c}` and `{a, x}` for `x ∉ {a, b, c}`, while two disjoint edges have the `4`
common neighbours that join an endpoint of one to an endpoint of the other.
-/
example : L[K[7]].IsSRGWith 21 10 5 4 where
  card := by decide
  regular := by intro v; decide +revert
  of_adj := by decide
  of_not_adj := by intro u v; decide +revert

/-!
The Paley graph of a field with `q ≡ 1 mod 4` elements (`paleyGraph`) is strongly
regular with parameters `(q, (q - 1) / 2, (q - 5) / 4, (q - 1) / 4)`. The general
proof counts the elements `x` for which `x` and `x - d` are both nonzero squares,
using character sums over the field, but for `q = 17` we can again use `decide`.
-/
example : (paleyGraph (ZMod 17)).IsSRGWith 17 8 3 4 where
  card := by decide
  regular := by intro v; decide +revert
  of_adj := by decide
  of_not_adj := by intro u v; decide +revert

/-!
In terms of the adjacency matrix `A`, the definition of a strongly regular graph says
exactly that `A ^ 2 = k • 1 + ℓ • A + μ • (J - 1 - A)`, where `J` is the all-ones
matrix and `J - 1 - A` is the adjacency matrix of the complement.
-/
#check IsSRGWith.matrix_eq
-- A ^ 2 = k • 1 + ℓ • A + μ • Gᶜ.adjMatrix α, where A = G.adjMatrix α

/-!
This quadratic equation forces `A` to have at most three distinct eigenvalues. It is
the starting point of the Hoffman–Singleton theorem: a Moore graph of diameter `2`
([Moore Graphs](https://jt496.github.io/GraphTheoryInLean/Distance/#section-moore-graphs))
must have girth `5` and be strongly regular with `ℓ = 0` and `μ = 1`. For such a
graph the equation reads `A ^ 2 + A - (k - 1) • 1 = J`, and a linear-algebra argument
then shows that its degree `k` must be `2`, `3`, `7` or `57`. (Existence of such a
graph with `k = 57` is currently an open problem.)

# The Hypercube and the Hamming Cube

When we first introduced the hypercube we gave two other constructions. One of these
was the Hamming cube `hypercubeHamming`: the graph on `Fin n → Bool` in which two
vertices are adjacent iff their Hamming distance, computed by Mathlib's `hammingDist`
for Pi-types, is one. Having identified the graph distance in `Q[n]` with the Hamming
distance (`edist_eq_hammingDist`), we are now in a position to prove that this
construction agrees with the one we adopted, i.e. `Q[n] ≃g hypercubeHamming n`.

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
`Fin n → Bool`, sending `(v, b)` to `Fin.snoc (equivPi n v) b`, so `b` is the last
coordinate. -/
def HypercubeVert.equivPi : (n : ℕ) → HypercubeVert n ≃ (Fin n → Bool)
  | 0 => Equiv.ofUnique Unit _
  | n + 1 => (equivPi n).prodCongr (Equiv.refl _) |>.trans <|
      (Equiv.prodComm _ _).trans <| Fin.snocEquiv fun _ => _

/-!
Unfolding the equiv one step is definitionally `Fin.snoc`, and marking this as
`@[simp]` lets `simp` compute with `equivPi` recursively.
-/
@[simp]
lemma HypercubeVert.equivPi_succ_apply {n : ℕ} (v : HypercubeVert n) (b : Bool) :
    equivPi (n + 1) (v, b) = Fin.snoc (v.equivPi n) b := rfl

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
  simp [hammingDist, Finset.card_filter, Fin.sum_univ_castSucc]

/-!
The Hamming distance of `HypercubeVert n` vertices agrees with the Hamming distance
of the corresponding functions `Fin n → Bool`, by induction on `n`.
-/
@[simp]
lemma HypercubeVert.hammingDist_equivPi {n : ℕ} (u v : HypercubeVert n) :
    _root_.hammingDist (u.equivPi n) (v.equivPi n) = u.hammingDist v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨u, b⟩ := u
    obtain ⟨v, c⟩ := v
    simp [hammingDist_snoc, ih]

/-!
Adjacency in the Hamming cube is Hamming distance one, by definition.
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
cube construction `hypercubeHamming n` on `Fin n → Bool`. -/
def hypercubeIsoHamming (n : ℕ) : Q[n] ≃g hypercubeHamming n where
  toEquiv := HypercubeVert.equivPi n
  map_rel_iff' := by
    simp [hypercube_adj_iff_hammingDist_eq_one]

/-!
This isomorphism is a bridge between the two constructions: results proved for
`Q[n]` by induction transport to `hypercubeHamming`, while statements that need
the coordinates of a vertex, such as identifying the automorphism group of the
hypercube, are more naturally proved for `hypercubeHamming` and transported back.

Transporting `edist_eq_hammingDist` along `hypercubeIsoHamming` shows that the graph
distance in the Hamming cube is exactly the Hamming distance.
-/
lemma edist_hypercubeHamming {n : ℕ} (x y : Fin n → Bool) :
    (hypercubeHamming n).edist x y = hammingDist x y := by
  obtain ⟨u, rfl⟩ := (HypercubeVert.equivPi n).surjective x
  obtain ⟨v, rfl⟩ := (HypercubeVert.equivPi n).surjective y
  exact ((hypercubeIsoHamming n).edist_eq u v).trans (by simp [edist_eq_hammingDist])

/-!
# The Automorphism Group of the Hypercube *

As a substantial application of the bridge we identify the automorphism group of the
hypercube: it is the *hyperoctahedral group*, the wreath product `ℤ/2 ≀ Sₙ` of order
`2 ^ n * n!`. Concretely every automorphism of the hypercube is uniquely a
composition of a *translation* (`xor` by a fixed vertex) and a
*coordinate permutation*, and the wreath product is the semidirect product
`(ℤ/2)ⁿ ⋊ Sₙ` that records how coordinate permutations act on translations.

We work in the Hamming model and transport the result to `Q[n]` at the end. The
proof has four steps.
1. Translations and coordinate permutations are automorphisms of the Hamming cube.
2. Together they give a group homomorphism from `(ℤ/2)ⁿ ⋊ Sₙ` to the Hamming cube's
   automorphism group.
3. This homomorphism is injective: evaluate at `0` and at the standard basis vectors
   `eᵢ`. (The standard basis vectors are given by `Pi.single` in Lean so our informal
   `eᵢ` refers to `Pi.single i true`. We introduce the notation `e i` below.)
4. It is surjective. After composing with a translation, an automorphism fixes `0`.
   It then preserves Hamming weight, so it permutes the basis vectors, which gives a
   permutation `σ`. Undoing `σ` leaves an automorphism fixing `0` and every `eᵢ`,
   which is the identity by a rigidity argument: the coordinates of a vertex can be
   read off from its distances to `0` and to the `eᵢ`.

The key to making this precise in Lean is that Mathlib makes `Bool` a `BooleanRing`,
with `0 = false`, `1 = true` and addition given by `xor`. Consequently the vertex
type `Fin n → Bool` of the Hamming cube is an additive group, namely `(ℤ/2)ⁿ`, with
pointwise `xor` (`^^`) as addition: translations are simply `(t + ·)`.
-/
example {n : ℕ} : AddCommGroup (Fin n → Bool) := inferInstance
example (a b : Bool) : a + b = (a ^^ b) := rfl

/-!
Addition on `Bool` vectors has characteristic two: negation is the identity and
adding the same vector twice gives `0`. Mathlib proves both facts in any Boolean
ring, as `BooleanRing.neg_eq` and `BooleanRing.add_self`, but it has no instance
making a product of Boolean rings a Boolean ring, so they do not apply to
`Fin n → Bool` directly. The missing instance is easy: Mathlib already provides
the pointwise ring structure on functions, and multiplication is idempotent because
it is idempotent in each coordinate.
-/
/-- A product of Boolean rings is a Boolean ring under the pointwise operations. -/
instance _root_.Pi.instBooleanRing {ι : Type*} {R : ι → Type*}
    [∀ i, BooleanRing (R i)] : BooleanRing (∀ i, R i) where
  isIdempotentElem a := funext fun i => BooleanRing.mul_self (a i)

/-!
The two lemmas are `simp` lemmas only once the `BooleanRing` namespace is open
(they are *scoped*), so we open it for the rest of the chapter with
`open scoped BooleanRing`. Mathlib has no lemma for `x + (x + y) = y`, so we add
one.
-/
open scoped BooleanRing
example {n : ℕ} (x : Fin n → Bool) : -x = x := by simp
example {n : ℕ} (x : Fin n → Bool) : x + x = 0 := by simp

@[simp]
lemma boolVec_add_add_cancel {n : ℕ} (x y : Fin n → Bool) : x + (x + y) = y := by
  rw [← add_assoc, BooleanRing.add_self, zero_add]

/-!
The vectors of Hamming weight (`hammingNorm`) one are exactly the standard basis
vectors `Pi.single i true` (all coordinates `false` except the `i`-th). For the rest
of the chapter we write `e i` for `Pi.single i true`, our informal `eᵢ`. The notation
is scoped to `hypercubeHamming`, so later files can use it with
`open scoped hypercubeHamming`.
-/
scoped[SimpleGraph.hypercubeHamming] notation:lead "e " i:max => Pi.single i true
open scoped hypercubeHamming

@[simp]
lemma hammingNorm_single {n : ℕ} (i : Fin n) :
    hammingNorm (e i : Fin n → Bool) = 1 := by
  simp [hammingNorm, Pi.single_apply, Finset.filter_eq']

lemma hammingNorm_eq_one_iff {n : ℕ} {x : Fin n → Bool} :
    hammingNorm x = 1 ↔ ∃ i, x = e i := by
  constructor
  · -- the set of `true` coordinates of `x` is a singleton `{i}`
    intro hx
    rw [hammingNorm, Finset.card_eq_one] at hx
    obtain ⟨i, hi⟩ := hx
    refine ⟨i, funext fun j => ?_⟩
    -- so `x j = true` exactly when `j = i`
    have hj : x j = true ↔ j = i := by
      simpa [Bool.zero_eq_false] using Finset.ext_iff.mp hi j
    by_cases hji : j = i
    · simpa [hji] using hj
    · simpa [hji, Bool.zero_eq_false] using hj
  · -- conversely, a basis vector has weight one
    rintro ⟨i, rfl⟩
    exact hammingNorm_single i

/-!
Adjacency in the Hamming cube has a clean algebraic description: `x` and `y` are
adjacent iff they differ by a basis vector.
-/
lemma hypercubeHamming_adj_iff_exists {n : ℕ} {x y : Fin n → Bool} :
    (hypercubeHamming n).Adj x y ↔ ∃ i, y = x + e i := by
  rw [hypercubeHamming_adj, hammingDist_eq_hammingNorm,
    BooleanRing.neg_eq, hammingNorm_eq_one_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← hi, boolVec_add_add_cancel]
  · rintro ⟨i, rfl⟩
    exact ⟨i, boolVec_add_add_cancel _ _⟩

/-!
## Translations and Coordinate Permutations

Translation by a fixed vector `t` is an automorphism of the Hamming cube: it
preserves the Hamming distance since `(t + x) - (t + y) = x - y`. Under the
isomorphism `hypercubeIsoHamming`, this corresponds to the automorphism
`hypercube.translate` of `Q[n]`. There we had to define `xor` on `HypercubeVert n`
and prove its basic properties (such as `HypercubeVert.xor_xor`) by hand. On
`Fin n → Bool`, addition is pointwise `xor`, and the group structure (associativity,
`0`, negation) comes for free from Mathlib, as do the characteristic-two facts once
we have the `BooleanRing` instance above.
-/
/-- Translation by `t` (pointwise `xor`) as an automorphism of the Hamming cube. -/
def hypercubeHamming.translate {n : ℕ} (t : Fin n → Bool) :
    hypercubeHamming n ≃g hypercubeHamming n where
  toEquiv := Equiv.addLeft t
  map_rel_iff' := by
    intro x y
    grind [Equiv.coe_addLeft, hypercubeHamming_adj, hammingDist_eq_hammingNorm]

@[simp]
lemma hypercubeHamming.translate_apply {n : ℕ} (t x : Fin n → Bool) :
    hypercubeHamming.translate t x = t + x := rfl

/-!
Permuting the coordinates by `σ : Equiv.Perm (Fin n)` also preserves the Hamming
distance, and hence is an automorphism of the Hamming cube.
-/
lemma hammingDist_comp_perm {ι : Type*} [Fintype ι] {β : Type*}
    [DecidableEq β] (σ : Equiv.Perm ι) (x y : ι → β) :
    hammingDist (x ∘ σ) (y ∘ σ) = hammingDist x y := Finset.card_equiv σ (by simp)

/-- Permutation of coordinates by `σ` as an automorphism of the Hamming cube;
`x` is sent to `x ∘ σ.symm` so that the `i`-th coordinate of the image is the
`σ⁻¹ i`-th coordinate of `x`. -/
def hypercubeHamming.permute {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    hypercubeHamming n ≃g hypercubeHamming n where
  toEquiv := σ.arrowCongr (Equiv.refl Bool)
  map_rel_iff' {x y} := by
    rw [hypercubeHamming_adj, hypercubeHamming_adj,
      ← hammingDist_comp_perm σ.symm x y]
    rfl

@[simp]
lemma hypercubeHamming.permute_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → Bool) : hypercubeHamming.permute σ x = x ∘ σ.symm := rfl

/-!
In the automorphism group the inverse `f⁻¹` is by definition `f.symm`, so the
inverses of translations and coordinate permutations can be computed by `rfl`. Since
`-t = t`, the inverse of translation by `t` is translation by `t` itself, so
translations are involutions (characteristic two again).
-/
@[simp]
lemma hypercubeHamming.translate_inv_apply {n : ℕ} (t x : Fin n → Bool) :
    (hypercubeHamming.translate t)⁻¹ x = t + x := rfl

@[simp]
lemma hypercubeHamming.permute_inv_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → Bool) : (hypercubeHamming.permute σ)⁻¹ x = x ∘ σ := rfl

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
def hyperoctahedralAction (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (Multiplicative (Fin n → Bool)) where
  toFun σ := AddEquiv.toMultiplicative (AddEquiv.arrowCongr σ (AddEquiv.refl Bool))
  map_one' := by ext t; rfl
  map_mul' σ ρ := by ext t; rfl

/-- The hyperoctahedral group `(ℤ/2)ⁿ ⋊ Sₙ`, i.e. the wreath product `ℤ/2 ≀ Sₙ`,
realized as a semidirect product with `(ℤ/2)ⁿ` as `Fin n → Bool` under pointwise
`xor`. -/
abbrev _root_.HyperoctahedralGroup (n : ℕ) : Type :=
  Multiplicative (Fin n → Bool) ⋊[hyperoctahedralAction n] Equiv.Perm (Fin n)

/-!
Translations and coordinate permutations give monoid homomorphisms into the
automorphism group of the Hamming cube. (Recall that multiplication of automorphisms
is composition, `(f * g) x = f (g x)`.)
-/
/-- Translations as a monoid homomorphism into the automorphism group of the Hamming
cube. -/
@[simps]
def hypercubeHamming.translateHom (n : ℕ) :
    Multiplicative (Fin n → Bool) →* (hypercubeHamming n ≃g hypercubeHamming n) where
  toFun t := hypercubeHamming.translate t.toAdd
  map_one' := by ext x; simp
  map_mul' t s := by ext x; simp [add_assoc]

/-- Coordinate permutations as a monoid homomorphism into the automorphism group of
the Hamming cube. -/
@[simps]
def hypercubeHamming.permuteHom (n : ℕ) :
    Equiv.Perm (Fin n) →* (hypercubeHamming n ≃g hypercubeHamming n) where
  toFun := hypercubeHamming.permute
  map_one' := by ext x; rfl
  map_mul' σ ρ := by ext x; rfl

/-!
These two homomorphisms are compatible with the action `hyperoctahedralAction`:
conjugating a translation by a coordinate permutation is the translation by the
permuted vector. `SemidirectProduct.lift` combines them into a monoid homomorphism
from the hyperoctahedral group to the automorphism group.
-/
/-- The homomorphism from the hyperoctahedral group to the automorphisms of the
Hamming cube, sending `(t, σ)` to the automorphism `x ↦ t + x ∘ σ.symm`, i.e.
coordinate permutation by `σ` followed by translation by `t`. -/
def hyperoctahedralToAut (n : ℕ) :
    HyperoctahedralGroup n →* (hypercubeHamming n ≃g hypercubeHamming n) :=
  SemidirectProduct.lift (hypercubeHamming.translateHom n)
    (hypercubeHamming.permuteHom n) (by
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
map `i ↦ e i` is injective.
-/
lemma single_true_left_inj {n : ℕ} {i j : Fin n}
    (h : (e i : Fin n → Bool) = e j) : i = j := by
  simpa [Pi.single_apply] using congrFun h i

lemma hyperoctahedralToAut_injective (n : ℕ) :
    Function.Injective (hyperoctahedralToAut n) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨t, σ⟩ h
  have happ (x : Fin n → Bool) : t.toAdd + x ∘ σ.symm = x := DFunLike.congr_fun h x
  obtain rfl : t = 1 := by simpa using happ 0
  obtain rfl : σ = 1 := Equiv.ext fun j => Eq.symm <| by
    simpa [Pi.single_apply, Equiv.symm_apply_eq] using
      congrFun (happ (e j)) j
  rfl

/-!
## Rigidity

The key step in proving surjectivity is a rigidity lemma: an automorphism `g` fixing
`0` and all the basis vectors is the identity. The point is that the coordinates of a
vertex can be read off from distances, which automorphisms preserve. Since the graph
distance in the Hamming cube is the Hamming distance (`edist_hypercubeHamming`),
every automorphism preserves the Hamming distance, and (if it fixes `0`) the Hamming
weight (`hammingNorm`), i.e. the number of `true` coordinates, which is the Hamming
distance to `0`.
-/
lemma hammingDist_aut {n : ℕ} (g : hypercubeHamming n ≃g hypercubeHamming n)
    (x y : Fin n → Bool) : hammingDist (g x) (g y) = hammingDist x y := by
  have h := g.edist_eq x y
  rw [edist_hypercubeHamming, edist_hypercubeHamming] at h
  exact_mod_cast h

lemma hammingNorm_aut {n : ℕ} {g : hypercubeHamming n ≃g hypercubeHamming n}
    (hg : g 0 = 0) (x : Fin n → Bool) : hammingNorm (g x) = hammingNorm x := by
  rw [← hammingDist_zero_right, ← hg, hammingDist_aut, hammingDist_zero_right]

/-!
Adding a basis vector `e i` flips the `i`-th coordinate; if that
coordinate was `true` this decreases the weight by one.
-/
lemma hammingNorm_add_single {n : ℕ} {x : Fin n → Bool} {i : Fin n}
    (h : x i = true) : hammingNorm (x + e i) + 1 = hammingNorm x := by
  have hset : ({k | (x + e i : Fin n → Bool) k ≠ 0} : Finset _) =
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
    x k = true ↔ hammingDist x (e k) < hammingDist x 0 := by
  rw [hammingDist_zero_right, hammingDist_eq_hammingNorm, BooleanRing.neg_eq]
  cases hk : x k
  · have h : (x + e k : Fin n → Bool) k = true := by
      simp [hk, Bool.add_eq_xor]
    have := hammingNorm_add_single h
    grind [add_assoc, BooleanRing.add_self, add_zero]
  · have := hammingNorm_add_single hk
    grind

/-!
An automorphism `g` fixing `0` and every `eₖ` preserves the distances from any `x`
to `0` and to each `eₖ`, so by the previous lemma `g x` and `x` agree in every
coordinate `k`, i.e. `g x = x`.
-/
lemma aut_eq_id_of_fix_zero_and_singles {n : ℕ}
    {g : hypercubeHamming n ≃g hypercubeHamming n} (h0 : g 0 = 0)
    (h1 : ∀ i, g (e i) = e i) (x : Fin n → Bool) :
    g x = x := by
  funext k
  -- `g` preserves Hamming distance and fixes `0` and `e k`
  have h₀ : hammingDist (g x) 0 = hammingDist x 0 := by
    simpa [h0] using hammingDist_aut g x 0
  have hₖ : hammingDist (g x) (e k) = hammingDist x (e k) := by
    simpa [h1 k] using hammingDist_aut g x (e k)
  rw [Bool.eq_iff_iff, apply_eq_true_iff_hammingDist_lt,
    apply_eq_true_iff_hammingDist_lt, h₀, hₖ]

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
  let g := (hypercubeHamming.translateHom n (Multiplicative.ofAdd (f 0)))⁻¹ * f
  have hg0 : g 0 = 0 := by
    simp [g]
  have hsingle : ∀ i : Fin n, ∃ j, g (e i) = e j := by
    intro i
    exact hammingNorm_eq_one_iff.mp (by rw [hammingNorm_aut hg0, hammingNorm_single])
  choose p hp using hsingle
  have hpinj : Function.Injective p := by
    intro i j hij
    have h' : g (e i) = g (e j) := by
      rw [hp i, hp j, hij]
    exact single_true_left_inj (g.injective h')
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective p (Finite.injective_iff_bijective.mp hpinj)
  have hh0 : ((hypercubeHamming.permuteHom n σ)⁻¹ * g) 0 = 0 := by
    simp [hg0]
  have hhsingle : ∀ i,
      ((hypercubeHamming.permuteHom n σ)⁻¹ * g) (e i) = e i := by
    intro i
    ext k; simp [hp i, σ, Pi.single_apply, hpinj.eq_iff]
  have hone : (hypercubeHamming.permuteHom n σ)⁻¹ * g = 1 := by
    ext x : 1
    simpa using aut_eq_id_of_fix_zero_and_singles hh0 hhsingle x
  -- so `g` is the permutation by `σ`
  have hg : g = hypercubeHamming.permuteHom n σ := (inv_mul_eq_one.mp hone).symm
  -- and `g` is `f` followed by undoing the translation by `f 0`, so `f` is the
  -- permutation by `σ` followed by that translation
  have hf : f = hypercubeHamming.translateHom n (Multiplicative.ofAdd (f 0)) *
      hypercubeHamming.permuteHom n σ := by
    rw [← hg, mul_inv_cancel_left]
  exact ⟨⟨Multiplicative.ofAdd (f 0), σ⟩, hf.symm⟩

/-!
## Characterization

Converting the bijective homomorphism into a group isomorphism, and transporting it
along `hypercubeIsoHamming` (using `Iso.autCongr`), we obtain the promised
characterization: the automorphism group of the `n`-dimensional hypercube is the
hyperoctahedral group `ℤ/2 ≀ Sₙ`.
-/
/-- The automorphism group of the Hamming cube is the hyperoctahedral group
`ℤ/2 ≀ Sₙ`. -/
noncomputable def hyperoctahedralMulEquivAutHamming (n : ℕ) :
    HyperoctahedralGroup n ≃* (hypercubeHamming n ≃g hypercubeHamming n) :=
  MulEquiv.ofBijective (hyperoctahedralToAut n)
    ⟨hyperoctahedralToAut_injective n, hyperoctahedralToAut_surjective n⟩

/-- The automorphism group of the hypercube `Q[n]` is the hyperoctahedral group
`ℤ/2 ≀ Sₙ`. -/
noncomputable def autHypercubeMulEquivHyperoctahedral (n : ℕ) :
    (Q[n] ≃g Q[n]) ≃* HyperoctahedralGroup n :=
  (hypercubeIsoHamming n).autCongr.trans
    (hyperoctahedralMulEquivAutHamming n).symm

/-!
In particular the hypercube `Q[n]` has exactly `2 ^ n * n!` automorphisms.
-/
lemma card_aut_hypercube (n : ℕ) :
    Nat.card (Q[n] ≃g Q[n]) = 2 ^ n * n.factorial := by
  rw [Nat.card_congr (autHypercubeMulEquivHyperoctahedral n).toEquiv,
    Nat.card_congr (SemidirectProduct.equivProd), Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

/-!
# Counting Copies *

In this section we count the *labelled* and *unlabelled* copies of a graph that we
met in [Copies](https://jt496.github.io/GraphTheoryInLean/Maps/#section-copies). We
first show that the unlabelled copies of a complete graph `K[s]` are just the
`s`-cliques. Automorphisms then explain the difference between labelled and
unlabelled copies: we derive the basic fact that (for finite graphs) the number of
labelled copies of a graph `A` in a graph `B` is equal to the number of unlabelled
copies of `A` in `B`, multiplied by the number of automorphisms of `A`. (Mathlib has
the inequality `copyCount_le_labelledCopyCount`, but not this identity.) We then
apply it to cycles.

Recall that `Copy A B` is the type of injective graph homomorphisms from `A` to `B`,
and that the following maps
([Which Notion of Subgraph?](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-which-notion-of-subgraph))
pass between copies of `A` in `B` and subgraphs of `B` isomorphic to `A`.
-/
section copies
open Subgraph
variable {V W : Type*} {G : SimpleGraph V}

#check Copy.toSubgraph     -- (f : Copy A B) : B.Subgraph
#check Copy.isoToSubgraph  -- (f : Copy A B) : A ≃g f.toSubgraph.coe
#check Subgraph.coeCopy    -- (C : B.Subgraph) : Copy C.coe B

/-!
## Copies of Complete Graphs

Mathlib's `copyCount` counts the unlabelled copies of `H` in `G` as the subgraphs of
`G` that are isomorphic to `H`.
-/
#source copyCount -- classical exact #{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}

/-!
It is noncomputable, so we cannot simply evaluate it. But the unlabelled copies of
`K[s]` are easy to count: they are the `s`-cliques. Any two vertices in the image of
a copy of a complete graph are adjacent, so the subgraph picked out by the copy is
the subgraph induced on its image.
-/
lemma Copy.toSubgraph_top (f : Copy (⊤ : SimpleGraph W) G) :
    f.toSubgraph = (⊤ : G.Subgraph).induce (Set.range f) := by
  ext x y
  · simp
  · simp only [Subgraph.map_adj, Subgraph.top_adj, SimpleGraph.top_adj,
      Relation.map_apply, Subgraph.induce_adj, Set.mem_range]
    constructor
    · rintro ⟨i, j, hij, rfl, rfl⟩
      exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, f.toHom.map_adj hij⟩
    · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩, h⟩
      exact ⟨i, j, fun hij => h.ne (congrArg f hij), rfl, rfl⟩

/-!
So a copy of the complete graph on `W` is determined by its vertex set, which is a
clique with `Fintype.card W` vertices (`isNClique_map_copy_top`). Conversely,
matching the vertices of such a clique `t` with `W` (`Fintype.equivOfCardEq`) gives
a copy with vertex set `t`. To compare with `copyCount`, we use
`copyCount_eq_card_image_copyToSubgraph`, which counts the subgraphs `f.toSubgraph`
instead.
-/
#check copyCount_eq_card_image_copyToSubgraph
/-!
In a finite graph counting the number of copies of a finite complete graph on `W` is
the same as counting the cliques of `G` with `Fintype.card W` vertices.
-/
open Finset in
theorem copyCount_top [Fintype W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G.copyCount (⊤ : SimpleGraph W) = #(G.cliqueFinset (Fintype.card W)) := by
  classical
  rw [copyCount_eq_card_image_copyToSubgraph]
  -- send a copy to its vertex set, and a clique to the subgraph it induces
  refine card_nbij' (fun G' => G'.verts.toFinset)
    (fun t => (⊤ : G.Subgraph).induce t) (fun G' hG' => ?_) (fun t ht => ?_)
    (fun G' hG' => ?_) (fun t _ => by simp)
  · -- the vertex set of a copy of `⊤` is a clique of the right size
    obtain ⟨f, -, rfl⟩ := mem_image.1 hG'
    simpa [Set.toFinset_range, map_eq_image, Copy.toEmbedding] using
      isNClique_map_copy_top f
  · -- the subgraph induced on a clique `t` is a copy of `⊤`
    replace ht := mem_cliqueFinset_iff.1 (mem_coe.1 ht)
    let φ : W ≃ t := Fintype.equivOfCardEq (by rw [Fintype.card_coe, ht.2])
    -- distinct vertices of the clique `t` are adjacent
    have hadj : ∀ i j, i ≠ j → G.Adj (φ i) (φ j) := by
      intro i j hij
      exact ht.1 (φ i).2 (φ j).2 (by simpa using hij)
    let f : Copy ⊤ G := ⟨⟨fun i => φ i, fun hij => hadj _ _ hij.ne⟩,
      Subtype.val_injective.comp φ.injective⟩
    -- the vertex set of `f` is `t`, since `φ` is a bijection onto `t`
    have hf : Set.range f = t := by
      ext x
      simp [f, φ.exists_congr_left]
    exact mem_coe.2 (mem_image.2 ⟨f, mem_univ _, by rw [Copy.toSubgraph_top, hf]⟩)
  · -- a copy of `⊤` is the subgraph induced on its vertex set
    obtain ⟨f, -, rfl⟩ := mem_image.1 hG'
    rw [Copy.toSubgraph_top]
    simp

/-!
In particular `G.copyCount K[s]` is the number of `s`-cliques of `G`. Since cliques
are computable, we can now compute `copyCount` for complete graphs. For example,
`K[5]` contains `10` triangles.
-/
example : K[5].copyCount K[3] = 10 := by
  rw [copyCount_top]
  decide

/-!
## Labelled and Unlabelled Copies

The identity relating labelled and unlabelled copies follows from a general
equivalence: `A.Copy B` is equivalent to the product of the subtype of subgraphs of
`B` that are isomorphic to `A` with the automorphisms of `A`.

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
noncomputable def chosenSubgraphIso {A : SimpleGraph V} {B : SimpleGraph W}
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
noncomputable def subgraphIsoEquivAut {A : SimpleGraph V} {B : SimpleGraph W}
    (C : {C : B.Subgraph | Nonempty (A ≃g C.coe)}) :
    (A ≃g (C : B.Subgraph).coe) ≃ (A ≃g A) where
  toFun f := f.trans (chosenSubgraphIso C).symm
  invFun σ := σ.trans (chosenSubgraphIso C)
  left_inv f := by ext b; simp
  right_inv σ := by ext b; simp

/-!
Next, `copyEquivSigmaIso` shows that a copy of `A` in `B` is the same as a subgraph
`C` together with a labelling `A ≃g C.coe`, packaged as a `Sigma` type. No
reference labelling is needed for this step, since the copy itself provides one.

Rather than prove `right_inv` directly, we show that `invFun` is injective and deduce
`right_inv` using `Function.LeftInverse.rightInverse_of_injective`. This avoids
comparing labellings of two subgraphs that are equal but not definitionally equal
([Definitional and Propositional Equalities](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/#section-definitional-and-propositional-equalities)),
and so have different types. (This is essentially the difficulty we met for walks in
[Copy](https://jt496.github.io/GraphTheoryInLean/Walks/#section-copy): the type
`G.Walk u v` records the endpoints of a walk, just as the type of a labelling records
the subgraph it labels.)
-/
#check Function.LeftInverse.rightInverse_of_injective

/-- `A.Copy B` is equivalent to the Sigma type of subgraphs of `B` that are
isomorphic to `A` with their isomorphisms. -/
@[simps]
noncomputable def copyEquivSigmaIso (A : SimpleGraph V) (B : SimpleGraph W) :
    A.Copy B ≃
      Σ C : {C : B.Subgraph | Nonempty (A ≃g C.coe)}, A ≃g (C : B.Subgraph).coe where
  toFun c := ⟨⟨c.toSubgraph, ⟨c.isoToSubgraph⟩⟩, c.isoToSubgraph⟩
  invFun y := (y.1 : B.Subgraph).coeCopy.comp y.2.toCopy
  -- `left_inv` is filled in automatically (`by ext; rfl`)
  -- although we still have to prove it again below.
  right_inv := by
    refine Function.LeftInverse.rightInverse_of_injective (fun c => by ext; rfl) ?_
    rintro ⟨⟨C, hC⟩, f⟩ ⟨⟨D, hD⟩, g⟩ h
    -- The images agree, and `C` and `D` are local variables, so we
    -- can substitute `C = D`.
    obtain rfl : C = D := by
      simpa [Copy.toSubgraph, Copy.comp, coeCopy, map_comp, map_iso_top,
        map_hom_top] using congrArg Copy.toSubgraph h
    -- Now `f` and `g` are labellings of the same subgraph, so `ext` applies.
    obtain rfl : f = g := by ext a; exact DFunLike.congr_fun h a
    rfl

/-!
Finally, `copyEquivSubgraphIsoProdAut` puts these pieces together: applying
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
(`B.copyCount A`) multiplied by the number of automorphisms of `A`. (Note the
argument order: `Copy A B` lists the copied graph first, like `A →g B`, while
`B.labelledCopyCount A` and `B.copyCount A` are invariants of the host graph `B`,
which comes first.)
-/
#source labelledCopyCount -- classical exact Fintype.card (Copy H G)
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
    (g : A ≃g B) [Finite V] : (Copy A B) ≃ (A ≃g B) where
  toFun f :=
    { Equiv.ofBijective f.toHom ⟨f.injective,
        (Finite.injective_iff_surjective_of_equiv g.toEquiv).1 f.injective⟩ with
      map_rel_iff' {a b} := by
        refine ⟨fun h => ?_, f.toHom.map_rel⟩
        -- `f.mapEdgeSet` is an injection between finite sets of the same size,
        -- hence a surjection, so the edge `s(f a, f b)` of `B` is the image of an
        -- edge of `A`.
        obtain ⟨⟨e', he'⟩, heq⟩ :=
          (Finite.injective_iff_surjective_of_equiv g.mapEdgeSet).1
            f.mapEdgeSet.injective ⟨s(f a, f b), h⟩
        obtain rfl : e' = s(a, b) :=
          Sym2.map.injective f.injective (congrArg Subtype.val heq)
        exact he' }
  invFun φ := φ.toCopy

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

/-!
Isomorphisms `A ≃g A'` and `B ≃g B'` identify the copies of `A` in `B` with the
copies of `A'` in `B'`, by composing on both sides. So isomorphic graphs have the
same copy counts. This lets us count copies in whichever model of a graph is most
convenient.
-/
/-- Isomorphisms `A ≃g A'` and `B ≃g B'` identify the copies of `A` in `B` with the
copies of `A'` in `B'`. -/
def Iso.copyCongr {V' W' : Type*} {A : SimpleGraph V} {A' : SimpleGraph V'}
    {B : SimpleGraph W} {B' : SimpleGraph W'} (eA : A ≃g A') (eB : B ≃g B') :
    Copy A B ≃ Copy A' B' where
  toFun f := (eB.toCopy.comp f).comp eA.symm.toCopy
  invFun f := (eB.symm.toCopy.comp f).comp eA.toCopy
  left_inv f := by ext; simp
  right_inv f := by ext; simp

lemma Iso.labelledCopyCount_eq {V' W' : Type*} [Fintype V] [Fintype V'] [Fintype W]
    [Fintype W'] {A : SimpleGraph V} {A' : SimpleGraph V'} {B : SimpleGraph W}
    {B' : SimpleGraph W'} (eA : A ≃g A') (eB : B ≃g B') :
    B.labelledCopyCount A = B'.labelledCopyCount A' := by
  simp only [labelledCopyCount, Fintype.card_eq_nat_card]
  exact Nat.card_congr (eA.copyCongr eB)

/-!
For unlabelled copies only the host graph needs to be finite, so the next lemma
assumes nothing about `A` and `A'`. Mathlib's `labelledCopyCount` also asks for the
copied graph to be finite, because it is defined as `Fintype.card (Copy A B)`, and
the `Fintype` instance on `Copy A B` is built from the one on homomorphisms
`A →g B`. This costs nothing: if `B` is finite and `A` is infinite then there are
no copies at all.
-/
lemma Iso.copyCount_eq_left {V' : Type*} {A : SimpleGraph V} {A' : SimpleGraph V'}
    [Fintype W] (g : A ≃g A') (B : SimpleGraph W) :
    B.copyCount A = B.copyCount A' := by
  classical
  unfold copyCount
  congr 1
  ext C
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨f⟩ => ⟨g.symm.trans f⟩, fun ⟨f⟩ => ⟨g.trans f⟩⟩

/-!
## Counting Copies of Cycles

By `labelledCopyCount_eq_copyCount_mul_labelledCopyCount`, the number of labelled
copies of a finite graph `A` in a finite graph `B` is the number of unlabelled copies
times the number of automorphisms of `A`. Since the automorphism group of `C[n + 3]`
is the dihedral group of order `2 * (n + 3)` (`autCycleGraphMulEquivDihedral`), this
expresses the number of labelled copies of a cycle in a graph in terms of the number
of unlabelled copies.
-/
theorem labelledCopyCount_cycleGraph [Fintype V] (G : SimpleGraph V) (n : ℕ) :
    G.labelledCopyCount C[n + 3] = G.copyCount C[n + 3] * (2 * (n + 3)) := by
  -- `Fintype.card_congr` won't work here because `labelledCopyCount` unfolds to
  -- `Fintype.card` with classical decidability instances, which are not defeq to the
  -- ones `Fintype.card_congr` synthesizes. We avoid this by converting both sides to
  -- `Nat.card` with `Fintype.card_eq_nat_card`, which works for any instance.
  rw [labelledCopyCount_eq_copyCount_mul_labelledCopyCount, labelledCopyCount,
    ← DihedralGroup.card, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    Nat.card_congr ((copyEquivAut C[n + 3]).trans
      (autCycleGraphMulEquivDihedral n).toEquiv)]

end copies

/-!
# Subcubes of the Hypercube *

As a second application of the Hamming cube model we determine all copies of a
smaller cube `Q[k]` inside `Q[n]`. The main result is another rigidity theorem: every
copy of `Q[k]` in `Q[n]` is *canonical*. That is, for some choice of `k` distinct
coordinates of `Q[n]` and a vertex `b` of `Q[n]`, it sends each vertex `x` of `Q[k]`
to `b + y`, where `y` is obtained by placing the coordinates of `x` in the chosen
positions, with `false` elsewhere. (In particular `b` is the image of `0`.) So its
image is a *subcube*, a translate of a coordinate subspace. We prove this by
induction on the Hamming weight, using a "parallelogram lemma" about the `4`-cycles
of the Hamming cube.

A canonical copy is determined by `b` and the chosen coordinates (in order), so
counting these gives

* `Q[n].labelledCopyCount Q[k] = 2 ^ n * n.descFactorial k`, and
* `Q[n].copyCount Q[k] = n.choose k * 2 ^ (n - k)` (when `k ≤ n`).

The second is the familiar answer "choose the `k` free coordinates and fix the
others"; the first refines it by the `2 ^ k * k!` automorphisms of `Q[k]`. Finally,
canonical copies preserve distances, so every copy of `Q[k]` in `Q[n]` is induced and
the labelled count is also the number of embeddings `Q[k] ↪g Q[n]`. As for the
automorphism group, we work with the Hamming cube and transport the results to `Q[n]`
at the end.

## The Parallelogram Lemma

If `x u y v` form a `4`-cycle in the Hamming cube (i.e. `u ≠ v` are common
neighbours of `x ≠ y`), then `u + v = x + y`; equivalently the cycle is a
two-dimensional "face" `x, x + eᵢ, x + eᵢ + eⱼ, x + eⱼ`.
-/
/-- The parallelogram lemma: if `u ≠ v` are common neighbours of `x ≠ y` in the
Hamming cube then `u + v = x + y`. -/
lemma hypercubeHamming_parallelogram {n : ℕ} {x y u v : Fin n → Bool}
    (hxu : (hypercubeHamming n).Adj x u) (huy : (hypercubeHamming n).Adj u y)
    (hxv : (hypercubeHamming n).Adj x v) (hvy : (hypercubeHamming n).Adj v y)
    (hxy : x ≠ y) (huv : u ≠ v) : u + v = x + y := by
  obtain ⟨i, rfl⟩ := hypercubeHamming_adj_iff_exists.1 hxu
  obtain ⟨j, rfl⟩ := hypercubeHamming_adj_iff_exists.1 huy
  obtain ⟨k, rfl⟩ := hypercubeHamming_adj_iff_exists.1 hxv
  obtain ⟨l, hq⟩ := hypercubeHamming_adj_iff_exists.1 hvy
  -- cancel the common `x`: `eᵢ + eⱼ = eₖ + eₗ`
  rw [add_assoc, add_assoc] at hq
  have hkey : e i + e j =
      (e k + e l : Fin n → Bool) := add_left_cancel hq
  -- Mathlib classifies the solutions of `eᵢ + eⱼ = eₖ + eₗ`: either `i = k` and
  -- `j = l`, or `i = l` and `j = k`, or `i = j` and `k = l` (as `true + true = 0`)
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

[Figure: Left: $Q_2$. Right: the canonical copy `subcubeCopy b d` of $Q_2$ in $Q_4$, with base point $b = \mathtt{FTFF}$ and free directions `d 0 = 0` and `d 1 = 3`](https://jt496.github.io/GraphTheoryInLean/figures/subcube.svg)
-/
/-- Extend a `k`-vector to an `n`-vector along an embedding `d : Fin k ↪ Fin n`,
placing `x i` in position `d i` and `false` elsewhere. -/
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
noncomputable def subcubeCopy {n k : ℕ} (b : Fin n → Bool) (d : Fin k ↪ Fin n) :
    Copy (hypercubeHamming k) (hypercubeHamming n) where
  toHom := (hypercubeHamming.translate b).toHom.comp (extendHom d)
  injective' := fun _ _ h => extendEmb_injective d (add_left_cancel h)

@[simp]
lemma subcubeCopy_apply {n k : ℕ} (b : Fin n → Bool) (d : Fin k ↪ Fin n)
    (x : Fin k → Bool) : subcubeCopy b d x = b + extendEmb d x := rfl

/-!
The base point and direction embedding are recoverable from the copy:
`subcubeCopy` is injective in `(b, d)`.
-/
lemma subcubeCopy_injective {n k : ℕ} :
    Function.Injective fun bd : (Fin n → Bool) × (Fin k ↪ Fin n) =>
      subcubeCopy bd.1 bd.2 := by
  rintro ⟨b, d⟩ ⟨b', d'⟩ h
  have happ : ∀ x, b + extendEmb d x = b' + extendEmb d' x := by
    intro x
    simpa using DFunLike.congr_fun h x
  have hb : b = b' := by simpa using happ 0
  subst hb
  have hd : d = d' := by
    apply DFunLike.ext
    intro i
    have hx := add_left_cancel (happ (e i))
    rw [extendEmb_single, extendEmb_single] at hx
    exact single_true_left_inj hx
  rw [hd]

/-!
## Rigidity: Every Copy is Canonical

Every copy of `Q[k]` in `Q[n]` is of the form `subcubeCopy b d`. Note that a copy is
an *injective homomorphism*: it preserves adjacency in the forward direction only,
so, unlike for automorphisms, no distance or weight preservation is available. We use
the parallelogram lemma instead. The proof has two steps: we first read off the
direction embedding `d` from the images of the basis vectors, and then show that
`f x = f 0 + extendEmb d x` by strong induction on the Hamming weight of `x`,
computing `f y` for `y` of weight `m + 2` from the images of the three vertices
`y + eᵢ`, `y + eⱼ`, `y + eᵢ + eⱼ` below it in the `4`-cycle through `y`.

First we prove a small helper lemma: a vector of Hamming weight at least two has two
distinct `true` coordinates.
-/
lemma exists_ne_true_true_of_one_lt_hammingNorm {n : ℕ} {y : Fin n → Bool}
    (hy : 1 < hammingNorm y) : ∃ i j, i ≠ j ∧ y i = true ∧ y j = true := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hy
  use i, j, hij
  simp_all [Bool.zero_eq_false]

/-!
A copy maps each square `y, y + eᵢ, y + eᵢ + eⱼ, y + eⱼ` of `Q[k]` to a `4`-cycle
in `Q[n]`, so by the parallelogram lemma the image of any corner is the sum of the
images of the other three.
-/
lemma copy_apply_eq_add_add {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) (y : Fin k → Bool)
    {i j : Fin k} (hij : i ≠ j) :
    f y = f (y + e i + e j) + f (y + e i) + f (y + e j) := by
  have hadj : ∀ (x : Fin k → Bool) (a : Fin k),
      (hypercubeHamming n).Adj (f x) (f (x + e a)) :=
    fun x a => f.toHom.map_adj (hypercubeHamming_adj_iff_exists.2 ⟨a, rfl⟩)
  -- three sides of the square `y, y + e i, y + e i + e j, y + e j` are mapped to
  -- edges by `hadj`; for the fourth we reorder the sum
  have h₄ : (hypercubeHamming n).Adj (f (y + e j)) (f (y + e i + e j)) := by
    rw [add_right_comm]
    exact hadj _ i
  -- opposite corners of the square are distinct, and so are their images
  have hne₁ : f y ≠ f (y + e i + e j) := fun h => by
    simpa [Pi.single_apply, hij] using congrFun (f.injective h) i
  have hne₂ : f (y + e i) ≠ f (y + e j) := fun h =>
    hij (single_true_left_inj (add_left_cancel (f.injective h)))
  have hpar : f (y + e i) + f (y + e j) = f y + f (y + e i + e j) :=
    hypercubeHamming_parallelogram (hadj y i) (hadj _ j) (hadj y j) h₄ hne₁ hne₂
  -- substitute `hpar` and cancel the two copies of `f (y + e i + e j)`
  rw [add_assoc, hpar, add_comm (f y), boolVec_add_add_cancel]

/-!
For the first step, each basis vector `eᵢ` is a neighbour of `0`, so its image is a
neighbour of `f 0` and differs from it in a single coordinate, which we call `d i`.
Two basis vectors with the same direction would have the same image, so `d` is
injective because `f` is.
-/
lemma exists_apply_single_eq_add_single {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) :
    ∃ d : Fin k ↪ Fin n, ∀ i, f (e i) = f 0 + e (d i) := by
  -- each basis vector is mapped to a neighbour of `f 0`, defining the
  -- direction map `d`
  have hD : ∀ i : Fin k, ∃ p : Fin n,
      f (e i) = f 0 + e p := by
    intro i
    have hadj : (hypercubeHamming n).Adj (f 0) (f (e i)) :=
      f.toHom.map_adj (hypercubeHamming_adj_iff_exists.2 ⟨i, (zero_add _).symm⟩)
    exact hypercubeHamming_adj_iff_exists.1 hadj
  choose d hd using hD
  have hdinj : Function.Injective d := by
    intro i j hdij
    have h : f (e i) = f (e j) := by
      rw [hd i, hd j, hdij]
    exact single_true_left_inj (f.injective h)
  exact ⟨⟨d, hdinj⟩, hd⟩

/-!
For the second step we show that the images of `0` and of the basis vectors
determine the whole copy. Here the direction embedding `d` is an input rather than
an output, so the statement applies to any `d` satisfying `hd`.
-/
lemma copy_apply_eq_add_extendEmb_of_single {n k : ℕ}
    {f : Copy (hypercubeHamming k) (hypercubeHamming n)} {d : Fin k ↪ Fin n}
    (hd : ∀ i, f (e i) = f 0 + e (d i))
    (x : Fin k → Bool) : f x = f 0 + extendEmb d x := by
  suffices H : ∀ (m : ℕ) (y : Fin k → Bool), hammingNorm y = m →
      f y = f 0 + extendEmb d y from H _ x rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · -- weight zero: `y = 0`
      intro y hy
      rw [hammingNorm_eq_zero] at hy
      simp [hy]
    rcases m with _ | m
    · -- weight one: `y` is a basis vector, handled by `hd`
      intro y hy
      obtain ⟨i, rfl⟩ := hammingNorm_eq_one_iff.mp hy
      rw [hd i, extendEmb_single]
    -- weight `m + 2`: `y` has two distinct `true` coordinates `i ≠ j`
    intro y hy
    obtain ⟨i, j, hij, hyi, hyj⟩ :=
      exists_ne_true_true_of_one_lt_hammingNorm (by grind : 1 < hammingNorm y)
    -- the three vertices below `y` in the four-cycle have smaller weight
    have hn₁ : hammingNorm (y + e i) = m + 1 := by
      have := hammingNorm_add_single hyi; grind
    have hn₂ : hammingNorm (y + e j) = m + 1 := by
      have := hammingNorm_add_single hyj; grind
    have h2j : (y + e i : Fin k → Bool) j = true := by
      simp [hij.symm, hyj]
    have hn₃ : hammingNorm (y + e i + e j) = m := by
      have := hammingNorm_add_single h2j; grind
    have hf₁ := ih (m + 1) (by grind) _ hn₁
    have hf₂ := ih (m + 1) (by grind) _ hn₂
    have hf₃ := ih m (by grind) _ hn₃
    -- `f y` is determined by the three smaller corners of the square
    rw [copy_apply_eq_add_add f y hij, hf₁, hf₂, hf₃]
    simp [extendEmb_add, add_assoc, add_comm, add_left_comm]

/-!
Combining the two steps:
-/
lemma exists_apply_eq_add_extendEmb {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) :
    ∃ d : Fin k ↪ Fin n, ∀ x, f x = f 0 + extendEmb d x := by
  obtain ⟨d, hd⟩ := exists_apply_single_eq_add_single f
  exact ⟨d, copy_apply_eq_add_extendEmb_of_single hd⟩

/-!
Every copy of `Q[k]` in `Q[n]` *is* a canonical subcube copy.
-/
lemma exists_eq_subcubeCopy {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) :
    ∃ (b : Fin n → Bool) (d : Fin k ↪ Fin n), f = subcubeCopy b d := by
  obtain ⟨d, hd⟩ := exists_apply_eq_add_extendEmb f
  exact ⟨f 0, d, Copy.ext fun x => by simpa using hd x⟩

/-!
## The Labelled Count

Rigidity and `subcubeCopy_injective` combine into a classification of the copies
of `Q[k]` in `Q[n]`: they correspond exactly to pairs of a base point and a
direction embedding. The labelled copy count follows by counting the pairs.

Sanity checks: for `k = n` the count is `2 ^ n * n!`, the order of the
automorphism group by `card_aut_hypercube` (every copy of `Q[n]` in itself is an
automorphism); for `k = 0` it is `2 ^ n`, the number of vertices; for `k = 1` it
is `2 ^ n * n`, the number of edges counted with direction.
-/
/-- Copies of `Q[k]` in `Q[n]` (in the Hamming model) are equivalent to pairs
`(b, d)` of a base point and a direction embedding. The inverse map sends `(b, d)` to
`subcubeCopy b d`; it is injective by `subcubeCopy_injective` and surjective by the
rigidity theorem `exists_eq_subcubeCopy`. -/
noncomputable def copyEquivProd (n k : ℕ) :
    Copy (hypercubeHamming k) (hypercubeHamming n) ≃
      (Fin n → Bool) × (Fin k ↪ Fin n) :=
  (Equiv.ofBijective (fun bd => subcubeCopy bd.1 bd.2)
    ⟨subcubeCopy_injective, fun f => by
      obtain ⟨b, d, hf⟩ := exists_eq_subcubeCopy f
      exact ⟨(b, d), hf.symm⟩⟩).symm

lemma labelledCopyCount_hypercubeHamming (n k : ℕ) :
    (hypercubeHamming n).labelledCopyCount (hypercubeHamming k) =
      2 ^ n * n.descFactorial k := by
  rw [labelledCopyCount, Fintype.card_eq_nat_card,
    Nat.card_congr (copyEquivProd n k), Nat.card_prod,
    ← Fintype.card_eq_nat_card, ← Fintype.card_eq_nat_card,
    Fintype.card_embedding_eq, Fintype.card_fun]
  simp

/-!
To transport this to `Q[n]` we use `Iso.labelledCopyCount_eq`: isomorphic graphs have
the same copy counts.
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
  -- `positivity` proves goals `0 < e` or `0 ≤ e` from the form of `e`
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
    BooleanRing.neg_eq, BooleanRing.neg_eq, ← extendEmb_add, hammingNorm_extendEmb]

lemma edist_subcubeCopy {n k : ℕ} (b : Fin n → Bool) (d : Fin k ↪ Fin n)
    (x y : Fin k → Bool) :
    (hypercubeHamming n).edist (subcubeCopy b d x) (subcubeCopy b d y) =
      (hypercubeHamming k).edist x y := by
  have h := hammingDist_aut (hypercubeHamming.translate b) (extendEmb d x)
    (extendEmb d y)
  simp only [hypercubeHamming.translate_apply] at h
  rw [edist_hypercubeHamming, edist_hypercubeHamming, subcubeCopy_apply,
    subcubeCopy_apply, h, hammingDist_extendEmb]

/-!
Since adjacency is distance one, a canonical copy reflects adjacency as well as
preserving it, and by rigidity every copy is canonical. So every copy of `Q[k]` in
`Q[n]` is *induced*. We prove this first in the Hamming model and then transport it
to the hypercube along the isomorphisms `hypercubeIsoHamming`, using `Iso.copyCongr`.
-/
lemma copy_hypercubeHamming_adj_iff {n k : ℕ}
    (f : Copy (hypercubeHamming k) (hypercubeHamming n)) {x y : Fin k → Bool} :
    (hypercubeHamming n).Adj (f x) (f y) ↔ (hypercubeHamming k).Adj x y := by
  obtain ⟨b, d, rfl⟩ := exists_eq_subcubeCopy f
  rw [← edist_eq_one_iff_adj, ← edist_eq_one_iff_adj, edist_subcubeCopy]

/-- Every copy of `Q[k]` in `Q[n]` is induced. -/
lemma copy_hypercube_adj_iff {n k : ℕ} (f : Copy Q[k] Q[n])
    {x y : HypercubeVert k} : Q[n].Adj (f x) (f y) ↔ Q[k].Adj x y := by
  have h := copy_hypercubeHamming_adj_iff
    ((hypercubeIsoHamming k).copyCongr (hypercubeIsoHamming n) f)
    (x := hypercubeIsoHamming k x) (y := hypercubeIsoHamming k y)
  simpa [Iso.copyCongr, Iso.map_adj_iff, -hypercubeHamming_adj] using h

/-!
A copy that reflects adjacency is a graph embedding `A ↪g B` (`Embedding`), and
Mathlib writes `A ⊴ B` (`IsIndContained`) for the existence of one. So if every copy
of `A` in `B` reflects adjacency, then the copies of `A` in `B` and the embeddings
`A ↪g B` are the same thing. (Mathlib has no induced analogue of
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

/-!
So the labelled count of copies of `Q[k]` in `Q[n]` also counts the embeddings.
-/
theorem card_embedding_hypercube (n k : ℕ) :
    Nat.card (Q[k] ↪g Q[n]) = 2 ^ n * n.descFactorial k := by
  have h := labelledCopyCount_hypercube n k
  rwa [labelledCopyCount, Fintype.card_eq_nat_card, Nat.card_congr
    (copyEquivEmbedding fun f _ _ => (copy_hypercube_adj_iff f).1)] at h

end SimpleGraph
