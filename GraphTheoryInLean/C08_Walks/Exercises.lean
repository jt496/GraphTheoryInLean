import GraphTheoryInLean.C08_Walks.C08_Walks
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
open HypercubeVert Walk
/-!
# Exercises

1. Prove by induction on `p` that reversing a walk does not change its length.
Hint: `reverse_cons` and `length_append`.
-/
example {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by
  sorry

/-!
2. Prove by induction on `p` that the support of `p.append q` is the support of `p`
followed by the tail of the support of `q` (the tail drops the shared vertex `v`).
Hint: in the `nil` case, `cons_tail_support`.
-/
example {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).support = p.support ++ q.support.tail := by
  sorry

/-!
3. Show that the `nil` walk is a trail.
-/
example (u : V) : (nil : G.Walk u u).IsTrail := by
  sorry

/-!
4. Show that if `p : G.Walk u v` has length `0` then `u = v`. Hint: use `cases p`.
-/
example {u v : V} (p : G.Walk u v) (hl : p.length = 0) : u = v := by
  sorry

/-!
5. Show that splitting a walk at a vertex on its support preserves the total length.
Hint: `Walk.take_spec`.
-/
example [DecidableEq V] {u v w : V} (p : G.Walk u v) (h : w ∈ p.support) :
    (p.takeUntil w h).length + (p.dropUntil w h).length = p.length := by
  sorry

/-!
6. The walk `pentagonWalk` travels once around the cycle `C[5]`. Show that it is an
Eulerian circuit. Hint: `decide` proves that it is Eulerian, using the `Decidable`
instance from the chapter. For `IsCircuit`, rewrite with `isCircuit_def` and
`isTrail_def` first.
-/
/-- The closed walk `0, 1, 2, 3, 4, 0` in the cycle `C[5]`. -/
private def Walk.pentagonWalk : C[5].Walk 0 0 :=
  cons (show C[5].Adj 0 1 by decide) <| cons (show C[5].Adj 1 2 by decide) <|
    cons (show C[5].Adj 2 3 by decide) <| cons (show C[5].Adj 3 4 by decide) <|
      cons (by decide) nil

example : pentagonWalk.IsEulerian ∧ pentagonWalk.IsCircuit := by
  sorry

/-!
7. Show that the tail of a cycle is never nil. Hint: a cycle has length at least
three.
-/
lemma Walk.IsCycle.tail_not_nil' {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    ¬ c.tail.Nil := by
  sorry

/-!
8. Prove that the reverse of a Hamiltonian cycle is a Hamiltonian cycle. Hint:
`isHamiltonianCycle_iff_isCycle_and_length_eq`.
-/
lemma Walk.IsHamiltonianCycle.reverse' [DecidableEq V] {u : V} {p : G.Walk u u}
    (hp : p.IsHamiltonianCycle) : p.reverse.IsHamiltonianCycle := by
  sorry

/-!
9. A `cons` walk is a Hamiltonian cycle iff its tail is Hamiltonian and has length at
least two.
-/
lemma Walk.cons_isHamiltonianCycle_iff' [DecidableEq V] {u v : V} (p : G.Walk v u)
    (h : G.Adj u v) :
    (cons h p).IsHamiltonianCycle ↔ p.IsHamiltonian ∧ 2 ≤ p.length := by
  sorry

/-!
10. Show that reversing a copy of a walk is the same as copying its reverse. Hint:
`subst_vars`.
-/
example {u v u' v' : V} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).reverse = p.reverse.copy hv hu := by
  sorry

/-!
11. Show that a walk is not nil iff it has positive length. Hint: use `cases p`;
then `Nil.nil` and `nofun` are useful.
-/
example {u v : V} (p : G.Walk u v) : ¬ p.Nil ↔ 0 < p.length := by
  sorry

/-!
12. Show that an injective homomorphism maps trails to trails. Mathlib has this as
`IsTrail.map`, but prove it directly. Hint: `isTrail_def`, `edges_map` and
`List.Nodup.map`.
-/
example {W : Type*} {H : SimpleGraph W} {f : G →g H} (hf : Function.Injective f)
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) : (p.map f).IsTrail := by
  sorry

/-!
13. Translating the walk `pathNat₁Walk 0 j` by `i`, with `Walk.map` along
`pathNat₁Translate i`, gives a walk from `0 + i` to `(0 + j) + i`, so before we can
compare it with `pathNat₁Walk i j` we must `copy` it. Show that the two walks are
then equal. Hint: compare supports with `Walk.ext_support`, then use `support_copy`,
`Walk.support_map` and `support_pathNat₁Walk`.
-/
example (i j : ℕ) :
    ((pathNat₁Walk 0 j).map (pathNat₁Translate i).toHom).copy
      (by simp [pathNat₁Translate]) (by simp [pathNat₁Translate, add_comm]) =
      pathNat₁Walk i j := by
  sorry

/-!
14. If `p` is a Hamiltonian walk of length at least two and there is an edge `h₁`
from its `i`-th vertex to its end and an edge `h₂` from its `(i + 1)`-th vertex to
its start, then `p.posaClosed h₁ h₂` is a Hamiltonian cycle.
-/
lemma Walk.IsHamiltonian.posaClosed_isHamiltonianCycle' {u v} {i} [DecidableEq V]
    {p : G.Walk u v} (hp : p.IsHamiltonian) (h2 : 2 ≤ p.length)
    (h₁ : G.Adj (p.getVert i) v) (h₂ : G.Adj (p.getVert (i + 1)) u) :
    (p.posaClosed h₁ h₂).IsHamiltonianCycle := by
  sorry

/-!
15. Show that the Hamming distance on the hypercube is symmetric.
-/
lemma HypercubeVert.hammingDist_comm' {n : ℕ} (u v : HypercubeVert n) :
    u.hammingDist v = v.hammingDist u := by
  sorry

/-!
The next few exercises are about the Gray code walk `grayWalk` and showing how to
build a Hamiltonian cycle in `Q[n + 2]` from it.
-/
/-- The Gray code Hamiltonian cycle in `Q[n + 2]`. -/
def Walk.grayCycle (n : ℕ) : Q[n + 2].Walk (grayStart (n + 2)) (grayStart (n + 2)) :=
  have adj : Q[n + 2].Adj (grayStart (n + 2)) (grayEnd (n + 2)):= by simp
  Walk.cons adj (grayWalk (n + 2)).reverse

/-!
16. Show that in the Gray code walk `grayWalk (n + 2)`, the second vertex is always
in the `false` slice of `Q[n + 2]`.
-/
lemma Walk.grayWalk_snd_false' (n : ℕ) : (grayWalk (n + 2)).snd.2 = false := by
  sorry

/-!
17. Show that `grayCycle n` is indeed a cycle.
-/
lemma Walk.grayCycle_isCycle' (n : ℕ) : (grayCycle n).IsCycle := by
  sorry

/-!
18. Show that `grayCycle n` is a Hamiltonian cycle.
-/
lemma Walk.grayCycle_isHamiltonian' (n : ℕ) : (grayCycle n).IsHamiltonianCycle := by
  sorry

/-!
19. Prove that `Q[n]` is Hamiltonian unless `n = 1`. (Recall that `Q[0]` is a single
vertex which is considered Hamiltonian.)
-/
lemma hypercube_isHamiltonian' {n : ℕ} (h1 : n ≠ 1) : Q[n].IsHamiltonian :=
  sorry

/-!
20. Show that the Grötzsch graph `mμ[C[5]]` is Hamiltonian. Hint:
`IsHamiltonian.mycielskian`.
-/
example : grotzschGraph.IsHamiltonian := by
  sorry

/-!
In the chapter we built `Walk.cycleGraphCycle`, the walk once around `C[n + 3]`,
and proved that it is a Hamiltonian cycle. The next two exercises pin down
exactly which cycle graphs and complete graphs are Hamiltonian. (Recall that a
graph on a single vertex is trivially Hamiltonian; why does `n = 2` fail? Hint:
`not_isHamiltonian_of_card_eq_two`.)
-/
/-!
21. Show that the cycle graph `C[n]` is Hamiltonian iff `n ≠ 0, 2`.
-/
lemma cycleGraph_isHamiltonian_iff' (n : ℕ) :
    C[n].IsHamiltonian ↔ n ≠ 0 ∧ n ≠ 2 := by
  sorry

/-!
22. Show that the complete graph `K[n]` is Hamiltonian iff `n ≠ 0, 2`.
-/
lemma completeGraph_isHamiltonian_iff' (n : ℕ) :
    K[n].IsHamiltonian ↔ n ≠ 0 ∧ n ≠ 2 := by
  sorry

/-!
The next three exercises return to the example from the chapter's closure section:
`C[5] ⊔ edge 0 2 ⊔ edge 0 3`, i.e. `C[5]` with the two chords `0 — 2` and `0 — 3`.
Mathlib's `Decidable` instance for adjacency in `edge u v` is currently defined using
a cast, so `decide` gets stuck on any graph built from `edge` (see
[Decidability and Kernel Reduction*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-decidability-and-kernel-reduction)).
So we redefine the graph using `fromRel` instead.
-/
/-- `C[5]` with the two chords `0 — 2` and `0 — 3`. -/
abbrev chordedC5 : SimpleGraph (Fin 5) :=
  C[5] ⊔ fromRel fun x y => x = 0 ∧ (y = 2 ∨ y = 3)

/-!
23. Check that `chordedC5` is the graph from the chapter. Hint: after `ext`, simplify
the adjacency relation and then `decide +revert` should complete the proof.
-/
example : chordedC5 = C[5] ⊔ edge 0 2 ⊔ edge 0 3 := by
  sorry

/-!
24. Show that `chordedC5` is not an Ore graph.
-/
example : ¬ chordedC5.IsOreGraph := by
  sorry

/-!
25. Show that the closure of `chordedC5` is complete, even though `chordedC5` is not
an Ore graph. Hint: `ext` and `decide +revert`.
-/
example : chordedC5.closure = ⊤ := by
  sorry

/-!
The remaining exercises develop the classical direct proof of Ore's theorem via
maximum-length paths. The chapter's crossing-pair machinery
(`Walk.IsMaximalPath.exists_cycle_spanning`) will be useful here; the exercises
supply the extremal argument that replaces the closure. We begin with some
warm-up properties of Ore graphs.
-/
/-!
26. In an Ore graph any two distinct vertices are either adjacent or have a common
neighbour. Hint: if distinct vertices `u` and `v` are non-adjacent and have no
common neighbour, then their neighbourhoods are disjoint subsets of `V \ {u, v}`,
so their degree sum is at most `|V| - 2`, contradicting the Ore condition.
-/
open Finset in
lemma IsOreGraph.adj_or_exists' [Fintype V] [G.LocallyFinite] (h : G.IsOreGraph)
    {u v : V} (hne : u ≠ v) : G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj v w := by
  sorry

/-!
27. Consequently any two vertices of an Ore graph are joined by a walk of length
at most two (in the language of later chapters: an Ore graph is connected, with
diameter at most two).
-/
lemma IsOreGraph.exists_walk_length_le_two' [Fintype V] [G.LocallyFinite]
    (h : G.IsOreGraph) (u v : V) : ∃ p : G.Walk u v, p.length ≤ 2 := by
  sorry

/-!
28. An Ore graph on at least three vertices contains a vertex of degree at least
two. Hint: among any three distinct vertices either some pair is non-adjacent, and
so the Ore condition forces its degree sum to be at least three, or all three are
pairwise adjacent.
-/
lemma IsOreGraph.exists_two_le_degree' [Fintype V] [G.LocallyFinite]
    (h : G.IsOreGraph) (hn : 3 ≤ Fintype.card V) : ∃ w, 2 ≤ G.degree w := by
  sorry

/-!
29. Existence of a vertex of degree at least two implies existence of a path of
length at least two.
-/
lemma Walk.exists_path_of_two_le_degree' [G.LocallyFinite] {v : V}
    (hv : 2 ≤ G.degree v) :
    ∃ (x y : V) (q : G.Walk x y), q.IsPath ∧ 2 ≤ q.length := by
  sorry

/-!
Mathlib proves the existence of a maximum-length path in a graph with
nonempty vertex set and finite edge set:
`Walk.exists_isPath_forall_isPath_length_le_length`. Notice that the signature of
this lemma doesn't actually mention the word "maximum" but spells it out
explicitly. Since we will use this idea repeatedly we make a definition, bundling
together the fact that `p` is a path with the maximality of its length. (A note
on terminology: such a `p` has *maximum* length: no path anywhere in `G` is
longer. This is stronger than being *maximal*, which would only say that `p`
itself cannot be extended to a longer path.)
-/
/-- A *maximum-length path*: a path such that no path in `G` is longer. -/
structure Walk.IsMaximumPath {u v : V} (p : G.Walk u v) : Prop extends
  isPath : p.IsPath where
  length_le : ∀ ⦃x y : V⦄ ⦃q : G.Walk x y⦄, q.IsPath → q.length ≤ p.length

/-!
30. Restate Mathlib's existence result compactly.
-/
variable (G) in
lemma Walk.exists_isMaximumPath' [Nonempty V] [Finite G.edgeSet] :
    ∃ (u v : V) (p : G.Walk u v), p.IsMaximumPath := by
  sorry

/-!
31. The reverse of a maximum-length path is again a maximum-length path.
-/
lemma Walk.IsMaximumPath.reverse' {u v : V} {p : G.Walk u v} (h : p.IsMaximumPath) :
    p.reverse.IsMaximumPath := by
  sorry

/-!
32. A maximum-length path in an Ore graph on at least three vertices has length
at least two.
-/
lemma IsOreGraph.two_le_length_of_isMaximumPath' [Fintype V] [G.LocallyFinite]
    {u v} (h : G.IsOreGraph)
    (hn : 3 ≤ Fintype.card V) {p : G.Walk u v} (hmax : p.IsMaximumPath) :
    2 ≤ p.length := by
  sorry

/-!
33. A maximum-length path is in particular a *maximal* path, in the sense of the
chapter's `Walk.IsMaximalPath`: neither endpoint has a neighbour missing from it.
Hint: if a neighbour of the start were missing then `cons` would give a strictly
longer path; for the end vertex apply the same argument to `p.reverse`, using
`IsMaximumPath.reverse`.
-/
lemma Walk.IsMaximumPath.isMaximalPath' {u v : V} {p : G.Walk u v}
    (hmax : p.IsMaximumPath) : p.IsMaximalPath := by
  sorry

/-!
34. If `p` is a walk from a vertex in a set `S` to a vertex outside of `S`, there
are adjacent vertices `c ∈ S` and `d ∉ S`. Hint: `Walk.exists_boundary_dart`.
-/
lemma Walk.exists_cross_adj' {a b} {S : Set V} (p : G.Walk a b) (ha : a ∈ S)
    (hb : b ∉ S) : ∃ c ∈ S, ∃ d ∉ S, G.Adj c d  := by
  sorry

/-!
35. In a non-nil closed walk the first vertex also occurs as the last, so a vertex
lies in the tail of the support iff it lies in the support.
-/
lemma Walk.mem_support_tail_iff' {a : V} {c : G.Walk a a} (hc : ¬c.Nil) {x : V} :
    x ∈ c.support.tail ↔ x ∈ c.support := by
  sorry

/-!
36. A cycle can be cut at any of its vertices to give a path from that vertex
visiting exactly the cycle's vertices, of length one less than the cycle. Hint:
rotate the cycle to start at `y` and take the reversed tail, as in the proof of the
chapter's `IsCycle.exists_isPath_of_mem_edges`.
-/
lemma Walk.IsCycle.exists_isPath_spanning' {a : V} {c : G.Walk a a}
    (hc : c.IsCycle) {y : V} (hy : y ∈ c.support) :
    ∃ (z : V) (q : G.Walk y z), q.IsPath ∧ q.length + 1 = c.length ∧
      (∀ x, x ∈ q.support ↔ x ∈ c.support) := by
  sorry

/-!
37. If `p` is a maximum-length path from `u`, every vertex is reachable from `u`,
and some cycle through `u` of length one more than `p` visits exactly the vertices
of `p`, then `p` is Hamiltonian. (Neither Ore's condition nor finiteness is needed.)
Hint: if `p` missed a vertex, a walk from `u` to it and `exists_cross_adj` would
yield an edge leaving the cycle. Break the cycle with `exists_isPath_spanning` and
extend the resulting path with this edge to give a strictly longer path,
contradicting maximality.
-/
lemma Walk.IsMaximumPath.isHamiltonian_of_isCycle' [DecidableEq V] {u v : V}
    {p : G.Walk u v} (hmax : p.IsMaximumPath) (hreach : ∀ w, G.Reachable u w)
    {c : G.Walk u u} (hc : c.IsCycle) (hlen : c.length = p.length + 1)
    (hsupp : ∀ x, x ∈ c.support ↔ x ∈ p.support) : p.IsHamiltonian := by
  sorry

/-!
38. A maximum-length path in an Ore graph is Hamiltonian. Hint: apply
`isHamiltonian_of_isCycle`. Ore's condition supplies the cycle, via
`two_le_length_of_isMaximumPath` and `IsMaximalPath.exists_cycle_spanning` (from the
chapter), and the reachability, via `exists_walk_length_le_two`.
-/
lemma Walk.isHamiltonian_of_isMaximumPath' [Fintype V] [DecidableEq V]
    [G.LocallyFinite] (h : G.IsOreGraph)
    (hn : 3 ≤ Fintype.card V) {u v : V} {p : G.Walk u v}
    (hmax : p.IsMaximumPath) : p.IsHamiltonian := by
  sorry

/-!
39. Give a direct proof of Ore's theorem, not using the closure: take a
maximum-length path; it is Hamiltonian of length ≥ 2, so
`IsHamiltonian.exists_isHamiltonianCycle_of_isOrePair` closes it into a Hamiltonian
cycle.
-/
example [Fintype V] [DecidableEq V] [G.LocallyFinite] (h : G.IsOreGraph)
    (hn : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
  sorry

/-! SOLUTIONS -/
/-!
1. Prove by induction on `p` that reversing a walk does not change its length.
Hint: `reverse_cons` and `length_append`.
-/
example {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [reverse_cons, length_append, ih, length_cons, length_cons, length_nil]

/-!
2. Prove by induction on `p` that the support of `p.append q` is the support of `p`
followed by the tail of the support of `q` (the tail drops the shared vertex `v`).
Hint: in the `nil` case, `cons_tail_support`.
-/
example {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).support = p.support ++ q.support.tail := by
  induction p with
  | nil => rw [nil_append, support_nil, List.singleton_append, cons_tail_support]
  | cons h p ih => rw [cons_append, support_cons, support_cons, ih, List.cons_append]

/-!
3. Show that the `nil` walk is a trail.
-/
example (u : V) : (nil : G.Walk u u).IsTrail := .nil

/-!
4. Show that if `p : G.Walk u v` has length `0` then `u = v`. Hint: use `cases p`.
-/
example {u v : V} (p : G.Walk u v) (hl : p.length = 0) : u = v := by
  cases p with
  | nil => rfl
  | cons h p => simp at hl

/-!
5. Show that splitting a walk at a vertex on its support preserves the total length.
Hint: `Walk.take_spec`.
-/
example [DecidableEq V] {u v w : V} (p : G.Walk u v) (h : w ∈ p.support) :
    (p.takeUntil w h).length + (p.dropUntil w h).length = p.length := by
  rw [← length_append, take_spec]

/-!
6. The walk `pentagonWalk` travels once around the cycle `C[5]`. Show that it is an
Eulerian circuit. Hint: `decide` proves that it is Eulerian, using the `Decidable`
instance from the chapter. For `IsCircuit`, rewrite with `isCircuit_def` and
`isTrail_def` first.
-/
example : pentagonWalk.IsEulerian ∧ pentagonWalk.IsCircuit := by
  rw [isCircuit_def, isTrail_def]
  decide

/-!
7. Show that the tail of a cycle is never nil. Hint: a cycle has length at least
three.
-/
lemma Walk.IsCycle.tail_not_nil {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    ¬ c.tail.Nil := by
  grind [length_tail_add_one, hc.three_le_length]

/-!
8. Prove that the reverse of a Hamiltonian cycle is a Hamiltonian cycle. Hint:
`isHamiltonianCycle_iff_isCycle_and_length_eq`.
-/
lemma Walk.IsHamiltonianCycle.reverse [DecidableEq V] {u : V} {p : G.Walk u u}
    (hp : p.IsHamiltonianCycle) : p.reverse.IsHamiltonianCycle :=
  -- we need `Fintype V`, which the Hamiltonian cycle provides
  have : Fintype V := hp.isHamiltonian_tail.fintype
  isHamiltonianCycle_iff_isCycle_and_length_eq.2
    ⟨hp.isCycle.reverse, by simpa using hp.length_eq⟩

/-!
9. A `cons` walk is a Hamiltonian cycle iff its tail is Hamiltonian and has length at
least two.
-/
lemma Walk.cons_isHamiltonianCycle_iff [DecidableEq V] {u v : V} (p : G.Walk v u)
    (h : G.Adj u v) :
    (cons h p).IsHamiltonianCycle ↔ p.IsHamiltonian ∧ 2 ≤ p.length := by
  rw [isHamiltonianCycle_isCycle_and_isHamiltonian_tail,
    cons_isCycle_iff_length_ne_one, and_assoc]
  constructor <;> rintro ⟨h1, h2⟩
  · exact ⟨by simpa using h2.2, by grind⟩
  · exact ⟨h1.isPath, by grind, by simpa using h1⟩

/-!
10. Show that reversing a copy of a walk is the same as copying its reverse. Hint:
`subst_vars`.
-/
example {u v u' v' : V} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).reverse = p.reverse.copy hv hu := by
  subst_vars
  rfl

/-!
11. Show that a walk is not nil iff it has positive length. Hint: use `cases p`;
then `Nil.nil` and `nofun` are useful.
-/
example {u v : V} (p : G.Walk u v) : ¬ p.Nil ↔ 0 < p.length := by
  cases p with
  | nil => exact ⟨fun h => (h Nil.nil).elim, fun h => (Nat.lt_irrefl 0 h).elim⟩
  | cons h p => exact ⟨fun _ => by simp, fun _ => nofun⟩

/-!
12. Show that an injective homomorphism maps trails to trails. Mathlib has this as
`IsTrail.map`, but prove it directly. Hint: `isTrail_def`, `edges_map` and
`List.Nodup.map`.
-/
example {W : Type*} {H : SimpleGraph W} {f : G →g H} (hf : Function.Injective f)
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) : (p.map f).IsTrail := by
  rw [isTrail_def, edges_map]
  exact hp.edges_nodup.map (Sym2.map.injective hf)

/-!
13. Translating the walk `pathNat₁Walk 0 j` by `i`, with `Walk.map` along
`pathNat₁Translate i`, gives a walk from `0 + i` to `(0 + j) + i`, so before we can
compare it with `pathNat₁Walk i j` we must `copy` it. Show that the two walks are
then equal. Hint: compare supports with `Walk.ext_support`, then use `support_copy`,
`Walk.support_map` and `support_pathNat₁Walk`.
-/
example (i j : ℕ) :
    ((pathNat₁Walk 0 j).map (pathNat₁Translate i).toHom).copy
      (by simp [pathNat₁Translate]) (by simp [pathNat₁Translate, add_comm]) =
      pathNat₁Walk i j := by
  apply Walk.ext_support
  rw [support_copy, Walk.support_map, support_pathNat₁Walk, support_pathNat₁Walk]
  have h : ⇑(pathNat₁Translate i).toHom = (i + ·) := funext fun k => add_comm k i
  rw [h, List.map_add_range', add_zero]

/-!
14. If `p` is a Hamiltonian walk of length at least two and there is an edge `h₁`
from its `i`-th vertex to its end and an edge `h₂` from its `(i + 1)`-th vertex to
its start, then `p.posaClosed h₁ h₂` is a Hamiltonian cycle.
-/
lemma Walk.IsHamiltonian.posaClosed_isHamiltonianCycle {u v} {i} [DecidableEq V]
    {p : G.Walk u v} (hp : p.IsHamiltonian) (h2 : 2 ≤ p.length)
    (h₁ : G.Adj (p.getVert i) v) (h₂ : G.Adj (p.getVert (i + 1)) u) :
    (p.posaClosed h₁ h₂).IsHamiltonianCycle := by
  have : Fintype V := hp.fintype
  apply isHamiltonianCycle_iff_isCycle_and_length_eq.2
          ⟨hp.isPath.posaClosed_isCycle  h2 h₁ h₂, ?_⟩
  simpa using hp.length_support

/-!
15. Show that the Hamming distance on the hypercube is symmetric.
-/
lemma HypercubeVert.hammingDist_comm {n : ℕ} (u v : HypercubeVert n) :
    u.hammingDist v = v.hammingDist u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases u with ⟨u, b⟩
    rcases v with ⟨v, c⟩
    grind [HypercubeVert.hammingDist]

/-!
16. Show that in the Gray code walk `grayWalk (n + 2)`, the second vertex is always
in the `false` slice of `Q[n + 2]`.
-/
lemma Walk.grayWalk_snd_false (n : ℕ) : (grayWalk (n + 2)).snd.2 = false := by
  -- the first half of `grayWalk (n + 2)`, exactly as in its definition
  let fH : Q[n + 2].Walk (grayStart (n + 2)) (grayEnd (n + 1), false) :=
    ((grayWalk (n + 1)).map (hypercube.embedFalse (n + 1)).toHom).copy
      (by simp) (by simp)
  have : fH.length = 2 ^ (n + 1) - 1 := by
    rw [length_copy, length_map, length_grayWalk]
  have hstep : (grayWalk (n + 2)).snd = (fH.append _).getVert 1 := rfl
  cases n with
  | zero => rfl
  | succ n =>
    have : 1 < fH.length := by grind
    rw [hstep, Walk.getVert_append, ite_eq_left this]
    simp [fH, getVert_map]

/-!
17. Show that `grayCycle n` is indeed a cycle.
-/
@[simp]
lemma Walk.grayCycle_isCycle (n : ℕ) : (grayCycle n).IsCycle := by
  apply (cons_isCycle_iff _ _).2 ⟨(grayWalk_isPath (n + 2)).reverse,?_⟩
  rw [edges_reverse, List.mem_reverse]
  intro hmem
  have hf := grayWalk_snd_false n
  rw [← (grayWalk_isPath (n + 2)).eq_snd_of_mem_edges hmem] at hf
  contradiction

/-!
18. Show that `grayCycle n` is a Hamiltonian cycle.
-/
lemma Walk.grayCycle_isHamiltonianCycle (n : ℕ) :
    (grayCycle n).IsHamiltonianCycle := by
  apply (cons_isHamiltonianCycle_iff _ _).2 ⟨?_, ?_⟩
  · exact isHamiltonian_reverse.2 <| grayWalk_isHamiltonian (n + 2)
  · grind [length_grayWalk, length_reverse]

/-!
19. Prove that `Q[n]` is Hamiltonian unless `n = 1`. (Recall that `Q[0]` is a single
vertex which is considered Hamiltonian.)
-/
lemma hypercube_isHamiltonian {n : ℕ} (h1 : n ≠ 1) : Q[n].IsHamiltonian :=
  match n with
  | 0 => fun h => by simp at h
  | 1 => (h1 rfl).elim
  | n + 2 => fun _ => ⟨_, _, grayCycle_isHamiltonianCycle n⟩

/-!
20. Show that the Grötzsch graph `mμ[C[5]]` is Hamiltonian. Hint:
`IsHamiltonian.mycielskian`.
-/
example : grotzschGraph.IsHamiltonian :=
  IsHamiltonian.mycielskian (cycleGraph_isHamiltonian 2) (by simp)

/-!
21. Show that the cycle graph `C[n]` is Hamiltonian iff `n ≠ 0, 2`.
-/
lemma cycleGraph_isHamiltonian_iff (n : ℕ) : C[n].IsHamiltonian ↔ n ≠ 0 ∧ n ≠ 2 :=
  match n with
  | 0 | 1 => by simp [IsHamiltonian]
  | 2     => by simp [not_isHamiltonian_of_card_eq_two]
  | n + 3 => by simp

/-!
22. Show that the complete graph `K[n]` is Hamiltonian iff `n ≠ 0, 2`.
-/
lemma completeGraph_isHamiltonian_iff (n : ℕ) :
    K[n].IsHamiltonian ↔ n ≠ 0 ∧ n ≠ 2 :=
  match n with
  | 0 | 1 => by simp [IsHamiltonian]
  | 2     => by simp [not_isHamiltonian_of_card_eq_two]
  | n + 3 => by simp [completeGraph_isHamiltonian]

/-!
23. Check that `chordedC5` is the graph from the chapter. Hint: after `ext`, simplify
the adjacency relation and then `decide +revert` should complete the proof.
-/
example : chordedC5 = C[5] ⊔ edge 0 2 ⊔ edge 0 3 := by
  ext x y
  simp only [sup_adj, fromRel_adj, edge_adj]
  decide +revert

/-!
24. Show that `chordedC5` is not an Ore graph.
-/
example : ¬ chordedC5.IsOreGraph := by
  -- the non-adjacent vertices `1` and `4` have degree sum `4 < 5`
  intro h
  have h14 := h 1 4
  -- `contrapose! h14` swaps the hypothesis `h14` and the goal `False`, negating both
  -- (plain `contrapose` does the same without simplifying the negations)
  contrapose! h14
  unfold IsOrePair
  decide

/-!
25. Show that the closure of `chordedC5` is complete, even though `chordedC5` is not
an Ore graph. Hint: `ext` and `decide +revert`.
-/
example : chordedC5.closure = ⊤ := by
  ext x y
  simp only [top_adj]
  decide +revert

/-!
26. In an Ore graph any two distinct vertices are either adjacent or have a common
neighbour. Hint: if distinct vertices `u` and `v` are non-adjacent and have no
common neighbour, then their neighbourhoods are disjoint subsets of `V \ {u, v}`,
so their degree sum is at most `|V| - 2`, contradicting the Ore condition.
-/
open Finset in
lemma IsOreGraph.adj_or_exists [Fintype V] [G.LocallyFinite] (h : G.IsOreGraph)
    {u v : V} (hne : u ≠ v) : G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj v w := by
  classical
  by_cases huv : G.Adj u v
  · exact Or.inl huv
  refine Or.inr ?_
  -- The union of the neighbourhoods of `u` and `v` lives in `V \ {u, v}`
  have h_sub : G.neighborFinset u ∪ G.neighborFinset v ⊆ univ \ {u, v} := by
    intro x hx
    simp only [mem_union, mem_neighborFinset, mem_sdiff, mem_univ, true_and,
      mem_insert, mem_singleton] at hx ⊢
    grind [adj_symm]
  -- So the cardinality of the union of the neighbourhoods is at most `|V| - 2`
  have h_card := card_le_card h_sub
  -- The cardinality of `V \ {u, v}` is exactly `|V| - 2`
  have h_univ_card : (univ \ {u, v} : Finset V).card = Fintype.card V - 2 := by
    grind
  -- there is `w` in the intersection of the neighbourhoods of `u` and `v`
  obtain ⟨w, hw⟩ : (G.neighborFinset u ∩ G.neighborFinset v).Nonempty := by
    by_contra! h_empty
    rw [← disjoint_iff_inter_eq_empty] at h_empty
    -- Evaluate the cardinality of the subset relation
    rw [card_union_of_disjoint h_empty] at h_card
    -- Since `G.degree x` is the cardinality of `G.neighborFinset x`,
    -- grind can close the arithmetic contradiction directly using Ore's
    -- condition at the pair `u`, `v`
    grind [card_neighborFinset_eq_degree, h u v hne huv]
  exact ⟨w, by simpa using hw⟩

/-!
27. Consequently any two vertices of an Ore graph are joined by a walk of length
at most two (in the language of later chapters: an Ore graph is connected, with
diameter at most two).
-/
lemma IsOreGraph.exists_walk_length_le_two [Fintype V] [G.LocallyFinite]
    (h : G.IsOreGraph) (u v : V) : ∃ p : G.Walk u v, p.length ≤ 2 := by
  by_cases heq : u = v
  · exact heq ▸ ⟨nil, by simp⟩
  · rcases h.adj_or_exists heq with  huv | ⟨w, h1, h2⟩
    · exact ⟨cons huv nil, by simp⟩
    · exact ⟨cons h1 (cons h2.symm nil), by simp⟩

/-!
28. An Ore graph on at least three vertices contains a vertex of degree at least
two. Hint: among any three distinct vertices either some pair is non-adjacent, and
so the Ore condition forces its degree sum to be at least three, or all three are
pairwise adjacent.
-/
open Finset in
lemma IsOreGraph.exists_two_le_degree [Fintype V] [G.LocallyFinite]
    (h : G.IsOreGraph) (hn : 3 ≤ Fintype.card V) : ∃ w, 2 ≤ G.degree w := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hn
  by_cases hadj : G.Adj a b
  · by_cases hadj' : G.Adj b c
    · refine ⟨b, ?_⟩
      rw [← card_neighborFinset_eq_degree]
      exact one_lt_card_iff.2 ⟨a, c, by simp [hadj.symm, hadj', hac]⟩
    · have : 3 ≤ G.degree b + G.degree c := hn.trans (h b c hbc hadj')
      grind
  · have : 3 ≤ G.degree a + G.degree b := hn.trans (h a b hab hadj)
    grind

/-!
29. Existence of a vertex of degree at least two implies existence of a path of
length at least two.
-/
lemma Walk.exists_path_of_two_le_degree [G.LocallyFinite] {v : V}
    (hv : 2 ≤ G.degree v) :
    ∃ (x y : V) (q : G.Walk x y), q.IsPath ∧ 2 ≤ q.length := by
  rw [← card_neighborFinset_eq_degree] at hv
  obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.1 hv
  rw [mem_neighborFinset] at hx hy
  exact ⟨x, y, cons hx.symm (cons hy nil), by simp_all [hx.symm.ne, hy.ne]⟩

/-!
30. Restate Mathlib's existence result compactly.
-/
variable (G) in
lemma Walk.exists_isMaximumPath [Nonempty V] [Finite G.edgeSet] :
    ∃ (u v : V) (p : G.Walk u v), p.IsMaximumPath :=
  let ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  ⟨u, v, p, hp, hmax⟩

/-!
31. The reverse of a maximum-length path is again a maximum-length path.
-/
lemma Walk.IsMaximumPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsMaximumPath) :
    p.reverse.IsMaximumPath :=
  ⟨h.isPath.reverse, fun _ _ _ hq => p.length_reverse ▸ h.length_le hq⟩

/-!
32. A maximum-length path in an Ore graph on at least three vertices has length
at least two.
-/
lemma IsOreGraph.two_le_length_of_isMaximumPath [Fintype V] [G.LocallyFinite]
    {u v} (h : G.IsOreGraph)
    (hn : 3 ≤ Fintype.card V) {p : G.Walk u v} (hmax : p.IsMaximumPath) :
    2 ≤ p.length := by
  obtain ⟨w, hw⟩ := h.exists_two_le_degree hn
  obtain ⟨x, y, q, hq, hlen⟩ := exists_path_of_two_le_degree hw
  exact hlen.trans (hmax.length_le hq)

/-!
33. A maximum-length path is in particular a *maximal* path, in the sense of the
chapter's `Walk.IsMaximalPath`: neither endpoint has a neighbour missing from it.
Hint: if a neighbour of the start were missing then `cons` would give a strictly
longer path; for the end vertex apply the same argument to `p.reverse`, using
`IsMaximumPath.reverse`.
-/
lemma Walk.IsMaximumPath.isMaximalPath {u v : V} {p : G.Walk u v}
    (hmax : p.IsMaximumPath) : p.IsMaximalPath := by
  -- the `start` case, stated for an arbitrary maximum-length path so that we can
  -- reuse it for the reverse of `p`
  have hstart : ∀ {x y : V} {q : G.Walk x y}, q.IsMaximumPath →
      ∀ w, G.Adj x w → w ∈ q.support := by
    intro x y q hq w h
    by_contra! hw
    simpa using hq.length_le <| (q.cons_isPath_iff h.symm).mpr ⟨hq.isPath, hw⟩
  exact ⟨hmax.isPath, hstart hmax,
    fun w h => by grind [hstart hmax.reverse w h, support_reverse]⟩

/-!
34. If `p` is a walk from a vertex in a set `S` to a vertex outside of `S`, there
are adjacent vertices `c ∈ S` and `d ∉ S`. Hint: `Walk.exists_boundary_dart`.
-/
lemma Walk.exists_cross_adj {a b} {S : Set V} (p : G.Walk a b) (ha : a ∈ S)
    (hb : b ∉ S) : ∃ c ∈ S, ∃ d ∉ S, G.Adj c d  := by
  obtain ⟨⟨⟨c, d⟩, hcd⟩, -, ⟨hc, hd⟩⟩ := p.exists_boundary_dart S ha hb
  use c, hc, d, hd, hcd

/-!
35. In a non-nil closed walk the first vertex also occurs as the last, so a vertex
lies in the tail of the support iff it lies in the support.
-/
lemma Walk.mem_support_tail_iff {a : V} {c : G.Walk a a} (hc : ¬c.Nil) {x : V} :
    x ∈ c.support.tail ↔ x ∈ c.support := by
  refine ⟨List.mem_of_mem_tail, fun hx => ?_⟩
  rw [← c.cons_tail_support] at hx
  obtain rfl | h := List.mem_cons.mp hx
  · exact c.end_mem_tail_support hc
  · exact h

/-!
36. A cycle can be cut at any of its vertices to give a path from that vertex
visiting exactly the cycle's vertices, of length one less than the cycle. Hint:
rotate the cycle to start at `y` and take the reversed tail, as in the proof of the
chapter's `IsCycle.exists_isPath_of_mem_edges`.
-/
lemma Walk.IsCycle.exists_isPath_spanning {a : V} {c : G.Walk a a}
    (hc : c.IsCycle) {y : V} (hy : y ∈ c.support) :
    ∃ (z : V) (q : G.Walk y z), q.IsPath ∧ q.length + 1 = c.length ∧
      (∀ x, x ∈ q.support ↔ x ∈ c.support) := by
  classical
  -- Rotate the cycle to start at `y`.
  have hd : (c.rotate y hy).IsCycle := (isCycle_rotate hy).mpr hc
  -- The rotated cycle is not nil, and has the same length as the original cycle
  have hdnn : ¬ (c.rotate y hy).Nil := hd.not_nil
  have hlen : (c.rotate y hy).length = c.length := c.length_rotate _ hy
  -- The path we want is the reversed tail of the rotated cycle, which has
  -- the correct length and contains the same vertices as the original cycle.
  refine ⟨_, (c.rotate y hy).tail.reverse, hd.isPath_tail.reverse, ?_, fun x => ?_⟩
  · grind [length_tail_add_one, length_reverse]
  · grind [support_reverse, support_tail_of_not_nil _ hdnn, ← mem_support_rotate_iff,
            mem_support_tail_iff]

/-!
37. If `p` is a maximum-length path from `u`, every vertex is reachable from `u`,
and some cycle through `u` of length one more than `p` visits exactly the vertices
of `p`, then `p` is Hamiltonian. (Neither Ore's condition nor finiteness is needed.)
Hint: if `p` missed a vertex, a walk from `u` to it and `exists_cross_adj` would
yield an edge leaving the cycle. Break the cycle with `exists_isPath_spanning` and
extend the resulting path with this edge to give a strictly longer path,
contradicting maximality.
-/
lemma Walk.IsMaximumPath.isHamiltonian_of_isCycle [DecidableEq V] {u v : V}
    {p : G.Walk u v} (hmax : p.IsMaximumPath) (hreach : ∀ w, G.Reachable u w)
    {c : G.Walk u u} (hc : c.IsCycle) (hlen : c.length = p.length + 1)
    (hsupp : ∀ x, x ∈ c.support ↔ x ∈ p.support) : p.IsHamiltonian := by
  rw [hmax.isPath.isHamiltonian_iff]
  by_contra! hcon
  -- Some vertex `w` is missing from the path.
  obtain ⟨w, hw⟩ := hcon
  -- The support of `c` (as a `Set V`) does not contain `w`
  have hw' : w ∉ {x | x ∈ c.support} := fun hwc => hw ((hsupp w).mp hwc)
  -- A boundary edge leaves `c`; break the cycle there and prepend it.
  obtain ⟨q⟩ := hreach w
  obtain ⟨x, hxc, z, hzc, hxz⟩ := q.exists_cross_adj c.start_mem_support hw'
  obtain ⟨z', q, hqpath, hqlen, hqsupp⟩ := hc.exists_isPath_spanning hxc
  have hznotin : z ∉ q.support := fun hzq => hzc ((hqsupp z).mp hzq)
  have hlong : (q.cons hxz.symm).IsPath :=
    (cons_isPath_iff hxz.symm q).mpr ⟨hqpath, hznotin⟩
  grind [length_cons, hmax.length_le hlong]

/-!
38. A maximum-length path in an Ore graph is Hamiltonian. Hint: apply
`isHamiltonian_of_isCycle`. Ore's condition supplies the cycle, via
`two_le_length_of_isMaximumPath` and `IsMaximalPath.exists_cycle_spanning` (from the
chapter), and the reachability, via `exists_walk_length_le_two`.
-/
lemma Walk.isHamiltonian_of_isMaximumPath [Fintype V] [DecidableEq V]
    [G.LocallyFinite] (h : G.IsOreGraph)
    (hn : 3 ≤ Fintype.card V) {u v : V} {p : G.Walk u v}
    (hmax : p.IsMaximumPath) : p.IsHamiltonian := by
  have h2 : 2 ≤ p.length := h.two_le_length_of_isMaximumPath hn hmax
  -- Build a cycle through exactly the vertices of `p`.
  obtain ⟨c, hcyc, hclen, hcsupp⟩ :=
    hmax.isMaximalPath.exists_cycle_spanning h2 (h u v)
  refine hmax.isHamiltonian_of_isCycle (fun w => ?_) hcyc hclen hcsupp
  obtain ⟨q, -⟩ := h.exists_walk_length_le_two u w
  exact q.reachable

/-!
39. Give a direct proof of Ore's theorem, not using the closure: take a
maximum-length path; it is Hamiltonian of length ≥ 2, so
`IsHamiltonian.exists_isHamiltonianCycle_of_isOrePair` closes it into a Hamiltonian
cycle.
-/
example [Fintype V] [DecidableEq V] [G.LocallyFinite] (h : G.IsOreGraph)
    (hn : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
  intro
  have : Nonempty V := Fintype.card_pos_iff.mp (hn.trans_lt' (by decide))
  -- A maximum-length path `p` is Hamiltonian and has length ≥ 2, so it closes up
  -- into a Hamiltonian cycle.
  obtain ⟨u, v, p, hmax⟩ := exists_isMaximumPath G
  have hham := p.isHamiltonian_of_isMaximumPath h hn hmax
  exact ⟨u, hham.exists_isHamiltonianCycle_of_isOrePair
    (h.two_le_length_of_isMaximumPath hn hmax) (h u v)⟩

/-! END SOLUTIONS -/

end SimpleGraph
