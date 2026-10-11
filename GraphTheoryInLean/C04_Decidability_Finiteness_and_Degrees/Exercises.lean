import GraphTheoryInLean.C04_Decidability_Finiteness_and_Degrees.C04_Decidability_Finiteness_and_Degrees
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-!
# Exercises

The first exercises are on finiteness and counting.

1. In the chapter we saw that `bad_card_edgeFinset` demanded more instances than its
statement used. Prove that a graph has at most `Fintype.card (Sym2 V)` edges,
assuming only the two instances that the statement itself mentions. (Why would it
have been a mistake to assume `[Fintype V] [DecidableRel G.Adj]` instead?)
-/
example [Fintype G.edgeSet] [Fintype (Sym2 V)] :
    G.edgeFinset.card ≤ Fintype.card (Sym2 V) := by
  sorry

/-!
2. Show that the edge set of a graph on a finite vertex type is finite, using
`Finite` rather than `Fintype`. Note that no `DecidableRel G.Adj` is needed, unlike
for `Fintype G.edgeSet`: why not?
-/
example [Finite V] : Finite G.edgeSet := by
  sorry

/-!
3. The chapter showed `G.edgeSet.ncard = G.edgeFinset.card`. Prove the `ℕ∞` version.
-/
example [Fintype G.edgeSet] : G.edgeSet.encard = G.edgeFinset.card := by
  sorry

/-!
4. The infinite path `pathNat₁` has infinitely many edges. Show that the `ℕ∞`-valued
`encard` of its edge set is therefore `⊤`, while the `ℕ`-valued `ncard` returns the
junk value `0`. Hint: the edges `s(n, n + 1)` are distinct for distinct `n`, so
`Set.infinite_of_injective_forall_mem` shows that the edge set is infinite.
-/
example : pathNat₁.edgeSet.encard = ⊤ ∧ pathNat₁.edgeSet.ncard = 0 := by
  sorry

/-!
5. The degree of a vertex is the `Nat.card` of its neighbourhood.
-/
example (v : V) [Fintype (G.neighborSet v)] :
    Nat.card (G.neighborSet v) = G.degree v := by
  sorry

/-!
6. In the complete graph every vertex is adjacent to every other vertex: its
`neighborFinset` is `Finset.univ` with the vertex itself removed.
-/
example (n : ℕ) (v : Fin n) : K[n].neighborFinset v = Finset.univ.erase v := by
  sorry

/-!
7. The infinite path `pathNat₁` has no minimum or maximum degree in the sense of
`minDegree` and `maxDegree`, since its vertex type is infinite. Show instead that `1`
is the least, and `2` the greatest, degree of a vertex of `pathNat₁`.
-/
example : IsLeast {d | ∃ v, pathNat₁.degree v = d} 1 ∧
    IsGreatest {d | ∃ v, pathNat₁.degree v = d} 2 := by
  sorry

/-!
8. A graph on an odd number of vertices that is regular of degree `d` must have `d`
even. (Hint: use `IsRegularOfDegree.two_mul_card_edgeFinset`. The statement does not
mention the edge set, so get the `Fintype G.edgeSet` instance that the proof needs
from `classical`.)
-/
example [Fintype V] [G.LocallyFinite] {d : ℕ} (h : G.IsRegularOfDegree d)
    (hV : Odd (Fintype.card V)) : Even d := by
  sorry

/-!
9. Prove that the complete graph on `Fin (n + 1)` has `n * (n + 1) / 2` edges.
-/
example (n : ℕ) :  K[n + 1].edgeFinset.card = n * (n + 1) / 2 := by
  sorry

/-!
10. Show that in any graph
`G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) / 2`.
-/
example [Fintype V] [Fintype G.edgeSet] :
    G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) / 2 := by
  sorry

/-!
11. Show that `k` times the number of vertices of degree at least `k` is at most
twice the number of edges. (The set of such vertices is a `Finset` written with the
set-builder notation of
[Set-Builder Notation](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-set-builder-notation).
Compare it with the handshake lemma.)
-/
example [Fintype V] [DecidableRel G.Adj] (k : ℕ) :
    k * ({v | k ≤ G.degree v} : Finset V).card ≤ 2 * G.edgeFinset.card := by
  sorry

/-!
12. The complement of the hypercube `Q[n]` is regular of degree `2 ^ n - 1 - n`.
(Hint: `IsRegularOfDegree.compl` takes `[DecidableRel G.Adj]`, so it needs `Q[n]` to
be regular with respect to the filtering instance for its neighbourhoods; see
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond).)
-/
example (n : ℕ) : (Q[n])ᶜ.IsRegularOfDegree (2 ^ n - 1 - n) := by
  sorry

/-!
13. We saw that an `n`-uniform blow-up of a locally finite graph is locally finite.
In this exercise we generalize this to the case when each of the classes in the
blow-up is finite (but they may have different sizes). We make this a `def` rather
than an `instance`: since `G[n]` is `G.blowUpGraph (fun _ => Fin n)`, an instance
would give a second route to `Fintype (G[n].neighborSet w)`, alongside the instance
from the chapter, creating a diamond (see
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond)).
-/
@[instance_reducible]
def locallyFiniteBlowUpGraph' {ι : Type*} (H : SimpleGraph ι) [H.LocallyFinite]
    (V : ι → Type*) [∀ i, Fintype (V i)] : LocallyFinite (H.blowUpGraph V) :=
  fun ⟨i, v⟩ => Fintype.ofEquiv (Σ k : H.neighborSet i, V k)
    -- the goal is to show the obvious `Equiv` between neighbourhoods
    sorry

/-!
14. Prove that if `V` is finite then the number of vertices in the `n`th iterated
Mycielskian is `2 ^ n * Fintype.card V + 2 ^ n - 1`.
-/
lemma card_mycielskianVert' (n : ℕ) [Fintype V] :
    Fintype.card (mμᵥ^n V) = 2 ^ n * Fintype.card V + 2 ^ n - 1 := by
  sorry

/-!
The next few exercises are on the degrees of vertices in the Mycielskian.

As in
[Mycielskian Degrees](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-mycielskian-degrees),
statements about degrees and edge sets take the `Fintype` instances they mention as
arguments. Those about `δ`, `Δ` and `degreeMultiset` take `[Fintype V]` and
`[DecidableRel G.Adj]` instead, since these definitions build their own instances
from them (see
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond)).
Use the `classical` tactic for any further instances a proof needs. (We also
`open Finset` since we will need quite a few lemmas about `Finset`.)

15. The degree of the new vertex `none` in the Mycielskian is the number of vertices
in the original graph.
-/
open Finset
lemma degree_mycielskian_none' [Fintype V] [Fintype (mμ[G].neighborSet none)] :
    mμ[G].degree none = Fintype.card V := by
  sorry

/-!
16. The degree of the right copy of a vertex in the Mycielskian is one more than the
degree of the vertex in the original graph.
-/
lemma degree_mycielskian_right' (v : V) [Fintype (G.neighborSet v)]
    [Fintype (mμ[G].neighborSet (v ᵣ))] :
    mμ[G].degree v ᵣ = G.degree v + 1 := by
  sorry

/-!
17. The number of edges in `mμ[G]` is `3 * G.edgeFinset.card + Fintype.card V`.
(Use the version of the handshake lemma that takes its instances as arguments.)
-/
lemma card_edgeFinset_mycielskian' [Fintype V] [Fintype G.edgeSet]
    [Fintype mμ[G].edgeSet] :
     #mμ[G].edgeFinset = 3 * # G.edgeFinset + Fintype.card V := by
  sorry

/-!
18. The maximum degree of `mμ[G]` is the maximum of `2 * Δ(G)` and the number of
vertices in `G`.
-/
lemma maxDegree_mycielskian' [Fintype V] [DecidableRel G.Adj] :
    Δ(mμ[G]) = max (2 * Δ(G)) (Fintype.card V) := by
  sorry

/-!
19. The minimum degree of `mμ[G]` is the minimum of `2 * δ(G)` and `δ(G) + 1`.
Deduce that `δ(mμ[G]) = δ(G) + 1` whenever `δ(G) ≥ 1`.
-/
lemma minDegree_mycielskian' [Fintype V] [DecidableRel G.Adj] :
    δ(mμ[G]) = min (2 * δ(G)) (δ(G) + 1) := by
  sorry

lemma minDegree_mycielskian_of_one_le' [Fintype V] [DecidableRel G.Adj]
    (h : 1 ≤ δ(G)) : δ(mμ[G]) = δ(G) + 1 := by
  sorry

/-!
20. The degreeMultiset of the complete graph `K[n]` is the multiset of `n` copies of
`n - 1`.
-/
theorem degreeMultiset_top' (n : ℕ) :
    K[n].degreeMultiset = Multiset.replicate n (n - 1) := by
  sorry

/-!
21. A multiset of `n` copies of `n - 1` is graphic, realized by the complete graph
`K[n]`.
-/
theorem graphic_const' (n : ℕ) :
    Graphic (Multiset.replicate n (n - 1)) := by
  sorry

/-!
22. Every graphic multiset has an even sum. (This shows that the parity condition in
the Erdős–Gallai theorem is necessary.)
-/
theorem Graphic.even_sum' {m : Multiset ℕ} (h : Graphic m) : Even m.sum := by
  sorry

/-!
23. In the chapter we computed the degree of the new vertex of `coneGraph H s`. Show
that an old vertex gains one on its degree exactly when it lies in `s`.
-/
lemma coneGraph_degree_some' [DecidableEq V] (H : SimpleGraph V) (s : Finset V)
    (w : V) [Fintype (H.neighborSet w)]
    [Fintype ((coneGraph H s).neighborSet (some w))] :
    (coneGraph H s).degree (some w) = H.degree w + (if w ∈ s then 1 else 0) := by
  sorry

/-!
24. The `degreeMultiset` of the cone: the new vertex contributes `#s`, and every old
vertex has its old degree plus one when it lies in `s`. (Hint: the stub below records
that `Finset.univ` on `Option V` is `none` followed by the image of `Finset.univ`
under `some`. This holds by `rfl`.)
-/
theorem coneGraph_degreeMultiset' [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : Finset V) :
    (coneGraph H s).degreeMultiset = #s ::ₘ (Finset.univ : Finset V).val.map
      (fun w => H.degree w + if w ∈ s then 1 else 0) := by
  have h : (Finset.univ : Finset (Option V)).val =
      none ::ₘ (Finset.univ : Finset V).val.map some := rfl
  sorry

/-!
25. The `degreeMultiset` of `mμ[G]` is the multiset of degrees
of `G` with each degree doubled, together with the degrees of the new vertices.
(Hint: the stub below records how `Finset.univ` unfolds on `Option α` and on
`α ⊕ β`. Both facts hold by `rfl`, as in exercise 24.)
-/
lemma degreeMultiset_mycielskian' [Fintype V] [DecidableRel G.Adj] :
    mμ[G].degreeMultiset = {Fintype.card V} + (G.degreeMultiset.map (2 * · ))
                           + (G.degreeMultiset.map (· + 1)) := by
  simp only [degreeMultiset]
  have h1 : (Finset.univ : Finset (Option (V ⊕ V))).val =
          none ::ₘ Multiset.map Option.some (Finset.univ : Finset (V ⊕ V)).val := rfl
  have h2 : (Finset.univ : Finset (V ⊕ V)).val = Multiset.map Sum.inl
                Finset.univ.val + Multiset.map Sum.inr Finset.univ.val := rfl
  sorry

/-!
26. In a locally finite graph `G`, there is a vertex of degree at least 3 iff
 `∃ a b c d, G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d`
-/
lemma exists_three_le_degree_iff' {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] : (∃ v, 3 ≤ G.degree v) ↔
      ∃ a b c d, G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  sorry

/-!
The final exercises return to decidability, and give decidable adjacency instances
for the line graph and the `hasse` graph, both of which Mathlib is missing.

27. Give a decidable adjacency instance for the line graph `L[G]` of a graph on a
vertex type with decidable equality. Recall that the vertices of `L[G]` are the edges
of `G`, and that two of them are adjacent iff they are distinct and share a vertex
(`lineGraph_adj_iff_exists`).

(Hint: to decide whether two edges `e₁ e₂ : Sym2 V` share a vertex, use
`Sym2.recOnSubsingleton` to write them as `s(a, b)` and `s(c, d)`, and reduce to the
four equalities `a = c`, `a = d`, `b = c` and `b = d` with `decidable_of_iff`.
Recursion on `Sym2` is only allowed when the result cannot depend on the order of the
two endpoints; `recOnSubsingleton` ensures this by requiring the result to lie in a
`Subsingleton`, which `Decidable p` is.)
-/
example {V : Type*} (G : SimpleGraph V) [DecidableEq V] : DecidableRel L[G].Adj :=
  sorry

/-!
28. In a locally finite order `a ⋖ b` holds iff `a < b` and the interval
`Finset.Ioo a b` is empty, so the covering relation is decidable. Give the instance,
building it with `decidable_of_iff` rather than `rw` so that `decide` can still
reduce it.
-/
example {α : Type*} [Preorder α] [DecidableEq α] [DecidableLT α]
    [LocallyFiniteOrder α] : DecidableRel ((· ⋖ ·) : α → α → Prop) :=
  sorry

/-!
29. Show that the `hasse` graph of a preorder with a decidable covering relation has
decidable adjacency.
-/
example (α : Type*) [Preorder α] [DecidableRel ((· ⋖ ·) : α → α → Prop)] :
    DecidableRel (hasse α).Adj :=
  sorry


/-! SOLUTIONS -/

/-!
1. In the chapter we saw that `bad_card_edgeFinset` demanded more instances than its
statement used. Prove that a graph has at most `Fintype.card (Sym2 V)` edges,
assuming only the two instances that the statement itself mentions. (Why would it
have been a mistake to assume `[Fintype V] [DecidableRel G.Adj]` instead?)
-/
example [Fintype G.edgeSet] [Fintype (Sym2 V)] :
    G.edgeFinset.card ≤ Fintype.card (Sym2 V) :=
  Finset.card_le_univ _
-- Assuming `[Fintype V] [DecidableRel G.Adj]` would restrict the lemma to callers
-- who obtain `Fintype G.edgeSet` by that particular route, exactly as for
-- `bad_card_edgeFinset`.

/-!
2. Show that the edge set of a graph on a finite vertex type is finite, using
`Finite` rather than `Fintype`. Note that no `DecidableRel G.Adj` is needed, unlike
for `Fintype G.edgeSet`: why not?
-/
example [Finite V] : Finite G.edgeSet :=
  -- `Sym2 V` is finite since `V` is (it is a quotient of `V × V`: `Quot.finite`),
  -- and a subtype of a finite type is finite (`Subtype.finite`). Being a
  -- proposition, `Finite` carries no data and so has nothing to compute; the
  -- decidability was only ever needed to *filter* `Finset.univ` down to the edges.
  inferInstance

/-!
3. The chapter showed `G.edgeSet.ncard = G.edgeFinset.card`. Prove the `ℕ∞` version.
-/
example [Fintype G.edgeSet] : G.edgeSet.encard = G.edgeFinset.card := by
  rw [← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard]

/-!
4. The infinite path `pathNat₁` has infinitely many edges. Show that the `ℕ∞`-valued
`encard` of its edge set is therefore `⊤`, while the `ℕ`-valued `ncard` returns the
junk value `0`.
-/
example : pathNat₁.edgeSet.encard = ⊤ ∧ pathNat₁.edgeSet.ncard = 0 := by
  have h : pathNat₁.edgeSet.Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun n : ℕ => s(n, n + 1))
      (fun a b hab => by grind [Sym2.eq_iff]) (fun n => by simp)
  exact ⟨h.encard_eq, h.ncard⟩

/-!
5. The degree of a vertex is the `Nat.card` of its neighbourhood.
-/
example (v : V) [Fintype (G.neighborSet v)] :
    Nat.card (G.neighborSet v) = G.degree v := by
  rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree]

/-!
6. In the complete graph every vertex is adjacent to every other vertex: its
`neighborFinset` is `Finset.univ` with the vertex itself removed.
-/
example (n : ℕ) (v : Fin n) : K[n].neighborFinset v = Finset.univ.erase v := by
  ext w; simp [ne_comm]

/-!
7. The infinite path `pathNat₁` has no minimum or maximum degree in the sense of
`minDegree` and `maxDegree`, since its vertex type is infinite. Show instead that `1`
is the least, and `2` the greatest, degree of a vertex of `pathNat₁`.
-/
example : IsLeast {d | ∃ v, pathNat₁.degree v = d} 1 ∧
    IsGreatest {d | ∃ v, pathNat₁.degree v = d} 2 := by
  -- the degrees `1` and `2` are attained at the vertices `0` and `1`
  refine ⟨⟨⟨0, by simp⟩, ?_⟩, ⟨⟨1, by simp⟩, ?_⟩⟩
  all_goals
    rintro _ ⟨v, rfl⟩
    simp only [degree_pathNat₁]
    split_ifs <;> simp

/-!
8. A graph on an odd number of vertices that is regular of degree `d` must have `d`
even. (Hint: use `IsRegularOfDegree.two_mul_card_edgeFinset`. The statement does not
mention the edge set, so get the `Fintype G.edgeSet` instance that the proof needs
from `classical`.)
-/
example [Fintype V] [G.LocallyFinite] {d : ℕ} (h : G.IsRegularOfDegree d)
    (hV : Odd (Fintype.card V)) : Even d := by
  classical
  have h2 : Even (Fintype.card V * d) := h.two_mul_card_edgeFinset ▸ even_two_mul _
  exact (Nat.even_mul.1 h2).resolve_left (Nat.not_even_iff_odd.2 hV)

/-!
9. Prove that the complete graph on `Fin (n + 1)` has `n * (n + 1) / 2` edges.
-/
example (n : ℕ) :  K[n + 1].edgeFinset.card = n * (n + 1) / 2 := by
  rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, Nat.choose_two_right,
      Nat.add_sub_cancel_right, mul_comm]

/-!
10. Show that in any graph
`G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) / 2`.
-/
example [Fintype V] [Fintype G.edgeSet] :
    G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) / 2 :=
  G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_two_right _).le

/-!
11. Show that `k` times the number of vertices of degree at least `k` is at most
twice the number of edges. (The set of such vertices is a `Finset` written with the
set-builder notation of
[Set-Builder Notation](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-set-builder-notation).
Compare it with the handshake lemma.)
-/
example [Fintype V] [DecidableRel G.Adj] (k : ℕ) :
    k * ({v | k ≤ G.degree v} : Finset V).card ≤ 2 * G.edgeFinset.card := by
  rw [← sum_degrees_eq_twice_card_edges]
  calc k * ({v | k ≤ G.degree v} : Finset V).card
      = ∑ v ∈ ({v | k ≤ G.degree v} : Finset V), k := by simp [mul_comm]
    _ ≤ ∑ v ∈ ({v | k ≤ G.degree v} : Finset V), G.degree v :=
        Finset.sum_le_sum fun v hv => by simpa using hv
    _ ≤ ∑ v, G.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-!
12. The complement of the hypercube `Q[n]` is regular of degree `2 ^ n - 1 - n`.
(Hint: `IsRegularOfDegree.compl` takes `[DecidableRel G.Adj]`, so it needs `Q[n]` to
be regular with respect to the filtering instance for its neighbourhoods; see
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond).)
-/
example (n : ℕ) : (Q[n])ᶜ.IsRegularOfDegree (2 ^ n - 1 - n) := by
  -- put the filtering instance in scope, so that `hypercube_isRegularOfDegree`
  -- produces the regularity statement `IsRegularOfDegree.compl` expects
  let : Q[n].LocallyFinite := fun v => Subtype.fintype _
  have := (hypercube_isRegularOfDegree n).compl
  rwa [card_hypercubeVert] at this

/-!
13. We saw that an `n`-uniform blow-up of a locally finite graph is locally finite.
In this exercise we generalize this to the case when each of the classes in the
blow-up is finite (but they may have different sizes). We make this a `def` rather
than an `instance`: since `G[n]` is `G.blowUpGraph (fun _ => Fin n)`, an instance
would give a second route to `Fintype (G[n].neighborSet w)`, alongside the instance
from the chapter, creating a diamond (see
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond)).
-/
/-- A blow-up of a locally finite graph with finite classes is locally finite. -/
@[instance_reducible]
def locallyFiniteBlowUpGraph {ι : Type*} (H : SimpleGraph ι) [H.LocallyFinite]
    (V : ι → Type*) [∀ i, Fintype (V i)] : LocallyFinite (H.blowUpGraph V) :=
  fun ⟨i, v⟩ => Fintype.ofEquiv (Σ k : H.neighborSet i, V k)
    { toFun := fun ⟨⟨k, hk⟩, y⟩ => ⟨⟨k, y⟩, hk⟩
      invFun := fun ⟨⟨k, y⟩, hadj⟩ => ⟨⟨k, hadj⟩, y⟩}

/-!
14. Prove that if `V` is finite then the number of vertices in the `n`th iterated
Mycielskian is `2 ^ n * Fintype.card V + 2 ^ n - 1`.
-/
lemma card_mycielskianVert (n : ℕ) [Fintype V] :
    Fintype.card (mμᵥ^n V) = 2 ^ n * Fintype.card V + 2 ^ n - 1 := by
  induction n with
  | zero => unfold MycielskianVert; grind
  | succ n ih =>
    unfold MycielskianVert
    grind [card_mycielskianVert_one, Nat.mul_sub_left_distrib, mul_add,
            ← mul_assoc, ← pow_succ']

/-!
15. The degree of the new vertex `none` in the Mycielskian is the number of vertices
in the original graph.
-/
@[simp]
lemma degree_mycielskian_none [Fintype V] [Fintype (mμ[G].neighborSet none)] :
    mμ[G].degree none = Fintype.card V := by
  classical
  have hnb : mμ[G].neighborFinset none = (univ : Finset V).image (· ᵣ) := by
    ext x; simp [← mem_neighborSet]
  rw [← card_neighborFinset_eq_degree, hnb,
    card_image_of_injective _ mycielskian.right_injective, card_univ]

/-!
16. The degree of the right copy of a vertex in the Mycielskian is one more than the
degree of the vertex in the original graph.
-/
@[simp]
lemma degree_mycielskian_right (v : V) [Fintype (G.neighborSet v)]
    [Fintype (mμ[G].neighborSet (v ᵣ))] :
    mμ[G].degree v ᵣ = G.degree v + 1 := by
  classical
  have hnb :
      mμ[G].neighborFinset (v ᵣ) = (G.neighborFinset v).image (· ₗ) ∪ {none} := by
    ext x; simp [← mem_neighborSet]
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, hnb,
    card_union_of_disjoint (by simp [← Finset.disjoint_coe]),
    card_image_of_injective _ mycielskian.left_injective, card_singleton]

/-!
17. The number of edges in `mμ[G]` is `3 * G.edgeFinset.card + Fintype.card V`.
(Use the version of the handshake lemma that takes its instances as arguments.)
-/
@[simp]
lemma card_edgeFinset_mycielskian [Fintype V] [Fintype G.edgeSet]
    [Fintype mμ[G].edgeSet] :
     #mμ[G].edgeFinset = 3 * # G.edgeFinset + Fintype.card V := by
  classical
  apply (Nat.mul_right_inj (show 2 ≠ 0 by decide)).1
  simp_rw [← sum_degrees_eq_twice_card_edges' mμ[G], Fintype.sum_option,
    degree_mycielskian_none, Fintype.sum_sum_type, degree_mycielskian_left,
    ← mul_sum, degree_mycielskian_right, sum_add_distrib,
    sum_degrees_eq_twice_card_edges' G, sum_const, card_univ, smul_eq_mul, mul_one]
  grind

/-!
18. The maximum degree of `mμ[G]` is the maximum of `2 * Δ(G)` and the number of
vertices in `G`.
-/
lemma maxDegree_mycielskian [Fintype V] [DecidableRel G.Adj] :
    Δ(mμ[G]) = max (2 * Δ(G)) (Fintype.card V) := by
  apply le_antisymm
  · apply maxDegree_le_of_forall_degree_le
    intro v
    rcases v with none | (v | v)
    · simp
    · rw [degree_mycielskian_left]
      exact (Nat.mul_le_mul_left 2 (G.degree_le_maxDegree v)).trans (le_max_left _ _)
    · rw [degree_mycielskian_right]
      exact (Nat.succ_le_of_lt (G.degree_lt_card_verts v)).trans (le_max_right _ _)
  · cases isEmpty_or_nonempty V
    · simp
    · apply max_le
      · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
        rw [hv, ← degree_mycielskian_left]
        exact mμ[G].degree_le_maxDegree (v ₗ)
      · rw [← G.degree_mycielskian_none]
        exact mμ[G].degree_le_maxDegree none
/-!
19. The minimum degree of `mμ[G]` is the minimum of `2 * δ(G)` and `δ(G) + 1`.
Deduce that `δ(mμ[G]) = δ(G) + 1` whenever `δ(G) ≥ 1`.
-/
lemma minDegree_mycielskian [Fintype V] [DecidableRel G.Adj] :
    δ(mμ[G]) = min (2 * δ(G)) (δ(G) + 1) := by
  obtain hV | hV := isEmpty_or_nonempty V
  · simp [minDegree]
  apply le_antisymm
  · obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
    apply le_min
    · rw [hv, ← degree_mycielskian_left]
      exact mμ[G].minDegree_le_degree (v ₗ)
    · rw [hv, ← degree_mycielskian_right]
      exact mμ[G].minDegree_le_degree (v ᵣ)
  · apply le_minDegree_of_forall_le_degree
    intro v
    rcases v with none | (v | v)
    · rw [degree_mycielskian_none]
      exact (min_le_right _ _).trans (Nat.succ_le_of_lt G.minDegree_lt_card)
    · rw [degree_mycielskian_left]
      exact (min_le_left _ _).trans (Nat.mul_le_mul_left 2 (G.minDegree_le_degree v))
    · rw [degree_mycielskian_right]
      -- `min_le_right ..` is `min_le_right _ _`: `..` fills in all the remaining
      -- explicit arguments with `_`
      exact (min_le_right ..).trans
        (Nat.add_le_add_right (G.minDegree_le_degree v) 1)

lemma minDegree_mycielskian_of_one_le [Fintype V] [DecidableRel G.Adj]
    (h : 1 ≤ δ(G)) : δ(mμ[G]) = δ(G) + 1 := by
  rw [minDegree_mycielskian]
  grind

/-!
20. The degreeMultiset of the complete graph `K[n]` is the multiset of `n` copies of
`n - 1`.
-/
theorem degreeMultiset_top (n : ℕ) :
    K[n].degreeMultiset = Multiset.replicate n (n - 1) := by
  simp [degreeMultiset]

/-!
21. A multiset of `n` copies of `n - 1` is graphic, realized by the complete graph
`K[n]`.
-/
theorem graphic_const (n : ℕ) :
    Graphic (Multiset.replicate n (n - 1)) :=
  degreeMultiset_top n ▸ graphic_degreeMultiset K[n]

/-!
22. Every graphic multiset has an even sum. (This shows that the parity condition in
the Erdős–Gallai theorem is necessary.)
-/
theorem Graphic.even_sum {m : Multiset ℕ} (h : Graphic m) : Even m.sum := by
  obtain ⟨V, _, G, _, rfl⟩ := h
  -- the sum of the degree multiset is, by definition, the sum of the degrees
  change Even (∑ v, G.degree v)
  rw [sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

/-!
23. In the chapter we computed the degree of the new vertex of `coneGraph H s`. Show
that an old vertex gains one on its degree exactly when it lies in `s`.
-/
@[simp]
theorem coneGraph_degree_some [DecidableEq V] (H : SimpleGraph V) (s : Finset V)
    (w : V) [Fintype (H.neighborSet w)]
    [Fintype ((coneGraph H s).neighborSet (some w))] :
    (coneGraph H s).degree (some w) = H.degree w + (if w ∈ s then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (coneGraph H s).neighborFinset (some w) =
     (H.neighborFinset w).map Function.Embedding.some ∪
       (if w ∈ s then {none} else ∅) := by
    ext x
    cases x <;> by_cases hw : w ∈ s <;> simp [hw]
  rw [hset]
  split_ifs with h <;> simp

/-!
24. The `degreeMultiset` of the cone: the new vertex contributes `#s`, and every old
vertex has its old degree plus one when it lies in `s`.
-/
theorem coneGraph_degreeMultiset [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : Finset V) :
    (coneGraph H s).degreeMultiset = #s ::ₘ (Finset.univ : Finset V).val.map
      (fun w => H.degree w + if w ∈ s then 1 else 0) := by
  unfold degreeMultiset
  -- `Finset.univ` on `Option V` is by definition `none` followed by the image of
  -- `Finset.univ` under `some`
  change (none ::ₘ (Finset.univ : Finset V).val.map some).map _ = _
  simp

/-!
25. The `degreeMultiset` of `mμ[G]` is the multiset of degrees
of `G` with each degree doubled, together with the degrees of the new vertices.
(Hint: the stub below records how `Finset.univ` unfolds on `Option α` and on
`α ⊕ β`. Both facts hold by `rfl`, as in exercise 24.)
-/
lemma degreeMultiset_mycielskian [Fintype V] [DecidableRel G.Adj] :
    mμ[G].degreeMultiset = {Fintype.card V} + (G.degreeMultiset.map (2 * · ))
                           + (G.degreeMultiset.map (· + 1)) := by
  simp only [degreeMultiset]
  -- Split the universe of `Option (V ⊕ V)` into the new vertex `none`, the left
  -- copies and the right copies.
  have h1 : (Finset.univ : Finset (Option (V ⊕ V))).val =
          none ::ₘ Multiset.map Option.some (Finset.univ : Finset (V ⊕ V)).val := rfl
  have h2 : (Finset.univ : Finset (V ⊕ V)).val = Multiset.map Sum.inl
                Finset.univ.val + Multiset.map Sum.inr Finset.univ.val := rfl
  rw [h1, h2]
  simp only [Multiset.map_cons, Multiset.map_add, Multiset.map_map, Function.comp,
    degree_mycielskian_none, degree_mycielskian_left, degree_mycielskian_right]
  rw [← Multiset.singleton_add]
  abel

/-!
26. In a locally finite graph `G`, there is a vertex of degree at least 3 iff
 `∃ a b c d, G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d`
-/
lemma exists_three_le_degree_iff {V : Type*} (G : SimpleGraph V)
    [G.LocallyFinite] : (∃ v, 3 ≤ G.degree v) ↔
      ∃ a b c d, G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · rintro ⟨a, ha⟩
    rw [← card_neighborFinset_eq_degree] at ha
    obtain ⟨b, c, d, hb, hc, hd, hbc, hbd, hcd⟩ := Finset.two_lt_card_iff.1 ha
    exact ⟨a, b, c, d, by simpa using hb, by simpa using hc,
        by simpa using hd, hbc, hbd, hcd⟩
  · rintro ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd⟩
    use a
    change 2 < _ -- `rw` can't see that `2 < #s` is the same as `3 ≤ #s`
    rw [← card_neighborFinset_eq_degree, Finset.two_lt_card_iff]
    use b, c, d
    simp_all

/-!
The final exercises return to decidability, and give decidable adjacency instances
for the line graph and the `hasse` graph, both of which Mathlib is missing.

27. Give a decidable adjacency instance for the line graph `L[G]` of a graph on a
vertex type with decidable equality. Recall that the vertices of `L[G]` are the edges
of `G`, and that two of them are adjacent iff they are distinct and share a vertex
(`lineGraph_adj_iff_exists`).

(Hint: to decide whether two edges `e₁ e₂ : Sym2 V` share a vertex, use
`Sym2.recOnSubsingleton` to write them as `s(a, b)` and `s(c, d)`, and reduce to the
four equalities `a = c`, `a = d`, `b = c` and `b = d` with `decidable_of_iff`.
Recursion on `Sym2` is only allowed when the result cannot depend on the order of the
two endpoints; `recOnSubsingleton` ensures this by requiring the result to lie in a
`Subsingleton`, which `Decidable p` is.)
-/
/-- Decidability of the adjacency relation for the line graph -/
instance {V : Type*} (G : SimpleGraph V) [DecidableEq V] :
    DecidableRel L[G].Adj := by
  intro e₁ e₂
  -- Two edges share a vertex iff one of the four endpoint pairs is equal
  have : Decidable (∃ v ∈ (e₁ : Sym2 V), v ∈ (e₂ : Sym2 V)) :=
    Sym2.recOnSubsingleton (e₁ : Sym2 V) fun a b =>
      Sym2.recOnSubsingleton (e₂ : Sym2 V) fun c d =>
        decidable_of_iff (a = c ∨ a = d ∨ b = c ∨ b = d) (by aesop)
  exact decidable_of_iff' _ SimpleGraph.lineGraph_adj_iff_exists

example : L[C[5]].Adj ⟨s(0, 1), by decide⟩ ⟨s(1, 2), by decide⟩ := by decide

/-!
28. In a locally finite order `a ⋖ b` holds iff `a < b` and the interval
`Finset.Ioo a b` is empty, so the covering relation is decidable. Give the instance,
building it with `decidable_of_iff` rather than `rw` so that `decide` can still
reduce it.

Note `_root_.` puts the instance at `CovBy.decidableRel`, outside the `SimpleGraph`
namespace that we are working in, since it is about orders rather than graphs.
-/
/-- Decidability of the covering relation of a locally finite order -/
instance _root_.CovBy.decidableRel {α : Type*} [Preorder α] [DecidableEq α]
    [DecidableLT α] [LocallyFiniteOrder α] :
    DecidableRel ((· ⋖ ·) : α → α → Prop) := fun a b =>
  decidable_of_iff (a < b ∧ Finset.Ioo a b = ∅)
    (by simp [covBy_iff_Ioo_eq, ← Finset.coe_Ioo])

/-!
29. Show that the `hasse` graph of a preorder with a decidable covering relation has
decidable adjacency.
-/
/-- Decidability of the adjacency relation for the Hasse graph -/
instance hasseAdjDecidable (α : Type*) [Preorder α]
    [DecidableRel ((· ⋖ ·) : α → α → Prop)] :
    DecidableRel (hasse α).Adj := fun u v =>
  -- `hasse` is a def, so we tell Lean what its adjacency unfolds to; the `CovBy`
  -- instance assumed above then does the rest.
  inferInstanceAs (Decidable (u ⋖ v ∨ v ⋖ u))

/-! END SOLUTIONS -/


end SimpleGraph
