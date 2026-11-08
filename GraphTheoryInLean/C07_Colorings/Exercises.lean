/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import GraphTheoryInLean.C07_Colorings.C07_Colorings
namespace SimpleGraph
open Finset
variable {V : Type*} {G : SimpleGraph V}

/-!
# Exercises

1. Show that the cycle graph `C[5]` is not `2`-colourable. Hint:
`chromaticNumber_cycleGraph_of_odd`.
-/
example : ¬ C[5].Colorable 2 := by
  sorry

/-!
2. Show that a graph `G` on `n` vertices satisfies `n ≤ χ G * χ Gᶜ`. Hint: combine
`natCard_le_chromaticNumber_mul_indepNum` with `cliqueNum_compl` and
`cliqueNum_le_chromaticNumber`.
-/
example : Nat.card V ≤ χ G * χ Gᶜ := by
  sorry

/-!
3. Recall the Kneser graph `Kn[n, k]`: the graph whose vertices are the `k`-element
subsets of `Fin n = {0, ..., n - 1}` with edges between disjoint subsets. Show that
it has an `(n - 2 * k + 2)`-colouring for `2 * k ≤ n` and `0 < k`. The colouring is
given below: colour a vertex by its least element, merging all the large colours into
one. This is the hardest exercise in this chapter: the case where both vertices
receive the merged colour needs a pigeonhole argument, which is
`isIndepSet_kneserGraph_of_card_lt` from [Cliques](#chapter-cliques). Here `s.min' h`
is the least element of a nonempty finset `s`, and its basic properties are
`Finset.min'_mem` and `Finset.min'_le`.

[Figure: The colouring below for the Petersen graph $\mathrm{Kn}(5,2)$, with $5 - 2 \cdot 2 + 2 = 3$ colours: a vertex is red if its least element is $0$, blue if its least element is $1$, and green (the merged colour) otherwise](https://jt496.github.io/GraphTheoryInLean/figures/kneser_colouring.svg)
-/
/-- The `(n - 2 * k + 2)`-colouring of the Kneser graph `Kn[n, k]`. -/
def kneserGraph.coloring' (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
    Kn[n, k].Coloring (Fin (n - 2 * k + 2)) where
  toFun s :=
    -- A vertex is `s : Finset (Fin n)` of size `k`. Since `0 < k`, `s` is
    -- nonempty. We colour `s` by its minimum element `m`.
    let m : Fin n := s.val.min' (card_pos.mp (by rw [s.property]; exact hk))
    -- Minima below `n - 2 * k + 1` keep their own colour; every larger minimum
    -- shares the last colour `n - 2 * k + 1`.
    if h : m.val < n - 2 * k + 1 then
      ⟨m.val, by grind⟩
    else
      ⟨n - 2 * k + 1, by grind⟩
  map_rel' := by
    sorry

/-!
4. Show that if `2 * k ≤ n`, `0 < k` and `Kn[n, k]` is `m`-colourable then
`n ≤ k * m`, so that `n ≤ k * χ Kn[n, k]`. Hint: use
`Colorable.natCard_le_mul_indepNum` and the independence number of the Kneser graph,
`indepNum_kneserGraph`, from the previous chapter; `Nat.add_one_mul_choose_eq` will
help with the binomial coefficients.
-/
theorem le_mul_of_colorable_kneserGraph' {n k m : ℕ} (hn : 2 * k ≤ n) (hk : 0 < k)
    (h : Kn[n, k].Colorable m) : n ≤ k * m := by
  sorry

/-!
5. Use the previous two exercises to show that the Petersen graph `Kn[5, 2]` has
chromatic number `3`.
-/
example : χ Kn[5, 2] = 3 := by
  sorry

/-!
6. Show that the chromatic number of the hypercube `Q[n + 1]` is `2`. Hint:
`chromaticNumber_eq_two_iff` reduces this to facts proved in this chapter.
-/
example (n : ℕ) : χ Q[n + 1] = 2 := by
  sorry

/-!
7. Prove the claim from the chapter that for `G : SimpleGraph ℕ` a vertex `v` has at
most `v` earlier neighbours.
-/
lemma degreeLT_le_self' (G : SimpleGraph ℕ) (v : ℕ) [Fintype (G.neighborLTSet v)] :
    G.degreeLT v ≤ v := by
  sorry

/-!
8. Show that the greedy colouring really is greedy: if `k` is less than the greedy
colour of `v`, then some earlier neighbour of `v` has greedy colour `k`. Hint:
rewrite with `greedy_eq_greedyChoice` and use `Nat.find_min`.
-/
lemma exists_greedy_eq_of_lt_greedy' (G : SimpleGraph ℕ) [DecidableRel G.Adj]
    {v k : ℕ} (hk : k < G.greedy v) :
    ∃ u ∈ G.neighborLTFinset v, G.greedy u = k := by
  sorry

/-!
9. An ordering of the vertices of `G` is a *perfect elimination ordering* if the
earlier neighbours of every vertex form a clique. (For example, ordering the vertices
of an interval graph by the left endpoints of their intervals gives such an
ordering.) Show that if the natural ordering of `G` is a perfect elimination ordering
and `G` has no `(k + 1)`-clique then `G` is `k`-colourable, so that the greedy
colouring uses no more colours than the largest clique needs. Hint: `v` together with
its earlier neighbours forms a `(degreeLT v + 1)`-clique, so `CliqueFree.mono` bounds
`degreeLT v`; now use `colorable_of_degreeLT_le`.
-/
example (G : SimpleGraph ℕ) {k : ℕ}
    (hG : G.CliqueFree (k + 1)) (h : ∀ v, G.IsClique (G.neighborLTSet v)) :
    G.Colorable k := by
  sorry

/-!
10. Show that if the greedy colour of `v` is `k` then `G` contains an increasing path
`f 0 < f 1 < ⋯ < f k = v`, in which consecutive vertices are adjacent. (We describe
the path by a function `f : ℕ → ℕ`, since walks only appear in the next chapter.)
Hint: prove the statement for all `v` with `G.greedy v = k` by induction on `k`.
Exercise 8 gives the vertex `u` before `v`, and `Function.update f (k + 1) v`
extends the path `f` ending at `u`.
-/
lemma exists_increasing_path_greedy' (G : SimpleGraph ℕ) [DecidableRel G.Adj]
    (v : ℕ) : ∃ f : ℕ → ℕ, f (G.greedy v) = v ∧
      ∀ i < G.greedy v, f i < f (i + 1) ∧ G.Adj (f i) (f (i + 1)) := by
  sorry

/-!
11. Deduce that if `G` has no increasing path on `k + 1` vertices then `G` is
`k`-colourable. In particular, a graph in which no path has `k + 1` vertices is
`k`-colourable. Hint: as in `colorable_of_degreeLT_le`, use
`colorable_iff_exists_bdd_nat_coloring` with `greedyColoringNat`.
-/
example (G : SimpleGraph ℕ) {k : ℕ}
    (h : ¬ ∃ f : ℕ → ℕ, ∀ i < k, f i < f (i + 1) ∧ G.Adj (f i) (f (i + 1))) :
    G.Colorable k := by
  sorry

/-!
12. Show that the greedy colouring of the complete graph on `ℕ` colours vertex `n`
with colour `n`. (See `greedy_crownGraph_eq` for a similar proof using
`Nat.strong_induction_on`.)
-/
example (n : ℕ) : (⊤ : SimpleGraph ℕ).greedy n = n := by
  sorry

/-!
13. The *infinite star* `starNat` joins `0` to every other natural number. Show that
`0` has infinitely many neighbours, so that `starNat` is not locally finite and the
bound `colorable_of_degree_le_of_countable` does not apply, but that `starNat` is
nevertheless `2`-colourable, using `colorable_of_degreeLT_le`: every vertex has at
most one earlier neighbour.
-/
/-- The infinite star on `ℕ`: the vertex `0` is adjacent to every other vertex. -/
abbrev starNat : SimpleGraph ℕ where
  Adj a b := (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0)

example : (starNat.neighborSet 0).Infinite ∧ starNat.Colorable 2 := by
  sorry

/-!
14. The crown graph shows that a bad ordering of the vertices can make the greedy
colouring use arbitrarily many colours. Conversely, show that a good ordering makes
it optimal: if `C` is a colouring of `G` in which every vertex comes before all
neighbours of larger colour, then the greedy colour of each vertex `v` is at most
`C v`. Hint: use strong induction on `v` and `greedy_le_card_image`, showing that the
greedy colours of the earlier neighbours of `v` all lie in `range (C v)`.
-/
example (G : SimpleGraph ℕ) [DecidableRel G.Adj] (C : G.Coloring ℕ)
    (hC : ∀ u v, G.Adj u v → C u < C v → u < v) (v : ℕ) : G.greedy v ≤ C v := by
  sorry

/-! SOLUTIONS -/

/-!
1. Show that the cycle graph `C[5]` is not `2`-colourable. Hint:
`chromaticNumber_cycleGraph_of_odd`.
-/
example : ¬ C[5].Colorable 2 := by
  rw [← chromaticNumber_le_iff_colorable,
    chromaticNumber_cycleGraph_of_odd 5 (by decide) (by decide)]
  decide

/-!
2. Show that a graph `G` on `n` vertices satisfies `n ≤ χ G * χ Gᶜ`. Hint: combine
`natCard_le_chromaticNumber_mul_indepNum` with `cliqueNum_compl` and
`cliqueNum_le_chromaticNumber`.
-/
example : Nat.card V ≤ χ G * χ Gᶜ :=
  -- an independent set of `G` is a clique of `Gᶜ`
  calc (Nat.card V : ℕ∞) ≤ χ G * ⍺ G := natCard_le_chromaticNumber_mul_indepNum
    _ = χ G * ω Gᶜ := by rw [cliqueNum_compl]
    -- `gcongr` ("generalized congruence") proves an inequality between two terms of
    -- the same shape by comparing the parts that differ: since multiplication by
    -- `χ G` is monotone, it reduces the goal to `ω Gᶜ ≤ χ Gᶜ`
    _ ≤ χ G * χ Gᶜ := by gcongr; exact cliqueNum_le_chromaticNumber

/-!
3. Recall the Kneser graph `Kn[n, k]`: the graph whose vertices are the `k`-element
subsets of `Fin n = {0, ..., n - 1}` with edges between disjoint subsets. Show that
it has an `(n - 2 * k + 2)`-colouring for `2 * k ≤ n` and `0 < k`. The colouring is
given below: colour a vertex by its least element, merging all the large colours into
one. This is the hardest exercise in this chapter: the case where both vertices
receive the merged colour needs a pigeonhole argument, which is
`isIndepSet_kneserGraph_of_card_lt` from [Cliques](#chapter-cliques). Here `s.min' h`
is the least element of a nonempty finset `s`, and its basic properties are
`Finset.min'_mem` and `Finset.min'_le`.
-/
/-- The `(n - 2 * k + 2)`-colouring of the Kneser graph `Kn[n, k]`. -/
def kneserGraph.coloring (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
    Kn[n, k].Coloring (Fin (n - 2 * k + 2)) where
  toFun s :=
    -- A vertex is `s : Finset (Fin n)` of size `k`. Since `0 < k`, `s` is
    -- nonempty. We colour `s` by its minimum element `m`.
    let m : Fin n := s.val.min' (card_pos.mp (by rw [s.property]; exact hk))
    -- Minima below `n - 2 * k + 1` keep their own colour; every larger minimum
    -- shares the last colour `n - 2 * k + 1`.
    if h : m.val < n - 2 * k + 1 then
      ⟨m.val, by grind⟩
    else
      ⟨n - 2 * k + 1, by grind⟩
  map_rel' := by
    intro u v hadj hcolor
    simp only [kneserGraph_adj, ne_eq, Order.lt_add_one_iff] at hadj hcolor
    split_ifs at hcolor with h1 h2 h3
    · -- the colour is the common minimum of `u` and `v`, which are disjoint
      have hune : u.val.Nonempty := card_pos.mp (by rw [u.2]; exact hk)
      have hvne : v.val.Nonempty := card_pos.mp (by rw [v.2]; exact hk)
      have h : u.val.min' hune = v.val.min' hvne :=
        Fin.val_injective (by simpa using congrArg Fin.val hcolor)
      exact Finset.disjoint_left.mp hadj.1 (min'_mem _ hune) (h ▸ min'_mem _ hvne)
    · grind -- impossible: one colour is ≤ `n - 2 * k`, the other is `n - 2 * k + 1`
    · grind -- impossible: one colour is ≤ `n - 2 * k`, the other is `n - 2 * k + 1`
    · -- `push Not` pushes the negations inwards (`¬ a ≤ b` becomes `b < a`)
      push Not at h1 h3
      -- both `u` and `v` lie in `{n - 2 * k + 1, ..., n - 1}`, which has only
      -- `2 * k - 1` elements, so they lie in an independent set of `Kn[n, k]`
      -- (`isIndepSet_kneserGraph_of_card_lt` from the previous chapter)
      let a : Fin n := ⟨n - 2 * k, by grind⟩
      have hsub (s : Finset (Fin n)) (hne : s.Nonempty)
          (hs : n - 2 * k < ↑(s.min' hne)) : s ⊆ Ioi a :=
        fun x hx => mem_Ioi.2 (hs.trans_le (min'_le _ x hx))
      have hind := isIndepSet_kneserGraph_of_card_lt (k := k) (s := Ioi a)
        (by grind [Fin.card_Ioi])
      exact hind (hsub _ _ h1) (hsub _ _ h3) hadj.2 hadj

/-!
4. Show that if `2 * k ≤ n`, `0 < k` and `Kn[n, k]` is `m`-colourable then
`n ≤ k * m`, so that `n ≤ k * χ Kn[n, k]`. Hint: use
`Colorable.natCard_le_mul_indepNum` and the independence number of the Kneser graph,
`indepNum_kneserGraph`, from the previous chapter; `Nat.add_one_mul_choose_eq` will
help with the binomial coefficients.
-/
theorem le_mul_of_colorable_kneserGraph {n k m : ℕ} (hn : 2 * k ≤ n) (hk : 0 < k)
    (h : Kn[n, k].Colorable m) : n ≤ k * m := by
  have : NeZero k := ⟨hk.ne'⟩
  -- `Kn[n, k]` has `n.choose k` vertices and independence number
  -- `(n - 1).choose (k - 1)`
  have hcard := h.natCard_le_mul_indepNum
  have hkn : k ≤ n / 2 := by grind
  simp only [indepNum_kneserGraph, hkn, ↓reduceIte, Nat.card_eq_fintype_card,
    Fintype.card_finset_len, Fintype.card_fin] at hcard
  -- `n * (n - 1).choose (k - 1) = n.choose k * k`
  have key := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  rw [Nat.sub_add_cancel (by grind), Nat.sub_add_cancel hk] at key
  have hpos : 0 < (n - 1).choose (k - 1) := Nat.choose_pos (by grind)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc n * (n - 1).choose (k - 1) = k * n.choose k := by rw [key, mul_comm]
    _ ≤ k * (m * (n - 1).choose (k - 1)) := Nat.mul_le_mul_left k hcard
    _ = k * m * (n - 1).choose (k - 1) := by ring

/-!
5. Use the previous two exercises to show that the Petersen graph `Kn[5, 2]` has
chromatic number `3`.
-/
example : χ Kn[5, 2] = 3 :=
  -- `kneserGraph.coloring` uses `5 - 2 * 2 + 2 = 3` colours, and `2` colours would
  -- need `5 ≤ 2 * 2`
  chromaticNumber_eq_iff_colorable_not_colorable.2
    ⟨by simpa using (kneserGraph.coloring 5 2 (by norm_num) (by norm_num)).colorable,
     fun h => by
       simpa using le_mul_of_colorable_kneserGraph (by norm_num) (by norm_num) h⟩

/-!
6. Show that the chromatic number of the hypercube `Q[n + 1]` is `2`. Hint:
`chromaticNumber_eq_two_iff` reduces this to facts proved in this chapter.
-/
example (n : ℕ) : χ Q[n + 1] = 2 := by
  -- bipartiteness was proved in this chapter, so it only remains to show
  -- `Q[n + 1] ≠ ⊥` for which we need a vertex of `Q[n]` (each gives an edge in
  -- the next dimension)
  obtain ⟨v⟩ : Nonempty (HypercubeVert n) := inferInstance
  refine chromaticNumber_eq_two_iff.2 ⟨IsBipartite.hypercube _, ?_⟩
  exact ne_bot_iff_exists_adj.2 ⟨(v, false), (v, true), by simp⟩

/-!
7. Prove the claim from the chapter that for `G : SimpleGraph ℕ` a vertex `v` has at
most `v` earlier neighbours.
-/
lemma degreeLT_le_self (G : SimpleGraph ℕ) (v : ℕ) [Fintype (G.neighborLTSet v)] :
    G.degreeLT v ≤ v := by
  -- We want to change the 2nd occurrence of `v` to `#(range v)` in the goal,
  -- but `rw` will change all occurrences, so we use `nth_rw 2` below
  nth_rw 2 [← Finset.card_range v]
  apply Finset.card_le_card
  intro x hx; simp_all

/-!
8. Show that the greedy colouring really is greedy: if `k` is less than the greedy
colour of `v`, then some earlier neighbour of `v` has greedy colour `k`. Hint:
rewrite with `greedy_eq_greedyChoice` and use `Nat.find_min`.
-/
lemma exists_greedy_eq_of_lt_greedy (G : SimpleGraph ℕ) [DecidableRel G.Adj]
    {v k : ℕ} (hk : k < G.greedy v) :
    ∃ u ∈ G.neighborLTFinset v, G.greedy u = k := by
  rw [greedy_eq_greedyChoice] at hk
  -- `k` is below the least colour that no earlier neighbour uses, so one uses it
  simpa using not_not.mp <| Nat.find_min (Finset.exists_notMem _) hk

/-!
9. An ordering of the vertices of `G` is a *perfect elimination ordering* if the
earlier neighbours of every vertex form a clique. (For example, ordering the vertices
of an interval graph by the left endpoints of their intervals gives such an
ordering.) Show that if the natural ordering of `G` is a perfect elimination ordering
and `G` has no `(k + 1)`-clique then `G` is `k`-colourable, so that the greedy
colouring uses no more colours than the largest clique needs. Hint: `v` together with
its earlier neighbours forms a `(degreeLT v + 1)`-clique, so `CliqueFree.mono` bounds
`degreeLT v`; now use `colorable_of_degreeLT_le`.
-/
example (G : SimpleGraph ℕ) {k : ℕ}
    (hG : G.CliqueFree (k + 1)) (h : ∀ v, G.IsClique (G.neighborLTSet v)) :
    G.Colorable k := by
  classical
  have hdeg : ∀ v, G.degreeLT v + 1 ≤ k := by
    intro v
    by_contra! hlt
    -- `v` and its earlier neighbours form a `(degreeLT v + 1)`-clique
    have hcl : G.IsNClique (G.degreeLT v + 1) (insert v (G.neighborLTFinset v)) := by
      refine ⟨?_, ?_⟩
      · rw [coe_insert, neighborLTFinset, Set.coe_toFinset]
        refine (h v).insert fun u hu _ => ?_
        exact ((G.mem_neighborLTSet v u).1 hu).2
      · rw [card_insert_of_notMem (by simp), degreeLT]
    exact hG.mono hlt _ hcl
  -- so `k = Δ + 1`, where every vertex has at most `Δ` earlier neighbours
  obtain ⟨Δ, rfl⟩ : ∃ Δ, k = Δ + 1 := ⟨k - 1, by grind [hdeg 0]⟩
  exact G.colorable_of_degreeLT_le fun v => by grind [hdeg v]

/-!
10. Show that if the greedy colour of `v` is `k` then `G` contains an increasing path
`f 0 < f 1 < ⋯ < f k = v`, in which consecutive vertices are adjacent. (We describe
the path by a function `f : ℕ → ℕ`, since walks only appear in the next chapter.)
Hint: prove the statement for all `v` with `G.greedy v = k` by induction on `k`.
Exercise 8 gives the vertex `u` before `v`, and `Function.update f (k + 1) v`
extends the path `f` ending at `u`.
-/
lemma exists_increasing_path_greedy (G : SimpleGraph ℕ) [DecidableRel G.Adj]
    (v : ℕ) : ∃ f : ℕ → ℕ, f (G.greedy v) = v ∧
      ∀ i < G.greedy v, f i < f (i + 1) ∧ G.Adj (f i) (f (i + 1)) := by
  suffices ∀ k v, G.greedy v = k → ∃ f : ℕ → ℕ, f k = v ∧
      ∀ i < k, f i < f (i + 1) ∧ G.Adj (f i) (f (i + 1)) from this _ v rfl
  intro k
  induction k with
  | zero => exact fun v _ => ⟨fun _ => v, rfl, by simp⟩
  | succ k ih =>
    intro v hv
    -- an earlier neighbour `u` of `v` has colour `k`, so a path ends at `u`
    have hk : k < G.greedy v := by grind
    obtain ⟨u, hu, hgu⟩ := G.exists_greedy_eq_of_lt_greedy hk
    rw [mem_neighborLTFinset] at hu
    obtain ⟨f, hfk, hf⟩ := ih u hgu
    -- and we extend it by `v`
    refine ⟨Function.update f (k + 1) v, by simp, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · simpa [Function.update_of_ne (show i ≠ k + 1 by grind),
        Function.update_of_ne (show i + 1 ≠ k + 1 by grind)] using hf i hi
    · simpa [Function.update_of_ne (show i ≠ i + 1 by grind), hfk] using
        ⟨hu.1, hu.2.symm⟩

/-!
11. Deduce that if `G` has no increasing path on `k + 1` vertices then `G` is
`k`-colourable. In particular, a graph in which no path has `k + 1` vertices is
`k`-colourable. Hint: as in `colorable_of_degreeLT_le`, use
`colorable_iff_exists_bdd_nat_coloring` with `greedyColoringNat`.
-/
example (G : SimpleGraph ℕ) {k : ℕ}
    (h : ¬ ∃ f : ℕ → ℕ, ∀ i < k, f i < f (i + 1) ∧ G.Adj (f i) (f (i + 1))) :
    G.Colorable k := by
  classical
  refine (colorable_iff_exists_bdd_nat_coloring _).2
    ⟨G.greedyColoringNat, fun v => ?_⟩
  -- if `k ≤ greedy v` then the first `k + 1` vertices of the path ending at `v`
  -- contradict `h`
  by_contra! hk
  obtain ⟨f, -, hf⟩ := G.exists_increasing_path_greedy v
  exact h ⟨f, fun i hi => hf i (by grind [greedyColoringNat_apply])⟩

/-!
12. Show that the greedy colouring of the complete graph on `ℕ` colours vertex `n`
with colour `n`. (See `greedy_crownGraph_eq` for a similar proof using
`Nat.strong_induction_on`.)
-/
example (n : ℕ) : (⊤ : SimpleGraph ℕ).greedy n = n := by
  -- as in `greedy_crownGraph_eq` we use strong induction on `n`
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- the earlier neighbours of `n` are `{0, ..., n - 1}`, and by induction they use
  -- exactly the colours `{0, ..., n - 1}`
  refine (⊤ : SimpleGraph ℕ).greedy_eq_of_image_eq_range ?_
  ext c
  grind [mem_neighborLTFinset, top_adj]

/-!
13. The *infinite star* `starNat` joins `0` to every other natural number. Show that
`0` has infinitely many neighbours, so that `starNat` is not locally finite and the
bound `colorable_of_degree_le_of_countable` does not apply, but that `starNat` is
nevertheless `2`-colourable, using `colorable_of_degreeLT_le`: every vertex has at
most one earlier neighbour.
-/
example : (starNat.neighborSet 0).Infinite ∧ starNat.Colorable 2 := by
  refine ⟨Set.infinite_of_injective_forall_mem (f := Nat.succ) Nat.succ_injective
    (by simp), starNat.colorable_of_degreeLT_le (Δ := 1) fun v => ?_⟩
  -- the only earlier neighbour that a vertex can have is `0`
  rw [degreeLT, Finset.card_le_one]
  intro a ha b hb
  rw [mem_neighborLTFinset] at ha hb
  grind

/-!
14. The crown graph shows that a bad ordering of the vertices can make the greedy
colouring use arbitrarily many colours. Conversely, show that a good ordering makes
it optimal: if `C` is a colouring of `G` in which every vertex comes before all
neighbours of larger colour, then the greedy colour of each vertex `v` is at most
`C v`. Hint: use strong induction on `v` and `greedy_le_card_image`, showing that the
greedy colours of the earlier neighbours of `v` all lie in `range (C v)`.
-/
example (G : SimpleGraph ℕ) [DecidableRel G.Adj] (C : G.Coloring ℕ)
    (hC : ∀ u v, G.Adj u v → C u < C v → u < v) (v : ℕ) : G.greedy v ≤ C v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  refine (G.greedy_le_card_image v).trans ?_
  -- every earlier neighbour `u` of `v` has `greedy u ≤ C u < C v`
  have hsub : (G.neighborLTFinset v).image G.greedy ⊆ range (C v) := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hc
    rw [mem_neighborLTFinset] at hu
    have hne : C u ≠ C v := C.valid hu.2.symm
    have hle : ¬ C v < C u := fun h => (hC v u hu.2 h).not_gt hu.1
    exact mem_range.2 ((ih u hu.1).trans_lt (by grind))
  simpa using card_le_card hsub

/-! END SOLUTIONS -/

end SimpleGraph
