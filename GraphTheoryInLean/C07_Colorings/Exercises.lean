import GraphTheoryInLean.C07_Colorings.C07_Colorings
namespace SimpleGraph
open Finset
variable {V : Type*} {G : SimpleGraph V}

/-!
# Exercises

1. Show that the cycle graph `C[5]` is not 2-colourable.
-/
example : ¬ C[5].Colorable 2 := by
  sorry

/-!
2. Show that if `G` has an edge then `2 ≤ χ G`. Hint: the endpoints of an edge form
a clique, so you can use `IsClique.card_le_chromaticNumber`.
-/
example {u v : V} (h : G.Adj u v) : 2 ≤ χ G := by
  sorry

/-!
3. Show that a graph `G` on `n` vertices satisfies `n ≤ χ G * χ Gᶜ` . Hint: combine
`natCard_le_chromaticNumber_mul_indepNum` with `cliqueNum_compl`.
-/
example : Nat.card V ≤ χ G * χ Gᶜ := by
  sorry

/-!
4. Show that the chromatic number of the hypercube `Q[n + 1]` is `2`. Hint:
`chromaticNumber_eq_two_iff` reduces this to facts proved in this chapter.
-/
example (n : ℕ) : χ Q[n + 1] = 2 := by
  sorry

/-!
5. The Kneser graph `Kn[n, k]` is `(n - 2 * k + 2)`-colourable for `2 * k ≤ n` and
`0 < k`. (Recall `Kn[n, k]` is the graph whose vertices are the `k`-element subsets
of `Fin n = {0, ..., n - 1}` with edges between disjoint subsets. This is the easy
part of the Kneser–Lovász theorem.) The colouring is given below: colour a vertex by
its least element, merging all the large colours into one. Show that it is a proper
colouring. This is the hardest exercise in this chapter: the case where both
vertices receive the merged colour needs a pigeonhole argument which is in Mathlib as
`Finset.inter_nonempty_of_card_lt_card_add_card`.
-/
/-- The explicit `(n - 2 * k + 2)`-colouring of the Kneser graph `Kn[n, k]`. -/
def kneserColoring' (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
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
6. Show that if `0 < k`, `2 * k ≤ n` and `Kn[n, k]` is `m`-colourable then
`n ≤ k * m`, so that `χ Kn[n, k] ≥ n / k`. Hint: use
`Colorable.natCard_le_mul_indepNum` and the independence number of the Kneser graph,
`indepNum_kneserGraph`, from the previous chapter; `Nat.add_one_mul_choose_eq` will
help with the binomial coefficients.
-/
theorem le_mul_of_colorable_kneserGraph' {n k m : ℕ} (hk : 0 < k) (hn : 2 * k ≤ n)
    (h : Kn[n, k].Colorable m) : n ≤ k * m := by
  sorry

/-!
7. Use the previous two exercises to show that the Petersen graph `Kn[5, 2]` has
chromatic number `3`.
-/
example : χ Kn[5, 2] = 3 := by
  sorry

/-!
8. Prove the claim from the chapter that for `G : SimpleGraph ℕ` a vertex `v` has at
most `v` earlier neighbours.
-/
lemma degreeLT_le_self' (G : SimpleGraph ℕ) (v : ℕ) [Fintype (G.neighborLTSet v)] :
    G.degreeLT v ≤ v := by
  sorry

/-!
9. The *infinite star* `starNat` joins `0` to every other natural number. Since `0`
has infinitely many neighbours, `starNat` is not locally finite, so the bound
`colorable_of_degree_le_of_countable` does not apply. Show that it is nevertheless
`2`-colourable, using `colorable_of_degreeLT_le`: every vertex has at most one
earlier neighbour.
-/
/-- The infinite star on `ℕ`: the vertex `0` is adjacent to every other vertex. -/
abbrev starNat : SimpleGraph ℕ where
  Adj a b := (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0)

example : (starNat.neighborSet 0).Infinite ∧ starNat.Colorable 2 := by
  sorry

/-!
10. Show that the greedy colouring of the complete graph on `ℕ` colours vertex `n`
with colour `n`. (See `greedy_crownGraph_eq` for a similar proof using
`Nat.strong_induction_on`.)
-/
example (n : ℕ) : (⊤ : SimpleGraph ℕ).greedy n = n := by
  sorry

/-!
11. The two definitions of the encoded version of a graph `G : SimpleGraph V` with
`[Encodable V]` as a `SimpleGraph ℕ` are the same.
-/
example [Encodable V] {G : SimpleGraph V} : G.encode = G.encodeMap := by
  sorry

/-! SOLUTIONS -/

/-!
1. Show that the cycle graph `C[5]` is not 2-colourable.
-/
example : ¬ C[5].Colorable 2 := by
  rw [← chromaticNumber_le_iff_colorable,
    chromaticNumber_cycleGraph_of_odd 5 (by decide) (by decide)]
  decide

/-!
2. Show that if `G` has an edge then `2 ≤ χ G`. Hint: the endpoints of an edge form
a clique, so you can use `IsClique.card_le_chromaticNumber`.
-/
example {u v : V} (h : G.Adj u v) : 2 ≤ χ G := by
  classical
  have hc : G.IsClique ({u, v} : Finset V) := by simpa using fun _ => h
  simpa [card_pair h.ne] using hc.card_le_chromaticNumber

/-!
3. Show that a graph `G` on `n` vertices satisfies `n ≤ χ G * χ Gᶜ`. Hint: combine
`natCard_le_chromaticNumber_mul_indepNum` with `cliqueNum_compl`.
-/
example : Nat.card V ≤ χ G * χ Gᶜ :=
  -- an independent set of `G` is a clique of `Gᶜ`
  calc (Nat.card V : ℕ∞) ≤ χ G * ⍺ G := natCard_le_chromaticNumber_mul_indepNum
    _ = χ G * ω Gᶜ := by rw [cliqueNum_compl]
    _ ≤ χ G * χ Gᶜ := by gcongr; exact cliqueNum_le_chromaticNumber

/-!
4. Show that the chromatic number of the hypercube `Q[n + 1]` is `2`. Hint:
`chromaticNumber_eq_two_iff` reduces this to facts proved in this chapter.
-/
example (n : ℕ) : χ Q[n + 1] = 2 := by
  -- bipartiteness was proved in this chapter, so it only remains to show
  -- `Q[n + 1] ≠ ⊥` for which we need a vertex of `Q[n]` (each gives an edge in
  -- the next dimension)
  obtain ⟨v⟩ : Nonempty (HypercubeVert n) := inferInstance
  refine chromaticNumber_eq_two_iff.2 ⟨hypercube_isBipartite _,?_⟩
  exact  ne_bot_iff_exists_adj.2 ⟨(v, false), (v, true), by simp⟩

/-!
5. The Kneser graph `Kn[n, k]` is `(n - 2 * k + 2)`-colourable for `2 * k ≤ n` and
`0 < k`. (Recall `Kn[n, k]` is the graph whose vertices are the `k`-element subsets
of `Fin n = {0, ..., n - 1}` with edges between disjoint subsets. This is the easy
part of the Kneser–Lovász theorem.) The colouring is given below: colour a vertex by
its least element, merging all the large colours into one. Show that it is a proper
colouring. This is the hardest exercise in this chapter: the case where both
vertices receive the merged colour needs a pigeonhole argument which is in Mathlib as
`Finset.inter_nonempty_of_card_lt_card_add_card`.
-/
/-- The explicit `(n - 2 * k + 2)`-colouring of the Kneser graph `Kn[n, k]`. -/
def kneserColoring (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
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
    · grind -- impossible since the equal colours are not equal
    · grind -- impossible since the equal colours are not equal
    · push Not at h1 h3
      -- both `u` and `v` lie in `{n - 2 * k + 1, ..., n - 1}`, which has only
      -- `2 * k - 1` elements, so by the pigeonhole principle they meet
      let a : Fin n := ⟨n - 2 * k, by grind⟩
      have hsub (s : Finset (Fin n)) (hne : s.Nonempty)
          (hs : n - 2 * k < ↑(s.min' hne)) : s ⊆ Ioi a :=
        fun x hx => mem_Ioi.2 (hs.trans_le (min'_le _ x hx))
      refine not_disjoint_iff_nonempty_inter.2 ?_ hadj.1
      exact inter_nonempty_of_card_lt_card_add_card (hsub _ _ h1) (hsub _ _ h3)
        (by grind [Fin.card_Ioi, u.2, v.2])


/-!
6. Show that if `0 < k`, `2 * k ≤ n` and `Kn[n, k]` is `m`-colourable then
`n ≤ k * m`, so that `χ Kn[n, k] ≥ n / k`. Hint: use
`Colorable.natCard_le_mul_indepNum` and the independence number of the Kneser graph,
`indepNum_kneserGraph`, from the previous chapter; `Nat.add_one_mul_choose_eq` will
help with the binomial coefficients.
-/
theorem le_mul_of_colorable_kneserGraph {n k m : ℕ} (hk : 0 < k) (hn : 2 * k ≤ n)
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
7. Use the previous two exercises to show that the Petersen graph `Kn[5, 2]` has
chromatic number `3`.
-/
example : χ Kn[5, 2] = 3 :=
  -- `kneserColoring` uses `5 - 2 * 2 + 2 = 3` colours, and `2` colours would need
  -- `5 ≤ 2 * 2`
  chromaticNumber_eq_iff_colorable_not_colorable.2
    ⟨by simpa using (kneserColoring 5 2 (by norm_num) (by norm_num)).colorable,
     fun h => by
       simpa using le_mul_of_colorable_kneserGraph (by norm_num) (by norm_num) h⟩

/-!
8. Prove the claim from the chapter that for `G : SimpleGraph ℕ` a vertex `v` has at
most `v` earlier neighbours.
-/
lemma degreeLT_le_self (G : SimpleGraph ℕ) (v : ℕ) [Fintype (G.neighborLTSet v)] :
    G.degreeLT v ≤ v := by
  -- the earlier neighbours of `v` lie in `{0, 1, …, v - 1}`
  nth_rw 2 [← Finset.card_range v]
  apply Finset.card_le_card
  intro x hx; simp_all

/-!
9. The *infinite star* `starNat` joins `0` to every other natural number. Since `0`
has infinitely many neighbours, `starNat` is not locally finite, so the bound
`colorable_of_degree_le_of_countable` does not apply. Show that it is nevertheless
`2`-colourable, using `colorable_of_degreeLT_le`.
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
10. Show that the greedy colouring of the complete graph on `ℕ` colours vertex `n`
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
11. The two definitions of the encoded version of a graph `G : SimpleGraph V` with
`[Encodable V]` as a `SimpleGraph ℕ` are the same.
-/
example [Encodable V] {G : SimpleGraph V} : G.encode = G.encodeMap := by
  ext a b
  simp only [encode_adj, encodeMap_adj]
  constructor
  · intro h
    match hda : Encodable.decode₂ V a, hdb : Encodable.decode₂ V b with
    | some u, some v =>
        simp only [hda, hdb] at h
        rw [Encodable.decode₂_eq_some] at hda hdb
        have hab : a ≠ b := by
          rintro rfl
          rw [← hdb, Encodable.encode_inj] at hda
          exact h.ne hda
        exact ⟨hab, u, v, h, hda, hdb⟩
    | none, _ | _, none => grind
  · rintro ⟨h, u, v, hadj, rfl, rfl⟩
    simpa

/-! END SOLUTIONS -/

end SimpleGraph
