import GraphTheoryInLean.C04_Decidability_Finiteness_and_Degrees.C04_Decidability_Finiteness_and_Degrees
import GraphTheoryInLean.C05_Maps.Exercises
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Order.Closure
namespace SimpleGraph
/-!
Walks are a fundamental concept in graph theory. In this chapter we look at how they
are defined in Mathlib. We will consider operations on walks such as concatenation
(`append`) and reversal (`reverse`), as well as the `length` (number of edges) and
`support` (list of vertices visited) of walks. We then meet the kinds of walks that
arise most frequently in graph theory: trails, paths, circuits and cycles, together
with Eulerian trails and Hamiltonian paths and cycles. Along the way we show that a
graph is bipartite iff it has no odd cycle.

The type of a walk records its endpoints, and this makes some plumbing necessary that
has no counterpart in informal graph theory: `Walk.Nil`, `Walk.copy` and
`Walk.transfer`. We then map walks along graph homomorphisms, and return to our
running examples: Hamming paths and the Gray code in the hypercube, and walks in the
Mycielskian. Finally we look at Hamiltonian graphs: we define Pósa rotations and
prove the Bondy–Chvátal theorem, with Ore's and Dirac's theorems as corollaries.

# Constructing Walks

Informally a *walk* in a graph `G` is a sequence of adjacent vertices
`v₀, v₁, ..., vₖ`, so the obvious way to formalize a walk in a `SimpleGraph V` seems
to be as a `List V` together with a proof that consecutive vertices are adjacent.
You may like to try this and see how far you get: defining functions on such walks,
for example concatenation, is possible but painful. As we will see, Mathlib takes a
slightly different approach.

In Mathlib walks are defined as an inductive type that encodes the endpoints directly
in the type. So a walk is always a walk from `u` to `v` for some explicit `u` and
`v`. Such a walk in the graph `G` has type `G.Walk u v`. So `G.Walk` is not a single
type but a *family* of types, one for each pair of endpoints, and walks with
different endpoints live in different types. In many respects this is an advantage,
but it does mean that we sometimes need to deal with type mismatches that have no
counterpart in informal graph theory. We look at this in detail in
[Plumbing: Fixing Type Mismatches](https://jt496.github.io/GraphTheoryInLean/Walks/#section-plumbing-fixing-type-mismatches).

Notice also that `G.Walk u v` is a `Type`, not a `Prop`: two walks with the same
endpoints can be different, and we can compute with them. The proposition that there
is *some* walk from `u` to `v` is `G.Reachable u v`, which we meet in
[Reachability](https://jt496.github.io/GraphTheoryInLean/Walks/#section-reachability).
-/
open Walk
section basics
variable {V : Type*} {G : SimpleGraph V} {u v w : V}

#source Walk  -- inductive Walk : V → V → Type u
              --   | nil {u : V} : Walk u u
              --   | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
/-!
So we see that `SimpleGraph.Walk` has two constructors: `Walk.nil` and `Walk.cons`
(in this respect it is very similar to `List`, which may be worth reviewing if it is
unfamiliar).
-/
#source List

/-!
The `Walk.nil` constructor returns a walk consisting of a single vertex `u` with no
edges.
-/
#check Walk.nil  -- {G : SimpleGraph V} {u : V} : G.Walk u u
example : G.Walk u u := Walk.nil
/-!
Notice that the constructor `Walk.nil` takes no explicit arguments. Its implicit
arguments (namely `V, G` and `u`) are all determined by the type `G.Walk u u` of the
walk we are building.

The `Walk.cons` constructor takes an edge `h : G.Adj u v` and an existing walk
`p : G.Walk v w` and creates the walk `G.Walk u w` by adding the edge to the start of
the walk `p`.
-/
#check Walk.cons -- .. (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w

/-!
Recall the path graph we defined on `ℕ`.
-/
#source pathNat₁
/-!
We give some examples of walks in this graph below. Notice that we have to specify
very little: Lean can infer many of the details from the type of walk we are building
in each case.

First we have the `nil` walk from `7` to `7`. (We have opened the namespace `Walk` in
this chapter so we can use `nil` rather than `Walk.nil`.)
-/
example : pathNat₁.Walk 7 7 := nil
/-!
Here the vertex `7` was determined by the type of walk so is not an explicit argument
to the constructor `nil`.

In our next example we are building a walk from `2` to `3`, as a `cons h nil` walk.
So the implicit `u` input to `nil` is `3` and the single edge `h` must be
`G.Adj 2 3`, which Lean can infer (and simp can prove).
-/
example : pathNat₁.Walk 2 3 := cons (by simp) nil

/-!
In the next example we are building a `cons h₁ (cons h₂ nil)` walk from `3` to `5`,
so the first edge must be `h₁ : G.Adj 3 v` and the second edge must be
`h₂ : G.Adj v 5`, for some vertex `v`. We need to tell Lean what `v` is in at least
one case, but once we do this for the first edge the second edge is determined (again
the actual existence of both edges is easily proved by simp). There are a few ways to
do this; we show two below.

First we use type ascription notation `(by simp : ...)` which tells Lean what we want
to prove and then gets `simp` to prove it.
-/
example : pathNat₁.Walk 3 5 :=
  cons (by simp : (pathNat₁).Adj 3 4) <| cons (by simp) nil
/-!
Alternatively we can use a variant of the `cons` constructor called `cons'` that
takes the three vertices as explicit arguments. Notice the difference in the
signatures of `cons` and `cons'` below.
-/
#check cons   -- .. `{u v w : V}` (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w
#check cons'  -- .. `(u v w : V)` (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w

example : pathNat₁.Walk 3 5 := cons' _ 4 _ (by simp) <| cons (by simp) nil

/-!
Even though `cons'` takes 3 explicit vertex arguments, we actually only need to give
one of them explicitly, since the other two can be inferred from the type of walk we
are building and the edge we are using.

Of course a walk may have repeated edges or vertices. So we can build the following
walk from `3` to `5`, which we write informally as `3 — 2 — 3 — 4 — 5 — 6 — 5`.
-/
private def pathNat₁35 : pathNat₁.Walk 3 5 :=
  cons' _ 2 _ (by simp) <| cons' _ 3 _  (by simp) <| cons' _ 4 _ (by simp)
    <| cons' _ 5 _ (by simp) <| cons' _ 6 _ (by simp) <| cons (by simp) nil

/-!
The key advantage of defining walks as an inductive type (as opposed to as a `List V`
with proofs of adjacency of consecutive vertices) is that many things are simply
*correct by construction*. The inductive nature of the type allows for simple
inductive definitions and proofs.

For example, the concatenation of two walks `p₁` and `p₂` is only defined when the
walks are compatible: i.e. if `p₁` is a walk from `u` to `v` then `p₂` must be a walk
from `v` to some `w`, and the result is then automatically a walk from `u` to `w`.
-/
#check Walk.append  -- ... : G.Walk u v → G.Walk v w → G.Walk u w
#source Walk.append -- def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
                    --   | nil, q => q
                    --   | cons h p, q => cons h (p.append q)

/-!
The *length* of a walk is the number of edges it contains. Again this has a simple
inductive definition.
-/
#source Walk.length
/-!
The length of the meandering walk `pathNat₁35` defined above is `6`.
-/
#eval pathNat₁35.length  -- 6

/-!
Since `Walk.append` is defined inductively on its first argument, proofs involving
`append` will often follow by induction on this argument. For example:
-/
example (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil =>
    rw [add_comm]
    rfl
  | cons h p ih =>
    rw [cons_append, length_cons, ih, length_cons, add_right_comm]

/-!
Given two walks `p` and `q` and an edge `h` from the end of `p` to the start of `q`,
we can form a new walk, `p.append (q.cons h)`, which has length
`p.length + q.length + 1`.
-/
example {u v w z} {h : G.Adj v w} {p : G.Walk u v} {q : G.Walk w z} :
    (p.append <| q.cons h).length = p.length + q.length + 1 := by
  simp [add_assoc]

/-!
If we want to add an edge at the end of a walk rather than at the start, we can use
`concat` instead of `cons`.
-/
#source Walk.concat

/-!
To build a walk from `i` to `i + j` in `pathNat₁` we can use `concat` to define it
inductively on `j`.
-/
/-- The walk from `i` to `i + j` in `pathNat₁`. -/
def Walk.pathNat₁Walk (i j : ℕ) : pathNat₁.Walk i (i + j) :=
  match j with
  | 0 => nil
  | j + 1 => (pathNat₁Walk i j).concat (by grind)

/-!
The walk `pathNat₁Walk i j` has length `j` since it is built by
concatenating `j` edges.
-/
@[simp]
lemma Walk.length_pathNat₁Walk (i j : ℕ) : (pathNat₁Walk i j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pathNat₁Walk, length_concat, ih]

/-!
# Vertices and Edges of a Walk

A walk visits a sequence of vertices and traverses a sequence of edges, and Mathlib
records both as lists.

## Support and getVert

The *support* of a walk is the sequence of vertices it visits in order, as a
`List V`.
-/
#source Walk.support
/-!
A `nil` walk has length `0` and support `[u]`. So in particular every walk has at
least one vertex in its support. (Note that if walks were defined in terms of lists
of vertices then we would have to decide what to do with the empty list.)
-/
example : (Walk.nil : G.Walk u u).support = [u] := rfl

/-!
The support of a `cons` walk consists of the first vertex of the new edge followed by
the support of the rest of the walk. (Note the use of `List` notation here: `a :: l`
is the list with head `a` and tail `l`).
-/
example (h : G.Adj u v) (p : G.Walk v w) :
    (Walk.cons h p).support = u :: p.support := Walk.support_cons h p

/-!
A walk is determined by its support, so nothing is lost compared with the list-based
model we considered at the start of the chapter.
-/
#check Walk.ext_support -- (h : p.support = q.support) : p = q

/-!
The start and end vertices of a walk belong to its support. Results involving the
start and end of a walk use "start" and "end" in their names, but `Walk.start` and
`Walk.end` are not defined. (By design, if we have a walk `p : G.Walk u v` then `u`
and `v` are already available as part of the type of `p` so we don't need special
names for them.)
-/
#check Walk.start_mem_support  -- (p : G.Walk u v) : u ∈ p.support
#check Walk.end_mem_support    -- (p : G.Walk u v) : v ∈ p.support

/-!
The support of the walk `pathNat₁Walk i j` from `i` to `i + j` in `pathNat₁` is
`[i, i + 1, ..., i + j]`, which can be expressed as `List.range' i (j + 1)`.
-/
#check List.range'

@[simp]
lemma Walk.support_pathNat₁Walk (i j : ℕ) :
    (pathNat₁Walk i j).support = List.range' i (j + 1) := by
  induction j with
  | zero => simp [pathNat₁Walk]
  | succ n ih => simp [pathNat₁Walk, support_concat, ih, List.range'_1_concat]

/-!
The `i`-th vertex of a walk can be obtained with `getVert`.
-/
#source Walk.getVert

/-!
If `p : G.Walk u v` and `i ≤ p.length`, then `p.getVert i` is the `i`-th vertex in
the support of the walk.
-/
example (p : G.Walk u v) : p.getVert 0 = u := p.getVert_zero

example (i : ℕ) : (Walk.nil : G.Walk u u).getVert i = u := Walk.getVert_nil u

example (h : G.Adj u v) (p : G.Walk v w) : (Walk.cons h p).getVert 1 = v := by
  rw [getVert_cons_succ, getVert_zero]

/-!
Notice that `getVert i` is well-defined for any `i : ℕ`, rather than requiring us to
check that `i ≤ p.length`, it simply returns the end vertex if `p.length ≤ i`.
-/
example (p : G.Walk v w) : p.getVert (p.length + 100) = w :=
  p.getVert_of_length_le (by simp)

/-!
If `i < p.length` then `p.getVert i` and `p.getVert (i + 1)` are adjacent.
-/
example {i} {p : G.Walk u v} (hi : i < p.length) :
    G.Adj (p.getVert i) (p.getVert (i + 1)) := p.adj_getVert_succ hi

/-!
We have `snd` and `penultimate` as abbreviations for `p.getVert 1` and
`p.getVert (p.length - 1)` respectively.
-/
#source Walk.snd         -- p.getVert 1
#source Walk.penultimate -- p.getVert (p.length - 1)

/-!
## Darts and Edges

Although edges in a `SimpleGraph` are undirected, walks have a direction: from start
to end, so darts crop up very naturally when working with walks.

The *darts* of a walk refers to the `List (Dart G)` of darts the walk uses in order.
-/
#source Walk.darts
example (h : G.Adj u v) (p : G.Walk v w) :
    (Walk.cons h p).darts = ⟨(u, v), h⟩ :: p.darts := Walk.darts_cons h p

/-!
The second vertex of a dart in a walk is a vertex in the support of that walk.
-/
#check dart_snd_mem_support_of_mem_darts

/-!
The *edges* of a walk is the `List (Sym2 V)` of edges it uses in order. So the
`edges` of a walk `cons h p` is `h` as an edge followed by `p.edges`.
-/
#source Walk.edges
example (h : G.Adj u v) (p : G.Walk v w) :
  (Walk.cons h p).edges = s(u, v) :: p.edges := Walk.edges_cons h p

/-!
If we append two walks then the edges of the resulting walk are the edges of the
first walk followed by the edges of the second walk. (Note `++` below is
`List.append`.)
-/
example (p₁ : G.Walk u v) (p₂ : G.Walk v w) :
    (p₁.append p₂).edges = p₁.edges ++ p₂.edges := Walk.edges_append p₁ p₂

/-!
We can also view the edges of a walk as a set of edges via `Walk.edgeSet`.
-/
#source Walk.edgeSet -- {e | e ∈ p.edges}

/-!
# New Walks from Old

We already saw how to concatenate two walks with `append` and how to use `cons` and
`concat` to add edges at the start and end of a walk. There are also a number of
other ways to build new walks from old.

Since edges in a `SimpleGraph` are undirected, we can reverse a walk `p : G.Walk u v`
to get a walk `p' : G.Walk v u`.
-/
#check Walk.reverse --  (p : G.Walk u v) : G.Walk v u
/-!
The reversed walk has the same length as the original walk.
-/
example (p : G.Walk u v) : p.reverse.length = p.length := Walk.length_reverse p

/-!
Given a vertex `u` that appears in a walk `p : G.Walk v w`, we can split the walk at
the first occurrence of `u` to get walks from `v` to `u` and from `u` to `w`.
-/

#check Walk.takeUntil  -- (p : G.Walk v w) (u : V) : u ∈ p.support → G.Walk v u

#check Walk.dropUntil  -- (p : G.Walk v w) (u : V) : u ∈ p.support → G.Walk u w

/-!
These two walks can be concatenated to give back the original walk. (Note `++` is not
actually defined for walks but is just useful informal notation for `Walk.append`.)
-/
#check Walk.take_spec -- p.takeUntil u h ++ p.dropUntil u h = p

/-!
Given a closed walk `c₁ : G.Walk v v` and a vertex `u` in its support, we can rotate
the walk to get a new closed walk `c₂ : G.Walk u u` (built as
`dropUntil ++ takeUntil`).
-/
#check Walk.rotate  -- (c : G.Walk v v) (u : V) (h : u ∈ c.support) : G.Walk u u

example [DecidableEq V] (c : G.Walk v v) (h : u ∈ c.support) :
  c.rotate u h = (c.dropUntil u h).append (c.takeUntil u h) := rfl

/-!
Using `getVert` we can also decompose walks by taking or dropping the first `n`
edges, so that `p.take n` ends at the vertex `p.getVert n`.
-/
#check Walk.take --  (p : G.Walk u v) (n : ℕ) : G.Walk u (p.getVert n)
#check Walk.drop --  (p : G.Walk u v) (n : ℕ) : G.Walk (p.getVert n) v
#check Walk.append_take_drop_eq  -- p.take n ++ p.drop n = p
/-!
Special cases of these include `tail` and `dropLast`.
-/
#check Walk.tail -- (p : G.Walk u v) : G.Walk p.snd v
#check Walk.dropLast -- (p : G.Walk u v) : G.Walk u p.penultimate

/-!
Notice that all of the walks defined using `getVert` have `p.getVert n` or similar in
their type so, when there is a choice, the `takeUntil`, `dropUntil` or `rotate` walks
may be easier to work with. A vertex such as `p.getVert n` is often only
*propositionally* (not definitionally) equal to the vertex we want, and the resulting
type mismatches are the subject of
[Plumbing: Fixing Type Mismatches](https://jt496.github.io/GraphTheoryInLean/Walks/#section-plumbing-fixing-type-mismatches).
-/

/-!
# Trails, Paths, Circuits and Cycles

There are a number of important special kinds of walks, such as paths, cycles, trails
and circuits, that crop up frequently in graph theory. Most of the common ones are
defined in Mathlib. We gather a summary of these below.

| Name  | Property | Mathlib |
|---|---|---|
| Trail | no repeated *edges* |`Walk.IsTrail` |
| Path | no repeated *vertices* | `Walk.IsPath` |
| Circuit | non-nil closed trail | `Walk.IsCircuit` |
| Cycle | circuit with no repeated vertex in its support's tail | `Walk.IsCycle` |
| Eulerian | trail using every edge of the graph | `Walk.IsEulerian` |
| Hamiltonian | path visiting every vertex of the graph | `Walk.IsHamiltonian` |
| Hamiltonian cycle | cycle visiting every vertex | `Walk.IsHamiltonianCycle` |
-/

/-!
## Trails and Paths

Recall that `List.Nodup` means that a list has no duplicated elements i.e. its
elements are pairwise distinct.
-/
#source List.Nodup -- def Nodup : List α → Prop := Pairwise (· ≠ ·)
/-!
A trail is a walk without duplicated edges.
-/
example (p : G.Walk u v) : p.IsTrail ↔ p.edges.Nodup := isTrail_def p
/-!
A path is a walk without duplicated vertices. Although the proof below is
`isPath_def`, if you look at the definition of `IsPath` you will see it
`extends IsTrail` so its default constructor asks for proofs of both `edges.Nodup`
and `support.Nodup`. But since a proof that there are no duplicate vertices in the
support trivially implies there are no duplicate edges, the `edges.Nodup` part of the
definition is redundant. For this reason we use the `IsPath.mk'` constructor when
proving that a walk is a path.
-/
example (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup := isPath_def p

#check IsPath.mk' -- easier to use than the default constructor `IsPath.mk`

/-!
[Figure: A trail that is not a path, and a path, in the same graph](https://jt496.github.io/GraphTheoryInLean/figures/trail_vs_path.svg)
-/

/-!
Any path is a trail.
-/
#check IsPath.isTrail   -- Walk.IsPath.isTrail : p.IsPath → p.IsTrail

/-!
If `p` is a path then so is `p.reverse`.
-/
example (p : G.Walk u v) (hp : p.IsPath) : p.reverse.IsPath := hp.reverse
/-!
If `p` is a path then the following subwalks of `p` are also paths.
-/
#check IsPath.takeUntil -- (p.takeUntil u h).IsPath
#check IsPath.dropUntil -- (p.dropUntil u h).IsPath
#check IsPath.take      -- (p.take n).IsPath
#check IsPath.drop      -- (p.drop n).IsPath

/-!
If `h : G.Adj u v` then a walk `cons h p` is a path iff `p` is a path that does not
visit `u`.
-/
#check cons_isPath_iff  --  (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support

/-!
If `p` is a path from `u` to `v` and it contains an edge `s(u, w)` then `w` is the
second vertex of `p`.
-/
#check IsPath.eq_snd_of_mem_edges

/-!
If we join two vertex-disjoint paths using an edge then we get a path. (We will need
this result a couple of times later in this chapter.)
-/
theorem Walk.IsPath.append_cons {u v w z} {h : G.Adj v w} {p : G.Walk u v}
    {q : G.Walk w z} (hp : p.IsPath) (hq : q.IsPath)
    (hd : (p.support).Disjoint q.support) : (p.append <| q.cons h).IsPath := by
  apply IsPath.mk'
  rw [support_append, support_cons, List.tail_cons, List.nodup_append']
  exact ⟨hp.support_nodup, hq.support_nodup, hd⟩

/-!
The walk from `i` to `i + j` in `pathNat₁` is a path.
-/
lemma Walk.isPath_pathNat₁Walk (i j : ℕ) : (pathNat₁Walk i j).IsPath := by
  induction j with
  | zero => exact IsPath.nil
  | succ n ih => exact (isPath_concat _).2 ⟨ih, by simp⟩

/-!
A walk is a path iff `getVert` is injective on the set `{i | i ≤ p.length}`.
-/
#check IsPath.getVert_injOn_iff

/-!
If there is a walk from `u` to `v` in a graph `G`, then there is a path from `u` to
`v`. Informally we might prove this by taking a shortest walk and proving that it is
a path. In Mathlib given any walk `p : G.Walk u v` we can get a path from `u` to `v`
using `Walk.bypass`. Note that this need not be a shortest path; it is simply the
walk constructed from `p` by removing closed subwalks between repeated vertices.

[Figure: `Walk.bypass` removes closed subwalks to produce a path](https://jt496.github.io/GraphTheoryInLean/figures/walk_bypass.svg)
-/
#source Walk.bypass
/-!
This returns a walk from `u` to `v` that is a path.
-/
#check Walk.bypass_isPath
/-!
Recall our meandering walk `pathNat₁35` from `3` to `5` in `pathNat₁`.
-/
#eval pathNat₁35.support        -- [3, 2, 3, 4, 5, 6, 5]
#eval pathNat₁35.bypass.support -- [3, 4, 5]

/-!
## Reachability

As we noted at the start of the chapter, `G.Walk u v` is a type rather than a
proposition. The proposition that there is *some* walk from `u` to `v` is
`G.Reachable u v`.
-/
#source Reachable -- def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)

/-!
Reachability is an equivalence relation.
-/
example : G.Reachable u u := Reachable.refl u
example (h : G.Reachable u v) : G.Reachable v u := h.symm
example (h : G.Reachable u v) (h' : G.Reachable v w) : G.Reachable u w := h.trans h'

/-!
Adjacent vertices are reachable from each other.
-/
example (h : G.Adj u v) : G.Reachable u v := h.reachable

/-!
Since `Walk.bypass` turns any walk into a path, there is a path between any two
reachable vertices.
-/
#check Reachable.exists_isPath

/-!
We study reachability and connectivity in detail in
[Connectivity](https://jt496.github.io/GraphTheoryInLean/Connectivity/#chapter-connectivity).
-/

/-!
## Circuits and Cycles

A *circuit* is a closed trail `p` (i.e. a walk from a vertex to itself without
repeated edges) that is not `nil`.
-/
#source Walk.IsCircuit -- Prop extends isTrail : IsTrail p where
                       --               ne_nil : p ≠ nil
/-!
A cycle is defined in Mathlib as a circuit in which the `tail` of its `support` has
no repeated vertices.
-/
#source Walk.IsCycle  -- Prop extends isCircuit : IsCircuit p where
                      --          support_nodup : p.support.tail.Nodup
/-!
[Figure: A circuit that is not a cycle, and a cycle, in the same graph](https://jt496.github.io/GraphTheoryInLean/figures/circuit_vs_cycle.svg)
-/

/-!
Any cycle is a circuit.
-/
example (c : G.Walk u u) (hc : c.IsCycle) : c.IsCircuit := hc.isCircuit

/-!
Since a cycle is a circuit, it is not equal to `nil`.
-/
example (c : G.Walk u u) (hc : c.IsCycle) : c ≠ nil := hc.isCircuit.ne_nil

/-!
There is a `3`-cycle in the complete graph `K[4]`.
-/
example : ∃ (c₃ : K[4].Walk 0 0), c₃.IsCycle ∧ c₃.length = 3 := by
  let c₃: K[4].Walk 0 0 := cons' 0 1 _ (by decide) <|
            cons (by decide) <| cons' 2 0 _ (by decide) nil
  exact ⟨c₃, by simp [c₃, isCycle_def, isTrail_def]⟩

/-!
The cycle `c₃` defined above and pictured below is `cons` applied three times: it
follows the edges `0 — 1`, `1 — 2` and `2 — 0`, so it is the cycle `0 1 2 0`. The
remaining vertex `3` of `K[4]` is not used.

[Figure: The 3-cycle 0 1 2 0 in the complete graph $K_4$](https://jt496.github.io/GraphTheoryInLean/figures/k4_3cycle.svg)
-/

/-!
A closed walk is a cycle if and only if it has length at least 3 and its tail is a
path.
-/
#check isCycle_iff_isPath_tail_and_le_length
/-!
If `c` is a cycle then `getVert` is injective on `{i | 1 ≤ i ∧ i ≤ c.length}`.
-/
#check IsCycle.getVert_injOn

/-!
So when is a `cons h p` walk a cycle? Clearly we need `p` to be a path, and also `h`
must be the adjacency from the end of `p` to the start of `p` (otherwise the new walk
is not closed). Given these two hypotheses, how could `cons h p` fail to be a cycle?
Well, we certainly have `(cons h p).support.tail.Nodup` since this is just
`p.support.Nodup` and `p` is a path. Also a `cons` walk is never `nil`. So the
failure must be that while `p` is a trail, `cons h p` is not a trail. This can only
happen if the edge corresponding to `h` is already present. Mathlib has this as
`cons_isCycle_iff`.
-/
#check cons_isCycle_iff --  (cons h p).IsCycle ↔ p.IsPath ∧ s(u, v) ∉ p.edges
/-!
In fact the only way that the path `p` could already contain this edge is if `p` is
the walk consisting of the single edge `h.symm`. This gives the following variant of
`cons_isCycle_iff`, which we will need later: `cons h p` is a cycle iff `p` is a path
of length not equal to 1. (The `simp only` call in the proof uses `tail_cons` and
`isPath_copy`, which involve `Walk.copy`: see
[Copy](https://jt496.github.io/GraphTheoryInLean/Walks/#section-copy).)
-/
theorem Walk.cons_isCycle_iff_length_ne_one {u v : V} (p : G.Walk v u)
    (h : G.Adj u v) : (cons h p).IsCycle ↔ p.IsPath ∧ p.length ≠ 1 := by
  have h0 : p.length ≠ 0 := fun h0 => h.ne (p.eq_of_length_eq_zero h0).symm
  simp only [isCycle_iff_isPath_tail_and_le_length, getVert_cons_succ, tail_cons,
    isPath_copy, length_cons, Nat.reduceLeDiff, ne_eq, and_congr_right_iff]
  grind

/-!
## Odd Cycles and Bipartite Graphs

Mathlib contains the following result saying that a graph is bipartite iff every
closed walk has even length.
-/
#check two_colorable_iff_forall_loop_even
  -- G.Colorable 2 ↔ ∀ u (w : G.Walk u u), Even w.length
/-!
However we would really like the stronger result about cycles rather than closed
walks: a graph is bipartite iff it contains no odd cycle. One direction is immediate,
since a cycle is a closed walk. For the other we need to show that a closed walk of
odd length contains a cycle of odd length. This is not currently in Mathlib.

A key step is `Walk.cons_isCycle_iff_length_ne_one`, which we have just proved: a
path closed up by an edge is a cycle, unless the path is just that edge.

We show first that any walk can be replaced by a path between the same endpoints
whose length has the same parity, unless the graph has an odd cycle. The proof is by
induction on the walk, mimicking `Walk.bypass`
([Trails and Paths](https://jt496.github.io/GraphTheoryInLean/Walks/#section-trails-and-paths))
while keeping track of parity. Given an edge `h : G.Adj a d` and a path `q` from `d`
to `b` with the same parity as the rest of the walk, either `a` is not on `q` and
`cons h q` is a path of the correct parity, or we split `q` at `a`. In this second
case `Walk.bypass` would discard the closed walk `cons h (q.takeUntil a)` and keep
`q.dropUntil a`. This preserves parity only if the closed walk has even length; if it
has odd length then it is an odd cycle.

[Figure: Left: skipping an even detour leaves a path from $a$ to $b$ of the same parity. Right: an odd detour is an odd cycle](https://jt496.github.io/GraphTheoryInLean/figures/odd_cycle_bypass.svg)
-/
#source Walk.bypass

lemma Walk.exists_isPath_or_odd_isCycle {a b : V} (p : G.Walk a b) :
    (∃ q : G.Walk a b, q.IsPath ∧ (Even q.length ↔ Even p.length)) ∨
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length := by
  classical
  induction p with
  | nil => exact .inl ⟨nil, .nil, Iff.rfl⟩
  | @cons a d b h p ih =>
    rcases ih with ⟨q, hq, hpar⟩ | hodd
    · by_cases ha : a ∈ q.support
      · have hlen := length_append _ _  ▸ congrArg length (q.take_spec ha)
        rcases Nat.even_or_odd (q.takeUntil a ha).length with he | ho
        · exact .inr ⟨a, cons h (q.takeUntil a ha),
            (cons_isCycle_iff_length_ne_one _ h).mpr ⟨hq.takeUntil ha, by grind⟩,
            by simp_all⟩
        · exact .inl ⟨q.dropUntil a ha, hq.dropUntil ha, by grind [length_cons]⟩
      · exact .inl ⟨cons h q, hq.cons ha, by grind [length_cons]⟩
    · exact .inr hodd

/-!
Now an odd closed walk `cons h p` contains an odd cycle: either the previous lemma
finds one directly, or it replaces `p` by a path `q` of even length, and then
`cons h q` is an odd cycle.
-/
theorem Walk.exists_odd_isCycle {u : V} (w : G.Walk u u) (hw : Odd w.length) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length := by
  cases w with
  | nil => simp at hw
  | cons h p =>
    refine p.exists_isPath_or_odd_isCycle.elim (fun ⟨q, hq, hpar⟩ => ?_) id
    have hqe : Even q.length := by grind [length_cons]
    exact ⟨_, cons h q, (cons_isCycle_iff_length_ne_one _ h).mpr ⟨hq, by grind⟩,
      by grind [length_cons]⟩

/-!
Hence a graph is bipartite iff it has no odd cycle.
-/
theorem isBipartite_iff_forall_isCycle_even :
    G.IsBipartite ↔ ∀ u (c : G.Walk u u), c.IsCycle → Even c.length := by
  refine ⟨fun h u c _ => two_colorable_iff_forall_loop_even.mp h u c, fun h => ?_⟩
  refine two_colorable_iff_forall_loop_even.mpr fun u w => ?_
  by_contra hw
  obtain ⟨v, c, hc, hodd⟩ := w.exists_odd_isCycle (Nat.not_even_iff_odd.mp hw)
  exact Nat.not_even_iff_odd.mpr hodd (h v c hc)

/-!
## Eulerian Trails

An *Eulerian trail* is a walk using every edge of the graph exactly once.
-/

#source Walk.IsEulerian
/-!
An Eulerian trail is a trail.
-/
#check Walk.IsEulerian.isTrail
/-!
A walk is Eulerian iff it is a trail that uses every edge of the graph.
-/
#check Walk.isEulerian_iff -- p.IsEulerian ↔ p.IsTrail ∧ ∀ e ∈ G.edgeSet, e ∈ p.edges

/-!
Whether a given walk is Eulerian is decidable. We do not need `Fintype V`: the naive
`∀ e, e ∈ G.edgeSet → …` quantifies over all of `Sym2 V`, but `isEulerian_iff` lets
us restrict it to `G.edgeFinset`, so only `Fintype G.edgeSet` is required (an
infinite graph can still have finitely many edges).
-/
/-- `Walk.IsEulerian` is decidable for walks in graphs with finitely many edges. -/
instance [DecidableEq V] [Fintype G.edgeSet] {p : G.Walk u v} :
    Decidable p.IsEulerian :=
  decidable_of_iff (p.edges.Nodup ∧ ∀ e ∈ G.edgeFinset, e ∈ p.edges) <| by
    simp [isEulerian_iff, isTrail_def]

/-!
For a given Eulerian trail in a graph with finitely many edges, we can now use
`decide` to prove that it `IsEulerian`. For example the walk `0 1 2 3 4 0 2 4 1 3 0`
traverses each of the ten edges of `K[5]` exactly once.
-/
private def eulerK5 : K[5].Walk 0 0 :=
  cons' _ 1 _ (by decide) <| cons (by decide) <|
  cons' 2 3 _ (by decide) <| cons (by decide) <|
  cons' 4 0 _ (by decide) <| cons (by decide) <|
  cons' 2 4 _ (by decide) <| cons (by decide) <|
  cons' 1 3 _ (by decide) <| cons (by decide) nil

/-!
And `decide` confirms that this walk is indeed Eulerian.
-/
example : eulerK5.IsEulerian := by decide

/-!
Beware that `IsEulerian` is a property of walks, not of graphs, and that it
constrains only the edges. An Eulerian trail never reaches an isolated vertex, so a
graph with an Eulerian trail need not be connected: a non-nil Eulerian trail visits
exactly the vertices that are not isolated.
-/
#check Walk.IsEulerian.mem_support_iff -- w ∈ p.support ↔ ¬G.IsIsolated w

/-!
At the other extreme, the `nil` walk at a vertex is Eulerian iff `G` has no
non-isolated vertices, that is, when `G` is edgeless.
-/
lemma Walk.isEulerian_nil_iff [DecidableEq V] (u : V) :
    (nil : G.Walk u u).IsEulerian ↔ G.support = ∅ := by
  rw [support_eq_bot_iff]
  refine ⟨fun h => h.nil_iff.mp Nil.nil, ?_⟩
  rintro rfl
  exact isEulerian_of_bot _

/-!
Currently Mathlib does not contain a characterization of graphs that admit Eulerian
trails, but it does have the necessary condition for graphs on a finite vertex set:
if `p` is an Eulerian trail in `G`, then every vertex of `G` has even degree, except
possibly the endpoints, which have even degree iff they are equal.
-/
#check Walk.IsEulerian.even_degree_iff
/-!
In a form more familiar to graph theorists: a graph with an Eulerian trail has either
no vertices of odd degree or exactly two.
-/
#check Walk.IsEulerian.card_odd_degree
/-!
The `Fintype V` assumption in this last result is overkill. Any Eulerian trail comes
with a proof that the edge set of the graph is finite: the walk itself is that
proof!
-/
#check Walk.IsEulerian.fintypeEdgeSet
/-!
Using this we can replace the `Fintype V` assumption with `Fintype (G.neighborSet x)`
which is needed in order to state the result in terms of degrees.
-/
theorem Walk.IsEulerian.even_degree_iff' {x u v : V} {p : G.Walk u v} [DecidableEq V]
    [Fintype (G.neighborSet x)] (h : p.IsEulerian) :
    Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  have := h.fintypeEdgeSet
  simp [← h.isTrail.even_countP_edges_iff, ← Multiset.coe_countP,
    Multiset.countP_eq_card_filter, ← card_incidenceFinset_eq_degree,
    incidenceFinset_eq_filter, ← h.edgesFinset_eq, Finset.card_def]

/-!
So every vertex of a graph with an Eulerian circuit has even degree.
-/
example {x u : V} {p : G.Walk u u} [DecidableEq V] [Fintype (G.neighborSet x)]
    (h : p.IsEulerian) : Even (G.degree x) := by
  simp [h.even_degree_iff']

/-!
We will revisit the more interesting question of which graphs admit Eulerian trails
in
[Eulerian Circuits and Trails](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-eulerian-circuits-and-trails).
-/
/-!
## Hamiltonian Paths and Cycles

A *Hamiltonian path* is a walk that visits every vertex of the graph exactly once.
-/
#source Walk.IsHamiltonian

/-!
Notice that `IsHamiltonian` is defined using `List.count`, and counting the
occurrences of a vertex in a list needs to decide whether two vertices are equal.
This is why `[DecidableEq V]` appears in almost every statement about Hamiltonian
walks below.

A Hamiltonian walk is a path. (Notice that this is a theorem, not part of the
definition.)
-/
#check Walk.IsHamiltonian.isPath
/-!
A path is Hamiltonian iff it contains every vertex of the graph.
-/
#check Walk.IsPath.isHamiltonian_iff
/-!
The length of a Hamiltonian path is exactly one less than the number of vertices in
the graph.
-/
example [Fintype V] [DecidableEq V] (p : G.Walk u v) (hp : p.IsHamiltonian) :
    p.length = Fintype.card V - 1 := hp.length_eq

/-!
A walk is a finite object: its support is a list. So in the same way that an
Eulerian trail in a graph provides a `Fintype` instance for its edge set, a
Hamiltonian path provides a `Fintype` instance for the vertex set (provided we also
have `DecidableEq V`).
-/
#source Walk.IsHamiltonian.fintype

/-!
A Hamiltonian *cycle* is a cycle containing every vertex of the graph. In Mathlib
this is defined as a cycle whose tail is a Hamiltonian path.
-/
#source Walk.IsHamiltonianCycle -- structure IsHamiltonianCycle (p : G.Walk a a) :
                                --      Prop extends p.IsCycle where
                                --   isHamiltonian_tail : p.tail.IsHamiltonian
/-!
The figure below shows a Hamiltonian path and a Hamiltonian cycle on the same
five-vertex graph. Both visit every vertex, but, just as for any path or cycle, they
need not use every edge: the grey chords are left untraversed (contrast this with an
Eulerian trail, which must use every edge).

[Figure: A Hamiltonian path and a Hamiltonian cycle on the same graph](https://jt496.github.io/GraphTheoryInLean/figures/hamiltonian.svg)
-/
/-!
A rotation of a walk is a Hamiltonian cycle iff the walk is a Hamiltonian cycle.
-/
#check Walk.isHamiltonianCycle_rotate

/-!
Mathlib also has the `SimpleGraph.IsHamiltonian` predicate, which is a property of
finite graphs rather than walks. A graph on a finite vertex set is *Hamiltonian* if
it contains a Hamiltonian cycle or is a single vertex.
-/
#source SimpleGraph.IsHamiltonian -- def IsHamiltonian (G : SimpleGraph α) : Prop :=
                                  --   Fintype.card α ≠ 1 →
                                  --     ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle

/-!
# Plumbing: Fixing Type Mismatches

The topics we will cover in this section don't appear in informal graph theory, but
they are vital when working with walks in Lean. The common theme they share is that
they allow us to fix type mismatches.

All of these mismatches come from the difference between definitional and
propositional equality, which we met in
[Definitional and Propositional Equalities](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/#section-definitional-and-propositional-equalities):
for a variable `n : ℕ`, `n + 0` computes to `n`, so the two are defeq, while `0 + n`
is stuck on the variable `n` and is only propositionally equal to `n`. Lean
identifies two types when they are defeq, but not when they are merely
propositionally equal. So a walk of type `G.Walk u (n + 0)` is also a walk of type
`G.Walk u n`, but a walk of type `G.Walk u (0 + n)` is not.
-/
example {G : SimpleGraph ℕ} {u n : ℕ} (p : G.Walk u (n + 0)) : G.Walk u n := p

/-- error: Type mismatch
  p
has type
  G.Walk u (0 + n)
but is expected to have type
  G.Walk u n -/
#guard_msgs (substring := true) in
example {G : SimpleGraph ℕ} {u n : ℕ} (p : G.Walk u (0 + n)) : G.Walk u n := p
/-!
## Nil

As we noted at the start of this chapter, the type of a walk encodes its endpoints.
We have already seen examples of how this allows for "correct by construction"
definitions (such as `Walk.append`), but it also has a cost. Simply stating the
proposition that two walks `p : G.Walk u v` and `q : G.Walk x y` are equal is only
possible if they have precisely the same endpoints. This kind of problem arises
frequently when working with *dependent types* such as `G.Walk u v`, which depend on
values (here the endpoints).

We first deal with the special case when one of the walks is `nil`, before turning to
the more general problem of endpoint mismatches with `Walk.copy`.

There are two natural ways to state a result about non-nil walks, i.e. walks that
have at least one edge. The first is to make the `cons` constructor explicit in the
statement of the result.
-/
example (h : G.Adj u v) (p : G.Walk v w) : 0 < (p.cons h).length := by
  simp

/-!
But this is not always convenient: it forces any caller of this result to have an
explicit `cons h p` walk, whereas often we have some opaque walk `q` which we know is
not `nil`, but whose first edge we don't know.

The second is to hypothesize that the walk is not `nil`. This is potentially
problematic: if the result is about a walk `p : G.Walk v w` then `p ≠ nil` does not
type-check since `nil` has type `G.Walk u u` for some `u`.
-/
/-- error: Type mismatch
  nil
has type
  Walk ?m.3 ?m.4 ?m.4
but is expected to have type
  G.Walk v w -/
#guard_msgs (substring := true) in
example (p : G.Walk v w) (h : p ≠ nil) : 0 < p.length := by sorry
/-!
The solution is to use the predicate `¬ p.Nil` instead.
-/
#source Walk.Nil -- inductive Nil : {v w : V} → G.Walk v w → Prop
                 --   | nil {u : V} : Nil (nil : G.Walk u u)
/-!
To understand how this all works, read on. Otherwise feel free to skip to the next
subsection [Copy](https://jt496.github.io/GraphTheoryInLean/Walks/#section-copy).

Recall that `Walk` is an inductive type with two constructors: `nil` (whose type
forces its two endpoints to coincide) and `cons` (which does not). Now suppose we
have a walk `p : G.Walk v w` and we try the naive test `p = nil`. For this equation
to type-check, Lean must unify the type of `nil`, namely `G.Walk u u`, with the type
of `p`, namely `G.Walk v w`, which forces `v` and `w` to be *defeq*. So `p = nil`
cannot even be *stated* unless `v` and `w` are already defeq.

`Nil` sidesteps this by being a `Prop`-valued predicate *indexed by the walk*. The
vertices `{v w : V}` appearing in its definition are indices, free to vary from one
constructor to the next, and its single constructor
`| nil {u : V} : Nil (nil : G.Walk u u)` fixes both of them to be the *same* vertex
`u`.

Two things follow immediately from this. Firstly, `Nil p` is a well-typed proposition
for *every* `p : G.Walk v w`, whatever its endpoints: so we have replaced an equation
that may not type-check with a predicate that always does. Secondly, the only way to
build a proof of `Nil p` is via this constructor, which applies precisely when `p` is
`nil`. There is no constructor mentioning `cons`, so `Nil (cons h q)` is simply
uninhabited.

The payoff comes when we *eliminate* a hypothesis `h : p.Nil`. If we use `cases h`
there is only one case! In this single case Lean must unify the indices `v, w` with
the constructor's `u`, so here `v` and `w` *are* defeq. Hence destructing `Nil` hands
us back exactly the propositional equality `v = w` that the dependent type was
hiding.
-/
example (p : G.Walk v w) (h : p.Nil) : v = w := by
  cases h with
  | nil => -- here the goal is `v = v`
    rfl

/-!
Notice that the proof of `Nil.eq` is exactly this same pattern matching.
-/
#source Walk.Nil.eq -- lemma Nil.eq {p : G.Walk v w} : p.Nil → v = w | .nil => rfl
/-!
Moreover, the fact that a `cons` walk is not `Nil` can be proved by `nofun`. There
are simply no cases to consider!
-/

example {h : G.Adj u v} {p : G.Walk v w} : ¬ (cons h p).Nil := by nofun

/-!
`Nil` is essentially a bespoke `Eq` for walks: both are single-constructor inductive
types indexed by values, whose single constructor forces the indices to coincide.
-/
#source Eq  -- inductive Eq : α → α → Prop where
            --  | refl (a : α) : Eq a a

/-!
Finally, we can prove that a non-nil walk has positive length as follows.
-/
example (p : G.Walk v w) (hn : ¬ p.Nil) : 0 < p.length := by
  cases p with
  | nil => exact hn.elim Nil.nil
  | cons _ _ => simp

/-!
The Mathlib API also relates `Nil` to `length` directly.
-/
#check Walk.length_eq_zero_iff -- p.length = 0 ↔ p.Nil

/-!
## Copy

Having solved the problem of type mismatches involving `nil`, we now turn to the more
general problem of type mismatches between arbitrary walks. For example if
`p : G.Walk u v₁` and `q : G.Walk v₂ w` where `v₁` and `v₂` are provably, but not
definitionally, equal then we can't directly form `Walk.append p q` since `append`
has a signature that expects compatible walks. If we try to write `p.append q` we get
a type error.
-/
/-- Application type mismatch: The argument
  q
has type
  G.Walk v₂ w
but is expected to have type
  G.Walk v₁ w
-/
#guard_msgs (substring := true) in
example {v₁ v₂ : V} (p : G.Walk u v₁) (q : G.Walk v₂ w) (h : v₂ = v₁) :
  G.Walk u w :=  p.append q

/-!
A quick fix for this is to change the type of `q` using `h : v₂ = v₁` and `▸`:
-/
example {v₁ v₂ : V} (p : G.Walk u v₁) (q : G.Walk v₂ w) (h : v₂ = v₁) :
  G.Walk u w :=  p.append (h ▸ q)

/-!
This changes the type of `q` without changing the walk itself.

Mathlib's `Walk.copy` packages this cast with a name, so we can state lemmas about
it, and it lets both endpoints be changed at once.
-/
#source Walk.copy
example {v₁ v₂ : V} (p : G.Walk u v₁) (q : G.Walk v₂ w) (h : v₂ = v₁) :
  G.Walk u w :=  p.append (q.copy h rfl)

/-!
A simple example of where we need to introduce a `Walk.copy` is in the proof that
`(p.cons h).tail = p`.

On paper this is completely obvious: `Walk.tail` is the walk obtained by dropping its
first edge, so `(p.cons h).tail` first adds and then drops the edge `h` to the start
of `p`. However the type of `(p.cons h).tail` is `G.Walk (p.cons h).snd w` while `p`
has type `G.Walk v w`. The vertex `(p.cons h).snd` unfolds to `p.getVert 0`, which is
provably but not definitionally equal to `v`. So the obvious equality does not type
check. Instead we have to state this using `Walk.copy`. (The definition of
`getVert` matches on the walk before the index, so even `p.getVert 0` is stuck until
Lean knows whether `p` is `nil` or a `cons`, although both cases give `v`.)
-/
#check tail_cons -- (cons h p).tail = p.copy ⋯ ⋯
/-!
Having introduced `Walk.copy` it's instructive to look at its API. Since
`hu : u = u'` and `hv : v = v'` are proofs of equality, `p.copy hu hv` is the walk
`p` itself, retyped as a walk from `u'` to `v'`. So every statement about `p` has a
counterpart for `p.copy hu hv`, saying the same thing. In each case the proof is
simply `subst_vars` followed by `rfl`.

For example `length_copy`, `support_copy`, `edges_copy` and `isPath_copy`.
-/
#check Walk.length_copy  -- (p.copy hu hv).length = p.length
#check Walk.support_copy -- (p.copy hu hv).support = p.support
#check Walk.edges_copy   -- (p.copy hu hv).edges = p.edges
#check Walk.isPath_copy  -- (p.copy hu hv).IsPath ↔ p.IsPath

/-!
The `subst_vars` is essential. As its source shows, `copy` is just the cast
`hu ▸ hv ▸ p`, and like the cast `h ▸ v` in the disjoint union `Σg`
(`SimpleGraph.sigma`), it is stuck while the endpoints are distinct variables. So not
even the length of a copied walk can be computed, and `rfl` fails.
-/
/-- error: Tactic `rfl` failed: The left-hand side
  (p.copy hu hv).length
is not definitionally equal to the right-hand side
  p.length -/
#guard_msgs (substring := true) in
example {u u' v v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by rfl

/-!
Substituting identifies `u'` with `u` and `v'` with `v`, so both casts are now along
definitional equations and disappear, after which `rfl` succeeds. (For the same
reason `copy_rfl_rfl`, which copies along `rfl` proofs, is itself proved by `rfl`.)
-/
example {u u' v v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by
  subst_vars
  rfl

/-!
Notice that the four `copy` lemmas listed above are all simp lemmas with `p.copy` on
the LHS so that simp will systematically remove `.copy` when possible by rewriting to
the original walk.

Another class of results involving `Walk.copy` are those that allow us to manipulate
a copied walk. For example if we add an edge to a `copy` using `cons` then this is
the same as taking a copy of the equivalent `cons` walk.
-/
#check Walk.cons_copy --  cons h (p.copy hv hw) = (cons ⋯ p).copy ⋯ hw

/-!
Some, but certainly not all, such results are simp lemmas. To understand why, we need
to read the doc-string for `Walk.copy`, in particular the following comment:

> The simp-normal form is for the `copy` to be pushed outward. That way calculations
can occur within the "copy context".

What this means is that lemmas involving `Walk.copy` are only marked as `@[simp]` if
they push the `copy` outwards. The simp normal form is
`(some_walk_not_involving_copy).copy hv hw`. (With `copy` on the outside, simp can
apply other walk simp lemmas freely to the inner walk without `copy` interfering.)

For example `cons_copy` and `append_copy_copy` are both good simp lemmas while
`copy_cons` is not.
-/
#source cons_copy --  cons h (p.copy hv hw) = (cons (hv ▸ h) p).copy rfl hw

#source append_copy_copy -- (p.copy hu hv) ++ (q.copy hv hw) = (p ++ q).copy hu hw

#source copy_cons --  (cons h p).copy hu hw = cons (hu ▸ h) (p.copy rfl hw)

/-!
To see what this means in practice, we consider the following concrete example.
Suppose that simp encounters `cons h₁ (cons h₂ (p.copy hv hw))`. In this case
`cons_copy` fires on the inner walk `cons h₂ (p.copy hv hw)`, rewriting to
`cons h₁ ((cons (hv ▸ h₂) p).copy rfl hw)`. Now there is again a `copy` inside a
`cons` so `cons_copy` fires again to give:
`(cons h₁ (cons (hv ▸ h₂) p)).copy rfl hw`.

The `copy` is now on the outside and the result is in normal form:
`(some_walk).copy rfl hw`.

If the equality proofs were both `rfl`, then `copy_rfl_rfl` would fire and eliminate
the `copy` entirely!
-/
#check Walk.copy_rfl_rfl -- (p.copy rfl rfl) = p

/-!
The following lemma (the `concat` analogue of `cons_copy` from above, not currently
in Mathlib) is a good simp lemma.
-/
@[simp]
lemma Walk.concat_copy {v w y v' w'} (h : G.Adj w y) (p : G.Walk v' w') (hv : v' = v)
    (hw : w' = w) : (p.copy hv hw).concat h = (p.concat (hw ▸ h)).copy hv rfl := by
  subst_vars
  rfl

/-!
As a worked example consider the following situation: we have `h₁ : G.Adj a b` and
`h₂ : G.Adj c d`, as well as walks `p : G.Walk u v` and `q : G.Walk v y`; and proofs
that `u = b`, `v = x` and `y = c`. Making heavy use of `Walk.copy` we can construct a
walk `G.Walk a d` that is essentially the incorrectly typed walk
`(cons h₁ (p ++ q)).concat h₂`. This walk has length `p.length + q.length + 2`.
-/
example {a b c d u v x y} (hub : u = b) (hvx : v = x) (hyc : y = c)
    (p : G.Walk u v) (q : G.Walk v y) (h₁ : G.Adj a b) (h₂ : G.Adj c d) :
    ((cons h₁ ((p.copy hub hvx).append (q.copy hvx hyc))).concat h₂).length
      = p.length + q.length + 2 := by
  -- simp would prove this, but it's nice to see the individual steps.
  rw [append_copy_copy, cons_copy, concat_copy, length_copy, length_concat,
    length_cons, length_append]

/-!
## Transfer

As well as encoding the endpoints of a walk, the type of a walk also encodes the
graph in which it lives: `p : G.Walk u v`.

Given two graphs `G` and `H` on the same vertex set, and a walk `p` in `G` that only
uses edges that are also in `H`, we would like to treat `p` as a walk in `H`. However
if Lean is expecting a `H.Walk u v` we can't simply give it `p : G.Walk u v` since
the type of `p` is wrong.

The solution is to use `Walk.transfer` which allows us to change the type of a walk
from `G.Walk u v` to `H.Walk u v` provided we have a proof that every edge in `p` is
also an edge of `H`.
-/
#check Walk.transfer
/-!
For example, if we take the `sup` (i.e. union) of a graph `G` with a graph `H`, then
any walk in `G` is also a walk in `G ⊔ H`.
-/
example (p : G.Walk u v) (H : SimpleGraph V) : (G ⊔ H).Walk u v :=
  p.transfer _ fun _ he => edgeSet_mono le_sup_left (p.edges_subset_edgeSet he)

/-!
It is tempting to assume that `Walk.transfer` follows the same simp normal form as
`Walk.copy`, but in fact the opposite is true. The difference is visible in the
definition itself: `Walk.copy` is *not* marked `@[simp]` (it is just the cast
`hu ▸ hv ▸ p`, which is stuck while the endpoints are variables), whereas the
recursive definition of `Walk.transfer` *is* tagged `@[simp]`.
-/
#source Walk.transfer --| nil => nil
                      --| cons' .. => cons _ (p.transfer ..)
/-!
So simp unfolds `transfer` through the structure of the walk: `(nil).transfer = nil`
and `(cons h p).transfer = cons _ (p.transfer ..)`. So unlike `copy`, which can never
be removed (except by `copy_rfl_rfl`) and is therefore collected on the *outside*,
`transfer` is pushed *inwards* until it vanishes at the `nil` leaves. The simp normal
form of `transfer` is therefore to *eliminate* it entirely; a `transfer` only
survives when it is applied to an opaque walk whose constructor simp cannot see.

The simp lemmas all serve this purpose: `transfer_append` distributes `transfer`
inwards over `append`, moving it towards the leaves:
-/
#check transfer_append -- (p ++ q).transfer = (p.transfer ..) ++ (q.transfer ..)
/-!
Two nested transfers fuse into a single one via `transfer_transfer`.
-/
#check transfer_transfer -- (p.transfer H hp).transfer K hp' = p.transfer K ⋯
/-!
Finally, simp lemmas such as `length_transfer`, `support_transfer` and
`edges_transfer` allow us to transfer properties of the walk across the transfer.
-/
#check length_transfer  -- (p.transfer H hp).length = p.length
#check support_transfer -- (p.transfer H hp).support = p.support
#check edges_transfer   -- (p.transfer H hp).edges = p.edges

/-!
## Plumbing Elsewhere in the API

`Walk.copy` and `Walk.transfer` have no informal counterparts, but the problem they
solve is not special to walks. It arises whenever a type encodes data and we need
to reconcile two versions of that data that are equal but not definitionally so.

`Walk.copy` shares its name and purpose with the `copy` functions found on many
structures in Mathlib (`Submonoid.copy`, `Subgraph.copy`, ...). These follow the
*range copy pattern*: given a structure and a set that is propositionally equal to
one of its fields (such as its carrier), `copy` returns an equal structure in which
that field is *definitionally* the new set. Whether the data being replaced lives in
a field or, as for walks, in the type, the effect is the same: a defeq problem
becomes a one-off proof obligation. We will meet another `copy` of this kind in the
next chapter (`ColoringOn.copy`).
-/

/-!
# Mapping Walks

Given a walk `p : G.Walk u v` and a graph homomorphism `f : G →g H` we can map `p` to
a walk in `H` from `f(u)` to `f(v)` using `Walk.map`.
-/
#source Walk.map
example {W : Type*} {H : SimpleGraph W} (f : G →g H) (p : G.Walk u v) :
    H.Walk (f u) (f v) := p.map f

/-!
When `G ≤ H` (and so trivially the edges of any walk in `G` lie in `H`)
`Walk.transfer` is equal to `Walk.map` along the subgraph inclusion homomorphism
`Hom.ofLE`.
-/
#check Hom.ofLE -- (h : G ≤ H) : G →g H
#check Walk.transfer_eq_mapLe --  (GH : G ≤ H) : p.transfer H hp = mapLe GH p

/-!
Recall `P[n]`, the `pathGraph` with `n` vertices on `Fin n`, and the embedding
`pathGraphEmbedding n k : P[n] ↪g P[n + k]`, which sends `i ↦ i + k`, so its image is
the last `n` vertices of `P[n + k]`.
-/
#check pathGraph
#check pathGraphEmbedding

/-!
We can use this embedding and `Walk.map` to define a walk from `0` to `n` in
`P[n + 1]`. Notice that we use `Walk.copy` to ensure its type is correct. (To be
precise, in the `succ n` case we want to get a walk that is `cons h p` where `p` is a
walk from `1` to `Fin.last (n + 1)`, rather than from `toHom 0` to
`toHom (Fin.last n)`. Without the use of `Walk.copy` the definition would still work,
but proofs would be more painful. You can remove the `.copy (by simp) (by simp)` and
see what happens!)
-/
/-- The walk from `0` to `n` in the `pathGraph` on `Fin (n + 1)`. -/
def Walk.pathGraphWalk (n : ℕ) : (P[n + 1]).Walk 0 (Fin.last n) :=
  match n with
  | 0 => nil
  | n + 1 =>
      (pathGraphWalk n).map (pathGraphEmbedding (n + 1) 1).toHom|>.copy
        (by simp) (by simp)|>.cons
          (by simp [pathGraph_adj] : P[n + 2].Adj 0 1)

/-!
We could have defined this walk directly; indeed we previously defined walks directly
in `pathNat₁` so why not give a direct definition here? The key difference here is
that the vertex type of each `P[n]` is different so the induction would be more
painful, and we would have fewer results to rely on in subsequent proofs. From the
`Walk.map` definition the proof that this is a Hamiltonian path will drop out very
easily below.
-/
/-!
First we show that this walk has length `n`.
-/
@[simp]
lemma Walk.length_pathGraphWalk {n} : (pathGraphWalk n).length = n := by
  induction n with
  | zero => rfl
  | succ _ ih => simp [ih, pathGraphWalk]

/-!
Before showing that this walk is a path we need one small lemma. Any copy of a path
is a path: the iff statement `isPath_copy` is already in Mathlib, but this version,
with dot notation, is missing and is exactly what we need next.
-/
theorem Walk.IsPath.copy {u v x v'} {p : G.Walk u v} (hp : p.IsPath) {hu : u = x}
    {hv : v = v'} : (p.copy hu hv).IsPath :=
  (isPath_copy ..).2 hp

/-!
This walk is a path.
-/
lemma Walk.pathGraphWalk_isPath {n} : (pathGraphWalk n).IsPath := by
  induction n with
  | zero => exact IsPath.nil
  | succ n ih =>
    -- `IsPath.copy` peels off the `copy`, so that the goal displays the `map` and
    -- Lean can read off the homomorphism before it checks `injective`
    apply (IsPath.map (pathGraphEmbedding ..).injective ih).copy.cons
    simp

/-!
Hence this walk is a Hamiltonian path.
-/
lemma Walk.pathGraphWalk_isHamiltonian {n} : (pathGraphWalk n).IsHamiltonian  :=
  isHamiltonian_iff_isPath_and_length_eq.mpr ⟨pathGraphWalk_isPath, by simp⟩

/-!
## Cycle Graphs and Complete Graphs are Hamiltonian

Having walked along the path graph from end to end we can wrap this Hamiltonian path
around in the cycle graph to give a Hamiltonian cycle. The path graph `P[n + 3]` is
a subgraph of `C[n + 3]` (`pathGraph_le_cycleGraph` in Mathlib) so `Walk.transfer`
moves `pathGraphWalk` into `C[n + 3]`, where the wrap-around edge from `0` to
`Fin.last (n + 2)` closes it into a Hamiltonian cycle. (Notice that we have used two
of our plumbing tools here: both `Walk.copy` and `Walk.transfer`.)
-/
/-- The walk once around `C[n + 3]`, built by transferring `pathGraphWalk` and
closing it with the wrap-around edge. -/
def Walk.cycleGraphCycle (n : ℕ) : C[n + 3].Walk 0 0 :=
  have adj : C[n + 3].Adj 0 (Fin.last (n + 2)) := by simp [cycleGraph_adj]
  Walk.cons adj (((pathGraphWalk (n + 2)).transfer C[n + 3]
    (fun e he => edgeSet_mono pathGraph_le_cycleGraph
      ((pathGraphWalk _).edges_subset_edgeSet he))).reverse)

/-!
This walk is a cycle: the transferred path is still a path, so it only remains to
check that the closing edge is not an edge of the path, which holds if its length is
not equal to 1 (which is true).
-/
lemma Walk.cycleGraphCycle_isCycle (n : ℕ) : (cycleGraphCycle n).IsCycle := by
  apply (cons_isCycle_iff_length_ne_one _ _).2
          ⟨(pathGraphWalk_isPath.transfer _).reverse, _⟩
  simp

/-!
Since it is a cycle of length `n + 3` containing the `n + 3` vertices of `C[n + 3]`,
it is a Hamiltonian cycle, and so cycle graphs (on at least three vertices) are
Hamiltonian.
-/
lemma Walk.cycleGraphCycle_isHamiltonianCycle (n : ℕ) :
    (cycleGraphCycle n).IsHamiltonianCycle := by
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  exact ⟨cycleGraphCycle_isCycle n, by simp [cycleGraphCycle]⟩

@[simp]
lemma cycleGraph_isHamiltonian (n : ℕ) : C[n + 3].IsHamiltonian :=
  fun _ => ⟨_, _, Walk.cycleGraphCycle_isHamiltonianCycle n⟩

/-!
Mathlib also has its own walk once around `C[n + 3]`, `cycleGraph.cycle`, built by a
direct recursion on the vertices rather than by transferring a path, together with
the facts that it is a cycle of length `n + 3`. (We built `cycleGraphCycle` here as a
worked example of `Walk.transfer`; in later chapters we will use Mathlib's
`cycleGraph.cycle`.)
-/
#check cycleGraph.cycle         -- (cycleGraph (n + 3)).Walk 0 0
#check cycleGraph.isCycle_cycle -- (cycleGraph.cycle n).IsCycle
#check cycleGraph.length_cycle  -- (cycleGraph.cycle n).length = n + 3

/-!
We give two easy but useful consequences. Firstly, Hamiltonicity is monotone: if
`G ≤ H` and `G` has a Hamiltonian cycle then the same cycle is a Hamiltonian cycle in
`H` (`IsHamiltonian.mono`). Since `C[n + 3] ≤ ⊤` this tells us
that the complete graph `K[n + 3]` is Hamiltonian.
-/
lemma completeGraph_isHamiltonian (n : ℕ) :
    K[n + 3].IsHamiltonian := (cycleGraph_isHamiltonian n).mono le_top

/-!
Secondly, being Hamiltonian is obviously preserved by isomorphism, so any complete
graph on at least three vertices is Hamiltonian: we transport the Hamiltonian cycle
of `K[n + 3]` along an isomorphism `K[n + 3] ≃g ⊤` built from an equivalence
`Fin (n + 3) ≃ V` using `Iso.completeGraph`. (This innocent-looking lemma will be
useful in the proof of the Bondy–Chvátal theorem below.)
-/
#check Iso.completeGraph

lemma top_isHamiltonian [Fintype V] [DecidableEq V] (hn : 3 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).IsHamiltonian := by
  obtain ⟨n, hcard⟩ : ∃ n, Fintype.card V = n + 3 :=
    ⟨Fintype.card V - 3, by grind⟩
  -- since `K[n + 3]` is Hamiltonian it contains a Hamiltonian cycle
  obtain ⟨a, c, hc⟩ := completeGraph_isHamiltonian n (by simp)
  -- which we transport along an isomorphism `K[n + 3] ≃g (⊤ : SimpleGraph V)`.
  have e : Fin (n + 3) ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  intro
  exact ⟨e a, c.map (Iso.completeGraph e).toHom, hc.map e.bijective⟩

end basics
/-!
# Walks in Hypercube and Mycielskian Graphs

We now return to two of our running examples, the hypercube `Q[n]` and the
Mycielskian `mμ[G]`, and build walks in each of them.

## Walks in Hypercubes

We will consider the two most natural walks in the hypercube: canonical shortest
paths and Gray code paths.

### Hamming Paths

Between any two vertices in the hypercube there may exist many different shortest
paths, each obtained by successively flipping one of the coordinates in which the two
vertices differ. More precisely if `u` and `v` differ in `k` coordinates then there
are `k!` different shortest paths between `u` and `v` obtained by flipping these
coordinates in different orders.

Clearly the length of any such path is the number of coordinates which need to be
flipped, which is the *Hamming distance* between the two vertices.

We will define a canonical choice of such a path, which we will then call
*the Hamming path* between the two vertices, by flipping coordinates from left to
right.

We will use induction on `n` and `Walk.map` to lift a path in `Q[n]` to `Q[n + 1]`
via the `embedBool` embedding we defined earlier. (Recall that `embedBool n b` sends
`v ↦ (v, b)`.)
-/
#check hypercube.embedBool

section hypercube
open hypercube HypercubeVert
/-!
We can define Hamming paths using `if-then-else` syntax to split on the value of the
last coordinate. The walk obtained from `Walk.map` starts at `(embedBool n b) u`,
which is `(u, b)` by definition but not syntactically, so in both cases we use
`Walk.copy` to convert it to the expected type `Q[n + 1].Walk (u, b) (v, c)` (in the
`b = c` case the end vertex `(v, b)` also needs the hypothesis `h : b = c`).

Since a Hamming path is a path between two `HypercubeVert n` vertices, we choose to
put it, and related definitions and results, in the `HypercubeVert` namespace.
(Although `(embedBool n b) u` and `(u, b)` are defeq, we discharge the first side
condition of each `Walk.copy` with `by simp` rather than `rfl`. Lean stores each such
proof as an auxiliary lemma, and with `rfl` its statement would be
`(embedBool n b).toHom u = (embedBool n b).toHom u`. The definition would still be
valid, but `rw` and `simp` would then fail to match this against `(u, b)`, so the
proofs below could not rewrite the `copy` away. Conversely, the final `rfl` in the
`else` branch cannot be a tactic proof. A term such as `rfl` is elaborated
immediately, and this is what fixes the end vertex of the `concat` to be `(v, c)`. A
tactic block is postponed until the rest of the expression has been elaborated, so
the adjacency proof `by simp [h]` would then face an unknown vertex.)
-/
/-- The Hamming path between two vertices in the hypercube. -/
def HypercubeVert.hammingPath : {n : ℕ} → (u v : HypercubeVert n) → Q[n].Walk u v
  | 0, _, _ => nil
  | n + 1, (u, b), (v, c) => if h : b = c then
      (u.hammingPath v |>.map (embedBool n b).toHom).copy (by simp) (by simp [h])
    else
      ((u.hammingPath v).map (embedBool n b).toHom |>.concat (by simp [h])).copy
        (by simp) rfl

/-!
We will also need a notion of the Hamming distance between two vertices in the
hypercube.

Mathlib has a `hammingDist` function for finite Pi-types, but we can't use this for
`HypercubeVert` (it isn't a Pi-type!) so we define a version for `HypercubeVert`
directly below.
-/
#check hammingDist -- [Fintype ι] [(i : ι) → DecidableEq (β i)]
                   --         (x y : (i : ι) → β i) : ℕ

/-- Hamming distance in `Q[n]` defined for `HypercubeVert n` directly. -/
protected def HypercubeVert.hammingDist : {n : ℕ} → (u v : HypercubeVert n) → ℕ
| 0, _, _ => 0
| _ + 1, (u, b), (v, c) => u.hammingDist v + if b = c then 0 else 1

/-!
There is only one `HypercubeVert 0` vertex, so the Hamming distance between any two
such vertices is `0`.
-/
@[simp]
lemma HypercubeVert.hammingDist_zero {u v : HypercubeVert 0} :
    u.hammingDist v = 0 := rfl

/-!
The Hamming distance between two vertices in `Q[n + 1]` is the Hamming distance
between the first `n` coordinates, plus `1` iff the last coordinates differ.
-/
@[simp]
lemma HypercubeVert.hammingDist_succ {n : ℕ} {u v : HypercubeVert (n + 1)} :
  u.hammingDist v =
    u.1.hammingDist v.1 + if u.2 = v.2 then 0 else 1 := rfl

/-!
The proofs of basic facts about `hammingPath` are by standard induction, using the
`split_ifs` tactic to deal with the `if-then-else` when needed.
-/
/-- The length of the Hamming path is equal to the Hamming distance between the two
vertices. -/
@[simp]
lemma HypercubeVert.length_hammingPath {n} (u v : HypercubeVert n) :
    (u.hammingPath v).length = u.hammingDist v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases u
    rcases v
    rw [hammingPath]
    split_ifs <;> simp_all

/-!
A Hamming path is a path.
-/
@[simp]
lemma HypercubeVert.hammingPath_isPath {n} (u v : HypercubeVert n) :
    (u.hammingPath v).IsPath := by
  induction n with
  | zero => exact Walk.IsPath.nil
  | succ n ih =>
    rcases u with ⟨u, b⟩
    rcases v with ⟨v, c⟩
    rw [hammingPath]
    split_ifs with h <;> apply Walk.IsPath.copy
    · apply IsPath.map (embedBool ..).injective (ih _ _)
    · apply IsPath.map (embedBool ..).injective (ih _ _)|>.concat
      -- the mapped path lies in the slice with last coordinate `b`, so it cannot
      -- visit the new end vertex `(v, c)`, as `b ≠ c`
      simp_rw [Walk.support_map, List.mem_map]
      rintro ⟨w, -, hw⟩
      -- `hw : (w, b) = (v, c)`, so comparing last coordinates gives `b = c`
      exact h (congrArg Prod.snd hw)

/-!
We will use Hamming paths to show that the hypercube is connected in
[Connected Graphs](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-connected-graphs),
and in
[Distance in the Hypercube](https://jt496.github.io/GraphTheoryInLean/Distance/#section-distance-in-the-hypercube)
we will see that the Hamming distance is the graph distance in `Q[n]`.
-/
/-!
### Gray Code

The hypercube contains a canonical Hamiltonian path called the *Gray code*
[Gray 1953](https://jt496.github.io/GraphTheoryInLean/Appendix/#bib-gray-1953) which
we will now define. Its endpoints are marked `@[implicit_reducible]` (as
`HypercubeVert` is) so that `grayStart (n + 1)` unfolds to `(grayStart n, false)`
when Lean checks the endpoints of the `Walk.copy`s below.
-/
/-- The first vertex of the Gray code walk is a nested tuple of `false`. -/
@[simp, implicit_reducible]
def HypercubeVert.grayStart : (n : ℕ) → HypercubeVert n
  | 0 => ()
  | n + 1 => (grayStart n, false)

/-- The last vertex of the Gray code walk is the same as the first, but flipped to
`true` in the new dimension. -/
@[simp, implicit_reducible]
def HypercubeVert.grayEnd : (n : ℕ) → HypercubeVert n
  | 0 => ()
  | n + 1 => (grayStart n, true)

/-- The Gray code walk in `Q[n]`. -/
def Walk.grayWalk : (n : ℕ) → Q[n].Walk (grayStart n) (grayEnd n)
  | 0 => nil  -- The nil walk from `()` to `()`
  | n + 1 =>
    -- First half: map the `n`-dim walk onto the `false` slice of `Q[n + 1]`
    -- This is a walk from `(grayStart n, false)` to `(grayEnd n, false)`
    -- in `Q[n + 1]`. We use `Walk.copy` to avoid mistyped endpoints in later proofs.
    let firstHalf := ((grayWalk n).map (embedFalse n).toHom).copy (by simp) (by simp)
    -- There is an edge joining the two halves of the
    -- walk and the two slices of `Q[n + 1]`:
    -- `(grayEnd n, false)` is adjacent to `(grayEnd n, true)`.
    let crossAdj : Q[n + 1].Adj (grayEnd n, false) (grayEnd n, true) := by
      simp
    -- Second half: reverse the `n`-dim walk, and map it onto the `true` slice. This
    -- is a walk from `(grayEnd n, true)` to `(grayStart n, true)` in `Q[n + 1]`.
    let secondHalf := ((grayWalk n).reverse.map (embedTrue n).toHom).copy
                          (by simp) (by simp)
    -- Now we append the second half to the first half using the cross edge
    firstHalf.append <| cons crossAdj secondHalf

/-!
[Figure: The Gray code walk in $Q_n$ for $n = 1, 2, 3, 4$, from `grayStart n` (green) to `grayEnd n` (red)](https://jt496.github.io/GraphTheoryInLean/figures/grayWalk.svg)

We can now easily prove that this walk has length `2 ^ n - 1` and that it is a path.
-/

@[simp]
lemma Walk.length_grayWalk {n} : (grayWalk n).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    grind [grayWalk, length_append, length_cons, length_copy, length_map,
             length_reverse]

/-!
The Gray code walk is a path.
-/
@[simp]
lemma Walk.grayWalk_isPath (n) : (grayWalk n).IsPath := by
  induction n with
  | zero => simp [grayWalk]
  | succ n ih =>
    apply (IsPath.map (embedBool ..).injective ih).copy.append_cons
            (IsPath.map (embedBool ..).injective ih.reverse).copy
    -- dot notation with `IsPath` has reduced our goal to proving that the
    -- two parts of the walk have disjoint support
    intro y hy hz
    rw [Walk.support_copy, Walk.support_map, List.mem_map] at hy hz
    -- the first half lies in the `false` slice and the second in the `true` slice,
    -- so `y = (a, false) = (b, true)`, and the last coordinates clash
    obtain ⟨a, -, rfl⟩ := hy
    obtain ⟨b, -, hb⟩ := hz
    have hlast : true = false := congrArg Prod.snd hb
    contradiction

/-!
Moreover it is clearly a Hamiltonian path, since `Q[n]` has `2 ^ n` vertices.
-/
@[simp]
lemma Walk.grayWalk_isHamiltonian (n : ℕ) : (grayWalk n).IsHamiltonian :=
  isHamiltonian_iff_isPath_and_length_eq.mpr
    ⟨grayWalk_isPath _, by rw [length_grayWalk, card_hypercubeVert]⟩

end hypercube

/-!
From here it is a short step to getting a Hamiltonian cycle in `Q[n]` (for `n > 1`);
see the
[Exercises](https://jt496.github.io/GraphTheoryInLean/Walks/#section-exercises-walks)
for details.

## Walks in the Mycielskian

Recall `mμ[G]`, the `mycielskian` of a graph `G`. Given any non-nil walk in `G`,
there is a natural way to define a walk in `mμ[G]`. We explore this construction in
detail below, using it to prove that every edge of `G` gives a `5`-cycle in `mμ[G]`,
and that `mμ[G]` contains a Hamiltonian path or cycle whenever `G` does (provided
`G` has at least two vertices).

Rather than defining the walks that give the Hamiltonian path and cycle directly, we
first define an auxiliary walk, `mycielskianAux`, that has a simple recursive
definition and from which it is easy to build paths and cycles in `mμ[G]` from paths
and cycles in `G`.

First, note that if `u — w` is a walk of length 1 in `G` (i.e. a single edge) then
there is a corresponding walk of length 2 in `mμ[G]`, given by `u ₗ — w ₗ — u ᵣ`.
Further, if `u — v — w` is a walk of length 2 in `G`, then there is a corresponding
walk of length 4 in `mμ[G]`: `u ₗ — v ᵣ — w ₗ — v ₗ — u ᵣ`. Notice that this second
example can be obtained from the first by taking the walk corresponding to the single
edge `v — w`, reversing it and adding the edges `u ₗ — v ᵣ` and `v ₗ — u ᵣ` to the
start and end respectively.

This generalizes, and allows us to define the walk `mycielskianAux` recursively.
Having built the walk in `mμ[G]` from `v ₗ` to `v ᵣ` corresponding to a non-nil walk
`p : G.Walk v w`, the walk for `cons h p`, where `h : G.Adj u v`, is formed by
prepending the edge `u ₗ — v ᵣ` to the reverse of the walk corresponding to `p` and
then concatenating the edge `v ₗ — u ᵣ` to give
`mycielskianAux(cons h p) = u ₗ — [mycielskianAux(p).reverse] — u ᵣ`.

[Figure: The two cases of the auxiliary zig-zag walk: `cons h nil` (left) and `cons h (cons h' p')` (right)](https://jt496.github.io/GraphTheoryInLean/figures/mycielskianAux.svg)
-/
section mycielskian
variable {V : Type*} {G : SimpleGraph V}

/-- Given a non-nil walk from `u` to `w` in `G`, this is the zig-zag walk from `u ₗ`
to `u ᵣ` in `mμ[G]`. -/
def Walk.mycielskianAux {u w : V} {p : G.Walk u w} (hn : ¬ p.Nil) :
    mμ[G].Walk u ₗ u ᵣ :=
  match p with
  | nil => (hn .nil).elim  -- This case is ruled out by the `¬ p.Nil` hypothesis
  | cons' u v w h p =>
    -- the last edge of the walk `v ₗ — u ᵣ`
    have hl : mμ[G].Adj v ₗ u ᵣ := by simpa using h.symm
    match p with
    | nil => cons (by simpa using h) <| cons hl nil -- `u ₗ — v ₗ — u ᵣ`
    | cons' _ x _ h' p' =>
      have hn' : ¬ (p'.cons h').Nil := nofun
      cons (by simpa using h) ((mycielskianAux hn').reverse.concat hl)

/-!
If we had marked the definition of `mycielskianAux` with the `@[simp]` attribute
then its automatically generated equational lemmas would be available for `simp` to
use with names like `mycielskianAux.eq_1`. We instead state these as simp lemmas
that have more meaningful names.
-/
@[simp]
lemma Walk.mycielskianAux_cons_nil {u v} (h : G.Adj u v) (hn : ¬ (cons h nil).Nil) :
    mycielskianAux hn =
      have hl : mμ[G].Adj v ₗ u ᵣ := by simpa using h.symm
      cons (by simpa using h) (cons hl nil) := rfl

@[simp]
lemma Walk.mycielskianAux_cons_cons {u v x w} (h : G.Adj u v) (h' : G.Adj v x)
    (p' : G.Walk x w) (hn : ¬ (cons h (cons h' p')).Nil) :
    mycielskianAux hn =
      have hn' : ¬ (cons h' p').Nil := nofun
      cons (by simpa using h)
        ((mycielskianAux hn').reverse.concat (by simpa using h.symm)) := rfl

/-!
From the definition of `mycielskianAux`, Lean automatically generates a
*functional induction* principle `mycielskianAux.induct`. It has one case for each
`match` case of the definition, named `case1` and `case2`, whose variables are the
pattern variables of that case, together with an induction hypothesis wherever the
definition calls itself. We use it with `induction hn using mycielskianAux.induct`:
its cases follow the definition exactly, which plain induction on the walk does not.
-/
#check mycielskianAux.induct -- slightly scary looking! (but useful)
/-!
The auxiliary walk is twice as long as the original walk.
-/
@[simp]
lemma Walk.length_mycielskianAux {u w} {p : G.Walk u w} (hn : ¬ p.Nil) :
    (mycielskianAux hn).length = 2 * p.length := by
  induction hn using mycielskianAux.induct with
  | case1 => rfl
  | case2 =>
    grind [length_cons, mycielskianAux_cons_cons, length_concat, length_reverse]

/-!
We can use the auxiliary walk to map any non-nil walk of length `k` in `G` to a
walk of length `2k + 2` in the Mycielskian. This preserves the property of being a
path and in particular maps Hamiltonian paths to Hamiltonian paths. We simply add the
two edges `u ᵣ — none — w ᵣ` at the end of the auxiliary walk.
-/
/-- Given a non-nil walk from `u` to `w` in `G`, this is a walk from `u ₗ` to
`w ᵣ` in `mμ[G]`. If the original walk was a (Hamiltonian) path then so is the new
walk. -/
protected def Walk.mycielskian {u w} {p : Walk G u w} (hn : ¬ p.Nil) :
    mμ[G].Walk u ₗ w ᵣ :=
  mycielskianAux hn|>.concat (by simp) |>.concat (by simp : mμ[G].Adj none _ )

/-!
[Figure: Converting a path in $G$ to one in its Mycielskian](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian_path.svg)

Using this walk we can also map closed walks in `G` to closed walks in the
Mycielskian. This preserves the property of being a cycle and in particular maps
Hamiltonian cycles to Hamiltonian cycles in the Mycielskian.
-/

/-- Given a closed walk from `u` to `u` in `G`, there is a walk from `u ᵣ` to `u ᵣ`
in `mμ[G]`. If the original walk was a (Hamiltonian) cycle then so is this new walk.
-/
def Walk.mycielskianClosed {u} (c : Walk G u u) : mμ[G].Walk u ᵣ u ᵣ :=
  match c with
  | nil => nil
  | cons h' nil => (h'.ne rfl).elim
  | cons' _ v _ h <| cons' _ w _ h' p =>
    Walk.mycielskian (not_nil_cons (h := h') (p := p)) |>.cons (by simpa using h)

/-!
The `mycielskianClosed` of a nil walk is nil.
-/
@[simp]
lemma Walk.mycielskianClosed_nil {u} :
    mycielskianClosed (nil : Walk G u u) = nil := rfl

@[simp]
lemma Walk.mycielskianClosed_cons_cons {u v w} (h : G.Adj u v) (h' : G.Adj v w)
    (p : Walk G w u) : mycielskianClosed (cons h (cons h' p)) =
      (Walk.mycielskian (not_nil_cons (h := h') (p := p))).cons
        (by simpa using h) := rfl

/-!
[Figure: Converting a cycle in $G$ to one in its Mycielskian](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian_cycle.svg)
-/
/-!
The `Walk.mycielskian` of a non-nil walk `p` has length `2 * p.length + 2`.
-/
@[simp]
lemma Walk.length_mycielskian {u w} (p : Walk G u w) (hn : ¬ p.Nil) :
    (p.mycielskian hn).length = 2 * p.length + 2 := by
  simp [Walk.mycielskian]
/-!
The `Walk.mycielskianClosed` of a non-nil closed walk `c` has length
`2 * c.length + 1`.
-/
@[simp]
lemma Walk.length_mycielskianClosed {u} {c : Walk G u u} (hn : ¬ c.Nil) :
    c.mycielskianClosed.length = 2 * c.length + 1 :=
  match c with
  | nil => (hn .nil).elim
  | cons h' nil => (h'.ne rfl).elim
  | cons h (cons h' p) => by
    grind [mycielskianClosed, length_cons, length_mycielskian]

/-!
Our next goal is to show that the `Walk.mycielskian` preserves the property of being
a path. It will be useful to first establish some simple properties of the auxiliary
walk `mycielskianAux`.
-/

/-!
The auxiliary walk only visits left or right copies of vertices from the original
walk.
-/
lemma Walk.exists_of_mem_support_mycielskianAux {u w z} {p : G.Walk u w}
    (hn : ¬ p.Nil) (hz : z ∈ (mycielskianAux hn).support) :
    ∃ y ∈ p.support, z = y ₗ ∨ z = y ᵣ := by
  induction hn using mycielskianAux.induct <;> aesop

/-!
In particular, the auxiliary walk does not visit `none`.
-/
@[simp]
lemma Walk.none_notMem_support_mycielskianAux {u w} {p : G.Walk u w} (hn : ¬ p.Nil) :
    none ∉ (mycielskianAux hn).support := by
  intro h_in
  obtain ⟨y, _, hy⟩ := exists_of_mem_support_mycielskianAux hn h_in
  cases hy <;> contradiction

/-!
If the original walk `p : G.Walk u w` is a path, then the auxiliary walk does not
visit `w ᵣ`.
-/
@[simp]
lemma Walk.end_right_notMem_support_mycielskianAux {u w} {p : G.Walk u w}
    (hn : ¬ p.Nil) (hp : p.IsPath) : w ᵣ ∉ (mycielskianAux hn).support := by
  induction hn using mycielskianAux.induct <;> aesop

/-!
The second vertex of the `Walk.mycielskian` is in the auxiliary walk.
-/
@[simp]
lemma Walk.snd_mem_support_mycielskianAux {u w} {p : G.Walk u w} (hn : ¬ p.Nil) :
  (p.mycielskian hn).snd ∈ (mycielskianAux hn).support := by
  induction hn using mycielskianAux.induct
    <;> rw [Walk.mycielskian] <;> aesop

/-!
If the original walk `p : G.Walk u w` is a path, then the auxiliary walk is also a
path.
-/
@[simp]
lemma Walk.IsPath.mycielskianAux {u w} {p : G.Walk u w} (hp : p.IsPath)
    (hn : ¬ p.Nil) : (mycielskianAux hn).IsPath := by
  apply IsPath.mk'
  induction hn using mycielskianAux.induct with
  | case1 u v h hl hn => simpa using h.ne
  | case2 u v h hl w x h' p' hn hnp' ih =>
    -- Using `simp` we can reduce this to a "simple" fact about lists
    -- of vertices that `grind` can solve
    simp only [mycielskianAux_cons_cons, support_cons, support_concat,
              support_reverse, List.nodup_cons]
    grind [isPath_def, exists_of_mem_support_mycielskianAux hnp']

/-!
If the original walk `p : G.Walk u w` is a path, then the `Walk.mycielskian` is a
path.
-/
@[simp]
lemma Walk.IsPath.mycielskian {u w} {p : G.Walk u w} (hp : p.IsPath) (hn : ¬ p.Nil) :
    (p.mycielskian hn).IsPath := by
  apply IsPath.mk'
  simp only [Walk.mycielskian, Walk.concat, support_append,
              support_cons, support_nil, List.append_assoc]
  apply List.nodup_append.mpr ⟨(hp.mycielskianAux hn).support_nodup, ?_⟩
  aesop

/-!
If the original walk `p : G.Walk u u` is a cycle then the `Walk.mycielskianClosed` is
a cycle. (In fact this holds under the weaker assumption that `p` is not nil and
`p.support.tail` contains no repeated vertices.)
-/
lemma Walk.mycielskianClosed_isCycle {u} {p : Walk G u u} (hn : ¬ p.Nil)
    (hc : p.support.tail.Nodup) : (mycielskianClosed p).IsCycle :=
  match p with
  | nil => (hn .nil).elim
  | cons h' nil => (h'.ne rfl).elim
  -- we use the `cons'` pattern here to make the InfoView more readable.
  | cons' _ v _ h (cons' _ w _ h' p) => by
    -- we now use `cons_isCycle_iff_length_ne_one` that we proved earlier to reduce
    -- this to showing that the `Walk.mycielskian` is a path of length not equal to 1
    rw [mycielskianClosed, cons_isCycle_iff_length_ne_one]
    -- We know that the `Walk.mycielskian` of a path is a path and `simp`
    -- can take care of the length.
    exact ⟨(IsPath.mk' hc).mycielskian (by simp), by simp⟩

/-!
The weaker assumption is exactly what we need for one application of the result. If
`h : G.Adj u v` then the closed walk `u — v — u` goes along an edge and straight
back, so it is not a cycle. But it is not nil, and the tail `[v, u]` of its support
has no repeated vertices, so its image `u ᵣ — v ₗ — u ₗ — v ᵣ — none — u ᵣ` is a
`5`-cycle. Hence every edge of `G` gives a `5`-cycle in `mμ[G]`. We will use this to
find the bridges of `mμ[G]` in
[Bridges](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-bridges)
and to compute its girth in
[The Girth of the Mycielskian](https://jt496.github.io/GraphTheoryInLean/Distance/#section-the-girth-of-the-mycielskian).
-/
lemma isCycle_mycielskianClosed_of_adj {u v : V} (h : G.Adj u v) :
    (mycielskianClosed (cons h (cons h.symm nil))).IsCycle :=
  mycielskianClosed_isCycle (by simp) (by simp [h.ne.symm])

/-!
If the original walk `p : G.Walk u w` is a Hamiltonian path, then the
`Walk.mycielskian` is a Hamiltonian path.
-/
protected lemma Walk.IsHamiltonian.mycielskian [DecidableEq V] {u w} {p : G.Walk u w}
    (hp : p.IsHamiltonian) (hn : ¬ p.Nil) : (p.mycielskian hn).IsHamiltonian := by
  have : Fintype V := hp.fintype
  apply isHamiltonian_iff_isPath_and_length_eq.2 ⟨hp.isPath.mycielskian hn, ?_⟩
  grind [length_mycielskian, Fintype.card_option, Fintype.card_sum, hp.length_eq,
    not_nil_iff_lt_length]

/-!
If the original walk `p : G.Walk u u` is a Hamiltonian cycle, then the
`Walk.mycielskianClosed` is a Hamiltonian cycle.
-/
lemma Walk.IsHamiltonianCycle.mycielskianClosed [DecidableEq V] {u} {p : G.Walk u u}
    (hp : p.IsHamiltonianCycle) : p.mycielskianClosed.IsHamiltonianCycle := by
  have : Fintype V := hp.isHamiltonian_tail.fintype
  refine isHamiltonianCycle_iff_isCycle_and_length_eq.2
    ⟨mycielskianClosed_isCycle hp.isCycle.not_nil hp.isCycle.support_nodup, ?_⟩
  grind [length_mycielskianClosed hp.isCycle.not_nil, hp.length_eq,
        Fintype.card_option, Fintype.card_sum]

/-!
Finally we can show that if `G` is Hamiltonian then `mμ[G]` is also Hamiltonian
(unless `G` has only one vertex, in which case `mμ[G]` is an edge plus an isolated
vertex and so is clearly not Hamiltonian).
-/
theorem IsHamiltonian.mycielskian [DecidableEq V] [Fintype V]
    (hH : G.IsHamiltonian) (hf : Fintype.card V ≠ 1) : mμ[G].IsHamiltonian := by
  intro
  have ⟨_, _, hc⟩ := hH hf
  exact ⟨_, _, hc.mycielskianClosed⟩

end mycielskian
/-!
# Hamiltonian Graphs: Ore, Dirac and Bondy–Chvátal *

In this section we prove three classical sufficient conditions for a graph to be
Hamiltonian. The oldest two are *Ore's theorem*
[Ore 1960](https://jt496.github.io/GraphTheoryInLean/Appendix/#bib-ore-1960), which
says that a finite graph on at least 3 vertices is Hamiltonian if the sum of the
degrees of every pair of non-adjacent vertices is at least the number of vertices in
the graph, and its immediate (but earlier) corollary *Dirac's theorem*
[Dirac 1952](https://jt496.github.io/GraphTheoryInLean/Appendix/#bib-dirac-1952)
(minimum degree at least half the number of vertices suffices).

Rather than prove Ore's theorem directly we prove the Bondy–Chvátal theorem
[Bondy–Chvátal 1976](https://jt496.github.io/GraphTheoryInLean/Appendix/#bib-bondy-chvatal-1976):
a graph is Hamiltonian iff its *closure* is, where the closure is obtained by
repeatedly joining non-adjacent vertices whose degree sum is at least the number of
vertices. Ore's theorem falls out immediately, since the closure of an Ore graph is
complete and complete graphs are Hamiltonian (`top_isHamiltonian`).

Recall that if `u ≠ v` then `G ⊔ edge u v` is the graph obtained from `G` by adding
the edge `u — v`.

The proof has four steps.

1. A *maximal* path (one that cannot be extended at either end) whose endpoints
   satisfy Ore's degree condition can be closed up into a cycle visiting exactly the
   same vertices. The tools are Pósa rotations and a counting argument.
2. If `u` and `v` are distinct non-adjacent vertices whose degree sum is at least
   `|V|`, then `G ⊔ edge u v` is Hamiltonian iff `G` is. Adding an edge can only
   help, so the hard part is the converse: a Hamiltonian cycle of `G ⊔ edge u v`
   gives one of `G`. If the cycle avoids the new edge `u — v`, it already lies in
   `G`. Otherwise, deleting `u — v` leaves a Hamiltonian path from `u` to `v` in `G`.
   A Hamiltonian path is certainly maximal, so step 1 closes it up into a Hamiltonian
   cycle of `G`.
3. Adding such edges repeatedly, in rounds, shows that a graph is Hamiltonian iff
   its closure is.
4. Ore's and Dirac's theorems follow, since the closure of an Ore graph is complete.

## Pósa Rotations

Before starting the proof of Bondy–Chvátal we first introduce the notion of a
*Pósa rotation*
[Pósa 1976](https://jt496.github.io/GraphTheoryInLean/Appendix/#bib-posa-1976) of a
walk. This is a key tool in the proof, but is also a more generally useful technique
for working with paths and cycles that has found numerous applications in modern
graph theory.

Given a walk `P = v₀, v₁, ..., vₖ` and an edge `vᵢ — vₖ` in the graph, we form a new
walk: `v₀, v₁, ..., vᵢ, vₖ, vₖ₋₁, ..., vᵢ₊₁`. This new "rotated" walk has the same
length as `P`, and still starts at `v₀`, but now ends at `vᵢ₊₁`.

Currently this isn't in Mathlib but we can easily define it for ourselves.

Given a walk `p : G.Walk u v` and an edge from the `i`-th vertex of `p` to its end
vertex `v`, i.e. `h : G.Adj (p.getVert i) v`, we split `p` at index `i` using
`Walk.take i` and `Walk.drop i`, which have types `G.Walk u (p.getVert i)` and
`G.Walk (p.getVert i) v` respectively. The rotated walk is then the concatenation of
`p.take i` with the edge from `p.getVert i` to `v` (i.e. `h`) followed by the reverse
of the tail of `p.drop i`, which goes from `v` to `p.getVert (i + 1)`.

[Figure: A Pósa rotation. Top: a path with a chord from $v_i$ to its endpoint $v_k$. Bottom: the rotated path, which ends at $v_{i+1}$](https://jt496.github.io/GraphTheoryInLean/figures/posa.svg)
-/
section bondy_chvatal
variable {V : Type*} {G : SimpleGraph V}
section posa
variable {u v : V} {p : G.Walk u v} {i : ℕ}

/-!
The existence of the edge `h : G.Adj (p.getVert i) v` helpfully implies that
`i < p.length`.
-/
lemma Walk.lt_length_of_adj_getVert_end (h : G.Adj (p.getVert i) v) :
    i < p.length := by
  by_contra!
  exact (p.getVert_of_length_le this ▸ h).ne rfl

/-!
One issue with giving the definition of the Pósa rotation is that although the
reverse of the tail of `p.drop i` goes from `v` to `p.getVert (i + 1)`, this is not
obvious from the type of this walk.
-/
#check (p.drop i).tail.reverse -- G.Walk v (p.drop i).snd

/-!
So to give the definition of Pósa rotation we need to use `Walk.copy` and give a
proof that `(p.drop i).snd = p.getVert (i + 1)` (which simp can provide).
-/
/-- The `i`-th Pósa rotation of a walk `p`. -/
def Walk.posaRotate (p : G.Walk u v) (h : G.Adj (p.getVert i) v) :
  G.Walk u (p.getVert (i + 1)) :=
  (p.take i).append <| cons h ((p.drop i).tail.copy (by simp) rfl).reverse

/-!
If `p` is a path then any Pósa rotation of `p` is also a path. The proof of this
makes heavy use of the `IsPath` dot notation.
-/
/-- The *Pósa rotation* of a path is a path. -/
theorem Walk.IsPath.posaRotate (hp : p.IsPath) (h : G.Adj (p.getVert i) v) :
  (p.posaRotate h).IsPath := by
  -- there are six applications of .IsPath notation in the next line
  apply (hp.take _).append_cons (hp.drop _).tail.copy.reverse
  -- it remains to prove that the two parts of the walk are disjoint
  have hnn : ¬ (p.drop i).Nil := by
    grind [nil_drop_iff, lt_length_of_adj_getVert_end h]
  rw [← p.append_take_drop_eq i, isPath_def, support_append, List.nodup_append',
       ← (p.drop i).support_tail_of_not_nil hnn] at hp
  simpa [-Walk.reverse_tail] using hp.2.2

/-!
The length of a walk is preserved under Pósa rotations.
-/
@[simp, grind =]
theorem Walk.length_posaRotate (p : G.Walk u v) (h : G.Adj (p.getVert i) v) :
    (p.posaRotate h).length = p.length := by
  grind [lt_length_of_adj_getVert_end h, posaRotate, length_append, length_cons,
    length_reverse, length_copy, take_length, Walk.tail, drop_length]

/-!
A Pósa rotation visits exactly the same vertices as the original walk.

Notice that in the last line of the proof below we use `conv_rhs`. At that point we
want to express `p` on the RHS of an `↔` in terms of `p.take i` and `p.drop i` etc,
but if we perform standard rewrites then *every* occurrence of `p` would be replaced,
resulting in a mess that we want to avoid. By using `conv_rhs` we focus on the RHS
and only rewrite there.
-/
@[simp]
lemma Walk.mem_support_posaRotate_iff {u v : V} {i : ℕ} (p : G.Walk u v)
    (h₁ : G.Adj (p.getVert i) v) (x : V) :
    x ∈ (p.posaRotate h₁).support ↔ x ∈ p.support := by
  have hi := lt_length_of_adj_getVert_end h₁
  have hdropnn : ¬ (p.drop i).Nil := by grind [nil_drop_iff]
  rw [posaRotate, mem_support_append_iff, support_cons, List.mem_cons,
      support_reverse, List.mem_reverse, support_copy,
      (p.drop i).support_tail_of_not_nil hdropnn]
  -- see note above about `conv_rhs` and why we use it here
  conv_rhs => rw [← p.append_take_drop_eq i, mem_support_append_iff,
      ← cons_tail_support (p.drop i), List.mem_cons]

/-!
[Figure: Closing a Pósa rotation. Top: the rotated path with an edge from its endpoint $v_{i+1}$ back to $v_0$. Bottom: the resulting cycle](https://jt496.github.io/GraphTheoryInLean/figures/posa_cycle.svg)

If `p` is a walk from `u` to `v` and `h₁ : G.Adj (p.getVert i) v` then we can form
the Pósa rotation ending at `p.getVert (i + 1)`. If there is also an edge
`h₂ : G.Adj (p.getVert (i + 1)) u` then we can use it to close the walk at `u`,
giving a `G.Walk u u`.
-/
/-- The closed walk obtained from a Pósa rotation by concatenating an edge from the
end of the rotated walk to the start of the original walk. -/
def Walk.posaClosed (p : G.Walk u v) (h₁ : G.Adj (p.getVert i) v)
    (h₂ : G.Adj (p.getVert (i + 1)) u) : G.Walk u u := (p.posaRotate h₁).concat h₂

/-!
The walk `p.posaClosed h₁ h₂` contains the same vertices as `p`.
-/
@[simp]
lemma Walk.mem_support_posaClosed_iff {u v : V} {i : ℕ} (p : G.Walk u v)
    (h₁ : G.Adj (p.getVert i) v) (h₂ : G.Adj (p.getVert (i + 1)) u) (x : V) :
    x ∈ (p.posaClosed h₁ h₂).support ↔ x ∈ p.support := by
  grind [posaClosed, support_concat, mem_support_posaRotate_iff, p.start_mem_support]

/-!
The length of the closed Pósa rotation is one more than the length of the original
walk.
-/
@[simp]
lemma Walk.length_posaClosed (p : G.Walk u v) (h₁ : G.Adj (p.getVert i) v)
    (h₂ : G.Adj (p.getVert (i + 1)) u) :
    (p.posaClosed h₁ h₂).length = p.length + 1 := by simp [posaClosed]

/-!
The `concat` analogue of `cons_isCycle_iff_length_ne_one` follows by reversing.
-/
lemma Walk.concat_isCycle_iff_length_ne_one (p : G.Walk u v) (h : G.Adj v u) :
    (p.concat h).IsCycle ↔ p.IsPath ∧ p.length ≠ 1 := by
  rw [← isCycle_reverse, reverse_concat, cons_isCycle_iff_length_ne_one,
    isPath_reverse_iff, length_reverse]

/-!
If `p` is a path of length at least 2 then the `posaClosed` walk is a cycle.
-/
lemma Walk.IsPath.posaClosed_isCycle (hp : p.IsPath) (h2 : 2 ≤ p.length)
    (h₁ : G.Adj (p.getVert i) v) (h₂ : G.Adj (p.getVert (i + 1)) u) :
    (p.posaClosed h₁ h₂).IsCycle :=
  (concat_isCycle_iff_length_ne_one ..).mpr ⟨hp.posaRotate h₁, by grind⟩
end posa

/-!
The key idea in all of the Hamiltonicity theorems we prove below goes back to Dirac.
We state it here with Ore's degree condition. Suppose `p = v₀, v₁, ..., vₖ` (with
`k ≥ 2`) is a *maximal* path whose endpoints, if non-adjacent, satisfy the Ore degree
condition: `deg v₀ + deg vₖ ≥ |V|`. Then `p` can be closed into a cycle containing
exactly the vertices of `p`.

If `v₀` and `vₖ` are adjacent this is immediate. Otherwise the Ore condition gives
`deg v₀ + deg vₖ ≥ |V|`. Every neighbour of `v₀` is `vᵢ₊₁` for some `i < k`, and
every neighbour of `vₖ` is `vⱼ` for some `j < k`. Since a path has distinct vertices,
these indices `i` and `j` form two subsets of `{0, ..., k - 1}` of sizes `deg v₀` and
`deg vₖ`, and `k < |V| ≤ deg v₀ + deg vₖ`. So by pigeonhole the two subsets share an
index `i`, and both edges `vᵢ₊₁ — v₀` and `vᵢ — vₖ` are present: a *crossing pair*.
The Pósa rotation `v₀, ..., vᵢ, vₖ, vₖ₋₁, ..., vᵢ₊₁` followed by the edge `vᵢ₊₁ — v₀`
is then the required cycle (this is the `Walk.posaClosed` we just defined).

## Counting Bijections and a Crossing Pair

We now prove a general counting lemma to help with the informal argument we gave
above. If `p` is a path containing every neighbour of a vertex `x`, and `f : ℕ → ℕ`
maps `{i | i < p.length}` into `{i | i ≤ p.length}`, is injective on
`{n | n < p.length}` and is surjective on `{j | j ≤ p.length ∧ p.getVert j ≠ x}`,
then the indices `i < p.length` with `G.Adj (p.getVert (f i)) x` number exactly
`G.degree x`. As we can see in its proof, the bijection is `i ↦ p.getVert (f i)` onto
the neighbours of `x`.
-/
open Finset

lemma Walk.IsPath.card_filter_adj_getVert_eq_degree [DecidableRel G.Adj] {u v x : V}
    [Fintype (G.neighborSet x)]
    {p : G.Walk u v} (hp : p.IsPath) (hall : ∀ w, G.Adj x w → w ∈ p.support)
    (f : ℕ → ℕ)
    (hf_le : ∀ i ∈ range p.length, f i ≤ p.length)
    (hf_inj : Set.InjOn f (range p.length))
    (hf_surj : ∀ j ≤ p.length, p.getVert j ≠ x → ∃ i ∈ range p.length, f i = j) :
    {i ∈ range p.length | G.Adj (p.getVert (f i)) x}.card = G.degree x := by
  rw [← card_neighborFinset_eq_degree]
  refine card_nbij (fun i => p.getVert (f i)) (fun i hi => ?_)
    (fun i₁ hi₁ i₂ hi₂ heq => ?_) ?_
  · -- `i ↦ p.getVert (f i)` maps the indices of neighbours of `x` to
    -- neighbours of `x`
    simpa [adj_comm] using (mem_filter.1 hi).2
  · -- it is injective on the indices of neighbours of `x`
    rw [coe_filter, Set.mem_ofPred_eq] at hi₁ hi₂
    exact hf_inj hi₁.1 hi₂.1 (hp.getVert_injOn (hf_le _ hi₁.1) (hf_le _ hi₂.1) heq)
  · -- it is surjective onto the neighbours of `x`
    intro w hw
    rw [mem_coe, mem_neighborFinset] at hw
    obtain ⟨n, rfl, hnle⟩ := mem_support_iff_exists_getVert.mp (hall _ hw)
    obtain ⟨i, hi, rfl⟩ := hf_surj n hnle hw.ne'
    exact ⟨i, mem_filter.2 ⟨hi, hw.symm⟩, rfl⟩

/-!
The indices `i < p.length` with `G.Adj (p.getVert (i + 1)) u` biject with the
neighbours of `u`, hence number exactly `G.degree u`. (This is the previous lemma
with `x = u` and `f i = i + 1`.)
-/
lemma Walk.IsPath.card_succ_adj_start [DecidableRel G.Adj] {u v : V}
    [Fintype (G.neighborSet u)]
    {p : G.Walk u v} (hp : p.IsPath) (hall : ∀ w, G.Adj u w → w ∈ p.support) :
    {i ∈ range p.length | G.Adj (p.getVert (i + 1)) u}.card = G.degree u := by
  refine hp.card_filter_adj_getVert_eq_degree hall (· + 1)
    (fun i hi => by grind)
    (fun a _ b _ h => by grind) ?_
  intro n hn hne
  have hn0 : n ≠ 0 := fun h0 => hne ((hp.getVert_eq_start_iff hn).mpr h0)
  exact ⟨n - 1, by grind⟩

/-!
The indices `i < p.length` with `G.Adj (p.getVert i) v` biject with the neighbours
of `v`, hence number exactly `G.degree v`. (This is
`IsPath.card_filter_adj_getVert_eq_degree` with `x = v` and `f i = i`.)
-/
lemma Walk.IsPath.card_adj_end [DecidableRel G.Adj] {u v : V}
    [Fintype (G.neighborSet v)]
    {p : G.Walk u v} (hp : p.IsPath) (hall : ∀ w, G.Adj v w → w ∈ p.support) :
    {i ∈ range p.length | G.Adj (p.getVert i) v}.card = G.degree v := by
  refine hp.card_filter_adj_getVert_eq_degree hall id
    (fun i hi => (mem_range.mp hi).le) (fun a _ b _ h => h) ?_
  intro n hn hne
  have hnl : n ≠ p.length := fun hL => hne ((hp.getVert_eq_end_iff hn).mpr hL)
  exact ⟨n, mem_range.mpr (by grind), rfl⟩

/-!
The next two results are about a *maximal path*. We define this as
`Walk.IsMaximalPath`, a structure extending `Walk.IsPath`. (The `end` field is
written `«end»` because `end` is a Lean keyword; French quotes turn it into an
ordinary name.)

(Compare `Walk.IsMaximumPath` in the exercises: that is the stronger condition
that no path anywhere in `G` is longer.)
-/
/-- A *maximal path*: a path that cannot be extended at either end, or equivalently
one for which every neighbour of either endpoint already lies on it. -/
structure Walk.IsMaximalPath {u v : V} (p : G.Walk u v) : Prop extends
  isPath : p.IsPath where
  /-- Every neighbour of the start vertex lies on the path. -/
  start : ∀ w, G.Adj u w → w ∈ p.support
  /-- Every neighbour of the end vertex lies on the path. -/
  «end» : ∀ w, G.Adj v w → w ∈ p.support

/-!
For a maximal path whose endpoints satisfy Ore's degree sum condition, pigeonhole on
the two counting lemmas gives the crossing pair: an index `i` with both
`G.Adj (p.getVert i) v` and `G.Adj (p.getVert (i + 1)) u`.
-/
lemma Walk.IsMaximalPath.exists_crossing_index [Fintype V] {u v : V}
    [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)] {p : G.Walk u v}
    (hmax : p.IsMaximalPath) (hcard : Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ i, G.Adj (p.getVert i) v ∧ G.Adj (p.getVert (i + 1)) u := by
  classical
  let A := {i ∈ range p.length | G.Adj (p.getVert (i + 1)) u}
  let B := {i ∈ range p.length | G.Adj (p.getVert i) v}
  have hA : A.card = G.degree u := hmax.isPath.card_succ_adj_start hmax.start
  have hB : B.card = G.degree v := hmax.isPath.card_adj_end hmax.end
  -- A path has ≤ `card V` distinct vertices, so `p.length < card V`.
  have hlen : p.length + 1 ≤ Fintype.card V := hmax.isPath.length_lt
  -- `A` and `B` both sit inside `range p.length`, but `|A| + |B| ≥ card V > length`.
  have hsub : A ∪ B ⊆ range p.length :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have hcardU : (A ∪ B).card ≤ p.length :=
    (card_le_card hsub).trans_eq (card_range _)
  have hunion := card_union_add_card_inter A B
  obtain ⟨i, hi⟩ : (A ∩ B).Nonempty := by rw [← card_pos]; grind
  grind

/-!
## Ore's Condition and Closing the Path

We can now put things together. Given a maximal path of length ≥ 2, either the
endpoints are adjacent (so it can be closed with `concat`) or the crossing pair gives
a `Walk.posaClosed`. In both cases we obtain a cycle based at `u` containing exactly
the vertices of `p`, of length `p.length + 1`.

Note that all we need for this is the degree-sum bound for the single pair of
endpoints, and only when they are non-adjacent. This is *Ore's condition* at a
pair of vertices, and since applying it one pair at a time will be a recurring theme,
we make it a definition: `IsOrePair`.
-/
/-- *Ore's condition* at a pair of vertices: if `u` and `v` are distinct and
non-adjacent then their degree sum is at least the number of vertices. (An
adjacent or equal pair satisfies the condition vacuously.) -/
def IsOrePair (G : SimpleGraph V) [Fintype V] (u v : V)
    [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)] : Prop :=
  u ≠ v → ¬ G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v

/-!
The `u ≠ v` condition matters when we require Ore's condition of every pair of
vertices to define an Ore graph below: without it the case `u = v` would demand
`|V| ≤ 2 * deg u` for every vertex, which is Dirac's condition rather than Ore's.
-/

lemma Walk.IsMaximalPath.exists_cycle_spanning [Fintype V] {u v : V}
    [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)] {p : G.Walk u v}
    (hmax : p.IsMaximalPath) (h2 : 2 ≤ p.length) (hcard : G.IsOrePair u v) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = p.length + 1 ∧
      (∀ x, x ∈ c.support ↔ x ∈ p.support) := by
  by_cases huv : G.Adj u v
  · -- Adjacent endpoints: close `p` with `concat`.
    refine ⟨p.concat huv.symm, (concat_isCycle_iff_length_ne_one p huv.symm).mpr
      ⟨hmax.isPath, (by grind)⟩, length_concat .., fun x => ?_⟩
    grind [support_concat, start_mem_support]
  · -- Non-adjacent endpoints: rotate via the crossing pair, close with `posaClosed`.
    have huv_ne : u ≠ v := by grind [isPath_iff_nil, hmax.isPath]
    obtain ⟨i, h₁, h₂⟩ := hmax.exists_crossing_index (hcard huv_ne huv)
    exact ⟨p.posaClosed h₁ h₂, hmax.isPath.posaClosed_isCycle h2 h₁ h₂,
      length_posaClosed .., fun x => by simp⟩

/-!
A Hamiltonian path is trivially maximal, since every vertex lies on it. So a
Hamiltonian path of length at least 2 whose endpoints form an Ore pair closes up into
a cycle visiting every vertex: a Hamiltonian cycle.
-/
lemma Walk.IsHamiltonian.exists_isHamiltonianCycle_of_isOrePair [Fintype V]
    [DecidableEq V] {u v : V} [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)]
    {p : G.Walk u v}
    (hp : p.IsHamiltonian) (h2 : 2 ≤ p.length) (hcard : G.IsOrePair u v) :
    ∃ c : G.Walk u u, c.IsHamiltonianCycle := by
  have hmax : p.IsMaximalPath :=
    ⟨hp.isPath, fun w _ => hp.mem_support w, fun w _ => hp.mem_support w⟩
  obtain ⟨c, hcyc, hclen, -⟩ := hmax.exists_cycle_spanning h2 hcard
  exact ⟨c, isHamiltonianCycle_iff_isCycle_and_length_eq.2
    ⟨hcyc, by grind [hp.length_support, Walk.length_support]⟩⟩

/-!
## The Bondy–Chvátal Theorem

The key observation of Bondy and Chvátal is that the degree condition above is only
ever needed one pair at a time: if `u` and `v` are distinct non-adjacent vertices
with `deg u + deg v ≥ |V|`, then `G` is Hamiltonian iff `G ⊔ edge u v` is
Hamiltonian. Repeatedly adding such edges yields the *closure* of `G`.

The first step towards the Bondy–Chvátal theorem is a piece of cycle surgery. A
Hamiltonian cycle of `G ⊔ edge u v` may use the new edge `u — v`, which is not
available in `G`. Deleting `u — v` from such a cycle `c` should leave a
Hamiltonian path from `u` to `v` that does lie in `G`, and the previous section
then closes this path up into a Hamiltonian cycle of `G`. Hamiltonicity plays no
part in the surgery itself, so we cut open an arbitrary cycle and record what the
resulting path inherits from it.

We first need to prove a simple lemma about darts of a cycle.
-/
#check darts_getElem_eq_getVert
/-!
If `d` is a dart of a cycle `c : G.Walk u u` and the first vertex of `d` is `u`, then
the second vertex of `d` is the second vertex of the cycle.
-/
lemma Walk.IsCycle.snd_eq_of_mem_darts {u : V} {c : G.Walk u u}
    (hc : c.IsCycle) {d : G.Dart} (hd : d ∈ c.darts) (hfst : d.fst = u) :
    d.snd = c.snd := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hd
  rw [darts_getElem_eq_getVert] at hfst ⊢
  have hilt : i < c.length := c.length_darts ▸ hi
  -- the dart leaves `u`, which only occurs at the ends, so its index is `0`
  have h0 : i = 0 := by
    rcases (hc.getVert_endpoint_iff hilt.le).1 hfst with h | h <;> grind
  subst h0
  rfl

/-!
Deleting an edge `u — v` from a cycle `c` leaves a path from `u` to `v` that is one
edge shorter than `c`, visits exactly the vertices of `c`, and avoids `u — v`.

The edge `u — v` of the cycle is the image of a dart, which either points from `u`
to `v` or from `v` to `u` (`dart_edge_eq_mk'_iff'`). Rotating the cycle to be based
at the dart's *first* vertex makes the dart the first dart of the cycle, and the
reversed tail of the rotated cycle then runs from the dart's first vertex to its
second. It is a path, since the tail of a cycle is a path; it visits every vertex of
the cycle, since the base vertex reappears at the end of the tail; and it avoids the
deleted first edge, since a cycle is a trail, so no edge is repeated. This is the
required path in the first case, and its reverse is the required path in the second.
-/
lemma Walk.IsCycle.exists_isPath_of_mem_edges {x u v : V} {c : G.Walk x x}
    (hc : c.IsCycle) (he : s(u, v) ∈ c.edges) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length + 1 = c.length ∧
      (∀ w, w ∈ p.support ↔ w ∈ c.support) ∧ s(u, v) ∉ p.edges := by
  classical
  -- cutting `c` open at a dart from `a` to `b` gives an `a`-`b` path
  have key : ∀ {a b : V}, ∀ d ∈ c.darts, d.fst = a → d.snd = b →
      ∃ p : G.Walk a b, p.IsPath ∧ p.length + 1 = c.length ∧
        (∀ w, w ∈ p.support ↔ w ∈ c.support) ∧ s(a, b) ∉ p.edges := by
    rintro a b d hd rfl rfl
    -- rotate `c` to be based at `d.fst`, so that `d` becomes its first dart
    have ha := c.dart_fst_mem_support_of_mem_darts hd
    have hr := hc.rotate ha
    rw [hr.snd_eq_of_mem_darts ((c.rotate_darts _ ha).perm.mem_iff.2 hd) rfl]
    -- the reversed tail of the rotated cycle is the required path
    refine ⟨_, hr.isPath_tail.reverse, ?_, fun w => ?_, ?_⟩
    · simpa using length_tail_add_one hr.not_nil
    · -- `d.fst` is dropped from the start of the support but is still the end
      have := cons_support_tail hr.not_nil
      grind [support_reverse, end_mem_support, mem_support_rotate_iff]
    · -- no edge is repeated, so the first edge does not occur in the tail
      have hnd := hr.edges_nodup
      rw [← (c.rotate _ ha).cons_tail_eq hr.not_nil, edges_cons] at hnd
      simpa using (List.nodup_cons.1 hnd).1
  -- the edge `u — v` is the image of a dart of `c`
  obtain ⟨d, hd, hde⟩ := List.mem_map.1 he
  rcases dart_edge_eq_mk'_iff'.1 hde with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · -- the dart points from `u` to `v`: cut there
    exact key d hd hfst hsnd
  · -- the dart points from `v` to `u`: cut there and reverse the resulting path
    obtain ⟨p, h1, h2, h3, h4⟩ := key d hd hfst hsnd
    exact ⟨p.reverse, h1.reverse, by simpa using h2, by simpa using h3,
      by simpa [Sym2.eq_swap] using h4⟩

/-!
If the cycle is Hamiltonian then the path visits every vertex, so it is a
Hamiltonian path (`IsPath.isHamiltonian_iff`).
-/
lemma Walk.IsHamiltonianCycle.exists_isHamiltonian_walk_of_mem_edges [DecidableEq V]
    {x u v : V} {c : G.Walk x x} (hc : c.IsHamiltonianCycle)
    (he : s(u, v) ∈ c.edges) :
    ∃ p : G.Walk u v, p.IsHamiltonian ∧ s(u, v) ∉ p.edges := by
  obtain ⟨p, hp, -, hsupp, hpe⟩ := hc.isCycle.exists_isPath_of_mem_edges he
  exact ⟨p, hp.isHamiltonian_iff.2 fun w => (hsupp w).2 (hc.mem_support w), hpe⟩

/-!
### Adding a Single Edge

We can now prove the heart of the Bondy–Chvátal theorem: if `u` and `v` satisfy
Ore's condition `IsOrePair`, then `G ⊔ edge u v` is Hamiltonian iff `G` is.

The interesting direction takes a Hamiltonian cycle `c` of `G ⊔ edge u v`. If `c`
avoids the edge `u — v` then it transfers directly to `G`. Otherwise our previous
lemma cuts `c` open into a Hamiltonian path from `u` to `v` avoiding `u — v`, which
transfers to `G`; since the path is Hamiltonian, every neighbour of `u` and of `v`
trivially lies on it, so `IsHamiltonian.exists_isHamiltonianCycle_of_isOrePair` (via
`IsMaximalPath.exists_cycle_spanning`) closes it back up into a cycle containing all
of `V`, using a crossing pair if `u` and `v` are non-adjacent in `G`. This is where
the degree condition enters. The reverse direction is simply monotonicity of
Hamiltonicity (`IsHamiltonian.mono` in Mathlib).

In both cases we transfer a walk in `G ⊔ edge u v` that avoids the new edge `u — v`
to `G`, so we first record that every edge of such a walk is an edge of `G`.
-/
lemma Walk.edges_mem_edgeSet_of_notMem {u v a b : V} (p : (G ⊔ edge u v).Walk a b)
    (hp : s(u, v) ∉ p.edges) : ∀ e ∈ p.edges, e ∈ G.edgeSet := fun e he => by
  have := p.edges_subset_edgeSet he
  grind [edgeSet_sup, edgeSet_edge_subset]

theorem sup_edge_isHamiltonian_iff [Fintype V] [DecidableEq V] {u v : V}
    [Fintype (G.neighborSet u)] [Fintype (G.neighborSet v)]
    (hcard : G.IsOrePair u v) :
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian := by
  refine ⟨fun hG => ?_, fun hG => hG.mono le_sup_left⟩
  -- dispose of the degenerate cases, where no edge has been added
  by_cases hne : u = v
  · rwa [hne, sup_edge_self] at hG
  by_cases hadj : G.Adj u v
  · rwa [G.sup_edge_of_adj hadj] at hG
  intro h1
  obtain ⟨a, c, hc⟩ := hG h1
  -- the graph has at least three vertices, since it has a cycle
  have h3 : 3 ≤ Fintype.card V := hc.length_eq ▸ hc.isCycle.three_le_length
  by_cases hmem : s(u, v) ∈ c.edges
  · -- the cycle uses the new edge: cut it open into a Hamiltonian path
    obtain ⟨p, hham, hpe⟩ := hc.exists_isHamiltonian_walk_of_mem_edges hmem
    -- the path avoids the new edge, so it transfers to `G`, where we close it up
    have hq := hham.transfer (p.edges_mem_edgeSet_of_notMem hpe)
    exact ⟨u, hq.exists_isHamiltonianCycle_of_isOrePair (by grind [hq.length_eq])
      hcard⟩
  · -- the cycle avoids the new edge: transfer it to `G` directly
    exact ⟨a, _, hc.transfer (c.edges_mem_edgeSet_of_notMem hmem)⟩

/-!
### The Closure of a Graph

Call a pair of vertices *eligible* if they are distinct, non-adjacent, and have
degree sum at least `|V|`. Any eligible pair is an `IsOrePair`, but not conversely:
an adjacent pair satisfies `IsOrePair` vacuously but is not eligible.

By `sup_edge_isHamiltonian_iff`, adding an edge between an eligible pair does not
change whether the graph is Hamiltonian, so we now simply keep adding such edges
until no eligible pair remains. The resulting graph is the
*Bondy–Chvátal closure* of `G`. A graph with no eligible pair, i.e. one in which any
two distinct vertices with degree sum at least `|V|` are already adjacent, is called
*closed*. (As we will see below, Mathlib's theory of closure operators
uses the same word for the same idea.)
-/
/-- A graph is *closed* (in the sense of Bondy and Chvátal) if it has no eligible
pair: any two distinct vertices with degree sum at least `|V|` are adjacent. -/
def IsClosed (G : SimpleGraph V) [Fintype V] [G.LocallyFinite] : Prop :=
  ∀ ⦃x y⦄, x ≠ y → Fintype.card V ≤ G.degree x + G.degree y → G.Adj x y

/-!
How should we define such a repeated process in Lean? Every function must be
total, so Lean has to be convinced that the recursion terminates. Our process
does terminate: each step adds an edge, and there are only finitely many. A standard
trick for such definitions is to add *fuel*: an extra natural number parameter that
decreases by one at each recursive call. The recursion is then structural (on the
fuel), so Lean accepts it with no termination proof at all.

Since this is our first encounter with fuel, we illustrate the idea with a simple
example: computing the remainder of a division.

In `modAux` below, the remainder `a % b` is computed by repeated subtraction, using
one unit of fuel per subtraction. (The test `0 < b` ensures we never waste time
subtracting zero, and matches Lean's convention that `a % 0 = a`.)
-/
/-- Subtract `b` from `a` while `0 < b ≤ a`, at most `fuel` times. -/
private def modAux : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | fuel + 1, a, b => if 0 < b ∧ b ≤ a then modAux fuel (a - b) b else a

/-!
If we start with enough fuel, `modAux` computes the remainder of `a` on division by
`b`.
-/
#eval modAux 6 17 5  -- 2 = 17 % 5
/-!
However if we start with too little fuel the computation may terminate too soon,
giving the wrong answer.
-/
#eval modAux 2 17 5   -- 7
/-!
How much fuel do we need? Since each subtraction reduces `a` by at least one,
starting with `fuel` equal to `a` is always enough to reach the remainder. (This can
easily be proved by induction on the fuel, the same pattern we use for the closure
below.)

Returning to the Bondy–Chvátal closure, the textbook definition adds eligible edges
one at a time, in any order. In Lean it is more convenient to proceed in rounds: in
each round we join all pairs that are currently eligible. A round adds at least one
edge unless the graph is already closed, so starting with `fuel` equal to the number
of missing edges of `G` (the number of edges in its complement `Gᶜ`) is enough to
reach a closed graph. Adding all eligible pairs at once also means that we never have
to choose an order in which to add them, so the closure is computable (at least in
principle; see below).

A single round, `closureStep` below, is `G ⊔ fromRel r`, where `r u v` says that `u`
and `v` have degree sum at least `|V|`. The graph `SimpleGraph.fromRel r` joins
distinct `u` and `v` whenever `r u v` or `r v u`, so the new edges join exactly the
eligible pairs. Since `closureStep` is an `abbrev`, Lean can see through it and find
its `DecidableRel` instance automatically, from those for `⊔` and `fromRel`.
-/
/-- One round of the closure process: join all eligible pairs of `G`. -/
abbrev closureStep [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : SimpleGraph V :=
  G ⊔ fromRel fun u v => Fintype.card V ≤ G.degree u + G.degree v

lemma closureStep_adj [Fintype V] [DecidableRel G.Adj] {x y : V} :
    G.closureStep.Adj x y ↔
      G.Adj x y ∨ x ≠ y ∧ Fintype.card V ≤ G.degree x + G.degree y := by
  simp [add_comm]

/-!
Iterating `closureStep` needs a `DecidableRel` instance for each intermediate graph,
so `closureAux` takes the instance for its graph as an argument, and each recursive
call uses the instance for `G.closureStep` above.
-/
/-- Run `fuel` rounds of the closure process. -/
def closureAux [Fintype V] [DecidableEq V] :
    ℕ → (G : SimpleGraph V) → [DecidableRel G.Adj] → SimpleGraph V
  | 0, G, _ => G
  | fuel + 1, G, _ => closureAux fuel G.closureStep

variable (G) in
/-- The *Bondy–Chvátal closure* of `G`: repeatedly join eligible pairs (distinct
non-adjacent vertices with degree sum at least `|V|`) until none remain. -/
def closure [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : SimpleGraph V :=
  closureAux #Gᶜ.edgeFinset G

/-!
The main result about the closure is the Bondy–Chvátal theorem: taking the closure
does not change whether the graph is Hamiltonian. Before proving it we record two
basic facts: the closure contains the original graph, and with enough fuel it really
is closed. We start with the first of these.
-/
lemma le_closureStep [Fintype V] [DecidableRel G.Adj] :
    G ≤ closureStep G := le_sup_left

lemma le_closureAux [Fintype V] [DecidableEq V] :
    ∀ (fuel : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], G ≤ closureAux fuel G
  | 0, _, _ => le_rfl
  | fuel + 1, G, _ => le_closureStep.trans (le_closureAux fuel G.closureStep)

theorem le_closure [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G ≤ G.closure := le_closureAux ..

/-!
Next, with enough fuel the closure really is closed. We first record that a round
leaves a graph unchanged if the graph is closed, so that once the process reaches a
closed graph it stays there. Since `IsClosed` takes a `LocallyFinite` argument, we
also need to transport closedness along an equality of graphs whose instances are
unrelated; `convert` handles the instances.
-/
lemma IsClosed.of_eq [Fintype V] {H : SimpleGraph V} [G.LocallyFinite]
    [H.LocallyFinite] (hGH : G = H) (hG : G.IsClosed) : H.IsClosed := by
  subst hGH
  convert hG

lemma IsClosed.closureStep_eq [Fintype V] [DecidableRel G.Adj]
    (hG : G.IsClosed) : closureStep G = G :=
  le_antisymm (fun _ _ h => (closureStep_adj.1 h).elim id fun ⟨hne, hd⟩ => hG hne hd)
    le_closureStep

lemma closureAux_eq_self [Fintype V] [DecidableEq V] :
    ∀ (fuel : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], G.IsClosed →
      closureAux fuel G = G
  | 0, _, _, _ => rfl
  | fuel + 1, G, _, hG =>
    (closureAux_eq_self fuel G.closureStep
      (hG.of_eq hG.closureStep_eq.symm)).trans hG.closureStep_eq

/-!
To even state that `G.closure` is closed we need a `DecidableRel` instance for its
adjacency relation. We define one by recursion on the fuel, from the instances for
`closureStep` above. This makes adjacency in the closure decidable, but only in
principle: deciding adjacency after `k` rounds needs the degrees after `k - 1`
rounds, each of which needs `|V|` adjacency queries after `k - 1` rounds, and so on,
so the cost grows exponentially with the number of rounds. (This could be made much
more efficient but we do not need to do so here: just don't try to evaluate it on
anything with more than a few vertices!)
-/
instance decidableRelClosureAux [Fintype V] [DecidableEq V] :
    ∀ (fuel : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj],
      DecidableRel (closureAux fuel G).Adj
  | 0, _, h => h
  | fuel + 1, G, _ => decidableRelClosureAux fuel G.closureStep

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel G.closure.Adj :=
  decidableRelClosureAux _ G

/-!
For example, `C[5]` with the two chords `0 — 2` and `0 — 3` added has 7 edges. It is
not an Ore graph: the non-adjacent vertices `1` and `4` both have degree `2`, so
their degree sum is `4 < 5`. But the first round joins the eligible pairs `1, 3` and
`2, 4`, after which `1` and `4` both have degree `3`, so the second round joins them
too, and the closure is the complete graph with `10` edges. So the closure can be
complete even when Ore's condition fails.

[Figure: Taking the closure of $C_5$ with the chords `0 — 2` and `0 — 3`](https://jt496.github.io/GraphTheoryInLean/figures/closure_rounds.svg)
-/
#eval (C[5] ⊔ edge 0 2 ⊔ edge 0 3).edgeFinset             -- 7 edges
#eval (C[5] ⊔ edge 0 2 ⊔ edge 0 3).closureStep.edgeFinset -- 9 edges
#eval (C[5] ⊔ edge 0 2 ⊔ edge 0 3).closure.edgeFinset    -- 10 edges (complete)

/-!
Conversely, a round leaves `G` unchanged only if `G` is closed, since it joins every
eligible pair. So if `G` is not closed then a round adds at least one missing edge,
and the number of missing edges strictly decreases.
-/
lemma isClosed_iff_closureStep_eq [Fintype V] [DecidableRel G.Adj] :
    G.IsClosed ↔ G.closureStep = G := by
  refine ⟨IsClosed.closureStep_eq, fun h x y hne hd => ?_⟩
  have : G.closureStep.Adj x y := closureStep_adj.2 (Or.inr ⟨hne, hd⟩)
  rwa [h] at this

lemma card_compl_edgeFinset_closureStep_lt [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : ¬G.IsClosed) :
    #(G.closureStep)ᶜ.edgeFinset < #Gᶜ.edgeFinset := by
  have hlt : G < G.closureStep :=
    lt_of_le_of_ne le_closureStep fun h => hG (isClosed_iff_closureStep_eq.2 h.symm)
  exact Finset.card_lt_card
    (edgeFinset_ssubset_edgeFinset.2 (compl_lt_compl_iff_lt.2 hlt))

/-!
We can now prove that the closure is closed, by induction on the fuel: each round
that changes the graph decreases the number of missing edges, which can never go
below zero, so if we start with enough fuel then the process must terminate with a
closed graph.
-/
lemma isClosed_closureAux [Fintype V] [DecidableEq V] :
    ∀ (fuel : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], #Gᶜ.edgeFinset ≤ fuel →
      (closureAux fuel G).IsClosed
  | 0, G, _, hf => by
    -- with no fuel left, `G` has no missing edges, so no eligible pair either
    intro x y hne _
    by_contra hadj
    have : s(x, y) ∈ Gᶜ.edgeFinset := by simpa [hne, closureAux] using hadj
    simp_all
  | fuel + 1, G, _, hf => by
    by_cases hG : G.IsClosed
    · -- `G` is already closed, and the closure does not change it
      exact hG.of_eq (closureAux_eq_self (fuel + 1) G hG).symm
    · -- some eligible pair is not yet adjacent, so a missing edge is added
      have := card_compl_edgeFinset_closureStep_lt hG
      exact isClosed_closureAux fuel G.closureStep (by grind)
/-!
The closure of a graph is closed.
-/
theorem isClosed_closure [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G.closure.IsClosed :=
  isClosed_closureAux _ G le_rfl

/-!
We now prove the Bondy–Chvátal theorem. The lemma `sup_edge_isHamiltonian_iff` adds
a single edge, whereas a round may add many, so we first add the edges of a round
one at a time, by induction on a finset of pairs. Each pair was eligible in `G`, and
adding edges only increases degrees, so it is still an `IsOrePair` in each of the
intermediate graphs. (These intermediate graphs carry no `LocallyFinite` instances
of their own, so the proof starts with `classical` to supply them.)
-/
/-!
Adding any finite set of pairs that are eligible in `G` preserves
Hamiltonicity.
-/
lemma sup_sup_edge_isHamiltonian_iff [Fintype V] [DecidableEq V] [G.LocallyFinite]
    (s : Finset (V × V))
    (hs : ∀ p ∈ s, Fintype.card V ≤ G.degree p.1 + G.degree p.2) :
    (G ⊔ s.sup fun p => edge p.1 p.2).IsHamiltonian ↔ G.IsHamiltonian := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    -- `p` still satisfies the degree condition in the bigger graph: degrees only
    -- grow when edges are added
    have hore : (G ⊔ s.sup fun q => edge q.1 q.2).IsOrePair p.1 p.2 := by
      intro _ _
      have hp' := hs p (Finset.mem_insert_self p s)
      exact hp'.trans (Nat.add_le_add (degree_le_of_le le_sup_left)
        (degree_le_of_le le_sup_left))
    rw [Finset.sup_insert, sup_comm (edge p.1 p.2), ← sup_assoc,
      sup_edge_isHamiltonian_iff hore,
      ih fun q hq => hs q (Finset.mem_insert_of_mem hq)]

/-!
A round adds exactly the edges `edge x y` for the pairs `(x, y)` with degree sum at
least `|V|` (for `x = y` the graph `edge x x` has no edges, so we don't need to
exclude them), so a round does not change whether the graph is Hamiltonian, and nor
does taking the closure.
-/
lemma closureStep_isHamiltonian_iff [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] : G.closureStep.IsHamiltonian ↔ G.IsHamiltonian := by
  let s : Finset (V × V) := {p | Fintype.card V ≤ G.degree p.1 + G.degree p.2}
  have hs : closureStep G = G ⊔ s.sup fun p => edge p.1 p.2 := by
    ext x y
    simp only [s, Finset.sup_eq_iSup, sup_adj, iSup_adj, edge_adj, mem_filter,
      mem_univ, true_and]
    aesop
  rw [hs, sup_sup_edge_isHamiltonian_iff _ fun p hp => by simpa [s] using hp]

lemma closureAux_isHamiltonian_iff [Fintype V] [DecidableEq V] :
    ∀ (fuel : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj],
      (closureAux fuel G).IsHamiltonian ↔ G.IsHamiltonian
  | 0, _, _ => Iff.rfl
  | fuel + 1, G, _ =>
    (closureAux_isHamiltonian_iff fuel G.closureStep).trans
      closureStep_isHamiltonian_iff

/-- *Bondy–Chvátal theorem*: a graph is Hamiltonian iff its closure is. -/
theorem closure_isHamiltonian_iff [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G.closure.IsHamiltonian ↔ G.IsHamiltonian := closureAux_isHamiltonian_iff ..

/-!
## Ore's Theorem and Dirac's Theorem

Combining the Bondy–Chvátal theorem `closure_isHamiltonian_iff` with
`top_isHamiltonian`, proved back in
[Cycle Graphs and Complete Graphs are Hamiltonian](https://jt496.github.io/GraphTheoryInLean/Walks/#section-cycle-graphs-and-complete-graphs-are-hamiltonian),
gives the form we need: if `G` has at least 3 vertices and its closure is complete
then `G` is Hamiltonian.
-/
theorem isHamiltonian_of_closure_eq_top [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V) (h : G.closure = ⊤) :
    G.IsHamiltonian := by
  rw [← closure_isHamiltonian_iff, h]
  exact top_isHamiltonian hn

/-- An *Ore graph*: every pair of vertices satisfies Ore's condition `IsOrePair`,
i.e. any two distinct non-adjacent vertices have degree sum at least the
number of vertices. -/
def IsOreGraph (G : SimpleGraph V) [Fintype V] [G.LocallyFinite] : Prop :=
  ∀ x y, G.IsOrePair x y

/-!
Ore's theorem is now a corollary: the closure of an Ore graph is complete. Two
observations make this trivial. Firstly, Ore's condition is inherited by any
supergraph: if `x ≠ y` are non-adjacent in `H ≥ G` then they are non-adjacent in `G`,
so Ore's condition gives them degree sum at least `|V|` in `G`, hence also in `H`.
-/
lemma IsOreGraph.mono [Fintype V] [G.LocallyFinite] {H : SimpleGraph V}
    [H.LocallyFinite] (hG : G.IsOreGraph)
    (hGH : G ≤ H) : H.IsOreGraph := fun x y hne hnadj =>
  (hG x y hne (fun h => hnadj (hGH h))).trans
    (Nat.add_le_add (degree_le_of_le hGH) (degree_le_of_le hGH))

/-!
Secondly, Ore's condition and closedness are complementary: the former says that
non-adjacent pairs have degree sum at least `|V|`, the latter that such pairs are
adjacent. So a closed Ore graph is complete.
-/
lemma IsOreGraph.eq_top_of_isClosed [Fintype V] [G.LocallyFinite]
    (hO : G.IsOreGraph) (hC : G.IsClosed) : G = ⊤ :=
  eq_top_iff.2 fun x y hne => by_contra fun hn => hn (hC hne (hO x y hne hn))

/-!
The closure of `G` is a closed graph above `G`, so it inherits Ore's condition and is
therefore complete.
-/
theorem IsOreGraph.closure_eq_top [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [G.LocallyFinite] (h : G.IsOreGraph) : G.closure = ⊤ :=
  (h.mono le_closure).eq_top_of_isClosed isClosed_closure

/-- *Ore's theorem*: a finite graph on at least three vertices in which every pair
of non-adjacent vertices has degree sum at least `|V|` is Hamiltonian. -/
theorem IsOreGraph.isHamiltonian [Fintype V] [DecidableEq V] [G.LocallyFinite]
    (h : G.IsOreGraph) (hn : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
  classical
  exact isHamiltonian_of_closure_eq_top hn h.closure_eq_top

/-!
Dirac's theorem is an immediate corollary. We state this as `|V| ≤ 2 * δ(G)` rather
than `|V| / 2 ≤ δ(G)`, because `Nat` division rounds down: for odd `|V|` the latter
is a strictly weaker assumption and the statement would then be false. (Two triangles
sharing a vertex have `|V| = 5` and `δ(G) = 2 = 5 / 2`, but the shared vertex is a
cut vertex, so the graph has no Hamiltonian cycle.)
-/
/-- *Dirac's theorem*: a finite graph on at least three vertices satisfying
`|V| ≤ 2 * δ(G)` is Hamiltonian. -/
theorem isHamiltonian_of_card_le_two_mul_minDegree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (hdeg : Fintype.card V ≤ 2 * δ(G)) :
    G.IsHamiltonian := by
  apply IsOreGraph.isHamiltonian (fun x y _ _ => ?_) hn
  grind [G.minDegree_le_degree x, G.minDegree_le_degree y]

/-!
Since our aim is to give as many examples as possible of different graph-theoretic
proof techniques in Lean, we also give the more direct classical proof of Ore's
theorem, via maximum-length paths. This approach is developed in the exercises to
this chapter.

## The Closure is the Least Closed Supergraph

Our construction proceeds in rounds, whereas the textbook definition adds eligible
pairs one at a time, in any order. A natural question is: could different orders
produce a different "closure"? It is easy to see that this is not the case. The key
observation is that a closed graph absorbs eligible edges: suppose `G ≤ K` with `K`
closed, and let `u`, `v` be an eligible pair in `G`. Adding edges only increases
degrees, so `u` and `v` also have degree sum at least `|V|` in `K`, and since `K` is
closed they must be adjacent there; hence `G ⊔ edge u v ≤ K`. Iterating, every graph
obtained from `G` by adding eligible edges, in any order (or in rounds), lies below
every closed graph above `G`. So if two runs of the process stop at closed graphs
`K₁` and `K₂`, then `K₁ ≤ K₂` and `K₂ ≤ K₁`, hence they are equal.

For our rounds the absorption argument is again an induction on fuel.
-/
lemma closureStep_le [Fintype V] [DecidableRel G.Adj]
    {K : SimpleGraph V} [K.LocallyFinite] (hGK : G ≤ K) (hK : K.IsClosed) :
    closureStep G ≤ K := by
    intro v w h
    apply (closureStep_adj.1 h).elim (fun h1 => hGK h1)
    rintro ⟨hne, hd⟩
    exact hK hne <| hd.trans
      <| Nat.add_le_add (degree_le_of_le hGK) (degree_le_of_le hGK)

lemma closureAux_le [Fintype V] [DecidableEq V] :
    ∀ (fuel : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (K : SimpleGraph V)
      [K.LocallyFinite], G ≤ K → K.IsClosed → closureAux fuel G ≤ K
  | 0, _, _, _, _, hGK, _ => hGK
  | fuel + 1, G, _, K, _, hGK, hK =>
    closureAux_le fuel G.closureStep K (closureStep_le hGK hK) hK

theorem closure_min [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {K : SimpleGraph V} [K.LocallyFinite] (hGK : G ≤ K) (hK : K.IsClosed) :
    G.closure ≤ K :=
  closureAux_le _ _ _ hGK hK

/-!
So `G.closure` is the *least* closed graph above `G`: a characterization that
mentions neither fuel nor rounds. Any other implementation of the closure process
must therefore produce exactly the same graph; in particular the closure does not
depend on the order in which eligible pairs are joined. Monotonicity and idempotence
of the closure follow easily.
-/
theorem closure_mono [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {H : SimpleGraph V} [DecidableRel H.Adj] (h : G ≤ H) :
    G.closure ≤ H.closure :=
  closure_min (h.trans le_closure) isClosed_closure

@[simp]
theorem closure_closure [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G.closure.closure = G.closure :=
  le_antisymm (closure_min le_rfl isClosed_closure) le_closure

end bondy_chvatal
/-!
A monotone map on a partial order that is *inflationary* (`G ≤ G.closure`) and
*idempotent* (`G.closure.closure = G.closure`) is what Mathlib calls a
`ClosureOperator`, and Mathlib also calls its fixed points *closed*. (Packaging
`closure` as a `ClosureOperator (SimpleGraph V)` takes a little more work, since
`G.closure` needs a `DecidableRel G.Adj` instance, which an arbitrary graph does not
come with.)
-/
#check ClosureOperator

end SimpleGraph
