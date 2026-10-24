import GraphTheoryInLean.C02_SimpleGraph.C02_SimpleGraph
import GraphTheoryInLean.C03_Constructions.C03_Constructions
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
namespace SimpleGraph
/-!
This chapter is about *computing* with graphs in Lean, and about the typeclass
machinery that makes computation possible. We begin with decidability: the contrast
between `Bool` and `Prop`, the `Decidable` class, the commands and tactics that use
it (`#eval`, `decide` and `native_decide`), and the `DecidableRel G.Adj` instances
required to decide adjacency. We then turn to finiteness, starting from the hierarchy
`List` → `Multiset` → `Finset` and arriving at `Fintype`, which is *data*, and
`Finite`, which is a proposition. Along the way we compare the ways Mathlib has of
counting the elements of a finite type or set. A point we return to more than once is
that because `Fintype` instances are data, the same type can receive two different
instances by two different routes of typeclass inference. This is known as a
*diamond*, after the shape of the two routes meeting at one type. Such a diamond is a
nuisance rather than a feature: the two instances are always equal, but not
*by definition*, so a theorem stated using one instance will not apply to a goal that
uses the other. We will see how to state theorems so that this does not happen.

The second half applies all this to graphs. We study finite neighbourhoods and vertex
degrees (including minimum and maximum degree, the handshake lemma and regular
graphs). We then compute with two families of graphs, hypercubes and Mycielskians,
building the `DecidableRel` and `Fintype` instances needed both to evaluate and to
prove facts about their degrees and edge counts.

Finally, an advanced section on degree sequences defines the degree multiset of a
graph, asks which multisets are *graphic*, states, without proof, the Erdős–Gallai
and Havel–Hakimi characterizations, and turns the latter into a function that
computes the edges of a graph with a given graphic degree sequence.

# Decidability

In classical logic the *law of the excluded middle* says that every proposition is
either true or false. For proofs this is very useful: it allows us to reason by
cases. In one branch of a proof we assume `p` holds and in the other we assume `¬ p`
holds. But for computations this isn't very helpful: we want to know *which* branch
to take.

## Bool and Prop

Lean has two different types that can play the role of truth-values. The first is
`Bool`, the ordinary inductive type with two elements `true` and `false`, which we
used for the vertices of the hypercube (`HypercubeVert`). The second is `Prop`, the
type of propositions: a term `p : Prop` is a statement, and a term `h : p` is a proof
of that statement.

The difference is that a `Bool` is a value that a program can compute and branch on,
while a `Prop` is a statement that we may or may not be able to prove. Lean provides
the usual Boolean operations `&&` (and), `||` (or) and `!` (not), each defined simply
by matching on `true` and `false`, and `bif b then x else y` returns `x` or `y`
according to the value of `b`. Combining these gives expressions that `#eval` can
evaluate.
-/
#eval bif !false && (false || true) then "apples" else "pears" -- "apples"

/-!
Lean has other `Bool`-valued functions such as `Nat.beq m n`, which checks whether
`m = n` by recursion on `ℕ`. We can use it to write a parity test.
-/
/-- Return `true` if `n` is even, `false` otherwise. -/
private def myEven (n : ℕ) : Bool := Nat.beq (n % 2) 0

#eval myEven 42 -- true
#eval myEven 123 -- false

/-!
Compare this with Mathlib's `Even`, which is a predicate: `Even n` is the statement
that `n = r + r` for some `r`. Nothing in this definition tells Lean how to find `r`,
or how to show that no such `r` exists.
-/
#print Even -- def Even : {α : Type u_2} → [Add α] → α → Prop :=
            --   fun {α} [Add α] a ↦ ∃ r, a = r + r
/-!
Mathlib states almost everything using `Prop`, since propositions can be quantified
over, rewritten with, and proved by any argument at all, constructive or not.

Going from `Bool` to `Prop` is easy: Lean coerces `b : Bool` to the proposition
`b = true`.
-/
#check fun b : Bool => (b : Prop) -- fun b ↦ b = true : Bool → Prop

/-!
Going from `Prop` to `Bool` is the hard direction, and this is exactly what the
decidability typeclass provides.

## The Decidable Class

To compute with a proposition we need to turn it into a `Bool`, that is, to *decide*
whether it is true or false. In computability theory, decidability is a property of a
*family* of propositions, such as "`n` is prime" for `n : ℕ`: the family is
*decidable* if there is a single algorithm that, given `n`, determines whether the
proposition holds. For one fixed proposition this notion is vacuous, since one of the
two algorithms "answer true" and "answer false" is always correct, even if we do not
know which.

In Lean, decidability is expressed by the typeclass `Decidable`. An instance of
`Decidable p` is not the claim that `p` is decidable but a piece of *data*: a Boolean
`decide p` giving the answer, packaged with a proof that this answer is correct.
-/
#source Decidable -- class Decidable (p : Prop) where
                  --   intro ::
                  --   decide : Bool
                  --   reflects_decide (p) : decide.Reflects p

/-!
The proof field uses `Bool.Reflects`, which is defined so that `true.Reflects p` is
`p` and `false.Reflects p` is `¬ p`. So an instance of `Decidable p` is either
`⟨true, h⟩` with `h : p`, or `⟨false, h⟩` with `h : ¬ p`, and Lean names these two as
`Decidable.isTrue h` and `Decidable.isFalse h`. Proofs are erased when code is
compiled, so evaluating an instance amounts to computing the Boolean `decide p`,
which tells us whether `p` is true or false.

So how do we provide such instances? Given a proof of `p` or `¬ p` we can construct a
`Decidable p` instance directly:
-/
example {p : Prop} (h : p) : Decidable p := ⟨true, h⟩
example {p : Prop} (h : ¬p) : Decidable p := ⟨false, h⟩
example {p : Prop} (h : p) : Decidable p := isTrue h

/-!
Instances like these do no computation of their own: they simply record an answer we
already know. Useful `Decidable` instances contain an algorithm that computes the
answer, and Lean can usually find a suitable instance automatically, as we now
explain.

`Decidable` is a *class*: a structure whose values, called *instances*, Lean finds
for us. Each `instance` declaration, in Mathlib or in our own files, registers a way
of building one, possibly from other instances. When a definition or theorem has an
argument in square brackets, an *instance argument* such as the `[Add α]` in `Even`
above, the caller does not supply it. Lean finds it by *typeclass inference*: it
searches the hypotheses in the local context first and then the registered instances,
combining instances as needed. (We also say that Lean *synthesizes* the instance, and
call this process *instance search*.) The term `inferInstance` and the tactic
`infer_instance` both ask for an instance in the same way.
-/
private def natNeDec (a b : ℕ) : Decidable (a ≠ b) := inferInstance

private def natEvenDec (m : ℕ) : Decidable (Even m) := by infer_instance

/-!
Using `#print` with `set_option pp.explicit true` below we can see exactly which
instance Lean has synthesized. For `Decidable (a ≠ b)`, Lean uses the instance
`instDecidableNot` to infer `Decidable (a ≠ b)` from the instance of decidable
equality on ℕ, `DecidableEq ℕ`, provided by `instDecidableEqNat`.
-/
#check instDecidableNot -- {p : Prop} [dp : Decidable p] : Decidable ¬p
#check instDecidableEqNat -- DecidableEq ℕ

set_option pp.explicit true in
#print natNeDec -- @inferInstance (Decidable (@Ne Nat a b))
                --      (@instDecidableNot (@Eq Nat a b) (instDecidableEqNat a b))

/-!
For `Decidable (Even m)` it uses the instance `Nat.instDecidablePredEven`, which says
that `Even : ℕ → Prop` is a decidable predicate (i.e. `Even m` is decidable for every
`m : ℕ`).
-/
#check Nat.instDecidablePredEven -- DecidablePred Even

/-!
Both examples are really families of instances: the arguments `(a b : ℕ)` and
`(m : ℕ)` make `natNeDec` and `natEvenDec` functions that produce a `Decidable`
instance for every choice of these arguments.

Once the arguments are supplied, the Boolean `decide` in each of these instances
evaluates to `true` or `false`. This allows us to use `Decidable` instances to
perform computations that depend on the truth-value of a proposition.

For example, the following function takes a decidable proposition `p`, computes the
Boolean `decide p` from its `Decidable p` instance, and branches on it with `bif` to
return a string telling us the truth-value of `p`.
-/
/-- Given a decidable proposition `p`, return a string indicating its truth-value. -/
def myIfThenElse (p : Prop) [Decidable p] : String :=
  bif decide p then "This is true" else "This is false"

#eval myIfThenElse (Even 42) -- "This is true"
#eval myIfThenElse (42 ≠ 42) -- "This is false"
example : myIfThenElse (12 + 12 ≠ 24) = "This is false" := by decide

/-!
In fact `if-then-else` conditionals are defined in almost exactly this way in Lean,
using the `ite` function, which branches on the Boolean `decide c`.
-/
#check ite -- {α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α

/-!
For comparison, the law of the excluded middle gives *every* proposition a
`Decidable` instance, `Classical.propDecidable`. It is built from `Classical.em`
using the axiom of choice, so it asserts that one of `isTrue h` or `isFalse h` exists
without saying which: it contains no algorithm and cannot be evaluated.
-/
#check Classical.propDecidable -- (a : Prop) : Decidable a

/-!
The `classical` tactic makes this instance available for the rest of a proof or
definition, but only as a fallback: if typeclass inference finds a genuine
`Decidable p` instance, that is used instead. In `myClassicalIfThenElse` below, `p`
is an arbitrary proposition with no `Decidable p` instance, so the `if-then-else`
uses `Classical.propDecidable`, and Lean refuses to compile the definition unless we
mark it `noncomputable`.
-/
/-- Given a proposition `p`, return a string indicating its truth-value. -/
noncomputable def myClassicalIfThenElse (p : Prop) : String := by
  classical
  exact if p then "This is true" else "This is false"

/-!
Printing the definition with explicit arguments shows an ordinary call to `ite`, in
which `classical` has supplied `Classical.propDecidable p` as the `Decidable p`
instance.
-/
set_option pp.explicit true in
#print myClassicalIfThenElse -- fun p ↦ @ite String p (Classical.propDecidable p) ..

/-!
Classical instances are not always avoidable: sometimes no algorithm exists. Equality
of real numbers is an obvious example. No algorithm can decide, for an arbitrary pair
of reals `x` and `y`, whether `x = y`, since it can only examine finitely many
rational approximations to each, and these may agree to every precision checked even
though `x ≠ y`.

Mathlib still provides an instance of `DecidableEq ℝ`, but it is built using
classical reasoning and so is noncomputable. It can be used in proofs but not in
computations.
-/
#synth DecidableEq ℝ -- Real.decidableEq

/-- error: failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'Real.decidableEq', which is 'noncomputable' -/
#guard_msgs (substring := true) in
#eval decide ((1 : ℝ) ≠ 2)

/-!
The families of instances we saw for `natNeDec` and `natEvenDec` are typical: an
algorithm in the computability sense corresponds to a family of `Decidable`
instances, one for each input. Lean has names for the two most common ones. For a
predicate `P : α → Prop`, `DecidablePred P` provides a `Decidable (P x)` instance for
every `x : α`.
-/
#source DecidablePred -- abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
                      --   (a : α) → Decidable (r a)
/-!
For example, the predicate `Nat.Prime : ℕ → Prop`, which expresses whether a number
is prime, is decidable.
-/
#synth DecidablePred  (fun n : ℕ => n.Prime) -- Nat.decidablePrime
#eval Nat.Prime 337031327       -- true
#eval Nat.Prime (337031327 + 1) -- false

/-!
We also have `DecidableRel r` for any relation `r : α → β → Prop`. This says that
`r a b` is decidable for every `a : α` and `b : β`, or more precisely, it provides an
instance of `Decidable (r a b)` for every `a : α` and `b : β`.
-/
#source DecidableRel  -- DecidableRel {α : Sort u} {β : Sort v} (r : α → β → Prop) :=
                      --            (a : α) → (b : β) → Decidable (r a b)
/-!
This last example is particularly relevant for graphs, since the adjacency relation
of a graph is a relation on the vertex set. For a graph `G : SimpleGraph V`, ensuring
that we have an instance of `DecidableRel G.Adj` allows us to perform computations
that depend on the truth-value of adjacency.
-/
#synth DecidableRel (fun a b : ℕ => a = b)  -- instDecidableEqNat
#synth DecidableRel (⊤ : SimpleGraph ℕ).Adj -- fun a b ↦ Top.adjDecidable ℕ a b
/-!
## Evaluating and Deciding

We have already used `#eval` and `decide` informally above and in earlier chapters.
So what do they do and how are they related to decidability?

Of the two `#eval` is the more powerful. It *runs* a program: the expression is
compiled and then executed, and the resulting value is printed. Nothing is proved
(the result never reaches Lean's kernel), but any value can be computed, and usually
quickly. So long as the output of the program is a value that can be printed, `#eval`
will work.

For example, `#eval` can decide whether a pair of vertices is adjacent in the
`5`-cycle. To do this it uses `instDecidableRelFinAdjCycleGraph`, the instance of
`DecidableRel C[n].Adj` from Mathlib. The line
`set_option trace.Meta.synthInstance true in` asks Lean to report how it searched for
the instances it needed: expand the trace attached to the `#eval` to see this. This
can be useful when instance search fails, or finds an instance you did not expect.
-/
set_option trace.Meta.synthInstance true in
#eval C[5].Adj 0 2            -- false
#check instDecidableRelFinAdjCycleGraph -- (n : ℕ) : DecidableRel C[n].Adj
/-!
The `decide` tactic instead *proves* a decidable proposition `p`: it asks the kernel
to reduce the Boolean `decide p` to `true`, and if this succeeds the proof is
`of_decide_eq_true rfl`. The result is a genuine proof, checked by the same small
trusted kernel as every other proof in Lean. The price is that kernel reduction is
much slower than running compiled code, so `decide` is only suitable for small
computations. Since `decide` is *proving* a proposition we can only use it to prove
true statements, so our previous example using `#eval` has to be negated to be used
with `decide`. Note that the `decide` tactic still uses the same instance of
`DecidableRel C[n].Adj` as `#eval` to decide adjacency.
-/
set_option trace.Meta.synthInstance true in
example : ¬ C[5].Adj 0 2 := by decide

/-!
We will introduce `Fintype` instances formally later in this chapter, but for now it
is enough to know that `K[n].edgeFinset` is a computable finite set of the edges of
the complete graph `K[n]`; while `K[n].edgeFinset.card` is this set's cardinality,
i.e. the number of edges in `K[n]`.

Again `#eval` can compute this quickly.
-/
#eval K[1000].edgeFinset.card -- 499500

/-!
We can also use `decide` to prove that the number of edges in `K[10]` is `45`, but it
is much slower and if we try to use `decide` to prove that the number of edges in
`K[1000]` is `499500` then it will complain.
-/
example : K[10].edgeFinset.card = 45 := by decide

/-- maximum recursion depth has been reached use `set_option maxRecDepth <num>` to
increase limit use `set_option diagnostics true` to get diagnostic information -/
#guard_msgs (substring := true) in
example : K[1000].edgeFinset.card = 499500 := by decide

/-!
In between `#eval` and `decide` sits the `native_decide` tactic, which proves a
proposition by *running* the compiled decision procedure and trusting the answer. It
should be as fast as `#eval`, but any proof using it then depends on the correctness
of the entire Lean compiler, not just the kernel, so it is banned in Mathlib. (This
project enables Mathlib's standard set of linters, which warns if you use it; a
project without those linters gives no warning.) For a full account of what is
trusted when checking a proof see
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
in the Lean Language Reference.
-/
example : K[1000].edgeFinset.card = 499500 := by native_decide

/-!
The following table summarizes the differences. (The final row previews a subtlety
that we will meet in
[Decidability and Kernel Reduction*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-decidability-and-kernel-reduction)
below.)

| Command/tactic | `#eval` | `decide` | `native_decide` |
| :--- | :--- | :--- | :---|
| What it is | command that runs code | tactic that builds a proof | tactic that builds a proof|
| Evaluated by | compiled code | kernel reduction | compiled code |
| Result | a printed value | a kernel-checked proof | a proof trusted as an axiom |
| Trusts | the entire compiler | only the kernel | the entire compiler |
| Speed | fast | slow (small cases only) | fast |
| Stuck by `Eq.rec` casts | no (proofs are erased) | yes | no |

All three of `#eval`, `decide`, and `native_decide` rely on having computable
`Decidable` instances. For graphs this means having an instance of
`DecidableRel G.Adj`, allowing us to compute adjacencies in `G`.

## Deciding Adjacency

Where does an instance of `DecidableRel G.Adj` used by `#eval` and `decide` come
from? Usually we would like Lean to synthesize these automatically by typeclass
inference.

To see which instance is synthesized for a particular graph we can use the `#synth`
command:
-/
#synth DecidableRel K[5].Adj -- fun a b ↦ Top.adjDecidable (Fin 5) a b
#check SimpleGraph.Top.adjDecidable -- the instance requires `[DecidableEq V]`

/-!
So the instance of decidable adjacency in the complete graph requires an instance of
`DecidableEq` for its vertex type. This is natural: any two vertices in a complete
graph are adjacent if and only if they are distinct. So deciding adjacency in a
complete graph is the same as deciding equality of vertices.

Note that for the empty graph (on any type) we always have decidability of the
adjacency relation, since no vertices are adjacent. This holds even on `ℝ`, where
equality itself is undecidable.
-/
#synth DecidableRel (⊥ : SimpleGraph ℝ).Adj
#check SimpleGraph.Bot.adjDecidable -- no assumption on `V` is required

/-!
If we revisit the three definitions `pathNat₁`, `pathNat₂` and `pathNat₃` of the path
graph on `ℕ` we can ask two obvious questions: do they have decidable adjacency and
if so will Lean automatically synthesize the required instance in each case?

The answer to the first question should be independent of which definition we use: as
we already proved they all define the same graph! So what would a method for deciding
adjacency in this graph look like? Given `a : ℕ` and `b : ℕ` we need to check if
`a + 1 = b` or `b + 1 = a` holds. Since `ℕ` has decidable equality this is clearly
decidable.

Turning to the second question of whether or not Lean will automatically synthesize
the required instance we see that the exact form of our definition matters. It turns
out that Lean can only infer the required instance for `pathNat₁`.
-/
#source pathNat₁ -- abbrev pathNat₁ : SimpleGraph ℕ where
                 --   Adj x y := x + 1 = y ∨ y + 1 = x
#synth DecidableRel pathNat₁.Adj -- fun a b ↦ instDecidableOr

/-!
Since `pathNat₁` is an `abbrev` Lean can see through its definition to find
`pathNat₁.Adj x y := x + 1 = y ∨ y + 1 = x`. Since `Or` is decidable and each of the
propositions `x + 1 = y` and `y + 1 = x` is decidable (using decidable equality on
`ℕ`) Lean can infer decidability of adjacency in `pathNat₁`.

For `pathNat₂` our definition is a `def` rather than an `abbrev`.
-/
#source pathNat₂ -- def pathNat₂ : SimpleGraph ℕ := SimpleGraph.fromRel (· + 1 = ·)
/-!
Lean can't see through the `def` so fails to infer the required instance.
-/
/-- error: failed to synthesize
  DecidableRel pathNat₂.Adj -/
#guard_msgs (substring := true) in
#synth DecidableRel pathNat₂.Adj -- fails

/-!
If we change the `def` to an `abbrev` then it works!
-/
abbrev pathNat₂' : SimpleGraph ℕ := SimpleGraph.fromRel (· + 1 = ·)
#synth DecidableRel pathNat₂'.Adj -- .. instDecidableRelAdjFromRelOfDecidableEq

/-!
Lean sees through the `abbrev` and finds
`pathNat₂' := SimpleGraph.fromRel (· + 1 = ·)`. It then finds the instance
`instDecidableRelAdjFromRelOfDecidableEq` which is the instance of decidable
adjacency for a graph defined from a decidable relation using the
`SimpleGraph.fromRel` constructor. In our case the relation is `(· + 1 = ·)`, i.e.
`fun x y => x + 1 = y` whose decidability can be inferred from the decidable equality
of `ℕ`.

Rather than changing the definition of `pathNat₂` to an `abbrev` we can also provide
a decidability instance for `pathNat₂.Adj` directly in two different ways. One way is
by `unfold`ing its definition and then calling `infer_instance`. The second way is to
use `inferInstanceAs` to specify the type of the instance we want to find. In the
latter case we know that Mathlib contains an instance of `DecidableRel` for the
adjacency relation of a graph defined using `SimpleGraph.fromRel` so we tell it to
use this.
-/
instance myDecidableRelPathNat₂ : DecidableRel pathNat₂.Adj := by
  unfold pathNat₂
  -- goal is now ⊢ DecidableRel (fromRel fun x1 x2 ↦ x1 + 1 = x2).Adj
  -- so Lean can use the instance `instDecidableRelAdjFromRelOfDecidableEq`
  infer_instance

example : DecidableRel pathNat₂.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

/-!
Finally we have `pathNat₃` which was defined using `SimpleGraph.fromEdgeSet`. Lean
again fails to infer the required instance (despite this being an `abbrev`).
-/
#source pathNat₃ -- abbrev pathNat₃ : SimpleGraph ℕ := SimpleGraph.fromEdgeSet
                 --                                       {e | ∃ n, e = s(n, n + 1)}

/-- error: failed to synthesize
  DecidableRel pathNat₃.Adj -/
#guard_msgs (substring := true) in
#synth DecidableRel pathNat₃.Adj

/-!
The problem here is that although Mathlib contains an instance for the decidability
of adjacency in any graph built by the `SimpleGraph.fromEdgeSet` constructor, this
instance requires that membership of the defining edge set be decidable. But Lean
doesn't know how to decide whether or not a given edge `s(a, b)` is in the edge set
`{e | ∃ n, e = s(n, n + 1)}`.
-/
#check instDecidableRelAdjFromEdgeSetOfDecidablePredSym2MemSetOfDecidableEq
          -- .. (s : Set (Sym2 V)) → [DecidablePred fun x ↦ x ∈ s]
          --     → [DecidableEq V] → DecidableRel (fromEdgeSet s).Adj

/-!
One solution in this case is to use the fact, which we already proved, that adjacency
in `pathNat₃` is the same as in `pathNat₁` and that Lean can infer decidable
adjacency of `pathNat₁`.
-/
#check pathNat₁_adj_iff_pathNat₃

/-!
Here we transfer the decidability instance from `pathNat₁` to `pathNat₃` using
`decidable_of_iff`. (Defining it by rewriting directly with
`pathNat₁_adj_iff_pathNat₃` would also type-check and work with `#eval`, but it would
leave `decide` permanently stuck: see
[Decidability and Kernel Reduction*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-decidability-and-kernel-reduction)
for an explanation.)
-/
instance : DecidableRel (pathNat₃.Adj) := fun u v =>
  decidable_of_iff (pathNat₁.Adj u v) pathNat₁_adj_iff_pathNat₃

example : pathNat₃.Adj 42 43 := by decide

/-!
### Decidability and Kernel Reduction *

We already provided decidable adjacency instances for several of the graphs
constructed in
[Constructions](https://jt496.github.io/GraphTheoryInLean/Constructions/#chapter-constructions).
We now provide two more, for the box product `G □ H` and the path graph `P[n]`, and
use them to explain why `rw` can be harmless or harmful inside a `Decidable`
instance.

In order to decide if `(g₁, h₁)` is adjacent to `(g₂, h₂)` in `G □ H` we need to
check if either `g₁ = g₂` and `H.Adj h₁ h₂` in `H`, or `h₁ = h₂` and `G.Adj g₁ g₂` in
`G`. So we need the obvious decidability assumptions on the vertex types of `G` and
`H` as well as their adjacency relations.
-/
/-- Decidability of the adjacency relation for the box product of two graphs. -/
instance boxProdDecidableRelAdj {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableEq V] [DecidableEq W] [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := by
  intro a b; rw [boxProd_adj]; infer_instance

/-!
This instance uses `rw` to reduce adjacency in `G □ H` to a decidable proposition
before calling `infer_instance`. This looks harmless, but can in some cases cause
problems.

A proof by `rw` inserts a *cast* (an application of the recursor `Eq.rec`) into the
term it builds. Whether this matters depends on how the instance is used: `#eval`
runs compiled code, from which all proofs, including the cast, have been erased, so
evaluation is unaffected. But `decide` proves a proposition `p` by asking the kernel
to reduce the Boolean `decide p` to `true`, which means first reducing the
`Decidable p` instance far enough to read off its `decide` field. The kernel can only
reduce an `Eq.rec` cast when the equation being cast along holds by definition (so
that, by proof irrelevance, the proof might as well be `rfl`). Otherwise the cast is
stuck, exactly as `h ▸ v` was in the disjoint union `Σg` (`SimpleGraph.sigma`) before
we substituted `i = j`.

For the box product instance, we got away with it: `boxProd_adj` is definitional
(proved by `Iff.rfl`), so the cast vanishes during kernel reduction. The recipe we
give below for `P[n]` avoids such problems entirely.
-/
example {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {x y : V × W} :
    (G □ H).Adj x y ↔ (G.Adj x.1 y.1 ∧ x.2 = y.2) ∨ (H.Adj x.2 y.2 ∧ x.1 = y.1) :=
  Iff.rfl

example : (K[2] □ K[3]).Adj (0, 0) (0, 1) := by decide

/-!
Now consider adjacency in the path graph `P[n]`. Since `pathGraph` is defined as a
`hasse` graph, the rewrite lemma `pathGraph_adj` is a genuine theorem, not provable
by `Iff.rfl`.
-/
example {n : ℕ} {u v : Fin n} :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val := by
  simp [pathGraph, hasse]

/-!
If we define `DecidableRel P[n].Adj` using the same `rw` recipe then we hit a
problem. We make this a `local instance`, active only until the end of the enclosing
`section`, so that it cannot interfere with the good instance defined below.
-/
section path_bad
/-- A `Decidable` instance defined via `rw` along a non-definitional equation: it
type-checks and works with `#eval`, but blocks kernel reduction. -/
local instance pathGraphAdjDecidableRw (n : ℕ) : DecidableRel P[n].Adj := by
  intro u v
  rw [pathGraph_adj]
  -- goal is now `⊢ Decidable (↑u + 1 = ↑v ∨ ↑v + 1 = ↑u)`
  -- which can be inferred, since `ℕ` has decidable equality
  infer_instance

/-!
With this instance, `#eval` works fine.
-/
#eval (P[17].Adj 13 14) -- true
/-!
But the tactic `decide` gets stuck on the cast. Note the `⋯ ▸ inferInstance` in the
error message below: `▸` is the cast inserted by `rw`.
-/
/-- error: Tactic `decide` failed to reduce
  @decide (P[17].Adj 13 14) (pathGraphAdjDecidableRw 17 13 14)
to `true` or `false`.

After unfolding the instance `pathGraphAdjDecidableRw`, reduction got stuck at
  ⋯ ▸ inferInstance

Hint: Reduction got stuck on `▸` (Eq.rec), which suggests that one of the `Decidable`
instances is defined using tactics such as `rw` or `simp`. To avoid tactics, make use
of functions such as `«inferInstanceAs»` or `decidable_of_decidable_of_iff` to alter
a proposition.
-/
#guard_msgs (substring := true) in
example : P[17].Adj 13 14 := by
  decide -- fails
end path_bad
/-!
So how should we fix this? The error message tells us what will work here: use
`decidable_of_decidable_of_iff`.
-/
#source decidable_of_decidable_of_iff -- .. (h : p ↔ q) : Decidable q where
                                      --      decide := decide p
                                      --      reflects_decide := ..
/-!
Note that this isn't a theorem, it is a function that provides a `Decidable` instance
for `q` using a `Decidable` instance for `p` and a proof of `p ↔ q`. Its Boolean is
simply `decide p`: it asks the instance for `p` for its verdict and returns the same
verdict for `q`. The proof `h : p ↔ q` is used only in the `reflects_decide` field,
to turn the proof that this verdict is correct for `p` into one for `q`.

The crucial difference from the `rw` version is where `h` ends up. The `rw` version
casts the *whole* instance along `h`, so the kernel has to get past the cast before
it can read off the `decide` field. Here `h` appears only inside `reflects_decide`,
which is a proof that `decide` never needs to reduce. The `decide` field itself
contains no `Eq.rec` cast, so nothing blocks kernel reduction.
-/
instance (n : ℕ) : DecidableRel P[n].Adj := fun _ _ =>
  decidable_of_decidable_of_iff pathGraph_adj.symm

/-!
Now both `#eval` and `decide` work fine!
-/
#eval P[17].Adj 13 14   -- true
example : P[17].Adj 13 14 := by decide
example : ¬ P[17].Adj 0 13 := by decide

/-!
In practice we rarely call `decidable_of_decidable_of_iff` directly:
`decidable_of_iff a h` is the same function with the proposition `a` given
explicitly, and `decidable_of_iff' b h` takes `h : a ↔ b` the other way round. We
used `decidable_of_iff` for `pathNat₃` above.
-/
#check decidable_of_iff  -- (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b
#check decidable_of_iff' -- (b : Prop) (h : a ↔ b) [Decidable b] : Decidable a
/-!
The `pathGraph` is a special case of the `hasse` graph, which is also missing a
decidable adjacency instance in Mathlib. Providing one, via decidability of the
covering relation of a locally finite order, is left to the exercises.

### More Decidable Adjacency Instances *

We give two more instances of decidable adjacency, for the disjoint unions
`SimpleGraph.sigma` and `SimpleGraph.sum`.

Recall `Σg G`, the `SimpleGraph.sigma` disjoint union of an indexed family of graphs.
-/
#source SimpleGraph.sigma -- protected def sigma (G : (i : ι) → SimpleGraph (V i)) :
                          --     SimpleGraph (Σ i, V i) where
                          --   Adj := fun ⟨i, u⟩ ⟨j, v⟩ =>
                          --            ∃ h : i = j, (G i).Adj u (h ▸ v)
/-!
We can give an instance of `DecidableRel (Σg G).Adj` for `SimpleGraph.sigma`,
assuming the index type has decidable equality and that each of the graphs in the
family has decidable adjacency. Here we have to do a case split on `i = j` (using the
decidable equality of the index type).
-/
instance {ι : Type*} {V : ι → Type*} (G : (i : ι) → SimpleGraph (V i))
    [DecidableEq ι] [∀ i, DecidableRel (G i).Adj] : DecidableRel (Σg G).Adj :=
  fun ⟨i, u⟩ ⟨j, v⟩ =>
    if h : i = j then
  -- when the indices agree, adjacency reduces to adjacency in the single graph `G i`
      decidable_of_iff ((G i).Adj u (h ▸ v)) (by subst h; simp)
    else
  -- vertices in different parts are never adjacent
      isFalse (by simp [h])

/-!
Recall `SimpleGraph.sum`, the disjoint union of two graphs `G ⊕g H`. Mathlib is
missing an instance of `DecidableRel (G ⊕g H).Adj`.
-/
instance {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj]
    [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj := fun u v =>
  match u, v with
  | Sum.inl u', Sum.inl v' => inferInstanceAs (Decidable (G.Adj u' v'))
  | Sum.inr u', Sum.inr v' => inferInstanceAs (Decidable (H.Adj u' v'))
  -- There is something slightly odd about the definition of `SimpleGraph.sum`
  -- Non-adjacency of vertices from different parts is defined using `false : Bool`,
  -- rather than `False : Prop`, hence the need for `Decidable false` below.
  | Sum.inl _, Sum.inr _ => inferInstanceAs (Decidable false)
  | Sum.inr _, Sum.inl _ => inferInstanceAs (Decidable false)

/-!
# Finite Types

The main constructive way of expressing that a type is finite in Mathlib is via the
`Fintype` class. Before we discuss `Fintype` we introduce the three closely related
data structures that underlie almost all finite reasoning in Mathlib: `List`,
`Multiset` and `Finset`.

## Lists, Multisets and Finsets

`List`, `Multiset` and `Finset` form a hierarchy: `List` (ordered, duplicates
allowed) → `Multiset` (unordered, duplicates allowed) → `Finset` (unordered, no
duplicates).

A `List α` is an ordered, finite sequence of elements of `α`, with duplicates
allowed. Both the order and the multiplicity of elements matter, so `[1, 1, 2]` and
`[2, 1, 1]` are *different* lists both containing `1` twice and `2` once.
-/
#check ([1, 1, 2] : List ℕ)              --  [1, 1, 2] : List ℕ
#eval ([2, 1, 1] : List ℕ) = [1, 1, 2]   -- false
#eval [2, 1, 1].count 1                  -- 2

/-!
A `Multiset α` is a `List α` in which we no longer care about the *order* of the
elements, but we *do* still record how many times each element occurs. Formally it is
the quotient of `List α` by permutation.
-/
#source Multiset -- def Multiset.{u} (α : Type u) : Type u :=
                 --   Quotient (List.isSetoid α)

/-!
Because order is forgotten the two lists above become *equal* as multisets, but the
repeated `1` is still counted twice.
-/
#eval ({2, 1, 1} : Multiset ℕ) = {1, 1, 2}   -- true
#eval ({2, 1, 1} : Multiset ℕ).count 1       -- 2

/-!
Any `List α` can be coerced to a `Multiset α` by forgetting the order of its
elements.
-/
#eval ([1, 3, 1, 2] : Multiset ℕ)            -- {1, 3, 1, 2}

/-!
Finally, a `Finset α` is a `Multiset α` that contains no duplicates. It is
implemented as a `Multiset` (its `val`) bundled with a proof (`nodup`) that this
multiset has no repeated elements.
-/
#source Finset -- structure Finset (α : Type*) where
               --   /- The underlying multiset -/
               --   val : Multiset α
               --   /- `val` contains no duplicates -/
               --   nodup : Nodup val
#check ({1, 2, 4} : Finset ℕ)         -- {1, 2, 4} : Finset ℕ
#eval ({3, 1, 1, 2} : Finset ℕ)       -- {3, 1, 2}

/-!
So a `Finset` is Mathlib's basic notion of a "finite set", and the one that
computations work with. Building one using `{...}` notation silently discards any
duplicates.
-/
example : ({1, 1, 2} : Finset ℕ) = {1, 2} := rfl

/-!
## Set-Builder Notation

Both `Set` and `Finset` can be written with the same *set-builder* notation
`{x | p x}`, but the two behave differently.

For a `Set α` the set-builder `{x | p x}` stands for `Set.ofPred (fun x => p x)`, the
set of *all* `x : α` satisfying `p`. No finiteness or decidability is required,
because a `Set α` is really just a predicate `α → Prop` in disguise.
-/
example : ({x : ℕ | x < 3} : Set ℕ) = Set.ofPred (fun x => x < 3) := rfl
/-!
The neighbourhoods and edge set of a graph are sets of exactly this form. For
instance `G.neighborSet v` is *definitionally* the set-builder `{w | G.Adj v w}`.
-/
example {V : Type*} (G : SimpleGraph V) (v : V) :
    G.neighborSet v = {w | G.Adj v w} := rfl
/-!
A `Finset α`, by contrast, must actually be finite. The fundamental way to build one
using a predicate is the form `{x ∈ s | p x}`, which carves out of an existing
`s : Finset α` the elements that satisfy `p`. This is notation for `Finset.filter`,
and because Lean has to test `p` on each element it needs a `DecidablePred p`
instance.
-/
example (s : Finset ℕ) : {x ∈ s | x < 3} = s.filter (fun x => x < 3) := rfl
#eval ({1, 2, 4, 5} : Finset ℕ).filter (fun x => x > 3) -- {4, 5}
/-!
The plain set-builder `{x | p x}` can also produce a `Finset`: it is the special case
of `{x ∈ s | p x}` in which `s` is `Finset.univ`, the `Finset` of *all* elements of
the ambient type. This only makes sense when there is a `[Fintype α]` instance.
(`Fintype` instances and `Finset.univ` are introduced properly in
[Fintypes](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-fintypes).)

Left to its own devices `{x | p x}` defaults to producing a `Set α`, but when the
expected type is `Finset α` and Lean can find a `Fintype α` instance (so that
`Finset.univ` exists) together with a `DecidablePred p`, the very same notation
elaborates to the `Finset α` `{x ∈ Finset.univ | p x}`, i.e. `Finset.univ.filter p`.
-/
example {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    ({x | p x} : Finset α) = Finset.univ.filter (fun x => p x) := rfl

#eval ({x | x < 3} : Finset (Fin 5))                 -- {0, 1, 2}
#eval ({x ∈ ({0, 1, 2, 3, 4} : Finset ℕ) | x < 3})   -- {0, 1, 2}

/-!
Finally the `{x ∈ s | p x}` notation also works for `Set α` where it abbreviates
`Set.ofPred (fun x => x ∈ s ∧ p x)`. This does not require decidability.

## Fintypes

A significant portion of work in graph theory is done with *finite* graphs. Nothing
is finite by default, so we have to explicitly add finiteness assumptions when we
want to talk about finite graphs.

There are different ways of expressing finiteness in Mathlib but for `SimpleGraph`
the most common is to provide `Fintype` instances (for the vertex type or edge set
etc).

A `Fintype V` instance is not just the proposition that `V` is finite: it is *data*.
A `Fintype V` instance is a `Finset V`, called `elems`, together with a proof that
`elems` contains every element of `V`. Since `Finset` already guarantees a lack of
duplicates, this ensures that `elems` contains each element of `V` *exactly* once.

Later in this chapter (see
[Cardinality](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-cardinality))
we will see examples of other finiteness assumptions: in particular `Finite`, but for
now we only consider `Fintype` since it is the most common and also the most
problematic!
-/
#source Fintype -- class Fintype (α : Type*) where
                --    /- The `Finset` containing all elements of a `Fintype` -/
                --  elems : Finset α
                --    /- A proof that `elems` contains every element of the type -/
                --  complete : ∀ x : α, x ∈ elems
/-!
While the underlying `Finset` of a `Fintype` instance is called `elems` we refer to
it as `Finset.univ` (it is after all the `Finset` version of `Set.univ`).
-/
#source Finset.univ -- def univ : Finset α := @Fintype.elems α _
#source Set.univ    -- def univ : Set α := {_a | True}

/-!
As with `Decidable` instances, `Fintype` instances are usually constructed
automatically by typeclass inference.

For example, for any `n : ℕ`, there is a `Fintype` instance for `Fin n`.
-/
#synth Fintype (Fin 5) -- Fin.fintype 5
#eval (Fin.fintype 5).elems     -- {0, 1, 2, 3, 4}
#check (Fin.fintype 5).complete --  ∀ (x : Fin 5), x ∈ Fintype.elems

/-!
This `Fintype` instance for `Fin n` is defined using `List.finRange n`, which is
`[0, 1, ⋯, n - 1]`, as a `List (Fin n)`, and a proof, `List.nodup_finRange n`, that
this list contains no duplicates. Together these define the `Finset` `elems`. The
proof `complete` that this contains every element of `Fin n` is given by
`List.mem_finRange`.
-/
#source Fin.fintype  -- instance Fin.fintype (n : ℕ) : Fintype (Fin n) :=
                     -- ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩
#eval List.finRange 5        -- [0, 1, 2, 3, 4]
#check List.nodup_finRange   -- List.nodup_finRange (n : ℕ) : (List.finRange n).Nodup
#check List.mem_finRange     -- {n : ℕ} (x : Fin n) : x ∈ List.finRange n

/-!
A set `s : Set α` can also be treated as a type, the subtype `↑s` of elements of `α`
that lie in `s`, so it too can have a `Fintype` instance. Such an instance is exactly
what we need to turn a `Set` into a `Finset`: `Set.toFinset s` requires
`[Fintype ↑s]` and has the same elements as `s`. In the other direction every
`Finset` coerces to a `Set`, written `(t : Set α)`.
-/
#check Set.toFinset     -- (s : Set α) [Fintype ↑s] : Finset α
#check Set.mem_toFinset -- a ∈ s.toFinset ↔ a ∈ s
example (t : Finset ℕ) : (t : Set ℕ).toFinset = t := Finset.toFinset_coe t

/-!
Mathlib's `Finset` versions of the sets attached to a graph are built in this way.
For instance, the `Finset` of edges `G.edgeFinset` is `G.edgeSet.toFinset`, so it
exists only when Lean can find a `Fintype G.edgeSet` instance, and `coe_edgeFinset`
turns it back into the edge set.
-/
#source edgeFinset    -- def edgeFinset : Finset (Sym2 V) := Set.toFinset G.edgeSet
#check coe_edgeFinset -- (G.edgeFinset : Set (Sym2 V)) = G.edgeSet

/-!
### Instance Arguments in Statements

If `G : SimpleGraph V` then a `Fintype V` instance is generally not enough to do
computations with the graph. For example, given just a `Fintype V` instance Lean
won't even let us talk about the number of edges in `G`.
-/
/--
failed to synthesize instance of type class
  Fintype ↑G.edgeSet
-/
#guard_msgs (substring := true) in
lemma bad_card_edgeFinset {V : Type*} (G : SimpleGraph V) [Fintype V] :
    ∃ n, G.edgeFinset.card = n := by
  sorry
/-!
This is because to form the `edgeFinset` of `G`, Lean needs to infer a `Fintype`
instance for the `edgeSet` of `G`. But it can't do this with just `Fintype V`.

This can be very confusing: surely a graph on a finite vertex set has finitely many
edges! But `Fintype` is more than the proposition that a type is finite, it is a
specific `Finset` of the elements of the type together with a proof that this
contains every element exactly once.

The `edgeSet` of a graph `G` is a set of unordered pairs, i.e. a `Set (Sym2 V)`. So
in order to infer a `Fintype` instance for `G.edgeSet` we need a `Fintype` instance
for `Sym2 V` *and* a way to decide whether or not any given pair of vertices are
adjacent in `G` (and so the corresponding edge belongs to the edge set), i.e. we need
an instance of `DecidableRel G.Adj`!

Assuming `Fintype V`, Lean can easily infer `Fintype (Sym2 V)`.
-/
example {V : Type*} [Fintype V] : Fintype (Sym2 V) := inferInstance
#check Sym2.instFintype -- the instance for `Fintype (Sym2 V)`
/-!
If we also provide a `DecidableRel G.Adj` instance then Lean can infer a `Fintype`
instance for `G.edgeSet`. The `DecidableRel G.Adj` allows Lean to take the
`Fintype (Sym2 V)` instance and filter it down to the edges of `G` to produce a
`Fintype G.edgeSet` instance.
-/

example {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    Fintype G.edgeSet := inferInstance
#source fintypeEdgeSet -- the instance used above:
        -- instance fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel G.Adj] :
        --     Fintype G.edgeSet := Subtype.fintype _
/-!
We can now complete the broken example from above.
-/
lemma bad_card_edgeFinset {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] : ∃ n, G.edgeFinset.card = n := by
  simp

/-!
Although this works, it isn't great style and we will take a moment to explain why.

While it is very common to use the `Fintype V` and `DecidableRel G.Adj` assumptions
to *infer* a `Fintype G.edgeSet` instance, this shouldn't be baked into a theorem in
this way. By using these instance assumptions we have proved that:

>  There exists `n : ℕ` such that the number of edges of `G` is `n`, provided that
   the finiteness of its edge set is inferred from the finiteness of `V` and the
   decidability of adjacency in `G`.

So if you have a graph `G`, which for some *other* reason you know to have finitely
many edges, then this result does not apply! A simple example is the empty graph on
`ℕ`. It has no edges, and Mathlib's instance `fintypeEdgeSetBot` makes its edge set a
`Fintype` (for any vertex type), but `ℕ` is infinite, so `bad_card_edgeFinset` cannot
be applied to it.
-/
#check fintypeEdgeSetBot -- Fintype ↑⊥.edgeSet
/--
failed to synthesize instance of type class
  Fintype ℕ
-/
#guard_msgs (substring := true) in
#check bad_card_edgeFinset (⊥ : SimpleGraph ℕ)

/-!
This is a lesson in how not to structure instance assumptions: a theorem should ask
for exactly the instances that its *statement* actually uses. Anything stronger
silently restricts the theorem to those callers who happen to obtain the required
instances by that particular route.

Here the conclusion mentions only `G.edgeFinset`, and `G.edgeFinset` is by definition
the `Finset` underlying a `[Fintype G.edgeSet]` instance. That single instance is the
*only* finiteness the statement needs, so it is the only one we should assume:
-/
theorem good_card_edgeFinset {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    ∃ n, G.edgeFinset.card = n := by simp
/-!
Stated this way the theorem is reusable, because Lean will discharge the
`[Fintype G.edgeSet]` argument from *whatever* is in scope at the call site. A caller
that has `[Fintype V] [DecidableRel G.Adj]` can get the instance by inference,
exactly the chain we traced from `Fintype (Sym2 V)` to `Fintype G.edgeSet`:
-/
example {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    ∃ n, G.edgeFinset.card = n := G.good_card_edgeFinset
/-!
While a caller that knows the edge set is finite for some entirely different reason,
such as the empty graph on `ℕ`, can supply the instance directly, with no mention of
`Fintype V` or decidable adjacency:
-/
example : ∃ n, (⊥ : SimpleGraph ℕ).edgeFinset.card = n := good_card_edgeFinset ⊥
/-!
Overly strong instance arguments don't make a theorem wrong, they just make it less
useful. (When you don't need to *compute* at all, the cleanest choice is often to
drop `Fintype` data entirely in favour of `Finite`/`Nat.card`; see
[Cardinality](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-cardinality).)

### Building `Fintype` Instances

Having told this cautionary tale, we now return to the basic question of how to infer
other common `Fintype` instances for graphs. Our next example is finiteness of the
neighbourhood of a vertex `v : V`: this is `Fintype (G.neighborSet v)`.

This would again follow from `Fintype V` and `DecidableRel G.Adj`, but we can get
away with less. We don't need `G.Adj a b` to be decidable for *all* pairs of
vertices, we only need to be able to decide whether or not any given vertex is
adjacent to `v`, i.e. we only need `DecidablePred (· ∈ G.neighborSet v)`. With this
Lean can filter the `Fintype V` instance down to the neighbours of `v` to produce a
`Fintype (G.neighborSet v)` instance.
-/
example {V : Type*} (G : SimpleGraph V) (v : V) [Fintype V]
    [DecidablePred (· ∈ G.neighborSet v)] : Fintype (G.neighborSet v) :=
  inferInstance

#check Subtype.fintype -- the instance used above

/-!
Obviously there are plenty of graphs with finite neighbourhoods that don't have
finite vertex sets, for example the infinite path graph `pathNat₁`. In such cases we
can provide our own `Fintype` instance for the neighbourhood of a vertex.

When we need to build a `Fintype` instance by hand like this, the following
constructors are often the most convenient starting points.
-/
#check Fintype.ofEquiv      -- given `Fintype α` and a bijection `α ≃ β`
                            -- we can get `Fintype β`
#check Fintype.ofSurjective -- given `Fintype α` and `f : α → β` surjective
                            -- we can get `Fintype β`
#check Fintype.ofInjective  -- given `Fintype β` and `f : α → β` injective
                            -- we can get `Fintype α`
#check Subtype.fintype      -- given `Fintype α` and `p : α → Prop` with
                            -- `DecidablePred p` we can get `Fintype {x // p x}`
#check Fintype.ofFinset     -- given `p : Set α`, `s : Finset α` and a proof
                            -- `∀ (x : α), x ∈ s ↔ x ∈ p` we can get `Fintype ↑p`

/-!
For the neighbourhoods of `pathNat₁`, `Fintype.ofFinset` is the natural choice: we
simply hand over the `Finset` of neighbours of each vertex and let `aesop` do the
rest.
-/
instance (n : ℕ) : Fintype (pathNat₁.neighborSet n) :=
  match n with
  | 0 =>  Fintype.ofFinset {1} (by aesop)
  | n + 1 =>  Fintype.ofFinset {n, n + 2} (by aesop)

/-!
We will explore finite neighbourhoods in more detail in
[Finite Neighbourhoods](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-finite-neighbourhoods).

## Cardinality

Counting crops up everywhere in graph theory: the number of vertices, the number of
edges, the degree of a vertex (the number of its neighbours), the size of a clique,
and so on. Mathlib offers several different notions of *cardinality*, and which one
to use depends on what kind of object we are counting and what finiteness information
we have available. We describe the main ones below.

### Counting a `Finset`: `Finset.card`

The most basic notion is the cardinality of a `Finset`. A `Finset α` is by
construction a finite collection of elements of `α`, so it always has a well-defined
size: a natural number. This is `Finset.card`, written either `s.card` or (after
`open Finset`) with the prefix notation `#s`.
-/
section finset
open Finset

#check Finset.card -- {α : Type u_1} → Finset α → ℕ
#eval ({0, 1, 2} : Finset ℕ).card -- 3
#eval #K[4].edgeFinset            -- 6
#eval #K[4, 3].edgeFinset         -- 12

end finset
/-!
In particular, the degree of a vertex (see
[Finite Neighbourhoods](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-finite-neighbourhoods)
below) is literally `#(G.neighborFinset v)`, and `#G.edgeFinset` is the number of
edges of `G`.

### Counting a Type: `Fintype.card`

When a type `α` carries a `Fintype α` instance it comes bundled with a canonical
`Finset` of *all* its elements, `Finset.univ`. The cardinality of the type is then
just the cardinality of that `Finset`:
-/
#check Fintype.card -- (α : Type u_4) → [Fintype α] → ℕ
#check Finset.card_univ  -- Finset.univ.card = Fintype.card α

#eval Fintype.card (Fin 5) -- 5
#eval Fintype.card (Sum (Option (Fin 5 × Bool)) (Fin 3 → Bool))
                                                 -- (1 + 5 * 2) + 2 ^ 3 = 19
/-!
Because it is built from `Finset.univ`, `Fintype.card` is *computable* whenever the
`Fintype` instance is: it is the notion we use with `#eval`, `decide` and
`native_decide`. For example the degree of a vertex `v` in a graph `G` is defined as
a `Finset.card`, but it equals `Fintype.card ↑(G.neighborSet v)`.
-/
#check card_neighborSet_eq_degree -- Fintype.card ↑(G.neighborSet v) = G.degree v

/-!
### Finiteness Without Data: the `Finite` Typeclass

Sometimes we know a type is finite but have no canonical enumeration of it, or we
simply don't want to drag `Fintype` data, and the `Decidable` instances it forces,
through a proof. For this Mathlib provides the `Finite` typeclass. It tells us that
there exist a natural number `n` and a bijection between the type and `Fin n`, the
canonical type of cardinality `n`.
-/
#source Finite -- class inductive Finite (α : Sort*) : Prop
              --    | intro {n : ℕ} : α ≃ Fin n → Finite _

example {α : Type*} : Finite α ↔ ∃ n, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin

/-!
The crucial difference is that `Finite V` is a *proposition* whereas `Fintype V` is
*data*.

| Aspect | `Fintype V` | `Finite V` |
| --- | --- | --- |
| Nature | *data* (a bundled structure) | a *proposition* (`Prop`-valued) |
| Carries | a `Finset V` of all elements | only `∃ n, Nonempty (V ≃ Fin n)` |
| Says | *how* to enumerate `V` | *that* `V` can be enumerated |
| Two instances | equal, but not always definitionally equal | definitionally equal (proof irrelevance) |
| Computable? | if the instance is (`Fintype.card`, `decide`) | no (use `Nat.card`) |

We always have `Fintype V → Finite V`; the reverse recovers data from a proof, so it
needs the axiom of choice and is noncomputable (but is still very useful in proofs).
-/
#check Finite.of_fintype   -- [Fintype α] : Finite α
#source Fintype.ofFinite   -- noncomputable def Fintype.ofFinite
                           --       (α : Type*) [Finite α] : Fintype α
/-!
So being data is not the same as being computable. `Fintype.ofFinite`, like any
instance built with the help of the `classical` tactic, is a perfectly good `Fintype`
instance for use in proofs, but `#eval` cannot run it.

One final remark about `Fintype` instances is that because two instances for the same
type need not be *definitionally equal*, they can be the source of *diamonds* in
typeclass inference. This can make proofs fail in mysterious ways. We will see a
simple example of one below in
[The Handshake Lemma](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-the-handshake-lemma).

### Counting with Only `Finite`: `Nat.card`

If all we have is `Finite α` (or nothing at all) we cannot use `Fintype.card`.
Instead we use `Nat.card α`, the cardinality of a type as a natural number, defined
for *every* type by falling back to `0` when the type is infinite.
-/
#check Nat.card -- Type u_3 → ℕ
#check Nat.card_eq_zero_of_infinite -- [Infinite α] : Nat.card α = 0
/-!
`Nat.card` agrees with `Fintype.card` whenever a `Fintype` instance happens to be
available, so the two never give conflicting answers on a finite type.
-/
#check Nat.card_eq_fintype_card -- [Fintype α] : Nat.card α = Fintype.card α
/-!
The trade-off is that `Nat.card` is noncomputable: it cannot be `#eval`-uated. Its
advantage is that it needs no `Fintype` data.

Beware of the `0` convention, though: `Nat.card α = 0` can mean either "`α` is empty"
*or* "`α` is infinite".

### Counting in `ℕ∞`: `ENat.card`

The `0`-on-infinite convention of `Nat.card` is convenient but lossy. When we want to
actually distinguish *infinite* from *empty* we use `ENat.card`, which takes values
in the extended naturals `ℕ∞ = WithTop ℕ` and returns `⊤` for infinite types.
-/
#check ENat.card -- Type u_3 → ℕ∞
#check ENat.card_eq_top  -- ENat.card α = ⊤ ↔ Infinite α
#check ENat.card_lt_top  -- ENat.card α < ⊤ ↔ Finite α
/-!
On a finite type it agrees with `Fintype.card` (cast into `ℕ∞`), and `Nat.card` is
recovered from it as `(ENat.card α).toNat`. Like `Nat.card`, `ENat.card` is
noncomputable.
-/
#check ENat.card_eq_coe_fintype_card -- [Fintype α] : ENat.card α = ↑(Fintype.card α)
example {V : Type*} : (ENat.card V).toNat = Nat.card V := rfl

/-!
### Counting a `Set`: `Set.ncard` and `Set.encard`

Finally these two ways of counting types extend to sets.

* `Set.ncard s : ℕ` is the size as a natural number, `0` if `s` is infinite. It is
  `Nat.card` of the corresponding subtype.
* `Set.encard s : ℕ∞` is the size in `ℕ∞`, `⊤` if `s` is infinite (the `Set` analogue
  of `ENat.card`).
-/
#check Set.ncard  -- {α : Type u_1} → Set α → ℕ
#check Set.encard -- {α : Type u_1} → Set α → ℕ∞
#check Nat.card_coe_set_eq -- (s : Set α) : Nat.card ↑s = s.ncard
/-!
When the set is the coercion of a `Finset`, `ncard` is just that `Finset`'s `card`.
-/
example {V : Type*} (s : Finset V) : (s : Set V).ncard = s.card :=
  Set.ncard_coe_finset _

/-!
So for a finite graph the (noncomputable) `G.edgeSet.ncard` and the (computable)
`G.edgeFinset.card` agree.
-/
example {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]

/-!
### Which One Should I Use?

| To count …   | given …                 | use                             | computable?[^1] |
| ---          | ---                     | ---                             | --- |
| a `Finset s` | (nothing)               | `#s` / `s.card`                 | yes |
| a type `α`   | `[Fintype α]`           | `Fintype.card α`                | yes |
| a type `α`   | `[Finite α]` or nothing | `Nat.card α` (`0` if infinite)  | no  |
| a type `α`   | nothing                 | `ENat.card α` (`⊤` if infinite) | no  |
| a `Set s`    | `[Fintype ↑s]`          | `Fintype.card ↑s`               | yes |
| a `Set s`    | (nothing)               | `s.ncard` / `s.encard`          | no  |

[^1]: Here "yes" means that the counting function is computable; an actual `#eval`
also needs the `Finset` or `Fintype` instance to have been built computably (not via
`Fintype.ofFinite`, `Set.Finite.toFinset` or `classical`).

As a rule of thumb: use `Finset.card` / `Fintype.card` when you want to *compute*
(with `#eval`, `decide`), and `Nat.card` / `ENat.card` (or `Set.ncard` /
`Set.encard`) when you only want to *reason*. The bridging lemmas above let you
switch between them whenever both are available. Sets also have a `Prop`-valued
finiteness predicate, `Set.Finite s`, which is the `Set` analogue of `Finite` and
from which `Set.Finite.toFinset` produces a (noncomputable) `Finset`. (Having said
all this, the current `SimpleGraph` API is heavily biased towards the use of
`Fintype` and `Finset`.)

# Degrees

The degree of a vertex is the size of its neighbourhood. For this to be a natural
number the neighbourhood must be finite, so we begin with finite neighbourhoods.

## Finite Neighbourhoods

We already saw finite neighbourhoods briefly above, using
`Fintype ↑(G.neighborSet v)` to form the `Finset` of neighbours of a vertex `v`.
-/
#source neighborFinset -- : Finset V := (G.neighborSet v).toFinset
/-!
So the *degree* of a vertex is the cardinality of its neighbourhood, assuming that
this neighbourhood is finite in the sense of `Fintype ↑(G.neighborSet v)`.
-/
#source degree -- def degree : ℕ := #(G.neighborFinset v)

#eval K[6].degree 3         -- 5
#eval K[5].neighborFinset 3 -- {0, 1, 2, 4}
#eval K[3, 2].neighborFinset (Sum.inl 1) -- {Sum.inr 0, Sum.inr 1}

/-!
Whenever we have `Fintype V` and `DecidableRel G.Adj` we automatically get an
instance of `Fintype ↑(G.neighborSet v)` for all vertices `v`.
-/
example {V : Type*} {v : V} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] :
    Fintype (G.neighborSet v) := inferInstance

/-!
However a vertex can have a finite neighbourhood even if the vertex set is infinite.
In results we can simply assume a vertex has a finite neighbourhood.
-/
example {V : Type*} (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = 0 ↔ G.neighborFinset v = ∅ := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero]

/-!
If we want to assume that all vertices have finite neighbourhoods, we can do this by
assuming `[G.LocallyFinite]`.
-/
#source LocallyFinite -- abbrev LocallyFinite := ∀ v : V, Fintype (G.neighborSet v)

/-!
In a locally finite graph, with no isolated vertices, all vertices have positive
degree. (Recall `G.support` is the set of non-isolated vertices.)
-/
example {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (h : ∀ v, v ∈ G.support) :
    ∀ v, 0 < G.degree v := by
  intro v
  obtain ⟨w, hadj⟩ := h v
  exact hadj.degree_pos_left

example {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] :
    G.LocallyFinite := inferInstance

/-!
Another situation in which we can obtain an instance of `G.LocallyFinite` without
requiring `Fintype V` is if we know that `G` has finitely many edges: every neighbour
of `v` is the other endpoint of an edge at `v`. Mathlib's equivalence
`incidenceSetEquivNeighborSet` between the edges at `v` and the neighbours of `v`
turns a `Fintype G.edgeSet` instance into a `Fintype (G.neighborSet v)` instance.
Notice that, unlike the instance built from `Fintype V`, this does not require
`DecidableRel G.Adj`.

We make this a `def` rather than an `instance`. As an instance it would give a second
route to `Fintype (G.neighborSet v)`, alongside the one through `Fintype V` and
`DecidableRel G.Adj`: a *diamond* of the kind we will meet in
[The Handshake Lemma](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-the-handshake-lemma).
-/
/-- A graph with finitely many edges is locally finite. -/
@[instance_reducible]
def locallyFiniteOfFintypeEdgeSet {V : Type*}
    {G : SimpleGraph V} [DecidableEq V] [Fintype G.edgeSet] : LocallyFinite G :=
  fun v => Fintype.ofEquiv {e ∈ G.edgeSet | v ∈ e} (G.incidenceSetEquivNeighborSet v)

/-!
The same equivalence shows that the degree of `v` is also the number of edges at `v`,
i.e. the size of `G.incidenceFinset v`, the `Finset` version of `incidenceSet`.
-/
#check card_incidenceFinset_eq_degree -- #(G.incidenceFinset v) = G.degree v

/-!
## Degrees in Complete Bipartite Graphs

We can compute the degrees of vertices in the complete bipartite graph `K[s, t]`
without having to make any assumptions about finiteness of neighbourhoods because
Lean can infer these automatically using the `Fintype` instances for `Fin s` and
`Fin t` and decidability of adjacency in `K[s, t]`.
-/
example (s t : ℕ) : K[s, t].LocallyFinite := inferInstance

/-!
Here we use the maps `Sum.inl` and `Sum.inr` that embed a type into the left and
right parts of a `Sum` type to describe the neighbourhoods. The neighbourhood of a
left vertex is the image of `Finset.univ : Finset (Fin t)` under `Sum.inr`, which we
form with `Finset.map`. This maps a `Finset` along an *embedding* `f : α ↪ β`, that
is, an injective function bundled with a proof that it is injective (we study
embeddings properly in
[Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#chapter-maps)). Since `f` is
injective there are no duplicates to remove, so unlike `Finset.image` it needs no
`DecidableEq β`, and `Finset.card_map` says that it preserves cardinality.
-/
#check Finset.card_map -- (s.map f).card = s.card

@[simp]
lemma degree_completeBipartiteGraph_inl (s t : ℕ) (i : Fin s) :
    K[s, t].degree (Sum.inl i) = t := by
  rw [← card_neighborFinset_eq_degree]
  -- the neighbourhood of a vertex in the left part is the entire right part,
  -- mapped along the embedding `Function.Embedding.inr : Fin t ↪ Fin s ⊕ Fin t`
  have : K[s, t].neighborFinset (Sum.inl i) = Finset.univ.map .inr := by
    ext x; cases x <;> simp
  simp [this]

@[simp]
lemma degree_completeBipartiteGraph_inr (s t : ℕ) (j : Fin t) :
    K[s, t].degree (Sum.inr j) = s := by
  rw [← card_neighborFinset_eq_degree]
  have : K[s, t].neighborFinset (Sum.inr j) = Finset.univ.map .inl := by
    ext x; cases x <;> simp
  simp [this]

/-!
## Degrees in the `n`-Uniform Blow-up of a Graph

Recall the `n`-uniform blow-up `G[n]` of a graph `G` (see `blowUpN`).
-/
#source blowUpGraph -- abbrev blowUpGraph (G : SimpleGraph ι) (V : ι → Type*) :
                    --   SimpleGraph (Σ i, V i) := SimpleGraph.comap Sigma.fst G
#source blowUpN -- abbrev blowUpN (G : SimpleGraph ι) (n : ℕ) :
                --   SimpleGraph (Σ _ : ι, Fin n) := G.blowUpGraph (fun _ => Fin n)
/-!
If `v : V` is a vertex with a finite neighbourhood in `G` then, in the `n`-uniform
blow-up `G[n]`, every vertex `⟨v, i⟩`, where `i : Fin n`, has a finite neighbourhood.
The neighbourhood of `⟨v, i⟩` in `G[n]` is `{⟨w, j⟩ | G.Adj v w}`, which is in
bijection with `G.neighborSet v × Fin n`, which in turn is finite since both factors
are finite.

Lean can't infer this automatically so we need to provide an instance. We hand the
bijection (or more precisely the `Equiv`) to `Fintype.ofEquiv` which then returns the
instance. An `Equiv` `α ≃ β` is a structure bundling a function `toFun : α → β`, its
inverse `invFun : β → α`, and proofs `left_inv` and `right_inv` that the two are
mutually inverse (see
[Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#chapter-maps)).
-/
/-- A vertex `w` in the `n`-uniform blow-up `G[n]` has a finite neighbourhood in
`G[n]` assuming `w.fst` has a finite neighbourhood in `G`. -/
instance {V : Type*} (G : SimpleGraph V) (n : ℕ) (w : Σ _ : V, Fin n)
    [Fintype (G.neighborSet w.fst)] : Fintype (G[n].neighborSet w) :=
  -- Given any vertex `w = ⟨v, i⟩` in the blow-up, its neighbourhood is equivalent to
  -- the product of the neighbourhood of `v` in `G` and `Fin n`.
  -- Lean can infer that the product `G.neighborSet v × Fin n` is finite since
  -- both factors are finite, so we just need to give the equivalence.
  Fintype.ofEquiv (G.neighborSet w.fst × Fin n)
  -- We now need to give the `Equiv` from
  -- `G.neighborSet v × Fin n` to `G[n].neighborSet ⟨v, i⟩`
    { toFun := fun ⟨⟨x, hx⟩, j⟩ => ⟨⟨x, j⟩, hx⟩
      invFun := fun ⟨⟨x, j⟩, hadj⟩ => ⟨⟨x, hadj⟩, j⟩
     -- since the proofs of `left_inv` and `right_inv` are `rfl` we can omit them
    }

/-!
This instance lets us talk about the degrees of vertices in the `n`-uniform blow-up
of any locally finite graph, and relate them to the degrees in the original graph.

If `v` has a finite neighbourhood in `G` then each vertex `⟨v, i⟩` of `G[n]` has
degree `G.degree v * n`. (The statement takes both neighbourhood instances as
arguments, as recommended in
[Instance Arguments in Statements](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-instance-arguments-in-statements);
the instance above is what supplies the second one whenever the lemma is used.)
-/
lemma degree_blowUpN {V : Type*} (G : SimpleGraph V) (n : ℕ) (v : V) (i : Fin n)
    [Fintype (G.neighborSet v)] [Fintype (G[n].neighborSet ⟨v, i⟩)] :
    G[n].degree ⟨v, i⟩ = G.degree v * n := by
  have h : G[n].neighborFinset ⟨v, i⟩ =
        (G.neighborFinset v).sigma (fun _ => Finset.univ) := by
    ext ⟨w, j⟩
    simp
  simp [← card_neighborFinset_eq_degree, h]

/-!
## Minimum and Maximum Degree

For a finite graph we can talk about the minimum degree `δ(G)` and maximum degree
`Δ(G)`. In Mathlib these are `G.minDegree` and `G.maxDegree`. Both require
`Fintype V` and `DecidableRel G.Adj`, and (very reasonably) default to `0` if `G` has
no vertices.

[Figure: A graph with vertices of minimum and maximum degree marked](https://jt496.github.io/GraphTheoryInLean/figures/minmaxdegree.svg)
-/
#source minDegree  -- def minDegree [DecidableRel G.Adj] : ℕ :=
                   --   WithTop.untopD 0 (univ.image fun v => G.degree v).min

#source maxDegree  -- def maxDegree [DecidableRel G.Adj] : ℕ :=
                   --   WithBot.unbotD 0 (univ.image fun v => G.degree v).max
/-!
We introduce the standard notation `δ(G)` for the minimum degree and `Δ(G)` for the
maximum degree of the graph `G`.
-/
@[inherit_doc minDegree] scoped notation "δ(" G ")" => SimpleGraph.minDegree G
@[inherit_doc maxDegree] scoped notation "Δ(" G ")" => SimpleGraph.maxDegree G

/-!
Every vertex has degree at least the minimum degree and at most the maximum degree.
-/
#check minDegree_le_degree  -- δ(G) ≤ G.degree v
#check degree_le_maxDegree  -- G.degree v ≤ Δ(G)

/-!
If `G` is a subgraph of `H` then `δ(G) ≤ δ(H)`.
-/
#check minDegree_le_minDegree -- G ≤ H → δ(G) ≤ δ(H)
/-!
The junk value `0` has a cost when we go the other way. If every vertex has degree at
least `k` then `k ≤ δ(G)`, but only when `V` is nonempty. Likewise a vertex of
minimum (or maximum) degree exists only when `V` is nonempty. The upper bound for
`Δ(G)` needs no such hypothesis, since the junk value `0` satisfies it anyway.
-/
#check le_minDegree_of_forall_le_degree -- [Nonempty V] (k : ℕ) :
                                        --   (∀ v, k ≤ G.degree v) → k ≤ δ(G)
#check maxDegree_le_of_forall_degree_le -- (k : ℕ) : (∀ v, G.degree v ≤ k) → Δ(G) ≤ k
#check exists_minimal_degree_vertex     -- [Nonempty V] : ∃ v, δ(G) = G.degree v
#check exists_maximal_degree_vertex     -- [Nonempty V] : ∃ v, Δ(G) = G.degree v

/-!
One problem with the definitions of `minDegree` and `maxDegree` is that they require
`Fintype V`, but plenty of graphs have finite minimum and maximum degree without
having finite vertex sets. For example the infinite path graph `pathNat₁` has minimum
degree `1` and maximum degree `2` but we can't state these facts using `minDegree`
and `maxDegree` (because `pathNat₁` has infinitely many vertices).

We can however characterize the neighbourhoods and degrees of vertices in `pathNat₁`.
-/
@[simp]
lemma neighborFinset_pathNat₁ (n : ℕ) [Fintype (pathNat₁.neighborSet n)] :
    pathNat₁.neighborFinset n = if n = 0 then {1} else {n - 1, n + 1} := by
  ext x; cases n <;> simp [eq_comm, or_comm]

@[simp]
lemma degree_pathNat₁ (n : ℕ) [Fintype (pathNat₁.neighborSet n)] :
    pathNat₁.degree n = if n = 0 then 1 else 2 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_pathNat₁]
  -- the `split_ifs` tactic is a convenient way to handle `if` statements
  split_ifs <;> grind

/-!
## The Handshake Lemma

In a finite graph the sum of all vertex degrees equals twice the number of edges.

[Figure: Each edge contributes two darts, one from each endpoint](https://jt496.github.io/GraphTheoryInLean/figures/handshake.svg)
-/
#check sum_degrees_eq_twice_card_edges -- ∑ v, G.degree v = 2 * G.edgeFinset.card

/-!
The proof counts the darts of `G` (`Dart`) in two ways. Each vertex `v` is the first
entry of exactly `G.degree v` darts, so the number of darts is the sum of the
degrees. Each edge gives exactly two darts, one in each direction, so the number of
darts is also twice the number of edges.
-/
#check dart_card_eq_sum_degrees      -- Fintype.card G.Dart = ∑ v, G.degree v
#check dart_card_eq_twice_card_edges -- Fintype.card G.Dart = 2 * #G.edgeFinset

/-!
The key to the first count is the bijection from the neighbourhood of `v` to the
darts of `G` whose first element is `v`.
-/
#check dartOfNeighborSet_injective -- Function.Injective (G.dartOfNeighborSet v)
#check dart_fst_fiber -- {d | d.toProd.1 = v} = image (G.dartOfNeighborSet v) univ

/-!
As noted in Mathlib's documentation, the handshake lemma sometimes refers to the
following consequence of this lemma: the number of vertices of odd degree is even.
-/
#check even_card_odd_degree_vertices -- Even #{v | Odd (G.degree v)}
/-!
Since we spent some time looking at instance arguments earlier, we note that the
signature of `sum_degrees_eq_twice_card_edges` follows the pattern of
`bad_card_edgeFinset`. It takes `[Fintype V]` and `[DecidableRel G.Adj]`, and its
statement derives two further instances from these: the `Fintype` instance for each
neighbourhood (used by `degree`) and the one for the edge set (used by `edgeFinset`).
So it only applies to graphs whose instances are synthesized by that route. The
instances its statement actually mentions are `[Fintype V]`, to sum over all
vertices, `[G.LocallyFinite]` and `[Fintype G.edgeSet]`.

We can easily derive a more general version with only these arguments. But we first
show how the obvious proof fails.
-/
/-- error: Type mismatch
  sum_degrees_eq_twice_card_edges G
has type
  ∑ v, @degree V G v (Subtype.fintype (Membership.mem (G.neighborSet v))) = 2 * G.edgeFinset.card
but is expected to have type
  ∑ v, @degree V G v (inst✝ v) = 2 * G.edgeFinset.card
-/
#guard_msgs in
example {V : Type*} (G : SimpleGraph V) [Fintype V] [Fintype G.edgeSet]
    [G.LocallyFinite] : ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  classical
  -- This makes `DecidableRel G.Adj` available,
  -- so we can use the original lemma.
  -- But the obvious proof fails due to a `Fintype` instance mismatch.
  exact G.sum_degrees_eq_twice_card_edges

/-!
The error is caused by `Fintype` instance *diamonds*. The `degree` function takes a
`Fintype (G.neighborSet v)` instance argument. We provided this via the
`G.LocallyFinite` instance, but the original lemma `sum_degrees_eq_twice_card_edges`
uses a different route: namely `Fintype V` + `DecidableRel G.Adj` to synthesize a
`Fintype (G.neighborSet v)` instance. Since these are not definitionally equal (see
[Definitional and Propositional Equalities](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/#section-definitional-and-propositional-equalities)),
Lean refuses to unify them, and the proof fails. The same happens with
`G.edgeFinset`: the lemma builds its `Fintype G.edgeSet` instance from `Fintype V`
and `DecidableRel G.Adj`, while we supplied one directly. The error message only
reports the first mismatch.

However any two `Fintype` instances `inst₁` and `inst₂` for the same type are
propositionally equal. Each instance consists of a `Finset` together with a proof
that the `Finset` contains every element of the type. So the two `Finset`s have the
same members and hence are equal by extensionality; while, by proof irrelevance, the
two proofs of completeness are equal: so `inst₁ = inst₂`.

This general argument means that `Fintype` is a `Subsingleton` (a type in which any
two elements are equal). We have the instance `Fintype.subsingleton`, so
`Subsingleton.elim` can produce a proof of `inst₁ = inst₂` for us whenever we need
one. This is exactly what `convert` does in our proof below.
-/
#synth (α : Type*) → Subsingleton (Fintype α) -- Fintype.subsingleton
#check Subsingleton.elim -- {α : Sort u} [h : Subsingleton α] (a b : α) : a = b

lemma sum_degrees_eq_twice_card_edges' {V : Type*} (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] [G.LocallyFinite] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  classical
  convert G.sum_degrees_eq_twice_card_edges

/-!
## Regular Graphs

If `G` is locally finite then we can talk about `G` being *regular of degree* `d` for
some `d : ℕ`.
-/
#source IsRegularOfDegree -- .. (d : ℕ) : Prop := ∀ v : V, G.degree v = d

/-!
If `G` is regular of degree `d` then its `n`-uniform blow-up is regular of degree
`d * n`.
-/
lemma IsRegularOfDegree.blowUpN {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (n d : ℕ) [G[n].LocallyFinite] (h : G.IsRegularOfDegree d) :
    G[n].IsRegularOfDegree (d * n) := by
  intro ⟨v, i⟩
  rw [degree_blowUpN, h v]

/-!
So the `n`-uniform blow-up of the complete graph on `m` vertices is regular of degree
`(m - 1) * n`.
-/
example (m n : ℕ) : K[m][n].IsRegularOfDegree ((m - 1) * n) :=
  IsRegularOfDegree.blowUpN K[m] n (m - 1)
    (by simpa using IsRegularOfDegree.top (V := Fin m))

/-!
Mathlib knows that the complete graph on a finite vertex type is regular, but it
doesn't state the converse: any graph that is regular of degree `n - 1`, where
`Fintype.card V = n`, is complete. It does, however, have the two ingredients. A
vertex is *universal* (`G.IsUniversal v`) iff it has degree `Fintype.card V - 1` and
a graph is complete iff every vertex is universal.
-/
#check degree_eq_card_sub_one -- G.degree v = Fintype.card V - 1 ↔ G.IsUniversal v
#check eq_top_iff_forall_isUniversal -- G = ⊤ ↔ ∀ v, G.IsUniversal v
/-!
A graph is regular of degree `Fintype.card V - 1` iff it is complete. (Mathlib's
`degree_eq_card_sub_one` uses the `Fintype` instance for neighbourhoods coming from
`DecidableRel G.Adj`, while ours comes from `G.LocallyFinite`; `convert` bridges the
two, just as it did in the proof of `sum_degrees_eq_twice_card_edges'`.)
-/
theorem isRegularOfDegree_card_sub_one_iff_eq_top {V : Type*} (G : SimpleGraph V)
    [Fintype V] [G.LocallyFinite] :
    G.IsRegularOfDegree (Fintype.card V - 1) ↔ G = ⊤ := by
  classical
  rw [eq_top_iff_forall_isUniversal]
  apply forall_congr'
  intro v
  convert G.degree_eq_card_sub_one v

/-!
Complements of regular graphs are also regular. In `Gᶜ` a vertex is adjacent to
exactly those other vertices that it is not adjacent to in `G`, so its degree is
given by `degree_compl`. Hence the complement of a graph on `n` vertices that is
regular of degree `k` is regular of degree `n - 1 - k`.
-/
#check degree_compl -- Gᶜ.degree v = Fintype.card V - 1 - G.degree v
#check IsRegularOfDegree.compl
  -- G.IsRegularOfDegree k → Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k)

/-!
For a regular graph the handshake lemma counts the edges: if `G` is regular of degree
`d` on `n` vertices and has `e` edges then `2 * e = n * d`. Here we need our new
version of the handshake lemma, since our instances come from `G.LocallyFinite` and
`[Fintype G.edgeSet]` rather than from `DecidableRel G.Adj`.
-/
lemma IsRegularOfDegree.two_mul_card_edgeFinset {V : Type*} {G : SimpleGraph V}
    {d : ℕ} [Fintype V] [Fintype G.edgeSet] [G.LocallyFinite]
    (h : G.IsRegularOfDegree d) : 2 * G.edgeFinset.card = Fintype.card V * d := by
  rw [← sum_degrees_eq_twice_card_edges' G]
  simp [h.degree_eq]

/-!
Dividing by `2`, the number of edges is `Fintype.card V * d / 2`. Division on `ℕ`
rounds down, but here nothing is lost, since the lemma above shows that
`Fintype.card V * d` is even.
-/
lemma IsRegularOfDegree.card_edgeFinset {V : Type*} {G : SimpleGraph V} {d : ℕ}
    [Fintype V] [Fintype G.edgeSet] [G.LocallyFinite] (h : G.IsRegularOfDegree d) :
    G.edgeFinset.card = Fintype.card V * d / 2 := by
  grind [h.two_mul_card_edgeFinset]

/-!
## Neighbours in a Set

It is often useful to count only the neighbours of a vertex `v` that lie in a given
finite set `s`. We call this number `G.degIn s v`. We define it as the size of
`s.bipartiteAbove G.Adj v`, which is Mathlib's name for `{w ∈ s | G.Adj v w}`. It
comes from Mathlib's double-counting library, so facts about `degIn` can be fed
straight into Mathlib's double-counting lemmas. We prove a few simple lemmas about
`degIn`, which we will use in
[Brooks' Theorem*](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-brooks-theorem),
for the
[Moore and Cage Bounds](https://jt496.github.io/GraphTheoryInLean/Distance/#section-moore-and-cage-bounds),
and in the proof of
[Füredi's Stability Theorem](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-f-redi-s-stability-theorem).
-/
section degIn
open Finset
variable {V : Type*} {G : SimpleGraph V}

/-- The number of neighbours of `v` lying in `s`. -/
def degIn (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) : ℕ :=
    #(s.bipartiteAbove G.Adj v)

/-!
`G.degIn s v` counts the vertices `w ∈ s` adjacent to `v`.
-/
lemma degIn_eq_card_filter [DecidableRel G.Adj] (s : Finset V) (v : V) :
    G.degIn s v = #{w ∈ s | G.Adj v w} := rfl

/-!
The set of neighbours of `x` lying in `s` is exactly `G.neighborFinset x ∩ s`.
-/
lemma filter_adj_eq_inter [DecidableEq V] [DecidableRel G.Adj]
    [G.LocallyFinite] (s : Finset V) (x : V) :
    {v ∈ s | G.Adj x v} = G.neighborFinset x ∩ s := by
  ext v; simp [mem_filter, mem_inter, mem_neighborFinset, and_comm]

/-!
Since `G.Adj` is symmetric, `bipartiteBelow` also counts the neighbours of `v` in
`s`.
-/
lemma degIn_eq_card_bipartiteBelow [DecidableRel G.Adj] (s : Finset V) (v : V) :
    G.degIn s v = #(s.bipartiteBelow G.Adj v) := by
  rw [degIn_eq_card_filter]
  congr 1
  ext; simp [adj_comm]

/-!
The number of neighbours of `x` in `s` is at most its degree.
-/
lemma degIn_le_degree [DecidableRel G.Adj] [G.LocallyFinite]
    (s : Finset V) (x : V) : G.degIn s x ≤ G.degree x := by
  classical
  rw [degIn_eq_card_filter, filter_adj_eq_inter, ← card_neighborFinset_eq_degree]
  exact card_le_card inter_subset_left

/-!
If `x` has at least as many neighbours in `s` as its degree, then every
neighbour of `x` lies in `s`.
-/
lemma neighborFinset_subset_of_degree_le_degIn [DecidableRel G.Adj] [G.LocallyFinite]
    (s : Finset V) (x : V) (hle : G.degree x ≤ G.degIn s x) :
    G.neighborFinset x ⊆ s := by
  classical
  have : G.degIn s x = G.degree x := (degIn_le_degree s x).antisymm hle
  rw [degIn_eq_card_filter, filter_adj_eq_inter,
    ← card_neighborFinset_eq_degree] at this
  have heq := eq_of_subset_of_card_le inter_subset_left (le_of_eq this.symm)
  grind

/-!
If every neighbour of `x` lies in `s`, then `x` has `G.degree x` neighbours in
`s`.
-/
lemma degIn_eq_degree [DecidableRel G.Adj] [G.LocallyFinite] {s : Finset V} {x : V}
    (h : G.neighborFinset x ⊆ s) : G.degIn s x = G.degree x := by
  classical
  rw [degIn_eq_card_filter, filter_adj_eq_inter, inter_eq_left.mpr h,
    card_neighborFinset_eq_degree]

/-!
The `degIn` of a vertex is monotone in the set.
-/
lemma degIn_mono [DecidableRel G.Adj] {s t : Finset V} (h : s ⊆ t) (x : V) :
    G.degIn s x ≤ G.degIn t x :=
  card_le_card (filter_subset_filter _ h)

/-!
The `degIn` of a vertex is additive over a disjoint union of sets.
-/
lemma degIn_union [DecidableRel G.Adj] [DecidableEq V] (s t : Finset V)
    (x : V) (h : Disjoint s t) :
    G.degIn (s ∪ t) x = G.degIn s x + G.degIn t x := by
  simp only [degIn_eq_card_filter]
  rw [filter_union,
    card_union_of_disjoint (h.mono (filter_subset _ _) (filter_subset _ _))]

/-!
If some neighbour of `x` lies outside `s`, then `x` has strictly less than
`G.degree x` neighbours in `s`.
-/
lemma degIn_lt_degree_of_adj_notMem [DecidableRel G.Adj] [G.LocallyFinite]
     {x y : V} (s : Finset V) (hadj : G.Adj x y) (hy : y ∉ s) :
    G.degIn s x < G.degree x := by
  classical
  rw [degIn_eq_card_filter, filter_adj_eq_inter, ← card_neighborFinset_eq_degree]
  apply card_lt_card
  rw [ssubset_iff_of_subset inter_subset_left]
  exact ⟨y, (mem_neighborFinset _ _ _).mpr hadj, fun h => hy (mem_inter.mp h).2⟩

/-!
If every neighbour of `x` except possibly `w` lies in `B`, then `x` has at most
one neighbour outside `B`.
-/
lemma degree_le_degIn_add_one [DecidableRel G.Adj] [G.LocallyFinite] (B : Finset V)
    {x : V} (w : V) (h : ∀ y, G.Adj x y → y ≠ w → y ∈ B) :
    G.degree x ≤ G.degIn B x + 1 := by
  rw [← card_neighborFinset_eq_degree]
  classical
  calc #(G.neighborFinset x) ≤ #(insert w {v ∈ B | G.Adj x v}) :=
        card_le_card fun y hy => by
          rw [mem_neighborFinset] at hy
          by_cases hyw : y = w
          · simp [hyw]
          · simp [h y hy hyw, hy]
    _ ≤ G.degIn B x + 1 := card_insert_le _ _

end degIn

/-!
# Computations with Hypercubes

In order to compute with the hypercube `Q[n]`, and to prove results about the degrees
of its vertices and the size of its edge set, we need decidable equality of its
vertices, decidable adjacency, and a `Fintype` instance for its vertices. As with
many proofs for the hypercube, each of these drops out easily by induction on `n`.
-/
/-- Vertices of the hypercube have decidable equality. -/
instance hypercubeDecidableEq (n : ℕ) : DecidableEq (HypercubeVert n) := by
  induction n <;> unfold HypercubeVert <;> infer_instance

/-!
Since we used the box product to define the hypercube, decidability of adjacency in
`Q[n]` follows from the box product instance `boxProdDecidableRelAdj` (see
[Decidability and Kernel Reduction*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-decidability-and-kernel-reduction)).
-/
/-- Decidability of the adjacency relation for the hypercube. -/
instance hypercubeDecidableRelAdj (n : ℕ) : DecidableRel Q[n].Adj := by
  induction n <;> unfold hypercube <;> infer_instance

example : Q[2].Adj (((), false), false) (((), false), true) := by decide

/-- The vertex type `HypercubeVert n` is finite. -/
instance hypercubeFintype (n : ℕ) : Fintype (HypercubeVert n) := by
  induction n <;> unfold HypercubeVert <;> infer_instance

/-!
The `n`-dimensional hypercube has `2 ^ n` vertices. We state this for an arbitrary
`Fintype` instance on `HypercubeVert n`, so that it applies whichever enumeration a
caller has: `convert` reduces it to the instance `hypercubeFintype`, since any two
`Fintype` instances on a type are equal.
-/
/-- The `n`-dimensional hypercube has `2 ^ n` vertices. -/
@[simp] lemma card_hypercubeVert (n : ℕ) [Fintype (HypercubeVert n)] :
    Fintype.card (HypercubeVert n) = 2 ^ n := by
  suffices h : @Fintype.card (HypercubeVert n) (hypercubeFintype n) = 2 ^ n by
    convert h
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← ih]; exact Fintype.card_prod _ _


example : Fintype.card (HypercubeVert 3) = 8 := by simp

/-!
We also give a `Nonempty` instance for `HypercubeVert n` since this will be useful in
later chapters.
-/
instance hypercubeNonempty {n : ℕ} : Nonempty (HypercubeVert n) := by
  induction n <;> unfold HypercubeVert <;> infer_instance

/-!
There is only one vertex in `Q[0]`, so we can give a `Subsingleton` instance for it.
-/
instance hypercubeZeroSubsingleton : Subsingleton (HypercubeVert 0) :=
  inferInstanceAs (Subsingleton (Unit))

/-!
Before we try some more interesting computations with hypercubes, we give a
convenient way to describe and print vertices of the hypercube.
-/
/-- Hypercube vertex as a binary string. -/
def hypercubeVertToBin : (n : ℕ) → HypercubeVert n → String
  | 0, _ => ""
  | n + 1, (v, b) => hypercubeVertToBin n v ++ if b then "1" else "0"

/-!
Lean has the `Repr` typeclass for types that can be pretty printed. We can now use
`hypercubeVertToBin` to give a `Repr` instance for `HypercubeVert n`.
-/
/-- A `Repr` instance for hypercube vertices to allow pretty printing. -/
instance hypercubeRepr {n : ℕ} : Repr (HypercubeVert n) where
  reprPrec v _ := hypercubeVertToBin n v

/-!
We can also define a convenient macro `v[...]` for writing out vertices of the
hypercube, along with scoped `OfNat` instances so that `0` and `1` can be used for
`false` and `true`.
-/
namespace HypercubeVert
scoped instance : OfNat Bool 0 := ⟨false⟩
scoped instance : OfNat Bool 1 := ⟨true⟩

/-- `v[b₀, …, bₙ₋₁]` is the vertex of `Q[n]` with coordinates `b₀, …, bₙ₋₁`, where
`0` and `1` stand for `false` and `true`. -/
scoped syntax "v[" term,* "]" : term
scoped macro_rules
  | `(v[ $[$xs],* ]) => do
    let mut acc ← `(())
    for x in xs do
      acc ← `(($acc, $x))
    return acc

#eval Q[3].neighborFinset v[0,1,1] -- {111, 010, 001}

example : Q[3].Adj v[1, 1, 1] v[1, 0, 1] := by simp

end HypercubeVert

/-!
Returning now to computations involving hypercubes, we note that Lean can infer that
every vertex in `Q[n]` has a "computable" `Fintype` instance for its neighbourhood
using `DecidableRel Q[n].Adj` and `Fintype (HypercubeVert n)`.

We can use this to compute the degree of a vertex in `Q[15]`. However this is a bad
idea since this is basically looking at each of the `2 ^ 15` vertices and checking
adjacency. (In the case of a `Q[30]` vertex this would simply time out.)
-/

#synth Q[15].LocallyFinite
-- fun v ↦ Subtype.fintype (Membership.mem (Q[15].neighborSet v))

open HypercubeVert -- for the `v[...]` vertex notation

#eval Q[15].degree v[0,1,0,0,1,1,1,1,1,1,0,1,1,0,1] -- 15

/-!
We can however give a more efficient `Fintype` instance for the neighbourhoods of
vertices in `Q[n]` using Mathlib's custom `boxProdFintypeNeighborSet` instance for
the box product, which is exactly how `Q[n]` is defined (for `n ≠ 0`).
-/
#check boxProdFintypeNeighborSet
/-!
We use `inferInstanceAs` to tell Lean to build the neighbourhood through the box
product, and the trace output confirms that it does indeed use it. (Here `f <| x`
means `f x`; it saves writing brackets around a long argument.)
-/
/-- An efficient `Fintype` instance for the neighbourhood of a vertex in `Q[n]`,
built through the box product rather than by filtering all `2 ^ n` vertices. -/
instance hypercubeFintypeNeighborSet (n : ℕ) (v : HypercubeVert n) :
    Fintype (Q[n].neighborSet v) := by
  induction n with
  | zero => infer_instance
  -- the induction hypothesis `ih` is in the local context, and local hypotheses of
  -- class type are candidates for instance synthesis, so this finds it
  | succ n ih => exact inferInstanceAs <| Fintype ((_ □ _).neighborSet _)

/-!
This is no longer simply filtering a set of `2 ^ 60` vertices!
-/
set_option trace.Meta.synthInstance true in
#synth Q[60].LocallyFinite -- hypercubeFintypeNeighborSet 60

#eval Q[60].degree v[0,1,1,0,1,0,1,0,1,0,0,1,1,0,1,0,1,0,1,0,0,0,1,1,0,
  0,1,1,0,1,0,1,0,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0,1,0,1,0,1,0,0,0,1,1,0] -- 60

/-!
The efficient instance also allows us to give a short proof that `Q[n]` is regular of
degree `n`, but now that `Q[n].neighborSet v` has two `Fintype` instances, stating
this result takes some care. We do so in the next section.

## Stating Results Across a Diamond *

We have just created a `Fintype` *diamond*: `Q[n].neighborSet v` now has two
instances, the one Lean synthesized by filtering all `2 ^ n` vertices and the
efficient one we built through the box product, `hypercubeFintypeNeighborSet`. This
is the situation we warned about in
[Instance Arguments in Statements](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-instance-arguments-in-statements)
and
[Cardinality](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-cardinality),
and explored in the proof of `sum_degrees_eq_twice_card_edges'`, so how much trouble
does it actually cause?

Mathlib has the same diamond, since `boxProdFintypeNeighborSet` is a global instance,
and nothing in Mathlib breaks because of it. The reason is visible in
`degree_boxProd`: its third instance argument is an *arbitrary* `Fintype` for the
box product neighbourhood `[Fintype ↑((G □ H).neighborSet x)]`, not
`boxProdFintypeNeighborSet`.
-/
#check degree_boxProd
/-!
So `degree_boxProd` works with whichever instance is in scope where it is used. Two
instances only cause difficulty when a theorem *statement* names one of them.

We therefore state the regularity of `Q[n]` with its `LocallyFinite` instance as an
argument. Without this, Lean would have written the synthesized instance, the
efficient `hypercubeFintypeNeighborSet`, into the statement, and the lemma could then
only be used where that is the instance in scope.

The proof, however, needs the efficient instance: because it is built through the box
product, `change` can restate a degree in `Q[n + 1]` as a degree in `Q[n] □ ⊤`, ready
for `degree_boxProd`. Since the instance is now an argument, the proof has to switch
to the efficient one itself, and this is what its first two lines do. The `let` puts
the efficient instance in the local context, where typeclass inference looks first.
(It must be a `let`, not a `have`: an instance is data, and `change` needs to see its
value.) Then `convert_to` restates the goal, so that its instance is synthesized as
the local one, and closes the gap between the two instances using the `Subsingleton`
argument from the proof of `sum_degrees_eq_twice_card_edges'`. In the InfoView the
goal looks the same before and after, since instance arguments are not displayed;
hovering over `IsRegularOfDegree` in the goal shows that `inst✝` has become `this`.
Because the switch happens inside the proof, no caller ever needs a `convert`.
-/
lemma IsRegularOfDegree.hypercube (n : ℕ) [Q[n].LocallyFinite] :
    Q[n].IsRegularOfDegree n := by
  -- swap out the instance for the efficient one
  let : Q[n].LocallyFinite := fun v => hypercubeFintypeNeighborSet n v
  -- the goal is `@IsRegularOfDegree _ Q[n] inst✝ n`, with the caller's instance
  convert_to Q[n].IsRegularOfDegree n
  -- the goal is now `@IsRegularOfDegree _ Q[n] this n`, with the efficient one
  induction n with
  | zero => exact IsRegularOfDegree.bot
  | succ n ih =>
    intro v
    -- `Q[n + 1]` is `Q[n] □ ⊤` by definition, and `this` is the box product instance
    change (Q[n] □ ⊤).degree v = n + 1
    rw [degree_boxProd, ih v.1]
    simp

/-!
The lemma now applies with whatever instance typeclass inference finds where it is
used. In the first example below, that is the global instance
`hypercubeFintypeNeighborSet`. In the second, it is the instance argument
`[Q[n].LocallyFinite]`, about which nothing is known; inference finds it because
local instances are tried first.
-/
example (n : ℕ) (v : HypercubeVert n) : Q[n].degree v = n :=
  IsRegularOfDegree.hypercube n v

example (n : ℕ) [Q[n].LocallyFinite] (v : HypercubeVert n) :
    Q[n].degree v + 1 = n + 1 := by
  rw [IsRegularOfDegree.hypercube n v]

/-!
Note, however, that an instance argument is filled in by *inference*, which for
`Q[n]` finds the efficient instance, not by matching the type that the caller
expects. Mathlib's `IsRegularOfDegree.minDegree_eq`, which says that a graph that is
regular of degree `d` has minimum degree `d`, takes `[DecidableRel G.Adj]` like
`minDegree` itself. So for `Q[n]` it asks for regularity with respect to the
filtering instance, and the obvious proof fails.
-/
/-- error: Application type mismatch: The argument
  IsRegularOfDegree.hypercube n
has type
  @IsRegularOfDegree (HypercubeVert n) Q[n] (hypercubeFintypeNeighborSet n) n
but is expected to have type -/
#guard_msgs (substring := true) in
example (n : ℕ) : δ(Q[n]) = n := (IsRegularOfDegree.hypercube n).minDegree_eq

/-!
Because our lemma takes its instance as an argument, putting the filtering instance
in scope with `let` fixes this. (Had the efficient instance been written into the
statement, we would need `convert` instead.) This `let` is the price of the diamond:
we need it whenever we combine the lemma with a result stated using `[Fintype V]` and
`[DecidableRel G.Adj]`.
-/
example (n : ℕ) : δ(Q[n]) = n := by
  let : Q[n].LocallyFinite := fun v => Subtype.fintype _
  exact (IsRegularOfDegree.hypercube n).minDegree_eq

/-!
Our own `IsRegularOfDegree.card_edgeFinset`, by contrast, takes its instances as
arguments, so it combines with `IsRegularOfDegree.hypercube` directly, with no `let`
required.
-/
/-- The `n`-dimensional hypercube has `n * 2 ^ (n - 1)` edges. -/
lemma card_edgeFinset_hypercube (n : ℕ) [Fintype Q[n].edgeSet] :
    Q[n].edgeFinset.card = n * 2 ^ (n - 1) := by
  rw [(IsRegularOfDegree.hypercube n).card_edgeFinset, card_hypercubeVert]
  cases n with
  | zero => rfl
  | succ n => rw [pow_succ, Nat.add_sub_cancel]; grind

/-!
All of this leads to the rule we follow in the rest of the guide. A second `Fintype`
instance is fine, and sometimes worth having for computation, but a theorem statement
should not commit to either instance. Whenever a statement depends on a `Fintype` (or
`LocallyFinite`) instance, for example through `degree`, `neighborFinset` or
`edgeFinset`, take that instance as an argument. If the proof needs a particular
instance, switch to it at the start of the proof with `let` and `convert_to`, as
above, and get any further instances the proof needs by using the `classical` tactic.

The rule can only be applied to instances that a definition takes as arguments.
Mathlib's `minDegree` and `maxDegree` take no neighbourhood instance: they take
`[Fintype V]` and `[DecidableRel G.Adj]` and build the neighbourhood instances from
these, by filtering. A statement about them therefore takes `[Fintype V]` and
`[DecidableRel G.Adj]` as arguments, and its neighbourhood instance is always the
filtering one. This is why `minDegree_eq` needed the `let` above.

# Computations with Mycielskians

Recall the iterated Mycielskian graphs (`iterMycielskian`). In order to do
computations with these graphs we need to provide computable instances of `Fintype`
for their vertices and `DecidableRel` for adjacency. We do this first for the
Mycielskian of a graph and then for the iterated Mycielskian.
-/

variable {V : Type*} {G : SimpleGraph V}

#source mycielskian -- def mycielskian (G : SimpleGraph V) :
                    --     SimpleGraph (Option (V ⊕ V)) where
                    --   Adj := fun x y => match x, y with
                    --     | some (Sum.inl v), some (Sum.inl w) => G.Adj v w
                    --     | some (Sum.inl v), some (Sum.inr w) => G.Adj v w
                    --     | some (Sum.inr v), some (Sum.inl w) => G.Adj v w
                    --     | none, some (Sum.inr w) => True
                    --     | some (Sum.inr v), none => True
                    --     | _, _ => False

/--
The Mycielskian of a graph with decidable adjacency also has decidable adjacency. -/
instance mycielskianDecidableRelAdj [DecidableRel G.Adj] : DecidableRel mμ[G].Adj :=
  fun x y => by
    rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _)
       <;> unfold mycielskian <;> infer_instance

#source MycielskianVert -- notation: `mμᵥ^n V`

/-- The vertex type of the `n`-th iterated Mycielskian of a graph with decidable
vertex equality also has decidable vertex equality. -/
instance iterMycielskianDecidableEq (n : ℕ) [DecidableEq V] :
    DecidableEq (mμᵥ^n V) := by
  induction n <;> unfold MycielskianVert <;> infer_instance

/-- The vertex type of the `n`-th iterated Mycielskian of a graph with finitely many
vertices also has finitely many vertices. -/
instance iterMycielskianFintype (n : ℕ) [Fintype V] : Fintype (mμᵥ^n V) := by
  induction n <;> unfold MycielskianVert <;> infer_instance

#source iterMycielskian -- notation: `mμ^n G`

/-- If `G` has decidable adjacency then so does the `n`-th iterated Mycielskian of
`G`. -/
instance iterMycielskianDecidableRelAdj (n : ℕ) [DecidableRel G.Adj] :
    DecidableRel (mμ^n G).Adj := by
  induction n <;> unfold iterMycielskian <;> infer_instance

/-!
These instances combine with those from earlier in the chapter. For example, Lean can
find a `Fintype` instance for the edge set of the 4th iterated Mycielskian of
`C[5][2]`, the `2`-uniform blow-up of `C[5]` (see `blowUpN`).
-/
#synth Fintype (mμ^4 (C[5][2])).edgeSet -- (mμ^4 C[5][2]).fintypeEdgeSet

/-!
The 6th iterated Mycielskian of `C[5]` has 383 vertices and 7271 edges; it has
minimum degree 8 and maximum degree 191.
-/
#eval Fintype.card (mμᵥ^6 (Fin 5)) -- 383
#eval (mμ^6 C[5]).edgeFinset.card -- 7271
#eval δ(mμ^6 C[5]) -- 8
#eval Δ(mμ^6 C[5]) -- 191

/-!
Recall the notation we introduced for the vertices of the iterated Mycielskian. The
vertex `v ₗ` is the left copy of `v` in the Mycielskian of a `SimpleGraph V`, and
`v ᵣ` is its right copy.

Recall also that the Grötzsch graph is the Mycielskian of `C[5]`. This has decidable
adjacency so we can reason about it in proofs using `decide`.
-/
example : grotzschGraph.Adj 2 ₗ 3 ᵣ := by
  decide

example : (mμ^7 C[5]).Adj (0 : Fin 5)ₗₗᵣᵣᵣₗₗ (1 : Fin 5)ᵣᵣₗₗₗᵣₗ := by decide
#eval (mμ^10 C[5]).degree none ᵣₗᵣₗᵣₗᵣ -- 199

/-!
## Mycielskian Degrees

As well as doing computations with Mycielskian graphs, we can also prove some general
results about their vertex degrees and the size of their edge sets. We prove one such
result below and leave the rest as exercises.

Note that we give no custom `Fintype` instances for the neighbourhoods of vertices in
the Mycielskian. As
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond)
explained, a second instance would do no harm as long as our statements do not name
one, but here there is no reason to write one. Unlike the hypercube, the default
instance is fast enough: it filters only the `2 * Fintype.card V + 1` vertices of
`Option (V ⊕ V)`, so the `#eval`s above run without difficulty.

The statement below mentions `G.degree v` and `mμ[G].degree v ₗ`, so, following the
rule from
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond),
it takes the `Fintype` instances for these two neighbourhoods as arguments. It needs
nothing else; in particular it holds whether or not `V` is finite. The proof begins
with the `classical` tactic, which supplies the `DecidableEq V` needed to form the
images and the union of finsets below.
-/
open Finset in
@[simp]
lemma degree_mycielskian_left (v : V) [Fintype (G.neighborSet v)]
    [Fintype (mμ[G].neighborSet (v ₗ))] : mμ[G].degree v ₗ = 2 * G.degree v := by
  classical
  have hnb : mμ[G].neighborFinset (v ₗ)
      = (G.neighborFinset v).image (· ₗ) ∪ (G.neighborFinset v).image (· ᵣ) := by
    ext x
    simp [← mem_neighborSet]
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, hnb,
    card_union_of_disjoint (by simp [← Finset.disjoint_coe]),
    card_image_of_injective _ mycielskian.left_injective,
    card_image_of_injective _ mycielskian.right_injective, two_mul]

/-!
If `V` is finite then the vertex type `Option (V ⊕ V)` of the Mycielskian has
`2 * |V| + 1` elements. (Counting the vertices of the `n`-th iterated Mycielskian is
left as an exercise.)
-/
@[simp]
lemma card_mycielskianVert_one [Fintype V] :
    Fintype.card (Option (V ⊕ V)) = 2 * Fintype.card V + 1 := by
  simp [two_mul]

/-!
We can list the edges of the Mycielskian of `C[5]` as follows but the output isn't
very readable.
-/
#eval (mμ[C[5]]).edgeFinset -- {s(none, some (Sum.inr 0)),...

/-!
The solution is to provide a custom `Repr` instance for the vertices of the
Mycielskian. We make it a `scoped instance`: it is active inside
`namespace SimpleGraph` (and wherever `SimpleGraph` is opened), so later chapters
print Mycielskian vertices this way, but other code using `Option (α ⊕ α)` is
unaffected.
-/
scoped instance mycielskianRepr [Repr V] :
    Repr (Option (V ⊕ V)) where
  reprPrec x _ := match x with
    | none => "∗"
    | v ₗ => repr v ++ "ₗ"
    | v ᵣ => repr v ++ "ᵣ"

#eval (mμ[C[5]]).edgeFinset -- {s(∗, 0ᵣ), s(∗, 1ᵣ),..., s(4ₗ, 3ᵣ)}

/-!
We can extend this to the vertices of the iterated Mycielskian.
-/
scoped instance iterMycielskianRepr [Repr V] (n : ℕ) :
    Repr (mμᵥ^n V) := by
  induction n <;> unfold MycielskianVert <;> infer_instance

#eval (mμ^2 C[5]).edgeFinset -- {s(∗, ∗ᵣ), s(∗, 0ₗᵣ),..., s(4ᵣₗ, 3ₗᵣ)}

/-!
# Degree Sequences *

There isn't a definition of degree sequence in Mathlib, so we provide one here. We
will take this to be the non-increasing sequence of degrees of the vertices of a
finite graph.

We start with the `Finset.univ` of all vertices of a `SimpleGraph V` and then take
its underlying `Multiset` (`univ.val`) and map it to the `Multiset` of degrees. We
will call this the `degreeMultiset` of the graph. (In
[The Laplacian](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-the-laplacian)
we meet the *degree matrix*, the diagonal matrix whose entries are these degrees.)
-/
/-- The multiset of degrees of a finite graph. -/
def degreeMultiset [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Multiset ℕ := Finset.univ.val.map (G.degree ·)

/-!
The *degree sequence* is then the sorted non-increasing list of degrees of the
vertices of a finite graph as a `List ℕ`.
-/
#check Multiset.sort -- returns a `List`

/-- The degree sequence of a finite graph, sorted in non-increasing order. -/
def degreeSequence [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    List ℕ := G.degreeMultiset.sort (· ≥ ·)

#eval (K[4, 5]).degreeSequence       -- [5, 5, 5, 5, 4, 4, 4, 4, 4]

#eval (mμ^6 C[5]).degreeSequence  -- [191, 190, 188, 184, 176, 160, 128, 128, ..., 8]

/-!
## Graphic Sequences

The graph realization problem asks: which non-increasing sequences of non-negative
integers occur as the degree sequence of a finite simple graph?

Rather than as a predicate on sorted lists, this is more naturally defined in Lean as
a predicate on `Multiset ℕ` (i.e. a list in which order doesn't matter). (Later when
we want to talk about graphic degree sequences we can simply use the fact that any
`List ℕ` can be coerced to a `Multiset ℕ`.)

We will call a `Multiset ℕ` *graphic* if it is the multiset of degrees of some finite
graph.

Since `G.degreeMultiset` requires `Fintype V` and `DecidableRel G.Adj` instances, we
will quantify over an arbitrary finite vertex type `V : Type` and carry the `Fintype`
and `DecidableRel` instances as existential witnesses that `degreeMultiset`
requires. (Every finite type, in any universe, is equivalent to a type in `Type`
(indeed to `Fin n` for some `n`), and transporting a graph along such an equivalence
leaves its degree multiset unchanged, so restricting to `Type` here loses no
generality.)
-/
/-- A multiset of degrees is *graphic* if it is the degree multiset of some finite
simple graph. -/
def Graphic (m : Multiset ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    m = G.degreeMultiset

/-!
Notice that `Graphic` doesn't actually mention the number of vertices in the graph
even though it must be the same as the cardinality of the multiset `m`. We can easily
deduce this as a theorem and leaving it out of the definition of `Graphic` makes it
easier to work with.
-/
theorem Graphic.exists_card_eq {m : Multiset ℕ} (h : Graphic m) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      m = G.degreeMultiset ∧ Fintype.card V = m.card := by
  obtain ⟨V, hFV, G, hDG, rfl⟩ := h
  exact ⟨V, hFV, G, hDG, rfl, (Multiset.card_map _ _).symm⟩

/-!
With `Graphic` quantifying over an arbitrary finite vertex type, the fact that every
finite simple graph has a graphic degree multiset is immediate: the graph itself is
the witness.
-/
theorem graphic_degreeMultiset {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Graphic (G.degreeMultiset) :=
  ⟨V, inferInstance, G, inferInstance, rfl⟩

/-!
Since a `Multiset` is just a `List` with its order forgotten (i.e. quotiented by the
permutation relation), there is a natural coercion from `List` to `Multiset`.
-/
#synth Coe (List ℕ) (Multiset ℕ) -- Multiset.instCoeList

/-- Every finite simple graph has a graphic degree sequence. -/
theorem graphic_degreeSequence {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Graphic (G.degreeSequence) :=
  ⟨V, inferInstance, G, inferInstance, by simp [degreeSequence]⟩

/-!
The multiset consisting of `n` copies of `k` is defined by `Multiset.replicate n k`.
-/
#check Multiset.replicate -- Multiset.replicate (n : ℕ) (a : α) : Multiset α
#eval Multiset.replicate 5 3 -- {3, 3, 3, 3, 3}

/-- The empty graph on `Fin n` has the all-zeros degree multiset. -/
theorem degreeMultiset_bot (n : ℕ) :
    E[n].degreeMultiset = Multiset.replicate n 0 := by
  simp [degreeMultiset]

/-- A multiset of `n` zeros is graphic, realized by the empty graph. -/
theorem graphic_zeros (n : ℕ) : Graphic (Multiset.replicate n 0) :=
  degreeMultiset_bot n ▸ graphic_degreeMultiset E[n]

/-!
In particular the empty multiset is graphic (notice that the empty multiset is
denoted by `0`).
-/
lemma graphic_zero : Graphic 0 := graphic_zeros 0

/-!
## The Erdős–Gallai Theorem

There are two major results in graph theory that characterize graphic sequences. One
is the *Erdős–Gallai* theorem
[Erdős–Gallai 1960](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-erdos-gallai-1960):
given a non-increasing sequence `[d₁, d₂, …, dₙ]` this says that the sequence is
graphic iff its sum is even and for each `1 ≤ k ≤ n` we have
`(d₁ + d₂ + … + dₖ) ≤ k * (k - 1) + (min(k, dₖ₊₁) + min(k, dₖ₊₂) + … + min(k, dₙ))`.

The necessity of this is easy informally: suppose we have a graph with this degree
sequence and `deg(vᵢ) = dᵢ`. Summing the first `k` terms we count the edges in the
subgraph induced by `sₖ = {v₁, …, vₖ}` twice and the edges in the bipartite graph
between `sₖ` and its complement once. No subgraph has more edges than a clique, so
the induced subgraph on `sₖ` has at most `k * (k - 1) / 2` edges and hence
contributes at most `k * (k - 1)` to the sum, while the number of edges in the
bipartite graph can be bounded above by considering how many edges each vertex `vₖ₊ᵢ`
sends to `sₖ`, which is clearly at most `min(k, dₖ₊ᵢ)`.

[Figure: The case $k = 3$ for degrees $(4, 4, 4, 4, 2, 2)$. The sum $d_1 + d_2 + d_3 = 12$ counts each edge inside $s_3$ (blue) twice and each edge leaving $s_3$ (orange) once, and is at most $3 \cdot 2 + \min(3, 4) + \min(3, 2) + \min(3, 2) = 13$](https://jt496.github.io/GraphTheoryInLean/figures/erdosGallai.svg)

We can use `List.take` and `List.drop` to express this predicate in Lean. The
`List.take k` function takes the first `k` elements of a list (or the whole list if
it has less than `k` elements) and `List.drop k` drops the first `k` elements of a
list (or returns the empty list if it has less than `k` elements).
-/
#check List.take
#check List.drop

/-- The predicate `ErdosGallaiLE m k` is true if the `k`-th Erdős–Gallai inequality
holds for `m : Multiset ℕ` and `k : ℕ`. -/
abbrev ErdosGallaiLE (m : Multiset ℕ) (k : ℕ) : Prop :=
    ((m.sort (· ≥ ·)).take k).sum ≤
        k * (k - 1) + (((m.sort (· ≥ ·)).drop k).map (min k)).sum

/-!
Now the Erdős–Gallai theorem can be stated as follows.
-/
theorem erdos_gallai (m : Multiset ℕ) :
    (Even m.sum ∧ ∀ (k : ℕ), k ≤ m.card → ErdosGallaiLE m k) ↔ Graphic m := by
  sorry

/-!
The Erdős–Gallai conditions are easy to check by computer, so (modulo its proof) the
theorem gives an efficient decision procedure for graphic sequences. It is a
beautiful and very useful result, but it doesn't actually give us a construction of a
graph from a given graphic sequence.

## The Havel–Hakimi Theorem: a Computable Constructor for Graphic Sequences

The *Havel–Hakimi* theorem
[Havel 1955](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-havel-1955)
[Hakimi 1962](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-hakimi-1962)
also characterizes graphic sequences and in the process provides a constructive
method for producing a graph with a given degree sequence.

The Havel–Hakimi theorem says that a non-increasing sequence `[d₁, d₂, …, dₙ]` is
graphic iff the sequence reduces to the empty sequence using the following recursive
procedure:

1. If the list is empty then accept.
2. Otherwise the list is `d :: tail` for some `d : ℕ`. If `tail` has at least `d`
   entries and none of its first `d` entries is zero, then remove the first entry
   from the list, reduce each of the next `d` entries by `1`, and recurse; otherwise
   reject.

The recursive call must again be given a non-increasing list. Rather than sorting
from scratch we can *merge*: the `d` decremented entries are still in non-increasing
order (subtracting `1` preserves the order, and since each was at least `1` no entry
is truncated at `0`), and so are the remaining entries, being a suffix of a sorted
list. Merging two sorted lists with `List.merge` takes linear time and gives exactly
the same list that sorting would have produced.

The check that none of the first `d` entries is zero matters even more in Lean than
on paper. Subtraction on `ℕ` is truncated, so `0 - 1 = 0`, and without the check
`[1, 0]` would reduce to `[0]` and then to `[]`, and so be accepted, although no
graph has one vertex of degree `1` and one of degree `0`.
-/
/-- *Havel–Hakimi*, assuming the input list is sorted in non-increasing order. -/
def havelHakimiAux : List ℕ → Bool
  | [] => true -- the empty graph on no vertices
  | d :: tail =>
    -- `s` is the next `d` entries.
    let s := tail.take d
    if (s.length == d) && s.all (· != 0) then
      -- reduce each of the next `d` entries by `1` and recurse
      havelHakimiAux ((s.map (· - 1)).merge (tail.drop d) (· ≥ ·))
    else
      false
  -- The recursive call is not on a sub-list of the input, so Lean cannot see for
  -- itself that `havelHakimiAux` terminates.
  -- `termination_by` tells it to check that the length of the list decreases
  --  at each call, and `decreasing_by` proves this.
termination_by l => l.length
decreasing_by
  grind [List.length_merge]

/-!
So we can decide whether a `Multiset ℕ` or `List ℕ` is graphic using Havel–Hakimi.

The input `m` is first sorted into non-increasing order, so this is correct for an
arbitrarily ordered list of degrees.
-/

/-- Decide whether a `Multiset ℕ` or `List ℕ` is graphic using Havel–Hakimi. -/
def havelHakimi (m : Multiset ℕ) : Bool := havelHakimiAux (m.sort (· ≥ ·))

#eval havelHakimi [6, 5, 4, 3, 2, 1, 1] -- false: it reduces to [4, 3, 2, 1, 0, 0]
                                        -- which has too many zeros so is rejected.

theorem havel_hakimi (m : Multiset ℕ) : havelHakimi m ↔ Graphic m := by
  sorry

/-!
Modulo a proof of the Havel–Hakimi theorem, we have an efficient decision procedure.
We make it a `local instance`, so that an instance based on a `sorry` is not
available outside of this chapter.
-/
local instance : DecidablePred Graphic := fun m =>
  decidable_of_iff _ (havel_hakimi m)

/-!
Since this instance relies on the `sorry` in the proof of `havel_hakimi`, `#eval`
will refuse to evaluate it, but we can still use it with `#eval!`, and the answers it
gives are still meaningful. As we saw in
[Decidability and Kernel Reduction*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-decidability-and-kernel-reduction),
the verdict of `decidable_of_iff` comes entirely from the `Decidable` instance for
its left-hand side, here `havelHakimi m = true`; the proof of the `Iff` is used only
to build the accompanying proof terms, and compiled code erases those. So `#eval!`
genuinely runs `havelHakimi`. What the `sorry` leaves unverified is *only* the claim
that its verdict agrees with `Graphic`.
-/
#eval! Graphic (mμ^3 C[5]).degreeMultiset -- true
#eval! Graphic [6, 5, 4, 3, 2, 1, 1] -- false

/-!
As with the Erdős–Gallai theorem we won't attempt a proof, but one of the crucial
ingredients is the following `coneGraph` construction. Given `H : SimpleGraph V` and
`s : Set V` this is the graph formed by adding a new vertex adjacent to exactly the
vertices in `s`. We build this on the vertex type `Option V` in the obvious way.

The cone graph appears naturally in the proof of the Havel–Hakimi theorem. We need to
show that a sequence `[d₁, d₂, …, dₙ]` is graphic iff the sequence
`[d₂ - 1, …, dₖ₊₁ - 1, dₖ₊₂, …, dₙ]` is graphic where `k = d₁`. The reverse direction
is easy: if the second sequence is graphic and it is realized by the graph `H`, and
`s` is the set of `d₁` vertices of `H` with degrees `d₂ - 1`, ..., `dₖ₊₁ - 1` then
`coneGraph H s` is a graph that realizes the original degree sequence.

[Figure: The sequence $(3, 3, 2, 2, 2)$ reduces to $(2, 2, 1, 1)$, which the path $H$ realizes. `coneGraph H s` joins the new vertex `none` to the $d_1 = 3$ vertices of $s$ (orange edges). The numbers are the degrees in $H$ and then in `coneGraph H s`, which realizes $(3, 3, 2, 2, 2)$](https://jt496.github.io/GraphTheoryInLean/figures/coneGraph.svg)
-/

/-- `coneGraph H s` adds a new vertex `none` to `H`, adjacent to precisely the
vertices in the set `s`. -/
@[simps]
def coneGraph (H : SimpleGraph V) (s : Set V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | none, some w => w ∈ s
    | some w, none => w ∈ s
    | some a, some b => H.Adj a b
    | none, none => False
  symm := ⟨by rintro (_ | a) (_ | b) h <;> simp_all [SimpleGraph.adj_comm]⟩
  loopless := ⟨by rintro (_ | a) h <;> simp_all⟩

/-!
If membership of the set `s` is decidable then the cone graph has a decidable
adjacency relation (assuming `H` does).
-/
instance (H : SimpleGraph V) (s : Set V) [DecidablePred (· ∈ s)]
    [DecidableRel H.Adj] : DecidableRel (coneGraph H s).Adj := by
  rintro (_ | a) (_ | b) <;> unfold coneGraph <;> infer_instance

/-!
If the set `s` is finite then the new vertex has degree `s.card`.
-/
@[simp]
theorem degree_coneGraph_none (H : SimpleGraph V) (s : Finset V)
    [Fintype ((coneGraph H s).neighborSet none)] :
    (coneGraph H s).degree none = s.card := by
  have h : (coneGraph H s).neighborFinset none = s.map Function.Embedding.some := by
    ext x; cases x <;> simp
  rw [← card_neighborFinset_eq_degree, h, Finset.card_map]

/-!
This is still a long way from the proof of Havel–Hakimi but we have at least one
crucial ingredient!

We can adapt the decision procedure `havelHakimiAux` above to construct the edges of
a graph with any given graphic degree sequence based on the `coneGraph` construction.

The following function takes a `List (ℕ × ℕ)`, i.e. a list of pairs `(d, v)`, where
the labels `v : ℕ` should be distinct and `d` is the required degree of the vertex
`v`. If the sequence is graphic it returns `some` list of the edges of a graph
realizing it, each edge given once as a pair `(v, w)`, in which each vertex `v` has
degree `d`; if not, it returns `none`. (The input list should be sorted in
non-increasing order of degrees.)

Each recursive step is exactly one `coneGraph` construction: it realizes the reduced
sequence by some graph `H`, then joins a new vertex `v` onto the `d` highest degree
vertices (no edges at all when `d = 0`), so the returned edge list is built up "cone
by cone". The inline comments below relate each piece to `coneGraph H s`.
-/
/-- Constructive Havel–Hakimi: given a labelled degree sequence `(d, v)`, sorted by
non-increasing `d`, return the edge list of a graph realizing it, or `none` if the
sequence is not graphic. -/
def havelHakimiEdges : List (ℕ × ℕ) → Option (List (ℕ × ℕ))
  | [] => some []      -- empty list returns no edges
  | (d, v) :: tail =>  -- vertex `v` has degree `d` (possibly `0`)
    let s := tail.take d
    if (s.length == d) && s.all (·.1 != 0) then
      -- This is the `coneGraph` reverse direction above.
      let next := (s.map (fun (p : ℕ × ℕ) => (p.1 - 1, p.2))).merge (tail.drop d)
                    (fun a b => a.1 ≥ b.1)
      -- Recurse to realize the sequence `next` by a graph `H` with edge list `E`
      match havelHakimiEdges next with
      | some E =>
        -- The edges `coneGraph H s` adds are `v` joined to each vertex of `s`.
        let new := s.map fun (p : ℕ × ℕ) => (v, p.2)
        some (new ++ E)
      | none => none -- `next` is not graphic, so neither is the original sequence
    else none
termination_by l => l.length
decreasing_by
  grind [List.length_merge]

#eval havelHakimiEdges <| [5, 4, 4, 4, 4, 3, 2].zip (.range 7)
    -- some [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4),
    --       (2, 3), (2, 4), (5, 6), (5, 3), (6, 4)]
/-!
We can check this answer by building the graph. Any relation `r` on `V` gives a graph
`SimpleGraph.fromRel r`, which makes `r` symmetric and removes any loops. As we saw
for `pathNat₂'`, Lean synthesizes decidable adjacency for such a graph when `r` is
decidable, provided the graph is an `abbrev`, so we can compute its degree sequence.
-/
/-- The graph on `Fin n` whose edges are the pairs in `E`. -/
abbrev graphOfEdgeList (n : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun v w => (v.val, w.val) ∈ E

#eval (havelHakimiEdges <| [5, 4, 4, 4, 4, 3, 2].zip (.range 7)).map
  fun E => (graphOfEdgeList 7 E).degreeSequence -- some [5, 4, 4, 4, 4, 3, 2]

#eval (havelHakimiEdges <| [6, 5, 4, 3, 2, 1, 1].zip (.range 7)).map
  fun E => (graphOfEdgeList 7 E).degreeMultiset -- none

/-!
If we give the `havelHakimiEdges` function a graphic degree sequence for a particular
graph there is absolutely no reason it should return the edges of the same graph (or
even an isomorphic copy of it).

For example if we give it the degree sequence of `C[6]` it returns the edges of two
disjoint copies of `C[3]`, i.e. `C[3] ⊕g C[3]`.
-/
#eval C[6].degreeSequence -- [2, 2, 2, 2, 2, 2]
#eval havelHakimiEdges                              -- some [(0, 1), (0, 2), (3, 4),
          <| C[6].degreeSequence.zip (.range 6) --       (3, 5), (4, 5), (1, 2)]

#eval (C[3] ⊕g C[3]).degreeSequence = C[6].degreeSequence -- true

end SimpleGraph
