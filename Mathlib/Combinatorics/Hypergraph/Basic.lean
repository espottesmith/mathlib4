/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.Graph.Basic

open Set

variable {α β : Type*} {x y z : α} {e f g : Set α} {l m n : Set (Set α)}

/-!

# Undirected hypergraphs

An *undirected hypergraph* (here abbreviated as *hypergraph*) `H` is a generalization of a graph
(see `Mathlib.Combinatorics.Graph`) and consists of a set of *vertices*, usually denoted `V` or
`V(H)`, and a set of *hyperedges*, denoted `E` or `E(H)`. In contrast with a graph, where edges are
unordered pairs of vertices, in hypergraphs, hyperedges are (unordered) sets of vertices of length
`0 ≤ |e| ≤ |V|`, where `e` is some hyperedge.

A hypergraph where `V = ∅` and `E = ∅` is *empty*. A hypergraph with a nonempty
vertex set (`V ≠ ∅`) and empty hyperedge set is *trivial*. A *complete hypergraph* is
one where `E(H) = 𝒫 V(H)`, where `𝒫 V(H)` is the *power set* of the vertex set.

If a hyperedge `e` contains only one vertex (i.e., `|e| = 1`), then it is a *loop*.

This module defines `Hypergraph α` for a vertex type `α` (hyperedges are defined as `Set Set α`).
In the near term, the hope is to provide an API for incidence and adjacency, as well as for
conversions:
- `Graph α β → Hypergraph α` (coersion/generalization of graph as 2-uniform hypergraph)
- `Hypergraph α → Graph α (α × α)` (as a *clique graph* or *two-section graph*)
- `Hypergraph α → Matrix α (Set α) γ` (the *incidence matrix* of the hypergraph)
- `Hypergraph α → Hypergraph α` (e.g., constructing the *dual* of a hypergraph)

## Main definitions

For `H : Hypergraph α`:

* `V(H)` denotes the vertex set of `H` as a term in `Set α`.
* `E(H)` denotes the hyperedge set of `H` as a term in `Set (Set α)`. Hyperedges must be subsets of
    `V(H)`.
* `H.Adj x y` means that there exists some hyperedge containing both `x` and `y` (or, in other
    words, `x` and `y` are incident on some shared hyperedge `e`).
* `H.EAdj e f` means that there exists some vertex that is incident on both hyperedge `e` and
    hyperedge `f : Set α`.

## Implementation details

This implementation is heavily inspired by Peter Nelson and Jun Kwon's `Graph` implementation,
which was in turn inspired by `Matroid`.

From `Mathlib.Combinatorics.Graph.Basic`:
"The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation."

## Acknowledgments

Credit to Shreyas Srinivas, GitHub user @NotWearingPants ("Snir" on the Lean Zulip), Ammar
Husain, and Aaron Liu for useful feedback on this implementation.
-/

structure Hypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The hyperedge set -/
  hyperedgeSet : Set (Set α)
  /-- All hyperedges must be subsets of the vertex set -/
  hyperedge_isSubset_vertexSet : ∀ ⦃e⦄, e ∈ hyperedgeSet → e ⊆ vertexSet

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `hyperedgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.hyperedgeSet H


section DefsPreds

/-! ## Basic Hypergraph Definitions & Predicates-/

/--
The set of all hyperedges `e ∈ E(H)` that a given vertex `x` is incident on
-/
def hyperedgesIncVertex (H : Hypergraph α) (x : α) : Set (Set α) := {e ∈ E(H) | x ∈ e }

/--
We define the *vertex hyperedge set* as the set of subsets of `E(H)` that each vertex in `V(H)` is
incident upon
-/
def hyperedgesIncVertices (H : Hypergraph α) : Set (Set (Set α)) :=
  {H.hyperedgesIncVertex x | x ∈ V(H)}

/--
Predicate to determine if a vertex is isolated, meaning that it is not incident on any hyperedges.
Note that this includes loops, i.e., if vertex `x` is isolated, there is no hyperedge with
associated vertex subset `{x}`
-/
def IsIsolated (H : Hypergraph α) (x : α) : Prop := ∀ e ∈ E(H), x ∉ e

/--
Predicate to determine if a hyperedge `e` is a loop, meaning that its associated vertex subset `s`
contains only one vertex, i.e., `|s| = 1`
-/
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := e ∈ E(H) ∧ Set.encard e = 1

/--
Predicate to determine if a hypergraph is empty
-/
def IsEmpty (H : Hypergraph α) : Prop := V(H) = ∅ ∧ E(H) = ∅

/--
Predicate to determine if a hypergraph is trivial

A hypergraph is trivial if it has a nonempty vertex set and an empty hyperedge set
-/
def IsTrivial (H : Hypergraph α) : Prop := Nonempty V(H) ∧ E(H) = ∅

/--
Predicate to determine is a hypergraph `H` is complete, meaning that each member of the power set of
the vertices (`𝒫 V(H)`) is represented in `E(H)`
-/
def IsComplete (H : Hypergraph α) : Prop := ∀ e ∈ 𝒫 V(H), e ∈ E(H)

/--
Predicate to determine if a hypergraph is simple

A simple hypergraph is one in which, for each hyperedge `e ∈ E(H)` (with associated vertex subset
`s : Set α`), there is no other hyperedge `f ∈ E(H)` (with associated vertex subset `t : Set α`)
such that `s ⊂ t`.
-/
def IsSimple (H : Hypergraph α) : Prop := ∀ e ∈ E(H), ∀ f ∈ E(H) \ {e}, ¬e ⊆ f

/--
Predicate to determine if a hypergraph is *`k`-uniform*.

In a `k`-uniform hypergraph `H`, all hyperedges `e ∈ E(H)` have the same cardinality, i.e.,
`|e| = k`.
-/
def IsKUniform (H : Hypergraph α) (k : ℕ) : Prop := ∀ e ∈ E(H), Set.ncard e = k

/--
Predicate to determine if a hypergraph is *`d`-regular*.

In a `d`-regular hypergraph `H`, all vertices `v ∈ V(H)` have the same degree, i.e., all vertices
are incident on `d` hyperedges.
-/
def IsDRegular (H : Hypergraph α) (d : ℕ) : Prop := ∀ l ∈ H.hyperedgesIncVertices, Set.ncard l = d

end DefsPreds

section Adjacency

/-! ## Vertex and Hyperedge Adjacency -/

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some
hyperedge `e ∈ E(H)` where `x` and `y` are both incident on `e`.

Note that we do not need to explicitly check that x, y ∈ V(H) here because a vertex that is not in
the vertex set cannot be incident on any hyperedge.
-/
def Adj (H : Hypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(H), x ∈ e ∧ y ∈ e

/--
Predicate for (hyperedge) adjacency. Analogous to `Hypergraph.Adj`, hyperedges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident on both `e` and `f`.

Note that we do not need to explicitly check that e, f ∈ E(H) here because a vertex cannot be
incident on a hyperedge that is not in the hyperedge set.
-/
def EAdj (H : Hypergraph α) (e : Set α) (f : Set α) : Prop :=
  ∃ x ∈ V(H), x ∈ e ∧ x ∈ f

/--
Neighbors of a vertex `x` in hypergraph `H`

A vertex `y` is a neighbor of vertex `x` if there exists some hyperedge `e ∈ E(H)` where `x` and
`y` are both incident on `e`, i.e., if the two vertices are adjacent (see `Hypergraph.Adj`)
-/
def neighbors (H : Hypergraph α) (x : α) := {y | H.Adj x y}

/--
Neighbors of a hyperedge `e` in hypergraph `H`

A hyperedge `f` is a neighbor of hyperedge `e` if there exists some vertex `x ∈ V(H)` where `x` is
incident on both `e` and `f`, i.e., if the two hyperedges are adjacent (see `Hypergraph.EAdj`)
-/
def hyperedgeNeighbors (H : Hypergraph α) (e : Set α) := {f | H.EAdj e f}

end Adjacency

section Card

/-! ## Cardinality -/

/--
The *order* of a hypergraph `H` is defined as the number of vertices contained in `H`
-/
noncomputable def order (H : Hypergraph α) : ENat := Set.encard V(H)

/--
The *size* of a hypergraph `H` is defined as the number of hyperedges contained in `H`
-/
noncomputable def size (H : Hypergraph α) : ENat := Set.encard E(H)

/--
The set of vertex *degrees* of a hypergraph `H`.

A vertex `x` has degree `n`, where `n` is the number of hyperedges in `E(H)` that `x` is incident
on.
-/
noncomputable def vertexDegrees (H : Hypergraph α) : Set ENat :=
  {Set.encard l | l ∈ H.hyperedgesIncVertices}

/--
The set of hyperedge *degrees* of a hypergraph `H`.

A hyperedge `e` has degree `n`, where `n` is the number of vertices in `V(H)` that are incident on
`e`.
-/
noncomputable def hyperedgeDegrees (H : Hypergraph α) : Set ENat := {Set.encard e | e ∈ E(H)}

end Card

section Sub
/-! ## Subhypergraphs, Partial Hypergraphs, and Section Hypergraphs -/

/--
Given a subset of the vertex set `V(H)` of a hypergraph `H` (`g : Set α`), the
*subhypergraph* `Hg` has `V(Hg) = g ∩ V(H)`, and `E(Hg)` is the subset of `E(H)` for which all
incident vertices are included in `g`.
-/
def subHypergraph (H : Hypergraph α) (g : Set α) :=
  Hypergraph.mk
  (g ∩ V(H))
  {e | e ∈ E(H) ∧ e ⊆ g}
  (sorry)

/--
Given a subset of the vertex set `V(H)` of a hypergraph `H` (`g`),the *induced subhypergraph* `Hg`
has `V(Hg) = g ∩ V(H)` and `E(Hg)` contains the (nonempty) subset of each hyperedge that intersects
with `g`.
-/
def inducedSubHypergraph (H : Hypergraph α) (g : Set α) :=
  Hypergraph.mk
  (g ∩ V(H))
  { { x | x ∈ (g ∩ e)} | e ∈ {f ∈ E(H) | g ∩ f ≠ ∅}}
  (sorry)

/--
Given a subset of the hyperedge set `E(H)` of a hypergraph `H` (`l : Set (Set α)`), the
*partial hypergraph* `Hˡ` has `E(Hˡ) = l ∩ E(H)` and `V(Hˡ)` is the subset of `V(H)` which is
incident on at least one hyperedge in `E(Hˡ)`.
-/
def partialHypergraph (H : Hypergraph α) (l : Set (Set α)) :=
  Hypergraph.mk
  {x | x ∈ V(H) ∧ ∃ e ∈ l, e ∈ E(H) ∧ x ∈ e}
  (l ∩ E(H))
  (sorry)

end Sub

end Hypergraph
