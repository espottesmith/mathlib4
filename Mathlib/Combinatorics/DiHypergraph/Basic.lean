/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# Directed hypergraphs

A *directed hypergraph* (here abbreviated as *dihypergraph*) `Dₕ` is a generalization of a directed
graph (see `Mathlib.Combinatorics.Digraph`). It consists of a set of vertices, denoted `V` or
`V(Dₕ)`, and a set of *directed hyperedges* (sometimes called *hyperarcs*), which we denote `E` or
`E(Dₕ)`. Note that, when we refer to *hyperedges* in this module, we are referring to directed
hyperegdges unless otherwise specified.  While, in a digraph, directed edges connect pairs of
vertices, directed hyperedges can connect arbitrary numbers of vertices.

This module defines `DiHypergraph α` for a vertex type `α`. We represent a directed hyperedge `e`
as a pair of sets of vertices (i.e., `e : (Set α) × (Set α)`). Each of the two sets in a directed
hyperedge is called a *side* or a *limb*. The first side is called the *source* or the *tail*, and
the second side is called the *destination* or *head* of the hyperedge.

## Main definitions

Basic directed hypergraph definitions:

* `DiHypergraph α`
* `BHypergraph α`: A special case of directed hypergraph where the destination of any hyperedge
    (*B-arc*) contains exactly one vertex.
* `FHypergraph α`: A special case of directed hypergraph where the source of any hyperedge (*F-arc*)
    contains exactly one vertex.
* `BFHypergraph α`: A special case of directed hypergraph where all hyperedges are either B-arcs
    or F-arcs; i.e., either the source contains exactly one vertex or the destination contains
    exactly one vertex.



## Implementation details

Because `hyperedgeSet` is a `Set (Set α)`, rather than a multiset, here we are assuming that
all hypergraphs are *without repeated hyperedge*. Further, a vertex cannot be present in a
hyperedge more than once; developing the theory of such *weighted directed hyperedges* (treating
the degeneracy of a vertex in a hyperedge source/destination as a kind of weight) is a topic for
future work.
-/

open Set

variable {α : Type*} {x y z : α} {d d' s s' : Set α} {e f g : (Set α) × (Set α)}

/--
An directed hypergraph with vertices of type `α` and hyperedges of type `((Set α) × (Set α))`,
as described by vertex and hyperedge sets `vertexSet : Set α` and
`hyperedgeSet : Set ((Set α) × (Set α))`.

The requirement `hyperedge_src_dst_isSubset_vertexSet` ensures that, for all hyperedges, all
vertices in the source and all vertices in the destination are part of `vertexSet`, i.e., all
hyperedge sides are subsets of the `vertexSet`.
-/
@[ext]
structure DiHypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The hyperedge set -/
  hyperedgeSet : Set ((Set α) × (Set α))
  /-- Each hyperedge is a pair (s, d), where s ⊆ vertexSet and d ⊆ vertexSet -/
  hyperedge_src_dst_isSubset_vertexSet : ∀ ⦃e⦄, e ∈ hyperedgeSet → e.1 ⊆ vertexSet ∧ e.2 ⊆ vertexSet

/--
A special case of `DiHypergraph` where all hyperedge destinations contain exactly one vertex, as
defined in `hyperedge_dst_one_vertex`.
-/
@[ext]
structure BHypergraph (α : Type*) extends DiHypergraph α where
  hyperedge_dst_one_vertex : ∀ e ∈ hyperedgeSet, ∃ x ∈ vertexSet, e.2 = {x}

/--
A special case of `DiHypergraph` where all hyperedge sources contain exactly one vertex, as defined
in `hyperedge_src_one_vertex`.
-/
@[ext]
structure FHypergraph (α : Type*) extends DiHypergraph α where
  hyperedge_src_one_vertex : ∀ e ∈ hyperedgeSet, ∃ x ∈ vertexSet, e.1 = {x}

/--
A special case of `DiHypergraph` where all hyperedges have a source containing exactly one vertex
or have a destination containing exactly one vertex, as defined in
`hyperedge_src_one_vertex_or_dst_one_vertex`.
-/
@[ext]
structure BFHypergraph (α : Type*) extends DiHypergraph α where
  hyperedge_src_one_vertex_or_dst_one_vertex :
    ∀ e ∈ hyperedgeSet, (∃ x ∈ vertexSet, e.1 = {x}) ∨ (∃ x ∈ vertexSet, e.2 = {x})

/--
Many results related to directed hypergraphs assume that hyperedge sides are nonempty. We define
a hypergraph with nonempty hyperedge sources/destinations as a special case of dihypergraph,
termed `NonEndlessDiHypergraph`.

The nonemptiness requirement is defined as `hyperedge_src_dst_nonempty`.
-/
@[ext]
structure NonEndlessDiHypergraph (α : Type*) extends DiHypergraph α where
  hyperedge_src_dst_nonempty : ∀ e ∈ hyperedgeSet, e.1.Nonempty ∧ e.2.Nonempty

namespace DiHypergraph

-- TODO: you are here

end DiHypergraph
