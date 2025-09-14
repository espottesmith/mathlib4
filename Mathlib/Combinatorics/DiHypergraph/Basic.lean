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
`V(Dₕ)`, and a set of *directed (hyper)edges* (sometimes called *hyperarcs*), which we denote `E` or
`E(Dₕ)`. Note that, when we refer to *edges* in this module, we are referring to directed edges
unless otherwise specified.  While, in a digraph, directed edges connect pairs of vertices,
directed edges in a dihypergraph can connect arbitrary numbers of vertices.

This module defines `DiHypergraph α` for a vertex type `α`. We represent a directed edge `e`
as a pair of sets of vertices (i.e., `e : (Set α) × (Set α)`). Each of the two sets in a directed
edge is called a *side* or a *limb*. The first side is called the *source* or the *tail*, and
the second side is called the *destination* or *head* of the edge.

## Main definitions

Basic directed hypergraph definitions:

* `DiHypergraph α`
* `IsBHypergraph`: A predicate defining a special case of dihypergraph where the destination of any
    edge (*B-arc*) contains exactly one vertex.
* `IsFHypergraph`: A predicate defining a special case of dihypergraph where the source of any edge
    (*F-arc*) contains exactly one vertex.
* `IsBFHypergraph`: A predicate defining a special case of dihypergraph where all edges are either
    B-arcs or F-arcs; i.e., either the source contains exactly one vertex or the destination
    contains exactly one vertex.
* `IsNonEndless`: A predicate defining a special case of dihypergraph where, for all edges, neither
    the source nor the destination are empty.

## Implementation details

Because `edgeSet` is a `Set((Set α) × (Set α))` rather than a multiset, here we are assuming that
all dihypergraphs are *without repeated edge*. Further, a vertex cannot be present in an edge more
than once; developing the theory of such *weighted directed edges* (treating the degeneracy of
a vertex in a edge source/destination as a kind of weight) is a topic for future work.
-/

open Set

variable {α : Type*} {x y z : α} {d d' s s' : Set α} {e f g : (Set α) × (Set α)}

/--
An directed hypergraph with vertices of type `α` and edges of type `((Set α) × (Set α))`, as
described by vertex and edge sets `vertexSet : Set α` and `edgeSet : Set ((Set α) × (Set α))`.

The requirement `edge_src_dst_isSubset_vertexSet` ensures that, for all edges, all
vertices in the source and all vertices in the destination are part of `vertexSet`, i.e., all
limbs of all edges are subsets of the `vertexSet`.
-/
@[ext]
structure DiHypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The edge set -/
  edgeSet : Set ((Set α) × (Set α))
  /-- Each edge is a pair (s, d), where s ⊆ vertexSet and d ⊆ vertexSet -/
  edge_src_dst_isSubset_vertexSet' : ∀ ⦃e⦄, e ∈ edgeSet → e.1 ⊆ vertexSet ∧ e.2 ⊆ vertexSet

namespace DiHypergraph

variable {Dₕ Dₕ' : DiHypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a dihypergraph `Dₕ` -/
scoped notation "V(" Dₕ ")" => DiHypergraph.vertexSet Dₕ

/-- `E(H)` denotes the `edgeSet` of a hypergraph `H` -/
scoped notation "E(" Dₕ ")" => DiHypergraph.edgeSet Dₕ

/-! ## DiHypergraph Basics -/

@[simp]
lemma edge_src_dst_isSubset_vertexSet (he : e ∈ E(Dₕ)) : e.1 ⊆ V(Dₕ) ∧ e.2 ⊆ V(Dₕ) :=
  Dₕ.edge_src_dst_isSubset_vertexSet' he

@[simp]
lemma src_isSubset_vertexSet (he : e ∈ E(Dₕ)) : e.1 ⊆ V(Dₕ) :=
  (Dₕ.edge_src_dst_isSubset_vertexSet he).1

@[simp]
lemma dst_isSubset_vertexSet (he : e ∈ E(Dₕ)) : e.2 ⊆ V(Dₕ) :=
  (Dₕ.edge_src_dst_isSubset_vertexSet he).2

/-! ## Vertex-Edge Incidence -/

lemma mem_vertexSet_of_mem_edgeSet_src_dst (he : e ∈ E(Dₕ)) (hx : x ∈ e.1 ∨ x ∈ e.2) : x ∈ V(Dₕ) :=
  by
    cases hx with
    | inl hsrc => apply Set.mem_of_subset_of_mem (src_isSubset_vertexSet he) hsrc
    | inr hdst => apply Set.mem_of_subset_of_mem (dst_isSubset_vertexSet he) hdst

lemma mem_vertexSet_of_mem_edgeSet_src (he : e ∈ E(Dₕ)) (hx : x ∈ e.1) : x ∈ V(Dₕ) :=
  mem_vertexSet_of_mem_edgeSet_src_dst he (by left; exact hx)

lemma mem_vertexSet_of_mem_edgeSet_dst (he : e ∈ E(Dₕ)) (hx : x ∈ e.2) : x ∈ V(Dₕ) :=
  mem_vertexSet_of_mem_edgeSet_src_dst he (by right; exact hx)

/--
The *tail star* of a vertex `x` is the set of all tails of edges `e ∈ E(Dₕ)` where `x` is in the
tail of `e`.
-/
def tail_star (Dₕ : DiHypergraph α) (x : α) : Set (Set α) := {t | e ∈ E(Dₕ) ∧ x ∈ e.1 ∧ t = e.1}

/--
The *head star* of a vertex `x` is the set of all heads of edges `e ∈ E(Dₕ)` where `x` is in the
head of `e`.
-/
def head_star (Dₕ : DiHypergraph α) (x : α) : Set (Set α) := {h | e ∈ E(Dₕ) ∧ x ∈ e.2 ∧ h = e.2}

/--
The *negative star* of a vertex `x` is the set of all edges `e ∈ E(Dₕ)` where `x` is in the tail of
`e`.
-/
def negative_star (Dₕ : DiHypergraph α) (x : α) : Set (Set α × Set α) := {e | e ∈ E(Dₕ) ∧ x ∈ e.1}

/--
The *negative degree* of a vertex `x` is the cardinality of the negative star of `x`.
-/
noncomputable def negative_degree (Dₕ : DiHypergraph α) (x : α) : ℕ∞ := (Dₕ.negative_star x).encard

/--
The *positive star* of a vertex `x` is the set of all edges `e ∈ E(Dₕ)` where `x` is in the head of
`e`.
-/
def positive_star (Dₕ : DiHypergraph α) (x : α) : Set (Set α × Set α) := {e | e ∈ E(Dₕ) ∧ x ∈ e.2}

/--
The *positive degree* of a vertex `x` is the cardinality of the positive star of `x`.
-/
noncomputable def positive_degree (Dₕ : DiHypergraph α) (x : α) : ℕ∞ := (Dₕ.positive_star x).encard


/-! ## Special Cases -/
section SpecialCase

/--
A special case of `DiHypergraph` where all hyperedge destinations contain exactly one vertex.
-/
def IsBHypergraph (Dₕ : DiHypergraph α) := ∀ e ∈ E(Dₕ), ∃ x ∈ V(Dₕ), e.2 = {x}

/--
A special case of `DiHypergraph` where all hyperedge sources contain exactly one vertex.
-/
def IsFHypergraph (Dₕ : DiHypergraph α) :=  ∀ e ∈ E(Dₕ), ∃ x ∈ V(Dₕ), e.1 = {x}

/--
A special case of `DiHypergraph` where all hyperedges have a source containing exactly one vertex
or have a destination containing exactly one vertex.
-/
def IsBFHypergraph (Dₕ : DiHypergraph α) :=
  ∀ e ∈ E(Dₕ), (∃ x ∈ V(Dₕ), e.1 = {x}) ∨ (∃ x ∈ V(Dₕ), e.2 = {x})

/--
Many results related to directed hypergraphs assume that hyperedge sides are nonempty. We define
a hypergraph with nonempty hyperedge sources/destinations as a special case of dihypergraph, which
we call "non-endless".
-/
def IsNonEndless (Dₕ : DiHypergraph α) := ∀ e ∈ E(Dₕ), e.1.Nonempty ∧ e.2.Nonempty

end SpecialCase

/-! Adjacency -/

section Adjacency

/--
Predicate for vertex adjacency. Two vertices `x` and `y` are adjacent if there is some edge
`e ∈ E(H)` where `x` is in the tail of `e  and `y` is in the head of `e`.

Note that we do not need to explicitly check that x, y ∈ V(H) here because a vertex that is not in
the vertex set cannot be incident to any edge.
-/
def Adj (Dₕ : DiHypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(Dₕ), x ∈ e.1 ∧ y ∈ e.2

/--
Predicate for edge adjacency. Analogous to `DiHypergraph.Adj`, edges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is in the head of e and in the tail of f.
-/
def EAdj (Dₕ : DiHypergraph α) (e : (Set α × Set α)) (f : (Set α × Set α)) : Prop :=
  e ∈ E(Dₕ) ∧ f ∈ E(Dₕ) ∧ ∃ x, x ∈ e.2 ∧ x ∈ f.1

end Adjacency

/-! ## Isolated vertices -/

section Isolated

/--
Predicate to determine if a vertex is isolated, meaning that it is not incident to any edges..
-/
def IsIsolated (Dₕ : DiHypergraph α) (x : α) : Prop := ∀ e ∈ E(Dₕ), x ∉ e.1 ∧ x ∉ e.2

end Isolated

/-! ## Empty Dihypergraphs -/

section Empty

/--
Predicate to determine if a dihypergraph is empty
-/
def IsEmpty (Dₕ : DiHypergraph α) : Prop := V(Dₕ) = ∅ ∧ E(Dₕ) = ∅

/--
Predicate to determine if a dihypergraph is nonempty
-/
def IsNonempty (Dₕ : DiHypergraph α) : Prop := (∃ x, x ∈ V(Dₕ)) ∨ (∃ e, e ∈ E(Dₕ))

/--
The empty dihypergraph of type α
-/
@[simps]
def emptyDiHypergraph (α : Type*) : DiHypergraph α where
  vertexSet := ∅
  edgeSet := ∅
  edge_src_dst_isSubset_vertexSet' := by
    intro e he
    exact False.elim he

lemma isBHypergraph_emptyDiHypergraph : (emptyDiHypergraph α).IsBHypergraph := by
  unfold IsBHypergraph
  simp

lemma isFHypergraph_emptyDiHypergraph : (emptyDiHypergraph α).IsFHypergraph := by
  unfold IsFHypergraph
  simp

lemma isBFHypergraph_emptyDiHypergraph : (emptyDiHypergraph α).IsBFHypergraph := by
  unfold IsBFHypergraph
  simp

lemma isNonEndless_emptyDiHypergraph : (emptyDiHypergraph α).IsNonEndless := by
  unfold IsNonEndless
  simp

end Empty

end DiHypergraph
