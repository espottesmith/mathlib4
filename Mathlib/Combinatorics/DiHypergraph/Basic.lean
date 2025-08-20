/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Hypergraph.Basic

open Set
open Hypergraph

variable {α : Type*} {x y z : α} {d d' s s' : Set α} {e f g : (Set α) × (Set α)}

@[ext]
structure DiHypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The hyperedge set. Each hyperedge is a pair (s, d), where s ⊆ vertexSet and d ⊆ vertexSet -/
  hyperedgeSet : Set ((Set α) × (Set α))
  /-- All hyperedges must be subsets of the vertex set -/
  hyperedge_src_dst_isSubset_vertexSet : ∀ ⦃e⦄, e ∈ hyperedgeSet → e.1 ⊆ vertexSet ∧ e.2 ⊆ vertexSet

@[ext]
structure BHypergraph (α : Type*) extends DiHypergraph α where
  hyperedge_dst_one_vertex : ∀ e ∈ hyperedgeSet, ∃ x ∈ vertexSet, e.2 = {x}

@[ext]
structure FHypergraph (α : Type*) extends DiHypergraph α where
  hyperedge_src_one_vertex : ∀ e ∈ hyperedgeSet, ∃ x ∈ vertexSet, e.1 = {x}

@[ext]
structure BFHypergraph (α : Type*) extends DiHypergraph α where
  hyperedge_src_one_vertex_or_dst_one_vertex :
    ∀ e ∈ hyperedgeSet, ∃ x ∈ vertexSet, e.1 = {x} ∨ e.2 = {x}

@[ext]
structure NonEndlessDiHypergraph (α : Type*) extends DiHypergraph α where
  hyperedge_src_dst_nonempty : ∀ e ∈ hyperedgeSet, e.1.Nonempty ∧ e.2.Nonempty

namespace DiHypergraph

-- TODO: you are here

end DiHypergraph
