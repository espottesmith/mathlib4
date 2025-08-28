/-
Copyright (c) 2025 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith, Bhavik Mehta
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# Neighborhood hypergraphs and vertex/hyperedge neighbors

TODO
-/

open Set

variable {α β γ : Type*} {x y : α} {e e' f g : Set α} {l : Set (Set α)}

namespace Hypergraph

variable {H : Hypergraph α}

/--
The neighbourhood of a subset `v` is the hypergraph formed by those hyperedges in `H` which contain
`v`, after having `v` removed from them.

Viewing a simple graph as a 2-uniform hypergraph and a set as a 1-uniform hypergraph, this
recovers the simple graph notion of neighbourhood.
-/
@[simps]
def neighborhood (H : Hypergraph α) (v : Set α) : Hypergraph α where
  vertexSet := V(H) \ v
  hyperedgeSet := {e | e ∈ E(H) ∧ v ⊆ e}.image (· \ v)
  hyperedge_isSubset_vertexSet' := by
    simp
    rintro _ e he hve rfl
    refine diff_subset_diff_left ?_
    exact Membership.mem.subset_vertexSet he

lemma mem_neighborhood {v : Set α} :
  e ∈ E(H.neighborhood v) ↔ ∃ e' ∈ E(H), v ⊆ e' ∧ e' \ v = e := by
  simp
  grind

/-- An alternate description of the edges of the neighbourhood hypergraph. -/
lemma mem_neighborhood' {v e : Set α} :
    e ∈ E(H.neighborhood v) ↔ e ∪ v ∈ E(H) ∧ Disjoint e v := by
  rw [mem_neighborhood]
  constructor
  · rintro ⟨e, he, he', rfl⟩
    rw [diff_union_of_subset he']
    exact ⟨he, Set.disjoint_sdiff_left⟩
  · rintro ⟨hev, hev'⟩
    use e ∪ v
    constructor
    · exact hev
    · constructor
      · exact Set.subset_union_right
      · have h : (e ∩ v) ⊆ ∅ := by exact Set.disjoint_iff.mp hev'
        exact Set.union_diff_cancel_right h

lemma card_neighbourhood {v : Set α} :
  E(H.neighborhood v).encard = {e ∈ E(H) | v ⊆ e}.encard := by
  simp
  refine InjOn.encard_image ?_
  unfold InjOn
  intro a₁ h0
  simp
  intro a₂ h1 h2 h3
  have h' : v ∪ (a₁ \ v) = v ∪ (a₂ \ v) := by grind
  rw [Set.union_diff_cancel, Set.union_diff_cancel] at h'
  · exact h'
  · exact h2
  exact h0.2

-- @[simp] lemma neighbourhood_isEmpty_iff [DecidableEq α] {v : Finset α} :
--     (G.neighbourhood v).IsEmpty ↔ ∀ e ∈ G, ¬ v ⊆ e := by
--   simp [IsEmpty, filter_eq_empty_iff]

-- @[simp] lemma neighbourhood_isNonempty_iff [DecidableEq α] {v : Finset α} :
--     (G.neighbourhood v).IsNonempty ↔ ∃ e ∈ G, v ⊆ e := by
--   simp [← coe_nonempty_iff, filter_nonempty_iff]

/--
The `neighbors` of a vertex `x` in a hypergraph `H` are those vertices that share a hyperedge with
`x`.

We define this based on the `neighborhood` construction; the hyperedge set of the neighborhood
hypergraph (`H.neighborhood {x}`) contains all neighbors of `x`.
-/
def neighbors (H : Hypergraph α) (x : α) : Set α := ⋃₀ E(H.neighborhood {x})

/--
The `neighbors` of a hyperedge `e` are those hyperedges that share at least one vertex with `e`,
i.e., hyperedges that are "hyperedge adjacent" (using `Hyperedge.EAdj`) with `e`.
-/
def hyperedge_neighbors (H : Hypergraph α) (e : Set α) : Set (Set α) := {e' | H.EAdj e e'}

-- TODO: lemmas

end Hypergraph
