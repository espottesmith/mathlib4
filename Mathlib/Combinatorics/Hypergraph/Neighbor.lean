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

/--
The neighbourhood of a subset `v` is the hypergraph formed by those edges in `G` which contain `v`,
after having `v` removed from them.
Viewing a simple graph as a 2-uniform hypergraph and a set as a 1-uniform hypergraph, this
recovers the simple graph notion of neighbourhood.
-/
@[simps]
def neighbourhood [DecidableEq α] (G : Hypergraph α) (v : Finset α) : Hypergraph α where
  verts := G.verts \ v
  edges := (G.edges.filter fun e ↦ v ⊆ e).image (· \ v)
  edge_subset_verts' := by
    simp only [Finset.mem_image, mem_filter, mem_coe, forall_exists_index, and_imp]
    rintro _ e he hve rfl
    exact sdiff_subset_sdiff_left he.subset_verts

lemma mem_neighbourhood [DecidableEq α] {v e : Finset α} :
    e ∈ G.neighbourhood v ↔ ∃ a ∈ G, v ⊆ a ∧ a \ v = e := by
  rw [← mem_coe]; simp [coe_neighbourhood, and_assoc]

/-- An alternate description of the edges of the neighbourhood hypergraph. -/
lemma mem_neighbourhood' [DecidableEq α] {v e : Finset α} :
    e ∈ G.neighbourhood v ↔ e ∪ v ∈ G ∧ Disjoint e v := by
  rw [mem_neighbourhood]
  constructor
  · rintro ⟨e, he, he', rfl⟩
    rw [sdiff_union_of_subset he']
    exact ⟨he, sdiff_disjoint⟩
  · rintro ⟨hev, hev'⟩
    exact ⟨_, hev, by simp, union_sdiff_cancel_right hev'⟩

lemma card_neighbourhood [DecidableEq α] {v : Finset α} :
    #(G.neighbourhood v).edges = #{e ∈ G | v ⊆ e} := by
  rw [coe_neighbourhood, card_image_of_injOn ((superset_injOn_sdiff _).mono (by simp))]
