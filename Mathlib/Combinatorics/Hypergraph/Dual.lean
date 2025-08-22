import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Hypergraph.Basic

open Set

variable {α β : Type*} {x y : α} {e e' e'' : Set α} {l : Set (Set α)}
variable {E E' : β} {X Y : Set β}

namespace Hypergraph

variable {H : Hypergraph α}

@[simps]
def dual (H : Hypergraph α) (f : Set α → β) : Hypergraph β where
  vertexSet := E(H).image f
  hyperedgeSet := V(H).image fun x ↦ (H.star x).image f
  hyperedge_isSubset_vertexSet' e he := by
    simp only [Set.mem_image] at he
    obtain ⟨v, hv, h⟩ := he
    rw [← h]
    refine image_mono ?_
    exact sep_subset E(H) fun e ↦ v ∈ e

@[simps]
def dual' (H : Hypergraph α) : Hypergraph (Set α) where
  vertexSet := E(H)
  hyperedgeSet := V(H).image fun x ↦ H.star x
  hyperedge_isSubset_vertexSet' e he := by
    simp only [Set.mem_image] at he
    obtain ⟨v, hv, h⟩ := he
    rw [← h]
    exact sep_subset E(H) fun e ↦ v ∈ e

scoped notation H "*" f => Hypergraph.dual H f

scoped notation H "*'" => Hypergraph.dual H

@[simp]
lemma mem_dual {f : Set α → β} {H : Hypergraph α} :
    X ∈ E(H.dual f) ↔ ∃ x ∈ V(H), (H.star x).image f = X := by apply Set.mem_image

@[simp]
lemma mem_dual' {E : Set (Set α)} :
    E ∈ E(H.dual') ↔ ∃ x ∈ V(H), H.star x = E := by apply Set.mem_image

-- TODO: (H*)* = H
-- Neither definition seems amenable to this proof
-- Possible case for Hypergraph α β instead of Hypergraph α

end Hypergraph
