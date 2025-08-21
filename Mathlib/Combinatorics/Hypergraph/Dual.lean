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
  hyperedgeSet := V(H).image fun x ↦ {e ∈ E(H) | x ∈ e}.image f
  hyperedge_isSubset_vertexSet' e he := by
    simp only [Set.mem_image] at he
    obtain ⟨v, hv, h⟩ := he
    rw [← h]
    refine image_mono ?_
    exact sep_subset E(H) fun x ↦ v ∈ x

scoped notation H "*" f => Hypergraph.dual H f

@[simp]
lemma mem_dual {f : Set α → β} {H : Hypergraph α} :
    X ∈ E(H.dual f) ↔ ∃ x ∈ V(H), {e ∈ E(H) | x ∈ e}.image f = X := by apply Set.mem_image

@[simp]
lemma dual_dual {H : Hypergraph α} {f : Set α → β} {f' : Set β → α} {e : Set α}
  (h : ∀ x ∈ V(H), f' ((H.star x).image f) = x)
  (hf : f.Injective)
  : (H.dual f).dual f' = H := by
    expose_names
    refine Hypergraph.ext ?_ ?_
    · simp
      grind
    · refine ext ?_
      intro e
      let E := (f e)
      have h' : e ∈ E(H) ↔ E ∈ V(H*f) := by
        simp
        constructor
        · intro hmem
          use e
        · intro hfe
          obtain ⟨e', he⟩ := hfe
          have he' : E = f e' := by exact Eq.symm he.2
          have hee : e = e' := by exact hf he'
          grind
      have h'' : E ∈ V(H*f) ↔ e ∈ E((H*f)*f') := by
        constructor
        · intro hmemE
          sorry
        · intro hmeme
          sorry
      exact Iff.trans (id (Iff.symm h'')) (id (Iff.symm h'))

end Hypergraph
