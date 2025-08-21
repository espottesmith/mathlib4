import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Hypergraph.Basic

open Set

variable {α : Type*} {x y : α} {e f g h : Set α} {l : Set (Set α)}

namespace Hypergraph

/-! ## Subhypergraphs, Partial Hypergraphs, and Section Hypergraphs -/

/--
Given a subset of the vertex set `g ⊆ V(H)` of a hypergraph `H`, the
*subhypergraph* `Hg` has `V(Hg) = g ∩ V(H)`, and `E(Hg)` is the subset of `E(H)` for which all
incident vertices are included in `g`.
-/
def subHypergraph (H : Hypergraph α) (g : Set α) :=
  Hypergraph.mk
  (g ∩ V(H))
  {e | e ∈ E(H) ∧ e ⊆ g}
  (by
    intro f hf
    have h0 : f ∈ {e | e ∈ E(H) ∧ e ⊆ g} → f ∈ E(H) ∧ f ⊆ g := by apply Set.mem_sep_iff.mp
    have h1 : f ∈ E(H) ∧ f ⊆ g → f ⊆ V(H) ∧ f ⊆ g := by
      intro q
      have h1' : f ∈ E(H) := by exact q.left
      have h1'' : f ⊆ V(H) := by apply H.hyperedge_isSubset_vertexSet h1'
      constructor
      exact h1''
      exact q.right
    have h2 : f ⊆ V(H) ∧ f ⊆ g → f ⊆ V(H) ∩ g := by exact Set.subset_inter_iff.mpr
    apply h0 at hf
    apply h1 at hf
    apply h2 at hf
    rw [Set.inter_comm g V(H)]
    exact hf
  )

/--
Given a subset of the vertex set `g ⊆ V(H)` of a hypergraph `H`,the *induced subhypergraph*
`Hg'` has `V(Hg') = g ∩ V(H)` and `E(Hg')` contains the subset of each hyperedge that intersects
with `g`.
-/
def inducedSubHypergraph (H : Hypergraph α) (g : Set α) :=
  Hypergraph.mk
  (g ∩ V(H))
  { { y | y ∈ (g ∩ e)} | e ∈ E(H) }
  (by
    intro q hq
    have h0 : ∃ e ∈ E(H), {y | y ∈ g ∩ e} = q := by exact hq
    obtain ⟨e, he⟩ := h0
    have h1 : e ⊆ V(H) := by exact H.hyperedge_isSubset_vertexSet he.left
    have h2 : q = {y | y ∈ g ∩ e} := by apply Eq.symm he.2
    have h3 : g ∩ e ⊆ g ∩ V(H) := by exact inter_subset_inter (fun ⦃a⦄ a ↦ a) h1
    exact Eq.trans_subset h2 h3
  )

/--
Given a subset of the hyperedge set `E(H)` of a hypergraph `H` (`l : Set (Set α)`), the
*partial hypergraph* `Hˡ` has `E(Hˡ) = l ∩ E(H)` and `V(Hˡ)` is the subset of `V(H)` which is
incident on at least one hyperedge in `E(Hˡ)`.
-/
def partialHypergraph (H : Hypergraph α) (l : Set (Set α)) : Hypergraph α where
  vertexSet := {x | ∃ e ∈ l, e ∈ E(H) ∧ x ∈ e}
  hyperedgeSet := l ∩ E(H)
  hyperedge_isSubset_vertexSet q hq _ hx := ⟨q, hq.1, hq.2, hx⟩

end Hypergraph
