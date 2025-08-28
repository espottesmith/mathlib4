/-
Copyright (c) 2025 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith, Bhavik Mehta
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BoolIndicator
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# Graph ↔ Hypergraph conversions

TODO: this
-/

open Set

variable {α β : Type*} {x y : α} {e e' : β} {he he' : Set α} {se se' : Sym2 α} {p p' : α × α}
variable {G : Graph α β} {H : Hypergraph α} {S : SimpleGraph α}

namespace Hypergraph

-- Graph -> Hypergraph coersion
-- Can't be Coe (I believe) because β type is totally unspecified
instance : CoeOut (Graph α β) (Hypergraph α) where
  coe G := Hypergraph.mk G.vertexSet { {x | G.Inc e' x} | e' ∈ G.edgeSet} (
    by
    intro he
    simp
    intro e h h'
    have hv : ∀ x ∈ he, x ∈ G.vertexSet := by
      intro x hx
      have hx' : G.Inc e x := by
        have hx'' : x ∈ {y | G.Inc e y} := by grind
        exact hx''
      exact Graph.Inc.vertex_mem hx'
    exact hv
  )

-- SimpleGraph -> Hypergraph coersion
instance [DecidableEq α] : Coe (SimpleGraph α) (Hypergraph α) where
  coe S := Hypergraph.mk
    {x | ∃ se ∈ S.edgeSet, Sym2.Mem x se}
    (S.edgeSet.image (fun se ↦ (se.toFinset).toSet))
    (
      by
      intro e hhe
      simp
      have hhse : ∃ se, se ∈ S.edgeSet ∧ (fun se' ↦ (se'.toFinset).toSet) se = e := by exact hhe
      obtain ⟨se, hse⟩ := hhse
      have hh : ∀ x ∈ e, x ∈ se.toFinset := by
        intro x hx
        grind
      have hh' : ∀ x ∈ e, x ∈ se := by
        intro x' hx'
        exact Sym2.mem_toFinset.mp (hh x' hx')
      refine subset_setOf.mpr ?_
      intro x'' hx''
      use se
      constructor
      · exact hse.1
      · exact hh' x'' hx''
    )

-- Hypergraph -> Graph (clique graph) coersion
instance : Coe (Hypergraph α) (Graph α (Sym2 α)) where
  coe H := Graph.mk
    V(H)
    (fun se x y ↦ se ∈ ⋃₀ { {se | se ∈ e.sym2} | e ∈ E(H)} ∧ Sym2.mk (x, y) = se) -- Awkward...
    (⋃₀ { {se | se ∈ e.sym2} | e ∈ E(H)})
    (by
      simp
      unfold Symmetric
      intro _ _ _ _ _ _ hxy
      rw [Sym2.eq_swap]
      exact hxy
    )
    (by
      simp
      intro se v w x y e he hse hvw e' he' hse' hxy
      have heq : (v = x ∧ w = y) ∨ (v = y ∧ w = x) := by
        refine Sym2.eq_iff.mp ?_
        apply Eq.trans hvw (hxy.symm)
      grind
    )
    (by -- Works, but super repetitive. Refactor?
      intro se
      let Q := {x | ∃ e ∈ E(H), {se | se ∈ e.sym2} = x}
      constructor
      · intro hse
        simp
        constructor
        · have h' : ∃ t ∈ Q, se ∈ t := by exact Set.mem_sUnion.mp hse
          obtain ⟨t, ht⟩ := h'
          have ht' : ∃ e ∈ E(H), {se | se ∈ e.sym2} = t := by exact ht.1
          obtain ⟨e, he⟩ := ht'
          use e
          constructor
          · exact he.1
          · rw[he.2.symm] at ht
            exact ht.2
        · use (Quot.out se).1, (Quot.out se).2
          simp
      · intro hxy
        simp
        obtain ⟨x, y, hxy'⟩ := hxy
        have h' : ∃ t ∈ Q, se ∈ t := by exact Set.mem_sUnion.mp hxy'.1
        obtain ⟨t, ht⟩ := h'
        have ht' : ∃ e ∈ E(H), {se | se ∈ e.sym2} = t := by exact ht.1
        obtain ⟨e, he⟩ := ht'
        use e
        constructor
        · exact he.1
        · rw[he.2.symm] at ht
          exact ht.2
    )
    (by
      intro se x y hfun
      let Q := {x | ∃ e ∈ E(H), {se | se ∈ e.sym2} = x}
      have h: ∃ e ∈ E(H), x ∈ e := by
        have h' : ∃ e ∈ E(H), se ∈ e.sym2 := by
          have h'' : ∃ t ∈ Q, se ∈ t := by exact Set.mem_sUnion.mp hfun.1
          obtain ⟨t, ht⟩ := h''
          have ht' : ∃ e ∈ E(H), {se | se ∈ e.sym2} = t := by exact ht.1
          obtain ⟨e, he⟩ := ht'
          use e
          constructor
          · exact he.1
          · rw[he.2.symm] at ht
            exact ht.2
        obtain ⟨e, he⟩ := h'
        use e
        constructor
        · exact he.1
        · have hsub : ↑se ⊆ e := by exact Set.mem_sym2_iff_subset.mp he.2
          have hmem : x ∈ (se : Set α) := by
            refine SetLike.mem_coe.mpr ?_
            refine Sym2.mem_iff_exists.mpr ?_
            use y
            rw [hfun.2]
          grind
      obtain ⟨e, he⟩ := h
      apply H.hyperedge_isSubset_vertexSet' he.1
      exact he.2
    )

-- Hypergraph -> SimpleGraph coersion
instance : Coe (Hypergraph α) (SimpleGraph α) where
  coe H := SimpleGraph.mk
    (fun x y ↦ x ≠ y ∧ (∃ e ∈ E(H), x ∈ e ∧ y ∈ e))
    (
      by
        unfold Symmetric
        intro x y hxy
        constructor
        · exact Ne.symm hxy.1
        · obtain ⟨e, he⟩ := hxy.2
          use e
          constructor
          · exact he.1
          · exact And.symm he.2
    )
    (
      by
      unfold Irreflexive
      simp
    )

-- Hypergraph -> Bipartite SimpleGraph coersion
def toBipartiteSimpleGraph (H : Hypergraph α) : SimpleGraph (Set α) :=
  SimpleGraph.mk
  (
    fun he he' ↦
      (he ≠ he' ∧ he ∈ E(H) ∧ ∃ x ∈ he, he' = {x}) ∨ (he' ≠ he ∧ he' ∈ E(H) ∧ ∃ x ∈ he', he = {x})
  )
  (
    by
      unfold Symmetric
      intro he he' hadj
      cases hadj with
      | inl hleft => (
        right
        exact hleft
      )
      | inr hright => (
        left
        exact hright
      )
  )
  (by
    unfold Irreflexive
    intro he
    simp
  )

end Hypergraph
