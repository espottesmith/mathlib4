/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
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

*Graphs* are a special case of hypergraphs; specifically, a graph is a 2-uniform hypergraph. This
file defines some conversions from graph types (`SimpleGraph α`, `Graph α β`) to `Hypergraph α` and
*vice versa*.

## Main definitions

`Coe` instances are provided for:
* `(SimpleGraph α) → (Hypergraph α)`
* `(Hypergraph α) → (Graph α (Sym2 α))`, i.e., the conversion from a hypergraph to its associated
  *two-section graph* (also called a *representing graph*, *primal graph*, *Gaifman graph*, or
  *clique graph*). The two-section graph of a hypergraph `H` contains edges for every pair of
  vertices connected by some hyperedge in `H`. Note that the edge type is `Sym2 α`; an edge is
  identified exactly by the (unordered) pair of vertices connected by the edge.
* `(Hypergraph α) → (SimpleGraph α)`. This is similar to the (Hypergraph α) → (Graph α (Sym2 α))`
  conversion above, except that edges are irreflexive, i.e., there can be no edge from `x : α` to
  `x`. This means that loop hyperedges (those containing one vertex) are implicitly erased in this
  conversion.

A `CoeOut` instance is also provided for `(Graph α β) → (Hypergraph α)`. This must be a `CoeOut`
instance, rather than a `Coe` instance, as the `β` type is unspecified in the target. Further, note
that `Graph` defines *multigraphs*, which can have repeated edges. `Hypergraph α` does not allow
duplicate hyperedges, so, where present, these are reduced to a single hyperedge.

Finally, we define the bipartite representation of a hypergraph:

  `toBipartiteSimpleGraph (H : Hypergraph α) : SimpleGraph (Set α)`

## Implementation details

Vertices in the `toBipartiteSimpleGraph` `SimpleGraph` are of type `Set α` and are of two different
natures: single-vertex sets ("vertex vertices", e.g., `{x}`), which represent the vertices of `H`,
and multi-vertex sets ("hyperedge vertices"), which represent the (irreflexive, i.e., non-loop)
hyperedges of `H`. Adjacency is defined such that a "vertex vertex" is adjacent to a hyperedge
vertex if and only if the vertex `x ∈ V(H)` associated with the vertex vertex (`{x}`) is incident on
the hyperedge associated with the hyperedge vertex; i.e., `x ∈ he`. Because this is a bipartite
representation, vertex vertices are never adjacent to vertex vertices, and hyperedge vertices are
never adjacent to hyperedge vertices.
-/

open Set

variable {α β : Type*} {x y : α} {e e' : β} {he he' : Set α} {se se' : Sym2 α} {p p' : α × α}
variable {G : Graph α β} {H : Hypergraph α} {S : SimpleGraph α}

namespace Hypergraph

/--
Coersion from a Graph (`G : Graph α β`) to a Hypergraph (`H : Hypergraph α`). Because the `β` type
is totally unspecified in the output (hypergraph) type, this can only be a `CoeOut` instance and not
`Coe`.

A graph is a special case of a hypergraph; specifically, graphs are 2-uniform hypergraphs.
-/
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

/--
Coersion from a `SimpleGraph` to a `Hypergraph`.

A simple graph is a 2-uniform hypergraph with the added property that all (hyper)edges are not loops
(i.e., `∀ he : Set α ∈ E(H), |he| > 1` ).
-/
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

/--
Coersion from a hypergraph `H` to a graph (`G : Graph α (Sym2 α)`), where `G` is the *clique graph*
of `H`. Two vertices `x` and `y : α` are adjacent in `G` (i.e., there is an edge connecting `x` and
`y`) if and only if they are adjacent in `H` (i.e., there exists a hyperedge in `H` containing both
`x` and `y`).

Edges in the output graph are represented by unordered pairs (`Sym2 α`) to facilitate the adjacency
definition and the symmetry requirement of `Graph` edges.

NOTE: the proofs of `G.edge_mem_iff_exists_isLink` and `G.left_mem_of_isLink` are rather long and,
in places, repetitive. A refactor would be desirable.
-/
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

/--
Coersion from a hypergraph to a simple graph. Because edges in a simple graph must be irreflexive,
i.e., there can be no edge from `x : α` to `x`, loop hyperedges (those containing one vertex) are
implicitly erased in this conversion.
-/
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

/--
The bipartite graph representation of a hypergraph.
-/
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

-- TODO: prove that the resulting graph is actually bipartite

end Hypergraph
