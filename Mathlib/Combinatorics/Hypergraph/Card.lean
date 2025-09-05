/-
Copyright (c) 2025 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith, Bhavik Mehta
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# Hypergraph cardinality

This module defines notions of cardinality for undirected hypergraphs, as well as special classes
of hypergraphs defined by some pattern of cardinality (e.g., *`k`-uniform* and *`d`-regular*
hypergraphs; see below).

## Main definitions

For `H : Hypergraph α`:

* `H.order` denotes the number of vertices in `H`
* `H.size` denotes the number of edges in `H`
* `H.vertexDegree x` denotes the cardinality of the star of a vertex `x : α`
* `H.edgeDegree e` denotes the cardinality of the edge `e : Set α`
* `H.IsKUniform` states that a hypergraph `H` is *`k`-uniform*, meaning that all edges in the edge
    set of `H` have degree (or, equivalently, cardinality) `k`
* `H.IsDRegular` states that a hypergraph `H` is *`d`-regular*, meaning that all vertices in the
    vertex set of `H` have degree `d`

## Implementation details

TODO

-/

open Set

variable {α β : Type*} {x y : α} {e f g h : Set α} {l : Set (Set α)}

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Undirected Hypergraph Cardinality -/

/--
The *order* of a hypergraph `H` is defined as the number of vertices contained in `H`
-/
noncomputable def order (H : Hypergraph α) : ENat := Set.encard V(H)

/--
The *size* of a hypergraph `H` is defined as the number of edges contained in `H`
-/
noncomputable def size (H : Hypergraph α) : ENat := Set.encard E(H)

/--
The *degree* of a vertex in a hypergraph `H`.

A vertex `x` has degree `n`, where `n` is the number of edges in `E(H)` that `x` is incident
on.
-/
noncomputable def vertexDegree (H : Hypergraph α) (x : α) : ENat := Set.encard (H.star x)

/--
The set of vertex *degrees* of a hypergraph `H`.
-/
noncomputable def vertexDegrees (H : Hypergraph α) : Set ENat := {H.vertexDegree x | x ∈ V(H)}

/--
The *degree* of a edge in hypergraph `H`.

A edge `e` has degree `n`, where `n` is the number of vertices in `V(H)` that are incident to
`e`.
-/
noncomputable def edgeDegree (e : Set α) : ENat := Set.encard e

/--
The set of edge *degrees* of a hypergraph `H`.
-/
noncomputable def edgeDegrees (H : Hypergraph α) : Set ENat := {edgeDegree e | e ∈ E(H)}

/--
Predicate to determine if a hypergraph is *`k`-uniform*.

In a `k`-uniform hypergraph `H`, all edges `e ∈ E(H)` have the same cardinality, i.e.,
`|e| = k`.
-/
def IsKUniform (H : Hypergraph α) (k : ENat) : Prop := ∀ e ∈ E(H), edgeDegree e = k

variable {k : ENat}

lemma isKUniform_iff_forall : H.IsKUniform k ↔ ∀ ⦃e⦄, e ∈ E(H) → Set.encard e = k := Iff.rfl

@[simp]
lemma isKUniform_iff_forall_edgeDegrees : H.IsKUniform k ↔ ∀ n ∈ H.edgeDegrees, n = k := by
  unfold IsKUniform
  constructor
  · intro hek n hn
    unfold edgeDegrees at hn
    have hn' : ∃ e ∈ E(H), edgeDegree e = n := by exact hn
    obtain ⟨e, he⟩ := hn'
    grind
  · intro hnk e heE
    unfold edgeDegrees at hnk
    have heD : (edgeDegree e) ∈ {x | ∃ e ∈ E(H), edgeDegree e = x} := by
      simp
      use e
    exact hnk (edgeDegree e) heD

@[simp]
lemma IsUniform.card_of_mem (hH : H.IsKUniform k) (he : e ∈ E(H)) : Set.encard e = k := by
  unfold IsKUniform at hH
  unfold edgeDegree at hH
  grind

lemma IsEmpty.isKUniform (hH : H.IsEmpty) : H.IsKUniform k := by
  unfold IsKUniform
  unfold IsEmpty at hH
  grind

lemma isKUniform_right_unique {k k' : ENat} (hH : E(H).Nonempty)
  (hk : H.IsKUniform k) (hk' : H.IsKUniform k') : k = k' := by
  obtain ⟨e, he⟩ := hH
  unfold IsKUniform at *
  have hek : edgeDegree e = k := by apply hk e he
  have hek' : edgeDegree e = k' := by apply hk' e he
  rw [hek.symm, hek'.symm]

lemma isKUniform_iff_eq_of_isNonempty {k k' : ENat} (hH : E(H).Nonempty) (hHk : H.IsKUniform k) :
    H.IsKUniform k' ↔ k' = k := ⟨(.symm <| isKUniform_right_unique hH hHk ·), (· ▸ hHk)⟩

@[simp] lemma emptyHypergraph_isKUniform : (emptyHypergraph α).IsKUniform k := by
  apply IsEmpty.isKUniform isEmpty_empty_hypergraph

lemma trivial_isKUniform : (trivialHypergraph f).IsKUniform k := by simp [IsKUniform]

lemma IsKUniform.le_card_verts (hE : E(H).Nonempty) (hH : H.IsKUniform k) : k ≤ H.order := by
  obtain ⟨e, he⟩ := hE
  unfold IsKUniform at hH
  unfold order
  rw [←hH e]
  · apply encard_le_encard (H.edge_isSubset_vertexSet he)
  · exact he

/--
Predicate to determine if a hypergraph is *`d`-regular*.

In a `d`-regular hypergraph `H`, all vertices `v ∈ V(H)` have the same degree, i.e., all vertices
are incident to `d` edges.
-/
def IsDRegular (H : Hypergraph α) (d : ENat) : Prop := ∀ x ∈ V(H), H.vertexDegree x = d

variable {d : ENat}

end Hypergraph
