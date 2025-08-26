/-
Copyright (c) 2025 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith, Bhavik Mehta
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-!
# Undirected hypergraphs

An *undirected hypergraph* (here abbreviated as *hypergraph*) `H` is a generalization of a graph
(see `Mathlib.Combinatorics.Graph` or `Mathlib.Combinatorics.SimpleGraph`) and consists of a set of
*vertices*, usually denoted `V` or `V(H)`, and a set of *hyperedges*, denoted `E` or `E(H)`. In
contrast with a graph, where edges are unordered pairs of vertices, in hypergraphs, hyperedges are
(unordered) sets of vertices; i.e., they are subsets of the vertex set `V`.

A hypergraph where `V = ∅` and `E = ∅` is *empty*. A hypergraph with a nonempty
vertex set (`V ≠ ∅`) and empty hyperedge set is *trivial*.

If a hyperedge `e` contains only one vertex (i.e., `|e| = 1`), then it is a *loop*.

This module defines `Hypergraph α` for a vertex type `α` (hyperedges are defined as `Set (Set α)`).

## Main definitions

For `H : Hypergraph α`:

* `V(H)` denotes the vertex set of `H` as a term in `Set α`.
* `E(H)` denotes the hyperedge set of `H` as a term in `Set (Set α)`. Hyperedges must be subsets of
    `V(H)`.
* `H.Adj x y` means that there exists some hyperedge containing both `x` and `y` (or, in other
    words, `x` and `y` are incident on some shared hyperedge `e`).
* `H.EAdj e f` means that there exists some vertex that is incident on both hyperedge `e` and
    hyperedge `f : Set α`.

## Implementation details

This implementation is heavily inspired by Peter Nelson and Jun Kwon's `Graph` implementation,
which was in turn inspired by `Matroid`.

Paraphrasing `Mathlib.Combinatorics.Graph.Basic`:
"The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : Set α` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation."

Because `hyperedgeSet` is a `Set (Set α)`, rather than a multiset, here we are assuming that
all hypergraphs are *without repeated hyperedge*.

## Acknowledgments

Credit to Shreyas Srinivas, GitHub user @NotWearingPants ("Snir" on the Lean Zulip), Ammar
Husain, Aaron Liu, and Tristan Figueroa-Reid for patient guidance and useful feedback on this
implementation.
-/

open Set

variable {α β γ : Type*} {x y : α} {e e' f g : Set α} {l : Set (Set α)}

/--
An undirected hypergraph with vertices of type `α` and hyperedges of type `Set α`,
as described by vertex and hyperedge sets `vertexSet : Set α` and `hyperedgeSet : Set (Set α)`.

The requirement `hyperedge_isSubset_vertexSet` ensures that all vertices in hyperedges are part of
`vertexSet`, i.e., all hyperedges are subsets of the `vertexSet`.
-/
@[ext]
structure Hypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The hyperedge set -/
  hyperedgeSet : Set (Set α)
  /-- All hyperedges must be subsets of the vertex set -/
  hyperedge_isSubset_vertexSet' : ∀ ⦃e⦄, e ∈ hyperedgeSet → e ⊆ vertexSet

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `hyperedgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.hyperedgeSet H


/-! ## Vertex-Hyperedge Incidence -/

@[simp]
lemma hyperedge_isSubset_vertexSet (he : e ∈ E(H)) : e ⊆ V(H) :=
  H.hyperedge_isSubset_vertexSet' he

lemma _root_.Membership.mem.subset_vertexSet (he : e ∈ E(H)) : e ⊆ V(H) :=
  H.hyperedge_isSubset_vertexSet he

lemma hyperedgeSet_subset_powerset_vertexSet {H : Hypergraph α} : E(H) ⊆ V(H).powerset := by
  intro e (he : e ∈ E(H))
  simpa using he.subset_vertexSet

lemma mem_vertexSet_of_mem_hyperedgeSet (he : e ∈ E(H)) (hx : x ∈ e) : x ∈ V(H) := by
  have h1 : e ⊆ V(H) := by apply H.hyperedge_isSubset_vertexSet he
  apply Set.mem_of_subset_of_mem h1 hx

/--
If edges `e` and `e'` have the same vertices from `G`, then they have all the same vertices.
This could be phrased as `e = e'`, but this formulation is more useful in combination with the `ext`
tactic.
-/
lemma forall_of_forall_verts (he : e ∈ E(H)) (he' : e' ∈ E(H))
    (h : ∀ x ∈ V(H), x ∈ e ↔ x ∈ e') : ∀ x, x ∈ e ↔ x ∈ e' :=
  fun x ↦ ⟨fun y ↦ (h x (he.subset_vertexSet y)).1 y,
  fun y ↦ (h x (he'.subset_vertexSet y)).2 y⟩

lemma sUnion_hyperedgeSet_subset_vertexSet : ⋃₀ E(H) ⊆ V(H) := by
  refine subset_powerset_iff.mp ?_
  exact hyperedgeSet_subset_powerset_vertexSet

/-! ## Vertex and Hyperedge Adjacency -/

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some
hyperedge `e ∈ E(H)` where `x` and `y` are both incident on `e`.

Note that we do not need to explicitly check that x, y ∈ V(H) here because a vertex that is not in
the vertex set cannot be incident on any hyperedge.
-/
def Adj (H : Hypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(H), x ∈ e ∧ y ∈ e

lemma Adj.symm (h : H.Adj x y) : H.Adj y x := by
  unfold Adj at *
  obtain ⟨e, he⟩ := h
  use e
  constructor
  · exact he.1
  constructor
  · exact he.2.2
  · exact he.2.1

-- Credit: Peter Nelson, Jun Kwon
lemma hypergraph_adj_comm (x y : α) : H.Adj x y ↔ H.Adj y x := ⟨.symm, .symm⟩

/--
Predicate for (hyperedge) adjacency. Analogous to `Hypergraph.Adj`, hyperedges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident on both `e` and `f`.
-/
def EAdj (H : Hypergraph α) (e : Set α) (f : Set α) : Prop :=
  e ∈ E(H) ∧ f ∈ E(H) ∧ ∃ x ∈ V(H), x ∈ e ∧ x ∈ f

lemma EAdj.symm {H : Hypergraph α} {e f : Set α} (h : H.EAdj e f) : H.EAdj f e := by
  unfold EAdj at *
  obtain ⟨v, hv⟩ := h.2.2
  constructor
  · exact h.2.1
  constructor
  · exact h.1
  · use v
    constructor
    · exact hv.1
    constructor
    · exact hv.2.2
    · exact hv.2.1

lemma EAdj.inter_nonempty (hef : H.EAdj e f) : (e ∩ f).Nonempty := by
  unfold EAdj at *
  have h' : ∃ x ∈ e, x ∈ f := by grind
  apply Set.inter_nonempty.mpr h'

-- Credit: Peter Nelson, Jun Kwon
lemma hypergraph_eadj_comm (e f) : H.EAdj e f ↔ H.EAdj f e := ⟨.symm, .symm⟩

/-! ## Basic Hypergraph Definitions & Predicates-/

/--
The *star* of a vertex is the set of all hyperedges `e ∈ E(H)` that a given vertex `x` is incident
on
-/
def star (H : Hypergraph α) (x : α) : Set (Set α) := {e ∈ E(H) | x ∈ e}

/--
We define the *star set* as the set of subsets of `E(H)` that each vertex in `V(H)` is
incident upon
-/
def stars (H : Hypergraph α) : Set (Set (Set α)) :=
  {H.star x | x ∈ V(H)}

/--
The *image* of a hypergraph `H : Hypergraph α` under function `f : α → β` is `Hᶠ : Hypergraph β`.

The vertex set of `Hᶠ` is the image of `V(H)` under `f`, and the hyperedge set of `Hᶠ` is the set
of images of the hyperedges (subsets of vertices) in `E(H)`.
-/
@[simps]
def image (H : Hypergraph α) (f : α → β) : Hypergraph β where
  vertexSet := V(H).image f
  hyperedgeSet := E(H).image (Set.image f)
  hyperedge_isSubset_vertexSet' := by
    simp
    intro e he
    have hev : e ⊆ V(H) := by exact Membership.mem.subset_vertexSet he
    refine image_subset_iff.mp ?_
    exact image_mono hev

lemma mem_image {f : α → β} {e : Set β} : e ∈ E(H.image f) ↔ ∃ e' ∈ E(H), f '' e' = e := Iff.rfl

lemma image_mem_image {f : α → β} (he : e ∈ E(H)) : e.image f ∈ E(H.image f) :=
  mem_image_of_mem _ he

lemma image_image {f : α → β} {g : β → γ} (H : Hypergraph α) :
  (H.image f).image g = H.image (g ∘ f) := by
    ext : 1
    case vertexSet => simp [Set.image_image]
    case hyperedgeSet => simp [Set.image_image]

/--
Predicate to determine if a vertex is isolated, meaning that it is not incident on any hyperedges.
Note that this includes loops, i.e., if vertex `x` is isolated, there is no hyperedge with
associated vertex subset `{x}`
-/
def IsIsolated (H : Hypergraph α) (x : α) : Prop := ∀ e ∈ E(H), x ∉ e

lemma not_exists_isolated_vertex_iff_sUnion_hyperedgeSet_eq_vertexSet :
  ⋃₀ E(H) = V(H) ↔ ∀ x ∈ V(H), ¬IsIsolated H x :=
    Iff.intro
    (by
      unfold IsIsolated
      intro h
      grind
    )
    (by
      unfold IsIsolated
      intro h
      have h' : ∀ x ∈ V(H), ∃ e ∈ E(H), x ∈ e := by grind
      refine Subset.antisymm ?_ h'
      apply Set.sUnion_subset
      exact fun t' a ↦ H.hyperedge_isSubset_vertexSet a
    )

/--
Predicate to determine if a hyperedge `e` is a loop, meaning that its associated vertex subset `s`
contains only one vertex, i.e., `|s| = 1`
-/
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := ∃ x ∈ V(H), e = {x}

lemma isLoop_encard_one (h : H.IsLoop e) : Set.encard e = 1 := by
  unfold IsLoop at h
  refine encard_eq_one.mpr ?_
  obtain ⟨x, hx⟩ := h
  use x
  exact hx.2

/--
Predicate to determine if a hypergraph is empty
-/
def IsEmpty (H : Hypergraph α) : Prop := V(H) = ∅ ∧ E(H) = ∅

/--
Predicate to determine if a hypergraph is nonempty
-/
def IsNonempty (H : Hypergraph α) : Prop := (∃ x, x ∈ V(H)) ∨ (∃ e, e ∈ E(H))

/--
The empty hypergraph of type α
-/
def emptyHypergraph (α : Type*) : Hypergraph α :=
  Hypergraph.mk
  ∅
  ∅
  (by
    intro e he
    have h1 : e = ∅ := by exact False.elim he
    exact Set.subset_empty_iff.mpr h1
  )

@[simp] lemma coe_nonempty : V(H).Nonempty → H.IsNonempty := by
  unfold IsNonempty
  unfold Set.Nonempty
  exact fun a ↦ Or.symm (Or.inr a)

lemma isEmpty_empty_hypergraph : IsEmpty (Hypergraph.emptyHypergraph α) := by
  unfold IsEmpty
  exact Prod.mk_inj.mp rfl

lemma isEmpty_eq_empty_hypergraph (h : H.IsEmpty) : emptyHypergraph α = H := by
  unfold IsEmpty at h
  have hv : V(emptyHypergraph α) = ∅ := rfl
  have he : E(emptyHypergraph α) = ∅ := rfl
  apply Hypergraph.ext_iff.mpr
  rw [h.1, hv, h.2, he]
  constructor
  · exact hv
  · exact he

@[simp]
lemma hyperedge_not_mem_empty : e ∉ E(emptyHypergraph α) :=
  by exact fun a ↦ a

lemma IsEmpty.eq (hH : H.IsEmpty) : V(H) = ∅ ∧ E(H) = ∅ := by exact hH

lemma isEmpty_iff_forall_not_mem : H.IsEmpty ↔ (∀ x, x ∉ V(H)) ∧ (∀ e, e ∉ E(H)) := by
  unfold IsEmpty
  constructor
  · intro h
    constructor
    · rw [h.1]
      apply Set.notMem_empty
    · rw [h.2]
      apply Set.notMem_empty
  · intro ho
    constructor
    · apply Set.eq_empty_iff_forall_notMem.mpr
      apply ho.left
    · apply Set.eq_empty_iff_forall_notMem.mpr
      apply ho.right

lemma IsEmpty.not_mem (hH : H.IsEmpty) {e : Set α} : e ∉ E(H) := by
  unfold IsEmpty at hH
  rw [hH.2]
  exact fun a ↦ a

lemma not_isEmpty : ¬H.IsEmpty ↔ H.IsNonempty := by
  unfold IsEmpty
  unfold IsNonempty
  constructor
  · intro h
    rw [not_and_or] at h
    cases h with
    | inl v_nonempty => (
      left
      refine nonempty_def.mp ?_
      exact nonempty_iff_ne_empty.mpr v_nonempty
    )
    | inr e_nonempty => (
      right
      refine nonempty_def.mp ?_
      exact nonempty_iff_ne_empty.mpr e_nonempty
    )
  · intro h'
    rw [not_and_or]
    cases h' with
    | inl v_nonempty => (
      left
      exact nonempty_iff_ne_empty.mp v_nonempty
    )
    | inr e_nonempty => (
      right
      exact nonempty_iff_ne_empty.mp e_nonempty
    )

lemma not_isNonempty : ¬H.IsNonempty ↔ H.IsEmpty :=
  not_iff_comm.mp not_isEmpty

alias ⟨_, IsEmpty.not_isNonempty⟩ := not_isNonempty
alias ⟨_, IsNonempty.not_isEmpty⟩ := not_isEmpty

variable (H) in
lemma isEmpty_or_isNonempty : H.IsEmpty ∨ H.IsNonempty := by
  unfold IsEmpty
  unfold IsNonempty
  grind


/--
Predicate to determine if a hypergraph is trivial

A hypergraph is trivial if it has a nonempty vertex set and an empty hyperedge set
-/
def IsTrivial (H : Hypergraph α) : Prop := Set.Nonempty V(H) ∧ E(H) = ∅

/--
A trivial hypergraph of type α with vertex set h
-/
def trivialHypergraph (f : Set α) :=
  Hypergraph.mk
  f
  ∅
  (by
    intro e he
    exact False.elim he
  )

lemma not_isEmpty_trivial_hypergraph (hh : IsTrivial H) : ¬IsEmpty H := by
  unfold IsEmpty
  unfold IsTrivial at hh
  refine not_and_of_not_or_not ?_
  left
  apply Set.nonempty_iff_ne_empty.mp hh.1

lemma hyperedge_not_mem_trivial (h : H.IsTrivial) : e ∉ E(H) := by
    unfold IsTrivial at *
    grind

/--
Predicate to determine is a hypergraph `H` is complete, meaning that each member of the power set of
the vertices (`𝒫 V(H)`) is represented in `E(H)`
-/
def IsComplete (H : Hypergraph α) : Prop := ∀ e ∈ 𝒫 V(H), e ∈ E(H)

/--
A complete hypergraph with vertex set `f`
-/
@[simps]
def completeOn (f : Set α) : Hypergraph α where
  vertexSet := f
  hyperedgeSet := 𝒫 f
  hyperedge_isSubset_vertexSet' := by simp

lemma mem_completeOn : e ∈ E(completeOn f) ↔ e ⊆ f := by
  constructor
  · exact fun a ↦ a
  · exact fun a ↦ a

lemma isComplete_completeOn (f : Set α) : (completeOn f).IsComplete := by exact fun e a ↦ a

lemma isComplete_not_isEmpty (h : H.IsComplete) : ¬ H.IsEmpty := by
  unfold IsComplete at h
  unfold IsEmpty
  have h0 : ∅ ∈ 𝒫 V(H) := by
    refine mem_powerset ?_
    apply Set.empty_subset
  apply not_and_or.mpr
  right
  grind

lemma completeOn_isNonempty {S : Set α} : (completeOn S).IsNonempty := by
  have h : E(completeOn S) = 𝒫 S := rfl
  have h' : ∅ ∈ E(completeOn S) := by
    refine mem_completeOn.mpr ?_
    apply Set.empty_subset
  unfold IsNonempty
  right
  use ∅

lemma isComplete_not_isTrivial (h : H.IsComplete) : ¬H.IsTrivial := by
  unfold IsComplete at h
  unfold IsTrivial
  have h' : ∅ ∈ E(H) := by grind
  apply not_and_or.mpr
  right
  exact ne_of_mem_of_not_mem' h' fun a ↦ a

lemma completeOn_not_isTrivial {S : Set α} : ¬(completeOn S).IsTrivial := by
  unfold IsTrivial
  apply not_and_or.mpr
  right
  exact ne_of_mem_of_not_mem' (fun ⦃a⦄ a ↦ a) fun a ↦ a

end Hypergraph
