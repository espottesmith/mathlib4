/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Hypergraph.Basic


/-!

# Walks on hypergraphs

## Main definitions

## Implementation details

## Tags

-/

universe u v
variable {α : Type u} {β : Type v} {x y z x' y' z' x'' y'' : α} {e e' f g : Set α}
variable {F F' : (α × Set α)}
variable {W W' : List (α × Set α)}

namespace Hypergraph

variable {H : Hypergraph α}

def IsWalk (H : Hypergraph α) : List (α × Set α) → Prop
  | [] => true
  | (_, e) :: [] => e = ∅
  | (x, e) :: (y, e') :: W => e ∈ E(H) ∧ x ∈ e ∧ y ∈ e ∧ x ≠ y ∧ H.IsWalk ((y, e') :: W)


@[ext]
structure WalkStruct (α : Type*) where
  -- The hypergraph on which this walk exists
  H : Hypergraph α
  -- The steps of the walk. The starting point (final element) must have associated edge ∅
  flags : List (α × Set α)
  -- The flags must form a valid sequence of adjacency-based steps
  flags_isWalk : H.IsWalk flags

inductive Walk : α → α → Type u
  | nil {x : α} : Walk x x
  | cons {x y z : α} {e : Set α} (he : e ∈ E(H))
    (hx : x ∈ e) (hy : y ∈ e) (hxy : x ≠ y) (p : Walk y z) : Walk x z

instance : DecidableEq Walk

attribute [refl] Walk.nil

@[simps]
instance Walk.instInhabited (x : α) : Inhabited (H.Walk x x) := ⟨Walk.nil⟩

namespace Walk

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (x : α) : H.Walk x x := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices and connecting edge as explicit arguments. -/
@[match_pattern]
abbrev cons' (x y z : α) (e : Set α) (he : e ∈ E(H)) (hx : x ∈ e) (hy : y ∈ e) (hxy : x ≠ y)
  (p : H.Walk y z) : H.Walk x z := Walk.cons he hx hy hxy p

end Walk


-- Walk in H is a (graph) walk in G(H), the incidence (bipartite) graph
-- hyperpath : all vertices distinct
-- path : walk whose vertices and edges distinct
-- hypercycle : closed hyperpath
-- cycle : closed path
-- trail : each flag is distinct
--    i.e., each combination of v and e can only appear consecutively in a walk at most once
--    intuition: we cannot "move out" of a vertex the same way more than once
--    and we cannot "move into" a vertex the same way more than once
-- strict trail : a walk whose edges are distinct
--    all strict trails are trails, since it's impossible to repeat flags if you don't repeat edges

end Hypergraph
