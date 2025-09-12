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

inductive IsWalk (H : Hypergraph α) : α → List (α × Set α) → Prop
  | nil : IsWalk H _ []
  | cons : ∀ {x y : α} {e : Set α} {W : List (α × Set α)}, e ∈ E(H) → x ∈ e → y ∈ e → x ≠ y →
      IsWalk H x W → IsWalk H y (.cons ⟨y, e⟩ W)

@[simps]
instance IsWalk.instInhabited (x : α) : Inhabited (H.IsWalk x []) := ⟨IsWalk.nil⟩

namespace IsWalk

/-- Pattern to get `IsWalk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (x : α) : H.IsWalk x [] := IsWalk.nil

/-- Pattern to get `IsWalk.cons` with the vertex, edge, and step list as explicit arguments. -/
@[match_pattern]
abbrev cons' (x y : α) (e : Set α) (W : List (α × Set α))
  (he : e ∈ E(H)) (hx : x ∈ e) (hy : y ∈ e) (hxy : x ≠ y) (p : H.IsWalk x W) :
  H.IsWalk y ((y, e) :: W) := IsWalk.cons he hx hy hxy p

/--
Change the vertices and steps of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context."

Credit: Kyle Miller
-/
protected def copy {x x' W W'} (p : H.IsWalk x W) (hx : x = x') (hW : W = W') : H.IsWalk x' W' :=
  hx ▸ hW ▸ p

/-- The length of a walk is the number of edges/darts along it. -/
-- TODO: you are here
-- Not sure why this isn't working...
def length {x : α} {W :  List (α × Set α)} : H.IsWalk x W → ℕ
  | nil => 0
  | cons _ _ _ _ _ => W.length

-- /-- The `support` of a walk is the list of vertices it visits in order. -/
-- def support {x : α} : H.IsWalk x W → List α
--   | nil => [x]
--   | cons _ _ _ _ p => x :: p.support

-- /-- The `darts` of a walk is the list of darts it visits in order. -/
-- def darts {u v : V} : G.Walk u v → List G.Dart
--   | nil => []
--   | cons h p => ⟨(u, _), h⟩ :: p.darts

-- def IsHyperPath (h : H.IsWalk x W) : Prop :=

-- def IsPath

-- def IsHyperCycle

-- def IsCycle

-- def IsTrail

-- def IsStrictTrail

end IsWalk


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
