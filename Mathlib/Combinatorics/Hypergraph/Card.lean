import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Hypergraph.Basic

open Set

variable {α : Type*} {x y : α} {e f g h : Set α} {l : Set (Set α)}

namespace Hypergraph

/-! ## Undirected Hypergraph Cardinality -/

/--
The *order* of a hypergraph `H` is defined as the number of vertices contained in `H`
-/
noncomputable def order (H : Hypergraph α) : ENat := Set.encard V(H)

/--
The *size* of a hypergraph `H` is defined as the number of hyperedges contained in `H`
-/
noncomputable def size (H : Hypergraph α) : ENat := Set.encard E(H)

/--
The *degree* of a vertex in a hypergraph `H`.

A vertex `x` has degree `n`, where `n` is the number of hyperedges in `E(H)` that `x` is incident
on.
-/
noncomputable def vertexDegree (H : Hypergraph α) (x : α) : ENat := Set.encard (H.star x)

/--
The set of vertex *degrees* of a hypergraph `H`.
-/
noncomputable def vertexDegrees (H : Hypergraph α) : Set ENat := {H.vertexDegree x | x ∈ V(H)}

/--
The *degree* of a hyperedge in hypergraph `H`.

A hyperedge `e` has degree `n`, where `n` is the number of vertices in `V(H)` that are incident on
`e`.
-/
noncomputable def hyperedgeDegree (e : Set α) : ENat := Set.encard e

/--
The set of hyperedge *degrees* of a hypergraph `H`.
-/
noncomputable def hyperedgeDegrees (H : Hypergraph α) : Set ENat := {hyperedgeDegree e | e ∈ E(H)}

/--
Predicate to determine if a hypergraph is *`k`-uniform*.

In a `k`-uniform hypergraph `H`, all hyperedges `e ∈ E(H)` have the same cardinality, i.e.,
`|e| = k`.
-/
def IsKUniform (H : Hypergraph α) (k : ℕ) : Prop := ∀ e ∈ E(H), hyperedgeDegree e = k

/--
Predicate to determine if a hypergraph is *`d`-regular*.

In a `d`-regular hypergraph `H`, all vertices `v ∈ V(H)` have the same degree, i.e., all vertices
are incident on `d` hyperedges.
-/
def IsDRegular (H : Hypergraph α) (d : ℕ) : Prop := ∀ x ∈ V(H), H.vertexDegree x = d

end Hypergraph
