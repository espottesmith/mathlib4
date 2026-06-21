/-- Collection of all tails -/
/-- Collection of all heads -/

/-- TODO
lemma sUnion_edgeSet_subset_vertexSet : ⋃₀ E(H) ⊆ V(H) :=
  subset_powerset_iff.mp edgeSet_subset_powerset_vertexSet
-/

/--
* `Dₕ.IsBHypergraph`: A predicate defining a special case of dihypergraph where the destination of
  any edge (*B-arc*) contains exactly one vertex.
* `IsFHypergraph`: A predicate defining a special case of dihypergraph where the source of any edge
  (*F-arc*) contains exactly one vertex.
* `IsBFHypergraph`: A predicate defining a special case of dihypergraph where all edges are either
  B-arcs or F-arcs; i.e., either the source contains exactly one vertex or the destination
  contains exactly one vertex.
* `IsNonEndless`: A predicate defining a special case of dihypergraph where, for all edges, neither
  the source nor the destination are empty.
-/


/-! ## Special Cases -/
section SpecialCase

/--
A special case of `Dihypergraph` where all hyperedge destinations contain exactly one vertex.
-/
@[expose]
def IsBHypergraph (Dₕ : Dihypergraph α) := ∀ e ∈ E(Dₕ), ∃ x ∈ V(Dₕ), e.2 = {x}

/--
A special case of `Dihypergraph` where all hyperedge sources contain exactly one vertex.
-/
@[expose]
def IsFHypergraph (Dₕ : Dihypergraph α) :=  ∀ e ∈ E(Dₕ), ∃ x ∈ V(Dₕ), e.1 = {x}

/--
A special case of `Dihypergraph` where all hyperedges have a source containing exactly one vertex
or have a destination containing exactly one vertex.
-/
@[expose]
def IsBFHypergraph (Dₕ : Dihypergraph α) :=
  ∀ e ∈ E(Dₕ), (∃ x ∈ V(Dₕ), e.1 = {x}) ∨ (∃ x ∈ V(Dₕ), e.2 = {x})

/--
Many results related to directed hypergraphs assume that hyperedge limbs are nonempty. We define
a hypergraph with nonempty hyperedge sources/destinations as a special case of dihypergraph, which
we call "non-endless".
-/
@[expose]
def IsNonEndless (Dₕ : Dihypergraph α) := ∀ e ∈ E(Dₕ), e.1.Nonempty ∧ e.2.Nonempty

end SpecialCase


