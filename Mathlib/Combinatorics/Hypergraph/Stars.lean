
/-- The *star* of a vertex `x` is the set of all edges `e ∈ E(H)` incident to `x`. -/
def star (H : Hypergraph α) (x : α) : Set (Set α) := {e ∈ E(H) | x ∈ e}

/-- The *star set* is the set of subsets of `E(H)` of edges incident to a vertex in `V(H)`. -/
def stars (H : Hypergraph α) : Set (Set (Set α)) := {H.star x | x ∈ V(H)}


