/-
Copyright (c) 2026 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
module
public import Mathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card

/-!
# Subhypergraphs of undirected hypergraphs

This file develops the basic theory of *subhypergraphs* of undirected hypergraphs of type 
`Hypergraph α`. Specifically, we consider *subhypergraphs*, *induced subhypergraphs*, and
*partial hypergraphs*.

## Main definitions

For `H H' : Hypergraph α`:

* `H ≤ H'`, the subhypergraph relation, is a partial order on hypergraphs. This is definitionally
  equivalent to `H.IsSubhypergraph H'`.
* `H ≤i H'` (`Hypergraph.IsInducedSubhypergraph`): `V(H) ⊆ V(H')`, and
  `E(H) = {e ∩ V(H) | e ∈ E(H') ∧ e ∩ V(H) ≠ ∅}`
* `H ≤p H'` (`Hypergraph.IsPartialHypergraph`): `V(H) ⊆ V(H')` and
  `E(H) = {e | e ∈ E(H') ∧ e ⊆ V(H)}`

## Implementation details

Following the general design of `Graph`, subgraphs are terms in `Hypergraph α`, rather than a
separate structure, to allow for reuse of notation and lemmas and to further allow for
subhypergraph order as a partial order on `Hypergraph α`.

## Tags

hypergraphs, subhypergraph, induced subhypergraph, partial hypergraph
-

-/

public section


