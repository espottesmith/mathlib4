/-
Copyright (c) 2025 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith, Bhavik Mehta
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# Supports for Undirected Hypergraphs

TODO
-/

open Set

variable {α : Type*} {x y : α} {e f g h : Set α} {l : Set (Set α)}

namespace Hypergraph

def support (H : Hypergraph α) : Set α := ⋃₀ E(H)

end Hypergraph
