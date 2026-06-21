/-
Copyright (c) 2026 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# Incidence Matrices

This module defines the incidence matrix of an undirected hypergraph and provides theorems connecting
hypergraph properties to computational properties of the matrix.

## Main definitions

* `Matrix.IsIncMatrix`: `I : Matrix V V α` is qualified as an "incidence matrix" if
  (1) every entry of `A` is `0` or `1`,
  TODO: other requirements of an incidence matrix?

* `Matrix.IsIncMatrix.toHypergraph`: for `I : Matrix V V α` and `h : I.IsAdjMatrix`,
  `h.toHypergraph` is the hypergraph induced by `I`.

* `Matrix.dual`: for `I : Matrix V V α`, `I.dual` is supposed to be
  the incidence matrix of the dual hypergraph of the hypergraph induced by `I`.

* `Hypergraph.incMatrix`: the incidence matrix of a `Hypergraph`.

-/

@[expose] public section


open Matrix


