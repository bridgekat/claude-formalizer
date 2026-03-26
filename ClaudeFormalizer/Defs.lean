/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Definitions for ε-light vertex subsets

This file defines the key notions for the ε-light subset theorem:
- `SimpleGraph.edgesWithin`: restriction of a graph to edges within a vertex subset
- `SimpleGraph.IsEpsilonLight`: the ε-lightness property
- The main theorem statement
-/

open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/-- The subgraph of `G` retaining only edges with both endpoints in `S`.
This is the graph `G_S = (V, E(S,S))` from the problem statement. -/
@[reducible]
def edgesWithin (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := fun {_ _} h => ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

instance edgesWithin.instDecidableRel
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (G.edgesWithin S).Adj :=
  fun _ _ => inferInstance

/-- A subset `S` of vertices is `ε`-light if `ε • L_G - L_{G_S}` is positive semidefinite,
where `L_G` is the Laplacian of `G` and `G_S` restricts edges to those within `S`. -/
def IsEpsilonLight (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (S : Finset V) : Prop :=
  (ε • G.lapMatrix ℝ - (G.edgesWithin S).lapMatrix ℝ).PosSemidef

/-- The edgesWithin graph is a subgraph of the original graph. -/
lemma edgesWithin_le (G : SimpleGraph V) (S : Finset V) :
    G.edgesWithin S ≤ G :=
  fun _ _ h => h.1

/-- The Laplacian of `edgesWithin` is PSD. -/
lemma posSemidef_lapMatrix_edgesWithin
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ((G.edgesWithin S).lapMatrix ℝ).PosSemidef :=
  SimpleGraph.posSemidef_lapMatrix _ _

end SimpleGraph

-- The main theorem `exists_large_epsilon_light_subset` is proved in `ClaudeFormalizer.Main`.
