module

public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Set.Card

/-!
# Definitions for the proof development

The declaration below deliberately duplicates the definition in `Challenge.lean`.
The Challenge imports only Mathlib and remains independent of this development.
Comparator checks `HasSymmetricFigureEight` alongside the results that use it.
-/

@[expose] public section

namespace CayleyErdősGyárfás

/-- The manuscript's symmetric figure-eight: two simple cycles of the same
power-of-two length, based at their unique common vertex, with one a left
translate of the other up to a cyclic change of basepoint.

For a closed walk, `support.tail` lists each cycle vertex once; `List.IsRotated`
expresses change of basepoint while preserving traversal order. Thus this
requires translation of the cycle, not merely translation of its vertex set.
This is the only manuscript-specific definition on the statement surface. -/
def HasSymmetricFigureEight {G : Type*} [Group G] (S : Set G) : Prop :=
  ∃ (n : ℕ) (v : G) (α β : (SimpleGraph.mulCayley S).Walk v v),
    2 ≤ n ∧ α.IsCycle ∧ β.IsCycle ∧
    α.length = 2 ^ n ∧ β.length = 2 ^ n ∧
    (∃ g : G, List.IsRotated (α.support.tail.map (g * ·)) β.support.tail) ∧
    ∀ w : G, (w ∈ α.support ∧ w ∈ β.support) ↔ w = v


end CayleyErdősGyárfás
