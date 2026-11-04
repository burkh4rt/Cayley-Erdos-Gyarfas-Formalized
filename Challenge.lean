module

public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Set.Card

/-!
# Odd-ordered Cayley graphs satisfy Erdős–Gyárfás

Independent statements for Michael C. Burkhart's arXiv:2611.05060, §1.
The four numbered results are given in paper order. The additional theorem
immediately after Theorem 1.1 states the stronger noncyclic conclusion
identified in the paragraph following that theorem.

`SimpleGraph.mulCayley S` has edges between `g` and `g * s` for `s ∈ S`
under the stated symmetry and identity-free hypotheses. `Subgroup.closure S = ⊤`
means that `S` generates the group. A closed walk `c` satisfying `c.IsCycle`
is a simple cycle, and `c.length` counts its edges. Every power-of-two length
in these statements has exponent at least two, as in the introduction.
-/

@[expose] public section

namespace CayleyErdősGyárfás

/-- Two simple cycles of length `2 ^ n`, based at their unique common vertex.
Left multiplication by `g` carries the first to the second up to a cyclic
change of basepoint. For a simple cycle, `support.tail` lists its vertices in
traversal order with one occurrence of each vertex. `List.IsRotated` allows
the traversal to start at a different vertex. -/
def HasSymmetricFigureEight {G : Type*} [Group G] (S : Set G) : Prop :=
  ∃ (n : ℕ) (v : G) (α β : (SimpleGraph.mulCayley S).Walk v v),
    2 ≤ n ∧ α.IsCycle ∧ β.IsCycle ∧
    α.length = 2 ^ n ∧ β.length = 2 ^ n ∧
    (∃ g : G, List.IsRotated (α.support.tail.map (g * ·)) β.support.tail) ∧
    ∀ w : G, (w ∈ α.support ∧ w ∈ β.support) ↔ w = v

/-- **Theorem 1.1** (`thm:main`). The Cayley graph of a finite group of odd
order contains a simple cycle of power-of-two length whenever its symmetric,
identity-free generating set has at least three elements. -/
theorem odd_order_cayley_contains_two_power_cycle
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G))
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  sorry

/-- **Stronger conclusion after Theorem 1.1.** For a noncyclic group of
odd order, every Cayley graph on a symmetric, identity-free generating set
contains a symmetric figure-eight. -/
theorem noncyclic_odd_order_symmetric_figure_eight
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S) (hgen : Subgroup.closure S = ⊤)
    (hncyclic : ¬ IsCyclic G) : HasSymmetricFigureEight S := by
  sorry

/-- **Lemma 1.2** (`lem:main`). A symmetric figure-eight lifts from the
quotient by an abelian normal subgroup of a finite odd-order group. The
quotient graph uses the image of `S` with its identity coset removed. -/
theorem symmetric_figure_eight_lifts_of_abelian
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G))
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hfigure : HasSymmetricFigureEight
      ((QuotientGroup.mk (s := A)) '' S \ {1})) :
    HasSymmetricFigureEight S := by
  sorry

/-- **Lemma 1.3** (`lem:index2`). A simple cycle of power-of-two length
in the quotient by a normal 2-subgroup guarantees such a cycle in the
original Cayley graph. The two lengths may differ. -/
theorem two_power_cycle_lifts_of_normal_two_subgroup
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P)
    (hcycle : ∃ (n : ℕ) (v : G ⧸ P)
      (c : (SimpleGraph.mulCayley
        ((QuotientGroup.mk (s := P)) '' S \ {1})).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  sorry

/-- **Corollary 1.4** (`cor:nilp`). The Cayley graph of a finite nilpotent
group contains a simple cycle of power-of-two length whenever its symmetric,
identity-free generating set has at least three elements. -/
theorem nilpotent_cayley_contains_two_power_cycle
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  sorry

end CayleyErdősGyárfás
