module

public import CayleyErdosGyarfas

/-!
# Proofs for arXiv:2611.05060

The imported development supplies `HasSymmetricFigureEight` and
`noncyclic_odd_order_symmetric_figure_eight`. Below are the four numbered
results in the paper's notation and order.
-/

public section

namespace CayleyErdősGyárfás

open scoped IsMulCommutative

/-- A simple cycle has at least three edges, so the two lower bounds on the
exponent are equivalent in the presence of `c.IsCycle`. -/
private theorem cycle_exponent_iff {V : Type*} (Γ : SimpleGraph V) :
    (∃ (n : ℕ) (v : V) (c : Γ.Walk v v), 1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n) ↔
    (∃ (n : ℕ) (v : V) (c : Γ.Walk v v), 2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n) := by
  constructor
  · rintro ⟨n, v, c, _, hc, hlen⟩
    exact ⟨n, v, c, two_power_cycle_exponent_ge_two hc hlen, hc, hlen⟩
  · rintro ⟨n, v, c, hn, hc, hlen⟩
    exact ⟨n, v, c, Nat.le_trans (by decide : 1 ≤ 2) hn, hc, hlen⟩

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
  classical
  apply (cycle_exponent_iff _).mp
  by_cases hcyclic : IsCyclic G
  · let := hcyclic
    exact abelian_cayley_contains_two_power_cycle S hone hcard
  · exact HasSymmetricFigureEight.contains_two_power_cycle
      (noncyclic_odd_order_symmetric_figure_eight S hodd hinv hone hgen hcyclic)

set_option linter.unusedVariables false in
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
  exact symmetric_figure_eight_lifts S hodd A hfigure

set_option linter.unusedVariables false in
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
  exact (cycle_exponent_iff _).mp
    (two_power_cycle_lifts S P hP ((cycle_exponent_iff _).mpr hcycle))

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
  apply (cycle_exponent_iff _).mp
  exact nilpotent_cycle_of_odd_order_theorem
    (fun T hodd hinv hone hgen hcard ↦ (cycle_exponent_iff _).mpr
      (odd_order_cayley_contains_two_power_cycle T hodd hinv hone hgen hcard))
    S hinv hone hgen hcard

end CayleyErdősGyárfás
