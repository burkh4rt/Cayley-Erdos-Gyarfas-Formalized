module

public import CayleyErdosGyarfas.BaseCases
public import CayleyErdosGyarfas.Basic
public import CayleyErdosGyarfas.FigureEightLifting
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! The commuting square construction used in the cyclic quotient case. -/

public section

namespace CayleyErdősGyárfás

open SimpleGraph

/-- A commuting square and its diagonal translate meet only at the diagonal
vertex when the diagonal product avoids the generators and their inverses. -/
theorem symmetric_figure_eight_of_commuting_square
    {G : Type*} [CommGroup G] (hodd : Odd (Nat.card G)) (S : Set G)
    {a b : G} (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hbinv : b ≠ a⁻¹)
    (hescape : a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G)) :
    HasSymmetricFigureEight S := by
  obtain ⟨c, hc, hlen, hsupp⟩ := four_cycle_of_commuting_generators_with_support
    S ha hb ha1 hb1 hab hbinv (Commute.all a b)
  have hsquare : Function.Injective (fun z : G ↦ z ^ 2) :=
    hodd.coprime_two_right.pow_left_bijective.1
  have hprod : a * b ≠ 1 := fun h ↦ hbinv (eq_inv_of_mul_eq_one_right h)
  have hsq (z : G) (hz : z ≠ 1) : z * z ≠ 1 := by
    intro h
    exact hz (hsquare (by simpa only [pow_two, one_mul] using h : z ^ 2 = (1 : G) ^ 2))
  have haesc : a * b ≠ a⁻¹ := fun h ↦ hescape (by simp [h])
  have hbesc : a * b ≠ b⁻¹ := fun h ↦ hescape (by simp [h])
  apply hasSymmetricFigureEight_of_cycle_translate c 2 (by decide) hc hlen (a * b) (a * b)
  intro x
  have hmem (z : G) : z ∈ c.support ↔ z = 1 ∨ z = a ∨ z = a * b ∨ z = b := by
    simp [hsupp, or_assoc, or_left_comm, or_comm]
  simp only [hmem]
  constructor
  · rintro ⟨hx, y, hy, heq⟩
    rcases hx with hx | hx | hx | hx <;> rw [hx] at heq ⊢
    · rcases hy with hy | hy | hy | hy <;> rw [hy] at heq
      · exact (hprod (by simpa using heq)).elim
      · exact (haesc (eq_inv_of_mul_eq_one_left heq)).elim
      · exact (hsq (a * b) hprod heq).elim
      · exact (hbesc (eq_inv_of_mul_eq_one_left heq)).elim
    · rcases hy with hy | hy | hy | hy <;> rw [hy] at heq
      · exact (hb1 (mul_left_cancel (by simpa using heq : a * b = a * 1))).elim
      · exact (hprod (mul_right_cancel (by simpa using heq : (a * b) * a = 1 * a))).elim
      · have h : (a * b) * b = 1 := by
          apply mul_left_cancel (a := a)
          simpa [mul_assoc, mul_left_comm, mul_comm] using heq
        exact (hbesc (eq_inv_of_mul_eq_one_left h)).elim
      · have h : b * b = 1 := by
          apply mul_left_cancel (a := a)
          simpa [mul_assoc] using heq
        exact (hsq b hb1 h).elim
    · rcases hy with hy | hy | hy | hy <;> rw [hy] at heq
      · exact (ha1 (mul_right_cancel (by simpa using heq : a * b = 1 * b))).elim
      · have h : a * a = 1 := by
          apply mul_right_cancel (b := b)
          simpa [mul_assoc, mul_left_comm, mul_comm] using heq
        exact (hsq a ha1 h).elim
      · have h : (a * b) * a = 1 := by
          apply mul_right_cancel (b := b)
          simpa [mul_assoc, mul_left_comm, mul_comm] using heq
        exact (haesc (eq_inv_of_mul_eq_one_left h)).elim
      · exact (hprod (mul_right_cancel (by simpa using heq : (a * b) * b = 1 * b))).elim
  · rintro rfl
    exact ⟨Or.inr (Or.inr (Or.inl rfl)), 1, Or.inl rfl, mul_one _⟩

/-- The simultaneous endpoint collisions force the two generators to generate a group of order five. -/
theorem card_eq_five_of_inverse_square_generators {G : Type*} [Group G]
    {a b : G} (ha1 : a ≠ 1) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hb : b = (a * a)⁻¹) (ha : a = b * b) : Nat.card G = 5 := by
  have ha5 : a ^ 5 = 1 := calc
    a ^ 5 = (a * a) * (a * a) * a := by simp [pow_succ, mul_assoc]
    _ = (b * b)⁻¹ * a := by rw [hb]; simp only [mul_inv_rev, inv_inv, mul_assoc]
    _ = 1 := by rw [← ha]; simp
  have hz : Subgroup.zpowers a = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le (Subgroup.zpowers a)).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact Subgroup.mem_zpowers a
    · subst x
      rw [hb]
      exact (Subgroup.zpowers a).inv_mem
        ((Subgroup.zpowers a).mul_mem (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a))
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ho : orderOf a = 5 := orderOf_eq_prime_iff.mpr ⟨ha5, ha1⟩
  exact (orderOf_eq_card_of_zpowers_eq_top hz).symm.trans ho


/-- One of the two diagonal products escapes the inverse set, unless the generated group has order five. -/
theorem generating_products_escape_inverse_set {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a b : G} (ha : a ≠ 1) (hb : b ≠ 1)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (hcard : Nat.card G ≠ 5) :
    a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G) ∨
      a * b⁻¹ ∉ ({a, a⁻¹, b, b⁻¹} : Set G) := by
  by_contra! h
  rcases h with ⟨h₁, h₂⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  have h₁' : a * b = a⁻¹ ∨ a * b = b⁻¹ := by
    rcases h₁ with h | h | h | h
    · exact False.elim (hb (mul_left_cancel (by simpa using h : a * b = a * 1)))
    · exact Or.inl h
    · exact False.elim (ha (mul_right_cancel (by simpa using h : a * b = 1 * b)))
    · exact Or.inr h
  have h₂' : a * b⁻¹ = a⁻¹ ∨ a * b⁻¹ = b := by
    rcases h₂ with h | h | h | h
    · have : b⁻¹ = 1 := mul_left_cancel (by simpa using h : a * b⁻¹ = a * 1)
      exact False.elim (hb (by simpa using this))
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (ha (mul_right_cancel (by simpa using h : a * b⁻¹ = 1 * b⁻¹)))
  have h₁'' : b = (a * a)⁻¹ ∨ a = (b * b)⁻¹ := by
    rcases h₁' with h | h
    · left
      calc b = a⁻¹ * (a * b) := by group
           _ = a⁻¹ * a⁻¹ := by rw [h]
           _ = (a * a)⁻¹ := by group
    · right
      calc a = (a * b) * b⁻¹ := by group
           _ = b⁻¹ * b⁻¹ := by rw [h]
           _ = (b * b)⁻¹ := by group
  have h₂'' : b = a * a ∨ a = b * b := by
    rcases h₂' with h | h
    · left
      calc b = (a * b⁻¹)⁻¹ * a := by group
           _ = (a⁻¹)⁻¹ * a := by rw [h]
           _ = a * a := by simp
    · right
      calc a = (a * b⁻¹) * b := by group
           _ = b * b := by rw [h]
  rcases h₁'' with h₁ | h₁ <;> rcases h₂'' with h₂ | h₂
  · have hsq : a ^ 2 = (a⁻¹) ^ 2 := by simpa [pow_two, mul_inv_rev] using h₂.symm.trans h₁
    have hinv := square_injective_of_odd_natCard hodd hsq
    exact ha (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using hinv))
  · exact hcard (card_eq_five_of_inverse_square_generators ha hgen h₁ h₂)
  · have hgen' : Subgroup.closure ({b, a} : Set G) = ⊤ := by simpa only [Set.pair_comm b a] using hgen
    exact hcard (card_eq_five_of_inverse_square_generators hb hgen' h₁ h₂)
  · have hsq : b ^ 2 = (b⁻¹) ^ 2 := by simpa [pow_two, mul_inv_rev] using h₂.symm.trans h₁
    have hinv := square_injective_of_odd_natCard hodd hsq
    exact hb (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using hinv))

/-- The cyclic-quotient square case of the manuscript. The conclusion in fact
holds for any abelian group generated by the two chosen elements, except for
the five-element obstruction to this particular figure-eight construction. -/
theorem symmetric_figure_eight_of_two_generators_not_five
    {G : Type*} [CommGroup G] (hodd : Odd (Nat.card G)) (hcard : Nat.card G ≠ 5)
    (S : Set G) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    {a b : G} (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hbinv : b ≠ a⁻¹)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    HasSymmetricFigureEight S := by
  obtain hescape | hescape := generating_products_escape_inverse_set hodd ha1 hb1 hgen hcard
  · exact symmetric_figure_eight_of_commuting_square hodd S ha hb ha1 hb1 hab hbinv hescape
  · have habi : a ≠ b⁻¹ := by
      intro h
      exact hbinv (by simpa only [inv_inv] using congrArg Inv.inv h.symm)
    have hbinv' : b⁻¹ ≠ a⁻¹ := fun h ↦ hab (inv_injective h).symm
    have hescape' : a * b⁻¹ ∉ ({a, a⁻¹, b⁻¹, (b⁻¹)⁻¹} : Set G) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_inv,
        or_assoc, or_left_comm, or_comm] using hescape
    exact symmetric_figure_eight_of_commuting_square hodd S ha (hinv b hb) ha1
      (by simpa using hb1) habi hbinv' hescape'

end CayleyErdősGyárfás
