module

public import CayleyErdosGyarfas.Definitions
public import CayleyErdosGyarfas.Lifting
public import Mathlib.Tactic

/-!
# Proved elementary cases

These results supply the abelian case mentioned in the introduction, using
Mathlib's Cayley graph and simple-cycle definitions throughout.
-/

public section

namespace CayleyErdősGyárfás

open SimpleGraph

/-- Distinct noninverse commuting generators produce the square
`1, s, s * t, t, 1` in the Cayley graph. -/
theorem four_cycle_of_commuting_generators_with_support
    {G : Type*} [Group G] (S : Set G) {s t : G}
    (hs : s ∈ S) (ht : t ∈ S) (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hst : s ≠ t) (hsti : t ≠ s⁻¹) (hcomm : Commute s t) :
    ∃ c : (mulCayley S).Walk 1 1, c.IsCycle ∧ c.length = 4 ∧ c.support = [1, s, s * t, t, 1] := by
  have hprod : s * t ≠ 1 := by
    intro h
    exact hsti (eq_inv_of_mul_eq_one_right h)
  have ha : (mulCayley S).Adj 1 s := by
    rw [mulCayley_adj']
    exact ⟨Ne.symm hs1, s, hs, Or.inl (one_mul s)⟩
  have hb : (mulCayley S).Adj s (s * t) := by
    rw [mulCayley_adj']
    exact ⟨by simpa using ht1, t, ht, Or.inl rfl⟩
  have hc : (mulCayley S).Adj (s * t) t := by
    rw [mulCayley_adj']
    exact ⟨by simpa using hs1, s, hs, Or.inr hcomm.eq⟩
  have hd : (mulCayley S).Adj t 1 := by
    rw [mulCayley_adj']
    exact ⟨ht1, t, ht, Or.inr (one_mul t).symm⟩
  let c : (mulCayley S).Walk 1 1 := .cons ha (.cons hb (.cons hc (.cons hd .nil)))
  refine ⟨c, ?_, rfl, rfl⟩
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · rw [Walk.isPath_def]
    simp [c, hs1, ht1, hst, hprod]
  · simp [c]

/-- The square construction, with only its simplicity and length retained. -/
theorem four_cycle_of_commuting_generators
    {G : Type*} [Group G] (S : Set G) {s t : G}
    (hs : s ∈ S) (ht : t ∈ S) (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hst : s ≠ t) (hsti : t ≠ s⁻¹) (hcomm : Commute s t) :
    ∃ c : (mulCayley S).Walk 1 1, c.IsCycle ∧ c.length = 4 := by
  obtain ⟨c, hc, hlen, _⟩ := four_cycle_of_commuting_generators_with_support
    S hs ht hs1 ht1 hst hsti hcomm
  exact ⟨c, hc, hlen⟩

/-- Every Cayley graph of a finite abelian group with at least three
nonidentity generators contains a simple four-cycle. -/
theorem abelian_cayley_contains_four_cycle
    {G : Type*} [CommGroup G] [Finite G] (S : Set G)
    (hone : (1 : G) ∉ S) (hcard : 3 ≤ S.ncard) :
    ∃ c : (mulCayley S).Walk 1 1, c.IsCycle ∧ c.length = 4 := by
  classical
  obtain ⟨s, hs⟩ := (Set.ncard_pos (s := S)).mp (show 0 < S.ncard by omega)
  have hpair : ({s, s⁻¹} : Set G).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le s ({s⁻¹} : Set G)
  obtain ⟨t, ht, htout⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({s, s⁻¹} : Set G).ncard < S.ncard by omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htout
  exact four_cycle_of_commuting_generators S hs ht
    (fun h ↦ hone (h ▸ hs)) (fun h ↦ hone (h ▸ ht))
    (Ne.symm htout.1) htout.2 (Commute.all s t)

/-- The abelian case of the manuscript's power-of-two cycle conclusion. -/
theorem abelian_cayley_contains_two_power_cycle
    {G : Type*} [CommGroup G] [Finite G] (S : Set G)
    (hone : (1 : G) ∉ S) (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  obtain ⟨c, hc, hlen⟩ := abelian_cayley_contains_four_cycle S hone hcard
  exact ⟨2, 1, c, by decide, hc, hlen⟩

/-- The powers of a generator of order at least three form a simple cycle. -/
theorem generator_order_cycle
    {G : Type*} [Group G] (S : Set G) {s : G}
    (hs : s ∈ S) (horder : 3 ≤ orderOf s) :
    ∃ (v : G) (c : (mulCayley S).Walk v v), c.IsCycle ∧ c.length = orderOf s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at horder
  apply exists_cycle_of_sequence horder (s ^ ·)
  · simp
  · intro i hi
    rw [mulCayley_adj']
    refine ⟨?_, s, hs, Or.inl (pow_succ s i).symm⟩
    simpa [pow_succ] using hs1
  · intro i hi j hj heq
    exact pow_injOn_Iio_orderOf hi hj heq

/-- If a generator of a 2-group has order at least three, its own orbit
already supplies a power-of-two cycle. -/
theorem two_group_cycle_of_generator_order
    {G : Type*} [Group G] (hG : IsPGroup 2 G) (S : Set G) {s : G}
    (hs : s ∈ S) (horder : 3 ≤ orderOf s) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  obtain ⟨n, hn⟩ := hG.exists_orderOf_eq_pow s
  obtain ⟨v, c, hc, hlen⟩ := generator_order_cycle S hs horder
  refine ⟨n, v, c, ?_, hc, hlen.trans hn⟩
  by_contra hn0
  have : n = 0 := by omega
  have horder1 : orderOf s = 1 := by simpa [this] using hn
  omega

/-- Two noncommuting generators trace a simple alternating cycle.
The vertex sequence is `(s*t)^i, (s*t)^i*s`. -/
theorem alternating_cycle_of_noncommuting_generators
    {G : Type*} [Group G] [Finite G] (S : Set G) {s t : G}
    (hs : s ∈ S) (ht : t ∈ S)
    (hnc : ¬ Commute s t) :
    ∃ (v : G) (c : (mulCayley S).Walk v v),
      c.IsCycle ∧ c.length = 2 * orderOf (s * t) := by
  have hs1 : s ≠ 1 := by intro h; apply hnc; simp [h]
  have ht1 : t ≠ 1 := by intro h; apply hnc; simp [h]
  have hpos := orderOf_pos (s * t)
  have hnot : orderOf (s * t) ≠ 1 := by
    intro h
    have htinv : t = s⁻¹ := eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.mp h)
    apply hnc
    rw [htinv]
    exact (Commute.refl s).inv_right
  have hcross : ∀ i j : ℕ, (s * t) ^ i ≠ (s * t) ^ j * s := by
    intro i j heq
    have hs_eq : s = ((s * t) ^ j)⁻¹ * (s * t) ^ i :=
      eq_inv_mul_iff_mul_eq.mpr heq.symm
    have hh : Commute (s * t) s := by
      nth_rw 2 [hs_eq]
      exact (((Commute.refl (s * t)).pow_right j).inv_right).mul_right
        ((Commute.refl (s * t)).pow_right i)
    apply hnc
    change s * t = t * s
    exact (mul_left_cancel (by simpa only [mul_assoc] using hh.eq)).symm
  let f : ℕ → G := fun i ↦
    if i % 2 = 0 then (s * t) ^ (i / 2) else (s * t) ^ (i / 2) * s
  apply exists_cycle_of_sequence (by omega) f
  · simp [f]
  · intro i hi
    by_cases hi0 : i % 2 = 0
    · have his : (i + 1) % 2 ≠ 0 := by omega
      have hid : (i + 1) / 2 = i / 2 := by omega
      simp only [f, hi0, his, hid, ite_true, ite_false]
      rw [mulCayley_adj']
      exact ⟨by simpa using hs1, s, hs, Or.inl rfl⟩
    · have his : (i + 1) % 2 = 0 := by omega
      have hid : (i + 1) / 2 = i / 2 + 1 := by omega
      simp only [f, hi0, his, hid, ite_true, ite_false, pow_succ]
      rw [mulCayley_adj']
      refine ⟨?_, t, ht, Or.inl (mul_assoc _ _ _)⟩
      simpa [← mul_assoc] using ht1
  · intro i hi j hj heq
    have hid : i / 2 < orderOf (s * t) := by omega
    have hjd : j / 2 < orderOf (s * t) := by omega
    by_cases hi0 : i % 2 = 0 <;> by_cases hj0 : j % 2 = 0
    · simp only [f, hi0, hj0, ite_true] at heq
      have := pow_injOn_Iio_orderOf hid hjd heq
      omega
    · simp only [f, hi0, hj0, ite_true, ite_false] at heq
      exact (hcross _ _ heq).elim
    · simp only [f, hi0, hj0, ite_true, ite_false] at heq
      exact (hcross _ _ heq.symm).elim
    · simp only [f, hi0, hj0, ite_false] at heq
      have heqpow := mul_right_cancel heq
      have := pow_injOn_Iio_orderOf hid hjd heqpow
      omega

/-- The pure 2-group case of Corollary 1.4.
Choose distinct noninverse generators. If they commute they give a square;
otherwise their alternating cycle has twice the order of their product. -/
theorem two_group_cayley_contains_two_power_cycle
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G) (S : Set G)
    (hone : (1 : G) ∉ S) (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  classical
  obtain ⟨s, hs⟩ := (Set.ncard_pos (s := S)).mp (show 0 < S.ncard by omega)
  have hpair : ({s, s⁻¹} : Set G).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le s ({s⁻¹} : Set G)
  obtain ⟨t, ht, htout⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({s, s⁻¹} : Set G).ncard < S.ncard by omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htout
  by_cases hcomm : Commute s t
  · obtain ⟨c, hc, hlen⟩ := four_cycle_of_commuting_generators S hs ht
      (fun h ↦ hone (h ▸ hs)) (fun h ↦ hone (h ▸ ht))
      (Ne.symm htout.1) htout.2 hcomm
    exact ⟨2, 1, c, by decide, hc, hlen⟩
  · obtain ⟨v, c, hc, hlen⟩ := alternating_cycle_of_noncommuting_generators S hs ht hcomm
    obtain ⟨n, hn⟩ := hG.exists_orderOf_eq_pow (s * t)
    refine ⟨n + 1, v, c, by omega, hc, ?_⟩
    rw [hlen, hn, pow_succ, Nat.mul_comm]

end CayleyErdősGyárfás
