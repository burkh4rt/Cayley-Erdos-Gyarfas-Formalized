module

public import CayleyErdosGyarfas.BaseCases
public import CayleyErdosGyarfas.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Proved cycle constructions used in the nilpotent reduction. -/

public section

namespace CayleyErdősGyárfás

open SimpleGraph

/-- Distinct, noninverse generators whose product has power-of-two order
produce a power-of-two cycle, whether or not they commute. -/
theorem two_power_cycle_of_generator_product
    {G : Type*} [Group G] [Finite G] (S : Set G) (hone : (1 : G) ∉ S)
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t) (htinv : t ≠ s⁻¹)
    (horder : ∃ k : ℕ, orderOf (s * t) = 2 ^ k) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  by_cases hcomm : Commute s t
  · obtain ⟨c, hc, hlen⟩ := four_cycle_of_commuting_generators S hs ht
      (fun h ↦ hone (h ▸ hs)) (fun h ↦ hone (h ▸ ht)) hst htinv hcomm
    exact ⟨2, 1, c, by decide, hc, hlen⟩
  · obtain ⟨v, c, hc, hlen⟩ := alternating_cycle_of_noncommuting_generators S hs ht hcomm
    obtain ⟨k, hk⟩ := horder
    refine ⟨k + 1, v, c, by omega, hc, ?_⟩
    rw [hlen, hk, pow_succ, Nat.mul_comm]

/-- A square of power-of-two order forces the element itself to have
power-of-two order. -/
theorem orderOf_two_power_of_square
    {G : Type*} [Group G] {s : G} (h : ∃ k : ℕ, orderOf (s * s) = 2 ^ k) :
    ∃ k : ℕ, orderOf s = 2 ^ k := by
  obtain ⟨k, hk⟩ := h
  have hp : s ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ', pow_mul, pow_two, ← hk]
    exact pow_orderOf_eq_one (s * s)
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
    (orderOf_dvd_of_pow_eq_one hp)
  exact ⟨j, hj⟩

/-- The generator-collision case in the manuscript's nilpotent proof.
No oddness assumption on the quotient is needed. -/
theorem two_power_cycle_of_quotient_generator_collision
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hone : (1 : G) ∉ S)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P)
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (heq : (QuotientGroup.mk s : G ⧸ P) = QuotientGroup.mk t) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  have hy : s⁻¹ * t ∈ P := by
    rw [← QuotientGroup.eq_one_iff]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq]
  have ho : ∃ k : ℕ, orderOf (s⁻¹ * t) = 2 ^ k := by
    simpa using hP.exists_orderOf_eq_pow (⟨s⁻¹ * t, hy⟩ : P)
  by_cases hti : t = s⁻¹
  · subst t
    obtain ⟨k, hk⟩ := orderOf_two_power_of_square ho
    have hpos := orderOf_pos s⁻¹
    have hge : 3 ≤ orderOf s⁻¹ := by
      by_contra h
      have hd : orderOf s⁻¹ ∣ 2 := by
        have : orderOf s⁻¹ = 1 ∨ orderOf s⁻¹ = 2 := by omega
        rcases this with h1 | h2
        · rw [h1]; exact one_dvd _
        · rw [h2]
      have hp : s⁻¹ * s⁻¹ = 1 := by
        simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one.mp hd : (s⁻¹) ^ 2 = 1)
      have hi : s⁻¹ = s := by simpa using (eq_inv_of_mul_eq_one_left hp)
      exact hst hi.symm
    obtain ⟨v, c, hc, hlen⟩ := generator_order_cycle S (hinv s hs) hge
    refine ⟨k, v, c, ?_, hc, hlen.trans hk⟩
    have : k ≠ 0 := by
      intro h
      have : orderOf s⁻¹ = 1 := by simpa only [h, pow_zero] using hk
      omega
    omega
  · exact two_power_cycle_of_generator_product S hone (hinv s hs) ht
      (Ne.symm hti) (by simpa using Ne.symm hst) ho

/-- A nontrivial involution is not a translate between two powers of the
product of itself and a conjugate involution. This separates the two fibers
in the four-block construction from the manuscript. -/
theorem involution_commutator_powers_disjoint
    {G : Type*} [Group G] {s t : G} (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    ∀ i j : ℕ, (s * t⁻¹ * s * t) ^ i ≠ (s * t⁻¹ * s * t) ^ j * s := by
  let c := t⁻¹ * s * t
  let x := s * t⁻¹ * s * t
  have hscx : s * c = x := by simp [x, c, mul_assoc]
  have hsxc : s * x = c := by
    rw [← hscx, ← mul_assoc, hs2, one_mul]
  have hc2 : c * c = 1 := calc
    c * c = t⁻¹ * (s * s) * t := by dsimp [c]; group
    _ = 1 := by rw [hs2]; simp
  have hc1 : c ≠ 1 := by
    intro h
    have hh : s = t * c * t⁻¹ := by dsimp [c]; group
    exact hs1 (by simpa [h] using hh)
  intro i j heq
  change x ^ i = x ^ j * s at heq
  have hs_eq : s = (x ^ j)⁻¹ * x ^ i := eq_inv_mul_iff_mul_eq.mpr heq.symm
  have hxs : Commute x s := by
    rw [hs_eq]
    exact (((Commute.refl x).pow_right j).inv_right).mul_right
      ((Commute.refl x).pow_right i)
  have hsc : Commute s c := by
    rw [← hsxc]
    exact (Commute.refl s).mul_right hxs.symm
  have hx2 : x * x = 1 := by
    have h := hsc.mul_pow 2
    rw [hscx] at h
    simpa only [pow_two, hs2, hc2, one_mul] using h
  have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx2).symm
  have hp (n : ℕ) : x ^ n = 1 ∨ x ^ n = x := by
    induction n with
    | zero => exact Or.inl (pow_zero _)
    | succ n ih =>
      rcases ih with h | h
      · exact Or.inr (by rw [pow_succ, h, one_mul])
      · exact Or.inl (by rw [pow_succ, h, hx2])
  have hs_cases : s = 1 ∨ s = x := by
    rcases hp i with hi | hi <;> rcases hp j with hj | hj
    · exact Or.inl (by simpa only [hi, hj, inv_one, one_mul] using hs_eq)
    · exact Or.inr (by simpa only [hi, hj, hxinv, mul_one] using hs_eq)
    · exact Or.inr (by simpa only [hi, hj, inv_one, one_mul] using hs_eq)
    · exact Or.inl (by simpa only [hi, hj, hxinv, hx2] using hs_eq)
  rcases hs_cases with hs | hs
  · exact hs1 hs
  · exact hc1 (by rw [← hsxc, hs, hx2])

/-- An involution in a normal subgroup and a generator outside it produce the
cycle obtained by repeating the four-letter commutator word. -/
theorem involution_commutator_cycle
    {G : Type*} [Group G] [Finite G] (S : Set G) {s t : G}
    (hs : s ∈ S) (ht : t ∈ S) (hti : t⁻¹ ∈ S) (hs1 : s ≠ 1) (hs2 : s * s = 1)
    (P : Subgroup G) [P.Normal] (hsP : s ∈ P) (htP : t ∉ P) :
    ∃ (v : G) (c : (mulCayley S).Walk v v),
      c.IsCycle ∧ c.length = 4 * orderOf (s * t⁻¹ * s * t) := by
  let x := s * t⁻¹ * s * t
  let φ := QuotientGroup.mk' P
  have hφs : φ s = 1 := (QuotientGroup.eq_one_iff s).mpr hsP
  have hφt : φ t ≠ 1 := fun h ↦ htP ((QuotientGroup.eq_one_iff t).mp h)
  have hφti : φ t⁻¹ ≠ 1 := by
    intro h
    exact hφt (by simpa only [map_inv, inv_inv, inv_one] using congrArg Inv.inv h)
  have hφti' : (1 : G ⧸ P) ≠ φ t⁻¹ := Ne.symm hφti
  have hφx : φ x = 1 := by simp [x, map_mul, map_inv, hφs]
  have ht1 : t ≠ 1 := fun h ↦ htP (h ▸ P.one_mem)
  have hti1 : t⁻¹ ≠ 1 := by
    intro h
    exact ht1 (by simpa only [inv_inv, inv_one] using congrArg Inv.inv h)
  have hcross : ∀ i j : ℕ, x ^ i ≠ x ^ j * s := involution_commutator_powers_disjoint hs1 hs2
  have hpos := orderOf_pos x
  let f : ℕ → G := fun i ↦
    if i % 4 = 0 then x ^ (i / 4)
    else if i % 4 = 1 then x ^ (i / 4) * s
    else if i % 4 = 2 then x ^ (i / 4) * s * t⁻¹
    else x ^ (i / 4 + 1) * t⁻¹
  have hadj (v : G) {u : G} (hu : u ∈ S) (hu1 : u ≠ 1) :
      (mulCayley S).Adj v (v * u) := by
    apply (mulCayley_adj' _ _ _).mpr
    exact ⟨by simpa using hu1, u, hu, Or.inl rfl⟩
  apply exists_cycle_of_sequence (n := 4 * orderOf x) (by omega) f
  · simp [f]
  · intro i hi
    have hri : i % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases ri : i % 4
    · have his : (i + 1) % 4 = 1 := by omega
      have hid : (i + 1) / 4 = i / 4 := by omega
      simpa [f, ri, his, hid] using hadj (x ^ (i / 4)) hs hs1
    · have his : (i + 1) % 4 = 2 := by omega
      have hid : (i + 1) / 4 = i / 4 := by omega
      simpa [f, ri, his, hid] using hadj (x ^ (i / 4) * s) hti hti1
    · have his : (i + 1) % 4 = 3 := by omega
      have hid : (i + 1) / 4 = i / 4 := by omega
      simpa [f, ri, his, hid, pow_succ, x, mul_assoc] using hadj (x ^ (i / 4) * s * t⁻¹) hs hs1
    · have his : (i + 1) % 4 = 0 := by omega
      have hid : (i + 1) / 4 = i / 4 + 1 := by omega
      simpa [f, ri, his, hid, mul_assoc] using hadj (x ^ (i / 4 + 1) * t⁻¹) ht ht1
  · intro i hi j hj heq
    have hid : i / 4 < orderOf x := by omega
    have hjd : j / 4 < orderOf x := by omega
    have hri : i % 4 < 4 := Nat.mod_lt _ (by decide)
    have hrj : j % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases ri : i % 4 <;> interval_cases rj : j % 4
    all_goals simp [f, ri, rj] at heq
    all_goals try { have hq := congrArg φ heq
                    simp only [map_mul, map_pow, hφx, hφs, one_pow, one_mul,
                      hφti, hφti'] at hq }
    all_goals try exact (hcross _ _ heq).elim
    all_goals try exact (hcross _ _ heq.symm).elim
    all_goals
      have heqpow : x ^ (i / 4) = x ^ (j / 4) := by
        first | exact heq | exact mul_right_cancel heq |
          exact mul_right_cancel (mul_right_cancel heq) |
          exact mul_right_cancel (b := x) (by simpa only [pow_succ] using heq)
      have := pow_injOn_Iio_orderOf hid hjd heqpow
      omega


/-- A generator in a proper normal 2-subgroup gives a power-of-two cycle:
either its own order is at least four, or an involution commutator supplies one. -/
theorem two_power_cycle_of_kernel_generator
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P) (hPtop : P ≠ ⊤)
    {s : G} (hs : s ∈ S) (hsP : s ∈ P) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  have hs1 : s ≠ 1 := fun h ↦ hone (h ▸ hs)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf s = 2 ^ k := by
    simpa using hP.exists_orderOf_eq_pow (⟨s, hsP⟩ : P)
  by_cases hge : 3 ≤ orderOf s
  · obtain ⟨v, c, hc, hlen⟩ := generator_order_cycle S hs hge
    refine ⟨k, v, c, ?_, hc, hlen.trans hk⟩
    have : k ≠ 0 := by
      intro h
      have : orderOf s = 1 := by simpa only [h, pow_zero] using hk
      omega
    omega
  · have hpos := orderOf_pos s
    have hne : orderOf s ≠ 1 := by simpa using hs1
    have ho : orderOf s = 2 := by omega
    have hs2 : s * s = 1 := by simpa only [ho, pow_two] using pow_orderOf_eq_one s
    obtain ⟨t, ht, htP⟩ : ∃ t ∈ S, t ∉ P := by
      by_contra h
      push Not at h
      have hle : Subgroup.closure S ≤ P := (Subgroup.closure_le P).mpr h
      rw [hgen] at hle
      exact hPtop (top_le_iff.mp hle)
    obtain ⟨v, c, hc, hlen⟩ := involution_commutator_cycle S hs ht (hinv t ht)
      hs1 hs2 P hsP htP
    have hxP : s * t⁻¹ * s * t ∈ P := by
      rw [← QuotientGroup.eq_one_iff]
      have hφs : (QuotientGroup.mk s : G ⧸ P) = 1 :=
        (QuotientGroup.eq_one_iff s).mpr hsP
      simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hφs]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, orderOf (s * t⁻¹ * s * t) = 2 ^ j := by
      simpa using hP.exists_orderOf_eq_pow (⟨s * t⁻¹ * s * t, hxP⟩ : P)
    refine ⟨j + 2, v, c, by omega, hc, ?_⟩
    rw [hlen, hj, pow_add]
    simp [Nat.mul_comm]


universe u

/-- The nilpotent corollary reduces to the odd-order theorem via a normal
Sylow 2-subgroup. The odd-order theorem is an explicit parameter, so this
helper records exactly the remaining dependency of the corollary. -/


theorem nilpotent_cycle_of_odd_order_theorem
    (hoddTheorem : ∀ {H : Type u} [Group H] [Finite H] (T : Set H),
      Odd (Nat.card H) → (∀ t ∈ T, t⁻¹ ∈ T) → (1 : H) ∉ T →
      Subgroup.closure T = ⊤ → 3 ≤ T.ncard →
      ∃ (n : ℕ) (v : H) (c : (mulCayley T).Walk v v),
        1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n)
    {G : Type u} [Group G] [Finite G] [Group.IsNilpotent G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤) (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  classical
  let P : Sylow 2 G := Classical.arbitrary _
  let N : Subgroup G := P
  have hN : IsPGroup 2 N := P.isPGroup'
  by_cases hNtop : N = ⊤
  · have hsurj : Function.Surjective N.subtype := by
      intro g
      exact ⟨⟨g, by rw [hNtop]; trivial⟩, rfl⟩
    exact two_group_cayley_contains_two_power_cycle (hN.of_surjective N.subtype hsurj) S hone hcard
  by_cases hkernel : ∃ s ∈ S, s ∈ N
  · obtain ⟨s, hs, hsN⟩ := hkernel
    exact two_power_cycle_of_kernel_generator S hinv hone hgen N hN hNtop hs hsN
  let φ := QuotientGroup.mk' N
  by_cases hinj : Set.InjOn φ S
  · let T : Set (G ⧸ N) := φ '' S \ {1}
    have hφone : (1 : G ⧸ N) ∉ φ '' S := by
      rintro ⟨s, hs, hsφ⟩
      exact hkernel ⟨s, hs, (QuotientGroup.eq_one_iff s).mp hsφ⟩
    have hTeq : T = φ '' S := by
      ext q
      simp only [T, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · exact And.left
      · intro hq
        exact ⟨hq, fun heq ↦ hφone (heq ▸ hq)⟩
    have hTcard : 3 ≤ T.ncard := by rw [hTeq, hinj.ncard_image]; exact hcard
    have hTgen : Subgroup.closure T = ⊤ := by
      rw [hTeq, ← MonoidHom.map_closure, hgen, Subgroup.map_top]
      exact φ.range_eq_top_of_surjective (QuotientGroup.mk'_surjective N)
    have hTinv : ∀ t ∈ T, t⁻¹ ∈ T := quotient_generators_inverse_closed S hinv N
    have hTone : (1 : G ⧸ N) ∉ T := by simp [T]
    have hodd : Odd (Nat.card (G ⧸ N)) := by
      apply Nat.not_even_iff_odd.mp
      rw [even_iff_two_dvd, ← Subgroup.index_eq_card]
      exact P.not_dvd_index
    exact two_power_cycle_lifts S N hN (hoddTheorem T hodd hTinv hTone hTgen hTcard)
  · have hcollision : ∃ s ∈ S, ∃ t ∈ S, s ≠ t ∧ φ s = φ t := by
      simpa only [Set.InjOn, not_forall, exists_prop, not_imp, and_assoc,
        and_left_comm, and_comm] using hinj
    obtain ⟨s, hs, t, ht, hst, heq⟩ := hcollision
    exact two_power_cycle_of_quotient_generator_collision S hinv hone N hN hs ht hst heq


end CayleyErdősGyárfás
