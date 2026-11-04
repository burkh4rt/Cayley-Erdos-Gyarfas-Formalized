module

public import CayleyErdosGyarfas.AffineModel
public import CayleyErdosGyarfas.CompatibleLifts
public import CayleyErdosGyarfas.CyclicCase
public import CayleyErdosGyarfas.AffineCases

/-! Reduction of the generator images to the three affine constructions. -/

public section

namespace CayleyErdősGyárfás

open scoped IsMulCommutative

/-- A scalar homomorphism with kernel `V` detects equality in the quotient. -/
theorem scalar_eq_iff_quotient_eq
    {G K : Type*} [Group G] [Field K]
    (V : Subgroup G) [V.Normal] (χ : G →* Kˣ) (hker : χ.ker = V) (a b : G) :
    χ a = χ b ↔ (QuotientGroup.mk (s := V) a) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq_iff_div_mem, ← hker]
  change χ a = χ b ↔ χ (a / b) = 1
  rw [map_div, div_eq_one]

/-- In a group of order five the two remaining nontrivial elements are
exactly the square and the inverse square of a chosen generator. -/
theorem square_or_inverse_square_of_card_five
    {Q : Type*} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 5) {a b : Q}
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : b ≠ a) (habi : b ≠ a⁻¹) :
    b = a ^ 2 ∨ b⁻¹ = a ^ 2 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hgen : Subgroup.zpowers a = ⊤ := zpowers_eq_top_of_prime_card hcard ha
  have hoa : orderOf a = 5 := (orderOf_eq_card_of_zpowers_eq_top hgen).trans hcard
  have ha5 : a ^ 5 = 1 := hoa ▸ pow_orderOf_eq_one a
  have hba : b ∈ Subgroup.zpowers a := hgen ▸ Subgroup.mem_top b
  have hfina : IsOfFinOrder a := isOfFinOrder_of_finite a
  have := hfina.mem_zpowers_iff_mem_range_orderOf.mp hba
  obtain ⟨i, hi, hib⟩ := Finset.mem_image.mp this
  have hi5 : i < 5 := by simpa [hoa] using hi
  interval_cases i
  · exact (hb (by simpa using hib.symm)).elim
  · exact (hab (by simpa using hib.symm)).elim
  · exact Or.inl hib.symm
  · right
    apply inv_eq_of_mul_eq_one_right
    rw [← hib, ← pow_add]
    exact ha5
  · exfalso
    apply habi
    apply eq_inv_of_mul_eq_one_left
    rw [← hib, ← pow_succ]
    exact ha5

/-- The three affine generator configurations used in the explicit
constructions. This is proof bookkeeping, not a submission statement. -/
@[expose] def HasNormalizedAffinePair {G : Type*} [Group G]
    (S : Set G) (K : Type*) [Field K] : Prop :=
  ∃ (s t : G) (r : Kˣ) (φ : G →* Equiv.Perm K),
    s ∈ S ∧ t ∈ S ∧ Function.Injective φ ∧ (r : K) ≠ 1 ∧
    (∀ z : K, φ s z = (r : K) * z) ∧
    ((∀ z : K, φ t z = z + 1) ∨
      (∀ z : K, φ t z = (r : K) * z + 1) ∨
      ((r : K) ^ 5 = 1 ∧ ∀ z : K, φ t z = (r : K) ^ 2 * z + 1))

/-- Reduction when the first chosen generator has nontrivial image in the
cyclic quotient. The only distinct-image exception to the quotient square
construction has quotient order five. -/
theorem affine_pair_reduction_of_scalar_ne_one
    {G K : Type*} [Group G] [Finite G] [Field K]
    (S : Set G) (hodd : Odd (Nat.card G))
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (V : Subgroup G) [V.Normal] [IsMulCommutative V] [IsCyclic (G ⧸ V)]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (χ : G →* Kˣ) (hker : χ.ker = V)
    (haffine : ∀ g : G, ∃ a : K, ∀ z : K, φ g z = (χ g : K) * z + a)
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hst : ¬ Commute s t)
    (hpair : Subgroup.closure ({s, t} : Set G) = ⊤)
    (hχs : χ s ≠ 1) : HasSymmetricFigureEight S ∨ HasNormalizedAffinePair S K := by
  classical
  have hrs : (χ s : K) ≠ 1 := fun h ↦ hχs (Units.ext h)
  have hnorm (t' : G) (ht' : t' ∈ S) (hst' : ¬ Commute s t')
      (hcase : χ t' = 1 ∨ χ t' = χ s ∨ ((χ s : K) ^ 5 = 1 ∧ χ t' = χ s ^ 2)) :
      HasNormalizedAffinePair S K := by
    obtain ⟨a, hsa⟩ := haffine s
    obtain ⟨b, htb⟩ := haffine t'
    obtain ⟨ψ, hψ, hψs, hψt⟩ :=
      normalize_two_affine_generators φ hφ s t' (χ s) (χ t') a b hsa htb hrs hst'
    refine ⟨s, t', χ s, ψ, hs, ht', hψ, hrs, hψs, ?_⟩
    rcases hcase with hcase | hcase | ⟨hr5, hcase⟩
    · left
      simpa [hcase] using hψt
    · right; left
      simpa [hcase] using hψt
    · right; right
      exact ⟨hr5, by simpa [hcase] using hψt⟩
  by_cases hχt : χ t = 1
  · exact Or.inr (hnorm t ht hst (Or.inl hχt))
  by_cases heq : χ t = χ s
  · exact Or.inr (hnorm t ht hst (Or.inr (Or.inl heq)))
  have hstinv : ¬ Commute s t⁻¹ := fun h ↦ hst (Commute.inv_right_iff.mp h)
  by_cases heqinv : χ t = (χ s)⁻¹
  · right
    apply hnorm t⁻¹ (hinv t ht) hstinv
    right; left
    simp [heqinv]
  have hqeq := scalar_eq_iff_quotient_eq V χ hker
  have hs1 : (QuotientGroup.mk (s := V) s) ≠ 1 := by
    intro hs1
    apply hχs
    have h := (hqeq s 1).mpr (by simpa using hs1)
    simpa using h
  have ht1 : (QuotientGroup.mk (s := V) t) ≠ 1 := by
    intro ht1
    apply hχt
    have h := (hqeq t 1).mpr (by simpa using ht1)
    simpa using h
  have hts : (QuotientGroup.mk (s := V) t) ≠ QuotientGroup.mk s :=
    fun h ↦ heq ((hqeq t s).mpr h)
  have htsi : (QuotientGroup.mk (s := V) t) ≠ (QuotientGroup.mk s)⁻¹ := by
    intro h
    apply heqinv
    have hh := (hqeq t s⁻¹).mpr (by simpa using h)
    simpa using hh
  by_cases hfive : Nat.card (G ⧸ V) = 5
  · have hs5 : (χ s : K) ^ 5 = 1 := by
      have hpow : (QuotientGroup.mk (s := V) s) ^ 5 = 1 := by
        simpa [hfive] using (pow_card_eq_one' (x := (QuotientGroup.mk (s := V) s)))
      have hh := (hqeq (s ^ 5) 1).mpr (by simpa using hpow)
      have hh' : χ s ^ 5 = 1 := by simpa using hh
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hh'
    obtain hsq | hsq := square_or_inverse_square_of_card_five hfive hs1 ht1 hts htsi
    · right
      apply hnorm t ht hst
      right; right
      refine ⟨hs5, ?_⟩
      have hh := (hqeq t (s ^ 2)).mpr (by simpa using hsq)
      simpa using hh
    · right
      apply hnorm t⁻¹ (hinv t ht) hstinv
      right; right
      refine ⟨hs5, ?_⟩
      have hh := (hqeq t⁻¹ (s ^ 2)).mpr (by simpa using hsq)
      simpa using hh
  · left
    apply symmetric_figure_eight_lifts S hodd V
    apply symmetric_figure_eight_of_two_generators_not_five
      (hodd.of_dvd_nat V.card_quotient_dvd_card) hfive
      ((QuotientGroup.mk (s := V)) '' S \ {1})
      (quotient_generators_inverse_closed S hinv V)
      (a := QuotientGroup.mk s) (b := QuotientGroup.mk t)
      ⟨⟨s, hs, rfl⟩, by simpa using hs1⟩ ⟨⟨t, ht, rfl⟩, by simpa using ht1⟩
      hs1 ht1 (Ne.symm hts) htsi
    rw [← Set.image_pair]
    change Subgroup.closure ((QuotientGroup.mk' V) '' ({s, t} : Set G)) = ⊤
    rw [← MonoidHom.map_closure (QuotientGroup.mk' V), hpair, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr QuotientGroup.mk_surjective

/-- Either the quotient square lifts, or inversions and an interchange of
the two chosen generators put their faithful action into one of the three
affine configurations. -/
theorem affine_pair_reduction
    {G K : Type*} [Group G] [Finite G] [Field K]
    (S : Set G) (hodd : Odd (Nat.card G))
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (V : Subgroup G) [V.Normal] [IsMulCommutative V] [IsCyclic (G ⧸ V)]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (χ : G →* Kˣ) (hker : χ.ker = V)
    (haffine : ∀ g : G, ∃ a : K, ∀ z : K, φ g z = (χ g : K) * z + a)
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hst : ¬ Commute s t)
    (hpair : Subgroup.closure ({s, t} : Set G) = ⊤) :
    HasSymmetricFigureEight S ∨ HasNormalizedAffinePair S K := by
  by_cases hχs : χ s = 1
  · have hχt : χ t ≠ 1 := by
      intro hχt
      have hsV : s ∈ V := hker ▸ hχs
      have htV : t ∈ V := hker ▸ hχt
      exact hst (congrArg Subtype.val (mul_comm (⟨s, hsV⟩ : V) (⟨t, htV⟩ : V)))
    exact affine_pair_reduction_of_scalar_ne_one S hodd hinv V φ hφ χ hker haffine
      ht hs (fun h ↦ hst h.symm) (by simpa [Set.pair_comm] using hpair) hχt
  · exact affine_pair_reduction_of_scalar_ne_one S hodd hinv V φ hφ χ hker haffine
      hs ht hst hpair hχs

/-- Case 3 with the scalar side conditions derived from odd group order. -/
theorem affine_case_three_of_odd_order
    {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : Kˣ) (hr : (r : K) ≠ 1) (h2 : (2 : K) ≠ 0)
    (hsact : ∀ z : K, φ s z = (r : K) * z)
    (htact : ∀ z : K, φ t z = (r : K) * z + 1) :
    HasSymmetricFigureEight S := by
  obtain ⟨hr2, hr4⟩ := scalar_action_square_and_fourth_ne_one hodd φ hφ s (r : K) hsact hr
  let q : K := (r : K)⁻¹
  have hq0 : q ≠ 0 := inv_ne_zero r.ne_zero
  have hq1 : q ≠ 1 := by simpa [q] using hr
  have hq2 : q ^ 2 ≠ 1 := by simpa [q] using hr2
  have hq4 : q ^ 4 ≠ 1 := by simpa [q] using hr4
  have hqminus : q ≠ -1 := by
    intro h
    apply hq2
    rw [h]
    norm_num
  have hqinv : q⁻¹ ≠ q := by
    intro h
    apply hq2
    calc
      q ^ 2 = q * q⁻¹ := by rw [h, pow_two]
      _ = 1 := mul_inv_cancel₀ hq0
  have hsq : q ^ 2 ≠ -1 := by
    intro h
    apply hq4
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h]; norm_num
  exact affine_case_three φ hφ S s t hs ht q hq0 hq1 hqminus hqinv h2 hsq
    (by simpa [q] using hsact) (by simpa [q] using htact)

end CayleyErdősGyárfás
