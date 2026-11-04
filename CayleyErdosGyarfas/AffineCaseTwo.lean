module

public import CayleyErdosGyarfas.AffineCases
public import CayleyErdosGyarfas.AffineModel
public import CayleyErdosGyarfas.CaseTwoCoordinates

/-!
# The exceptional cyclic quotient of order five

The sixteen letters below are exactly the manuscript's word for `β`.
`CaseTwoCoordinates` verifies its vertex coordinates and their intersections.
The polynomial `19*r^2-r+19` records the possible extra intersections; explicit
integer identities show that at least one of the scalars `r` and `r^2` avoids
these intersections. The latter corresponds to the manuscript's replacement
of `(s,t)` by `(t,s⁻¹)`.
-/

public section

namespace CayleyErdősGyárfás

private theorem fifth_scalar_data {K : Type*} [Field K] (r : K)
    (hr : r ≠ 1) (hr5 : r^5 = 1) :
    orderOf r = 5 ∧ r ≠ 0 ∧ r^4+r^3+r^2+r+1 = 0 ∧ (5:K) ≠ 0 := by
  have hord : orderOf r = 5 := by
    have hd := orderOf_dvd_of_pow_eq_one hr5
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact (hr (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr5
  have hC : r^4+r^3+r^2+r+1 = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hr)
    linear_combination hr5
  refine ⟨hord, hr0, hC, ?_⟩
  intro hfive
  have hzero : (r-1)^4 = 0 := by
    linear_combination hC - r*(r^2-r+1)*hfive
  exact hr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero))

private theorem fifth_scalar_indicator_alternative {K : Type*} [Field K] (r : K)
    (hC : r^4+r^3+r^2+r+1 = 0) :
    19*r^2-r+19 ≠ 0 ∨ 19*(r^2)^2-r^2+19 ≠ 0 := by
  by_contra! h
  have hP := h.1
  have hQ : -19*r^3-20*r^2-19*r = 0 := by linear_combination h.2 - 19*hC
  have ha : (341:K) = 0 := by
    linear_combination (19*r+360)*hC + (-r^3-20*r^2-20*r-1)*hP
  have hb : (7581:K) = 0 := by
    linear_combination (19*r^2+381*r+399)*hP + (19*r+360)*hQ
  have hfalse : (1:K) = 0 := by linear_combination 1823*ha - 82*hb
  exact one_ne_zero hfalse

set_option maxHeartbeats 2000000 in
private theorem affine_case_two_good_scalar {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : K) (hr : r ≠ 1) (hr5 : r^5 = 1) (h2 : (2:K) ≠ 0)
    (hP : 19*r^2-r+19 ≠ 0)
    (hsact : ∀ z, φ s z = r*z) (htact : ∀ z, φ t z = r^2*z+1) :
    HasSymmetricFigureEight S := by
  obtain ⟨horder, hr0, hC, h5⟩ := fifth_scalar_data r hr hr5
  obtain ⟨hcoords_inj, hcoords_inter⟩ := caseTwo_coordinates r horder hC h2 h5 hP
  have hir : r⁻¹ = r^4 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_succ'] using hr5
  have hir2 : (r^2)⁻¹ = r^3 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [← pow_add] using hr5
  have hsinv : ∀ z, φ s⁻¹ z = r^4*z := by
    intro z
    simpa [hir] using affine_inv_apply φ hr0
      (fun z ↦ show φ s z = r*z+0 by simpa using hsact z) z
  have htinv : ∀ z, φ t⁻¹ z = r^3*(z-1) := by
    intro z
    simpa [hir2] using affine_inv_apply φ (pow_ne_zero 2 hr0) htact z
  have hp5 : r^5 = 1 := by
    simpa [horder] using (pow_mod_orderOf r 5).symm
  have hp6 : r^6 = r := by
    simpa [horder] using (pow_mod_orderOf r 6).symm
  have hp10 : r^10 = 1 := by
    simpa [horder] using (pow_mod_orderOf r 10).symm
  have hp11 : r^11 = r := by
    simpa [horder] using (pow_mod_orderOf r 11).symm
  let letters : ℕ → G
    | 0 => s
    | 1 => t
    | 2 => s
    | 3 => s
    | 4 => s
    | 5 => t⁻¹
    | 6 => s
    | 7 => t
    | 8 => s
    | 9 => t⁻¹
    | 10 => s
    | 11 => s
    | 12 => s
    | 13 => t
    | 14 => s
    | 15 => t⁻¹
    | _ => 1
  let f (i : ℕ) : G := (List.ofFn (fun j : Fin i ↦ letters j)).prod
  let e : ℕ → ℕ := caseTwoExponent
  let b : ℕ → K := caseTwoOffset r
  have hstep (i : ℕ) : f (i+1) = f i * letters i := by
    simp only [f, List.ofFn_succ', List.prod_concat]
    rfl
  have haction : ∀ i < 17, ∀ z : K, φ (f i) z = r^(e i)*z+b i := by
    intro i
    induction i with
    | zero =>
      intro hi z
      simp [f, e, b, caseTwoExponent, caseTwoOffset]
    | succ i ih =>
      intro hi z
      rw [hstep, affine_mul_apply, ih (by omega)]
      have hi16 : i < 16 := by omega
      interval_cases i <;>
        simp only [letters, e, b, caseTwoExponent, caseTwoOffset,
          hsact, htact, htinv] <;> ring_nf
      all_goals (try simp only [hp5, hp6])
      all_goals ring
  have hinj : ∀ i < 16, ∀ j < 16, f i = f j → i = j := by
    intro i hi j hj hij
    have hh : r^(e i) = r^(e j) ∧ b i = b j :=
      affine_eq_coeffs (a := r^(e i)) (b := b i) (c := r^(e j)) (d := b j)
        (fun z ↦ by rw [← haction i (by omega), hij, haction j (by omega)])
    exact congrArg Fin.val (hcoords_inj (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩)
      (Prod.ext hh.1 hh.2))
  have hclose : f 16 = f 0 := by
    apply hφ
    ext z
    simp [haction, e, b, caseTwoExponent, caseTwoOffset]
  have hadj (i : ℕ) (hi : i < 16) :
      (SimpleGraph.mulCayley S).Adj (f i) (f (i+1)) := by
    have hne : f i ≠ f (i+1) := by
      intro h
      by_cases hi15 : i = 15
      · have hh := hinj 15 (by omega) 0 (by omega) (by simpa [hi15, hclose] using h)
        omega
      · have hh := hinj i hi (i+1) (by omega) h
        omega
    have hstep : f (i+1) = f i * letters i := by
      simp only [f, List.ofFn_succ', List.prod_concat]
      rfl
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨hne, ?_⟩
    rw [hstep]
    interval_cases i <;> simp only [letters]
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inr (by simp)⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inr (by simp)⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inr (by simp)⟩
  obtain ⟨c, hc, hlen, hsupport⟩ := exists_cycle_of_sequence_with_support
    (n := 16) (by decide) f hclose hadj hinj
  let L : List (K × K) := List.ofFn (fun i : Fin 16 ↦ (r^(e i),b i))
  have hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2 := by
    intro x hx
    rw [hsupport, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    by_cases hi : i.val < 16
    · exact ⟨(r^(e i),b i), List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩,
        haction i (by omega)⟩
    · have hi16 : i.val = 16 := by omega
      refine ⟨(1,0), List.mem_ofFn.mpr ⟨⟨0,by decide⟩,by simp [e,b,caseTwoExponent,caseTwoOffset]⟩, ?_⟩
      intro z
      rw [haction i i.isLt, hi16]
      simp [e,b,caseTwoExponent,caseTwoOffset]
  have hmember (i : ℕ) (hi : i < 17) : f i ∈ c.support := by
    rw [hsupport]
    exact List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩
  have hf0 : f 0 = 1 := by simp [f]
  let c' := c.copy hf0 hf0
  have hc' : c'.IsCycle := by simpa [c'] using hc
  have hlen' : c'.length = 2^4 := by simpa [c'] using hlen
  apply figureEight_of_affine_coordinate_intersection_general φ hφ S c' 4
    (by decide) hc' hlen' L
    (by simpa [c'] using hvertices)
    (t*s⁻¹*s⁻¹) (f 14) (f 1) 1 1 r 1
  · intro z
    simp only [affine_mul_apply, hsinv, htact]
    ring_nf
    simp only [hp10]
    ring
  · intro z
    rw [haction 14 (by decide)]
    simp [e,b,caseTwoExponent,caseTwoOffset]
  · simpa [c'] using hmember 14 (by decide)
  · simpa [c'] using hmember 1 (by decide)
  · apply hφ
    ext z
    simp only [affine_mul_apply, hsinv, htact]
    rw [haction 1 (by decide), haction 14 (by decide)]
    simp only [e,b,caseTwoExponent,caseTwoOffset]
    ring_nf
    simp only [hp11]
  · intro p hp q hq heq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hcoords_inter i j (by simpa only [one_mul] using heq)

/-- The manuscript's second affine case, where the two images in the
cyclic quotient of order five are distinct and not inverse. The two candidate
sixteen-cycles are the stated word and the word obtained by replacing
`(s,t)` with `(t,s⁻¹)`. -/
theorem affine_case_two {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S) (hsi : s⁻¹ ∈ S)
    (r : Kˣ) (hr : (r:K) ≠ 1) (hr5 : (r:K)^5 = 1) (h2 : (2:K) ≠ 0)
    (hsact : ∀ z, φ s z = (r:K)*z)
    (htact : ∀ z, φ t z = (r:K)^2*z+1) :
    HasSymmetricFigureEight S := by
  obtain ⟨horder, hr0, hC, h5⟩ := fifth_scalar_data (r:K) hr hr5
  rcases fifth_scalar_indicator_alternative (r:K) hC with hP | hP
  · exact affine_case_two_good_scalar φ hφ S s t hs ht (r:K) hr hr5 h2 hP hsact htact
  · have hr2 : (r:K)^2 ≠ 1 := by
      intro h
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [horder] at hd
      norm_num at hd
    have hsinv : ∀ z, φ s⁻¹ z = (r:K)⁻¹*z := by
      intro z
      simpa using affine_inv_apply φ hr0
        (fun z ↦ show φ s z = (r:K)*z+0 by simpa using hsact z) z
    have hnoncomm : ¬ Commute t s⁻¹ := by
      intro h
      have hh := congrArg (fun g ↦ φ g 0) h.eq
      simp only [affine_mul_apply, htact, hsinv, mul_zero, zero_add,
        mul_one] at hh
      exact hr (inv_eq_one.mp hh.symm)
    obtain ⟨ψ, hψ, hsnew, htnew⟩ := normalize_two_affine_generators
      φ hφ t s⁻¹ (r^2) r⁻¹ 1 0
      (by simpa using htact) (by simpa using hsinv)
      (by simpa using hr2) hnoncomm
    have hrnew5 : ((r:K)^2)^5 = 1 := by
      calc
        ((r:K)^2)^5 = ((r:K)^5)^2 := by ring
        _ = 1 := by rw [hr5]; simp
    have hir : (r:K)⁻¹ = (r:K)^4 := by
      apply inv_eq_of_mul_eq_one_right
      simpa [pow_succ'] using hr5
    apply affine_case_two_good_scalar ψ hψ S t s⁻¹ ht hsi ((r:K)^2)
      hr2 hrnew5 h2 hP
    · simpa using hsnew
    · intro z
      simpa only [Units.val_inv_eq_inv_val, hir, ← pow_mul] using htnew z

end CayleyErdősGyárfás
