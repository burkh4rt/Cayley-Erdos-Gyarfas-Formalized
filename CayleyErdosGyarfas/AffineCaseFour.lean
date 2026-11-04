module

public import CayleyErdosGyarfas.AffineCases
public import CayleyErdosGyarfas.AffineModel

/-! The fourth affine case: one generator is a translation. -/

public section

namespace CayleyErdősGyárfás


theorem caseFour_good_translate {K : Type*} [Field K] (r : K)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (h2 : (2 : K) ≠ 0)
    (hneg : ∀ k : ℕ, r ^ k ≠ -1) :
    (2*r ≠ 1 ∧ r ≠ -2 ∧ r^2+r ≠ 1 ∧ r^2+2*r ≠ 1) ∨
    (2*r ≠ -1 ∧ r ≠ 2 ∧ r^2-r ≠ 1 ∧ r^2-2*r ≠ 1) ∨
    ((7 : K) = 0 ∧ (r = 2 ∨ 2*r = 1)) := by
  by_cases hplus : 2*r ≠ 1 ∧ r ≠ -2 ∧ r^2+r ≠ 1 ∧ r^2+2*r ≠ 1
  · exact Or.inl hplus
  by_cases hminus : 2*r ≠ -1 ∧ r ≠ 2 ∧ r^2-r ≠ 1 ∧ r^2-2*r ≠ 1
  · exact Or.inr (Or.inl hminus)
  right; right
  simp only [not_and_or, not_not] at hplus hminus
  rcases hplus with hp | hp | hp | hp <;>
    rcases hminus with hm | hm | hm | hm
  · exact (h2 (by linear_combination hm-hp)).elim
  · exact (hneg 1 (by linear_combination hp-hm)).elim
  · exact (hneg 2 (by linear_combination r*hp-hm)).elim
  · exact ⟨by linear_combination (2*r-3)*hp-4*hm, Or.inr hp⟩
  · exact (hr1 (by linear_combination hm-hp)).elim
  · have h4 : (2 : K)*2 = 0 := by linear_combination hp-hm
    exact (mul_ne_zero h2 h2 h4).elim
  · exact (hneg 2 (by linear_combination hp+hm)).elim
  · exact (hneg 3 (by linear_combination (r^2-r)*hp-hm)).elim
  · exact (hneg 2 (by linear_combination -hp+r*hm)).elim
  · exact (hneg 2 (by linear_combination hp-hm)).elim
  · have h : (2 : K)*r = 0 := by linear_combination hp-hm
    exact (mul_ne_zero h2 hr0 h).elim
  · exact (hneg 4 (by linear_combination (r^2-1)*hp-r*hm)).elim
  · exact (hneg 3 (by linear_combination r*hp+(1-r)*hm)).elim
  · exact ⟨by linear_combination hp-(r+4)*hm, Or.inl hm⟩
  · exact (hneg 4 (by linear_combination (r^2-1)*hp-2*r*hm)).elim
  · have h : (2 : K)*2*r = 0 := by linear_combination hp-hm
    exact (mul_ne_zero (mul_ne_zero h2 h2) hr0 h).elim


set_option maxRecDepth 2000 in
theorem caseFour_translate_plus {K : Type*} [Field K] (r : K)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrminus : r ≠ -1)
    (hrsq : r^2 ≠ 1) (h2 : (2:K) ≠ 0)
    (hbad1 : 2*r ≠ 1) (hbad2 : r ≠ -2)
    (hbad3 : r^2+r ≠ 1) (hbad4 : r^2+2*r ≠ 1)
    (x y : K × K)
    (hx : x ∈ [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)])
    (hy : y ∈ [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)])
    (heq : (r*y.1,r+r*y.2) = x) : x = (r,r) := by
  have hrsqr : r*r ≠ r := by
    intro h
    exact hr1 (mul_left_cancel₀ hr0 (by simpa using h))
  have hrsq' : r*r ≠ 1 := by simpa [pow_two] using hrsq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq, mul_one, mul_zero] at heq ⊢ <;>
    simp only [true_and, false_and, hr1, hrsq', hrsqr] at heq
  all_goals first
    | rfl
    | exact (hr0 (by linear_combination heq)).elim
    | exact (hr0 (by linear_combination -heq)).elim
    | exact (hr1 (by linear_combination heq)).elim
    | exact (hr1 (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination heq)).elim
    | exact (hbad3 (by linear_combination heq)).elim
    | exact (hbad4 (by linear_combination heq)).elim
    | exact (hrsq (by linear_combination heq)).elim
    | exact (hrminus (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hrminus (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hbad2 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (zero_ne_one (by linear_combination heq)).elim
set_option maxRecDepth 2000 in
theorem caseFour_translate_minus {K : Type*} [Field K] (r : K)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrminus : r ≠ -1)
    (hrsq : r^2 ≠ 1) (h2 : (2:K) ≠ 0)
    (hbad1 : 2*r ≠ -1) (hbad2 : r ≠ 2)
    (hbad3 : r^2-r ≠ 1) (hbad4 : r^2-2*r ≠ 1)
    (x y : K × K)
    (hx : x ∈ [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)])
    (hy : y ∈ [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)])
    (heq : (r*y.1,-r+r*y.2) = x) : x = (r,0) := by
  have hrsqr : r*r ≠ r := by
    intro h
    exact hr1 (mul_left_cancel₀ hr0 (by simpa using h))
  have hrsq' : r*r ≠ 1 := by simpa [pow_two] using hrsq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq, mul_one, mul_zero] at heq ⊢ <;>
    simp only [true_and, false_and, hr1, hrsq', hrsqr] at heq
  all_goals first
    | rfl
    | exact (hr0 (by linear_combination heq)).elim
    | exact (hr0 (by linear_combination -heq)).elim
    | exact (hr1 (by linear_combination heq)).elim
    | exact (hr1 (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination heq)).elim
    | exact (hbad3 (by linear_combination heq)).elim
    | exact (hbad4 (by linear_combination heq)).elim
    | exact (hrsq (by linear_combination heq)).elim
    | exact (hrminus (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hrminus (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hbad2 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (zero_ne_one (by linear_combination heq)).elim
    | exact (zero_ne_one (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination -heq)).elim
    | exact (hbad2 (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hr1 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hrminus (by linear_combination heq)).elim
    | exact (hrminus (by linear_combination -heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ h2; linear_combination -heq)).elim

set_option maxRecDepth 2000 in
theorem caseFour_cycle {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : K) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrminus : r ≠ -1)
    (hsact : ∀ z, φ s z = r*z) (htact : ∀ z, φ t z = z+1) :
    ∃ c : (SimpleGraph.mulCayley S).Walk 1 1,
      c.IsCycle ∧ c.length = 8 ∧
      c.support = [1,t,t*s,t*s*t,t*s*t*s⁻¹,s*t*s⁻¹,s*t,s,1] := by
  let f : ℕ → G
    | 0 => 1 | 1 => t | 2 => t*s | 3 => t*s*t
    | 4 => t*s*t*s⁻¹ | 5 => s*t*s⁻¹
    | 6 => s*t | 7 => s | _ => 1
  let v : ℕ → K × K
    | 0 => (1,0) | 1 => (1,1) | 2 => (r,1) | 3 => (r,1+r)
    | 4 => (1,1+r) | 5 => (1,r) | 6 => (r,r) | 7 => (r,0)
    | _ => (1,0)
  have hsinv : ∀ z, φ s⁻¹ z = r⁻¹*z := by
    intro z
    simpa using affine_inv_apply φ hr0
      (fun z ↦ show φ s z = r*z+0 by simpa using hsact z) z
  have haction (i : ℕ) (hi : i < 9) (z : K) :
      φ (f i) z = (v i).1*z+(v i).2 := by
    interval_cases i <;>
      simp only [f, v, affine_mul_apply, hsinv, hsact, htact, map_one,
        Equiv.Perm.one_apply, one_mul, add_zero] <;>
      field_simp <;> ring
  have hinj : ∀ i < 8, ∀ j < 8, f i = f j → i = j := by
    intro i hi j hj hij
    have hh : v i = v j := by
      apply Prod.ext
      · exact (affine_eq_coeffs (fun z ↦ by rw [← haction i (by omega), hij,
          haction j (by omega)])).1
      · exact (affine_eq_coeffs (fun z ↦ by rw [← haction i (by omega), hij,
          haction j (by omega)])).2
    interval_cases i <;> interval_cases j <;> try rfl
    all_goals simp only [v, Prod.mk.injEq] at hh
    all_goals simp only [hr1, hr1.symm,
      false_and, true_and, and_false, zero_ne_one, one_ne_zero] at hh
    all_goals first
      | contradiction
      | exact (hr0 (by linear_combination hh)).elim
      | exact (hr0 (by linear_combination -hh)).elim
      | exact (hr1 (by linear_combination hh)).elim
      | exact (hr1 (by linear_combination -hh)).elim
      | exact (hrminus (by linear_combination hh)).elim
      | exact (hrminus (by linear_combination -hh)).elim
      | exact (zero_ne_one (by linear_combination hh)).elim
      | exact (zero_ne_one (by linear_combination -hh)).elim
  have hadj (i : ℕ) (hi : i < 8) :
      (SimpleGraph.mulCayley S).Adj (f i) (f (i+1)) := by
    have hne : f i ≠ f (i+1) := by
      intro heq
      by_cases hi7 : i = 7
      · have hh := hinj 7 (by omega) 0 (by omega) (by simpa [hi7, f] using heq)
        omega
      · have hh := hinj i hi (i+1) (by omega) heq
        omega
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨hne, ?_⟩
    interval_cases i
    · exact ⟨t, ht, Or.inl (by simp [f])⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inr (by simp [f])⟩
    · refine ⟨t, ht, Or.inr ?_⟩
      apply hφ
      ext z
      simp only [f, affine_mul_apply, hsinv, hsact, htact]
      field_simp
      ring
    · exact ⟨s, hs, Or.inl (by simp [f, mul_assoc])⟩
    · exact ⟨t, ht, Or.inr rfl⟩
    · exact ⟨s, hs, Or.inr (by simp [f])⟩
  obtain ⟨c, hc, hlen, hsupport⟩ := exists_cycle_of_sequence_with_support
    (n := 8) (by decide) f rfl hadj hinj
  refine ⟨c, hc, hlen, ?_⟩
  simpa [f, List.ofFn_succ] using hsupport






set_option maxRecDepth 2000 in
theorem caseFour_exception {G K : Type*} [Group G] [Field K] [CharP K 7]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (hsact : ∀ z, φ s z = 2*z) (htact : ∀ z, φ t z = z+1) :
    HasSymmetricFigureEight S := by
  have h2 : (2:K) ≠ 0 := fun h ↦ by
    have hh := (CharP.cast_eq_zero_iff K 7 2).mp h
    norm_num at hh
  have h2inv : (2:K)⁻¹ = 4 := by
    apply inv_eq_of_mul_eq_one_right
    reduce_mod_char!
  have hsinv : ∀ z, φ s⁻¹ z = 4*z := by
    intro z
    simpa [h2inv] using affine_inv_apply φ h2
      (fun z ↦ show φ s z = 2*z+0 by simpa using hsact z) z
  have htrans (n : ℕ) (z : K) : φ (t^n) z = z+n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', affine_mul_apply, htact, ih, Nat.cast_add, Nat.cast_one]
      ring
  let f : ℕ → G
    | 0 => 1 | 1 => t | 2 => t^2 | 3 => t^3 | 4 => t^4 | 5 => t^5
    | 6 => t^5*s | 7 => t^5*s*t | _ => 1
  let v : ℕ → K × K
    | 0 => (1,0) | 1 => (1,1) | 2 => (1,2) | 3 => (1,3) | 4 => (1,4)
    | 5 => (1,5) | 6 => (2,5) | 7 => (2,0) | _ => (1,0)
  have haction (i : ℕ) (hi : i < 9) (z : K) :
      φ (f i) z = (v i).1*z+(v i).2 := by
    interval_cases i
    all_goals simp only [f, v, affine_mul_apply, hsact, htact, htrans, map_one,
      Equiv.Perm.one_apply, one_mul, add_zero, Nat.cast_ofNat]
    all_goals ring_nf
    all_goals reduce_mod_char!
  have hinj : ∀ i < 8, ∀ j < 8, f i = f j → i = j := by
    intro i hi j hj hij
    have hh : v i = v j := by
      apply Prod.ext
      · exact (affine_eq_coeffs (fun z ↦ by rw [← haction i (by omega), hij,
          haction j (by omega)])).1
      · exact (affine_eq_coeffs (fun z ↦ by rw [← haction i (by omega), hij,
          haction j (by omega)])).2
    interval_cases i <;> interval_cases j <;> try rfl
    all_goals simp only [v, Prod.mk.injEq] at hh
    all_goals obtain ⟨hha, hhb⟩ := hh
    all_goals solve
      | have hz := sub_eq_zero.mpr hha
        reduce_mod_char! at hz
        first
        | exact (one_ne_zero hz).elim
        | have hn := (CharP.cast_eq_zero_iff K 7 _).mp hz
          norm_num at hn
      | have hz := sub_eq_zero.mpr hhb
        reduce_mod_char! at hz
        first
        | exact (one_ne_zero hz).elim
        | have hn := (CharP.cast_eq_zero_iff K 7 _).mp hz
          norm_num at hn
  have hadj (i : ℕ) (hi : i < 8) :
      (SimpleGraph.mulCayley S).Adj (f i) (f (i+1)) := by
    have hne : f i ≠ f (i+1) := by
      intro heq
      by_cases hi7 : i = 7
      · have hh := hinj 7 (by omega) 0 (by omega) (by simpa [hi7, f] using heq)
        omega
      · have hh := hinj i hi (i+1) (by omega) heq
        omega
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨hne, ?_⟩
    interval_cases i
    · exact ⟨t, ht, Or.inl (by simp [f])⟩
    · exact ⟨t, ht, Or.inl (by simp [f, pow_succ])⟩
    · exact ⟨t, ht, Or.inl (by simp [f, pow_succ])⟩
    · exact ⟨t, ht, Or.inl (by simp [f, pow_succ])⟩
    · exact ⟨t, ht, Or.inl (by simp [f, pow_succ])⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · refine ⟨s, hs, Or.inr ?_⟩
      apply hφ
      ext z
      simp only [f, affine_mul_apply, hsact, htact, htrans, map_one,
        Equiv.Perm.one_apply, Nat.cast_ofNat]
      ring_nf
      reduce_mod_char!
  obtain ⟨c, hc, hlen, hsupport⟩ := exists_cycle_of_sequence_with_support
    (n := 8) (by decide) f rfl hadj hinj
  have hsupp : c.support = [1,t,t^2,t^3,t^4,t^5,t^5*s,t^5*s*t,1] := by
    simpa [f, List.ofFn_succ] using hsupport
  let L : List (K × K) := [(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,0)]
  have hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2 := by
    intro x hx
    rw [hsupp] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact ⟨v 0, by simp [v, L], haction 0 (by decide)⟩
      | exact ⟨v 1, by simp [v, L], haction 1 (by decide)⟩
      | exact ⟨v 2, by simp [v, L], haction 2 (by decide)⟩
      | exact ⟨v 3, by simp [v, L], haction 3 (by decide)⟩
      | exact ⟨v 4, by simp [v, L], haction 4 (by decide)⟩
      | exact ⟨v 5, by simp [v, L], haction 5 (by decide)⟩
      | exact ⟨v 6, by simp [v, L], haction 6 (by decide)⟩
      | exact ⟨v 7, by simp [v, L], haction 7 (by decide)⟩
  have hs_eq : t^5*s*t = s := by
    apply hφ
    ext z
    rw [hsact]
    simpa only [f, v, add_zero] using haction 7 (by decide) z
  apply figureEight_of_affine_coordinate_intersection_general φ hφ S c 3 (by decide)
    hc (by simpa using hlen) L hvertices s s 1 2 0 2 0
  · simpa using hsact
  · simpa using hsact
  · rw [← hs_eq]; simp [hsupp]
  · simp [hsupp]
  · simp
  · intro p hp q hq heq
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try rfl
    all_goals simp only [Prod.mk.injEq] at heq
    all_goals obtain ⟨hha, hhb⟩ := heq
    all_goals solve
      | have hz := sub_eq_zero.mpr hha
        reduce_mod_char! at hz
        first
        | exact (one_ne_zero hz).elim
        | have hn := (CharP.cast_eq_zero_iff K 7 _).mp hz
          norm_num at hn
      | have hz := sub_eq_zero.mpr hhb
        reduce_mod_char! at hz
        first
        | exact (one_ne_zero hz).elim
        | have hn := (CharP.cast_eq_zero_iff K 7 _).mp hz
          norm_num at hn



/-- The manuscript’s fourth affine case. The commutator of a translation
and its scalar conjugate gives an eight-cycle. Two explicit translates work
unless the scalar is 2 or its inverse in characteristic 7; the exceptional
word `t⁵ s t s⁻¹` then supplies a symmetric figure-eight. -/
theorem affine_case_four {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : K) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (h2 : (2:K) ≠ 0)
    (hsact : ∀ z, φ s z = r*z) (htact : ∀ z, φ t z = z+1) :
    HasSymmetricFigureEight S := by
  have hneg := scalar_action_pow_ne_neg_one hodd φ hφ s r hsact h2
  have hrminus : r ≠ -1 := by simpa only [pow_one] using hneg 1
  have hrsq : r^2 ≠ 1 :=
    (scalar_action_square_and_fourth_ne_one hodd φ hφ s r hsact hr1).1
  have hsinv : ∀ z, φ s⁻¹ z = r⁻¹*z := by
    intro z
    simpa using affine_inv_apply φ hr0
      (fun z ↦ show φ s z = r*z+0 by simpa using hsact z) z
  rcases caseFour_good_translate r hr0 hr1 h2 hneg with hplus | hminus | ⟨h7, hexc⟩
  case inr.inr =>
    have : CharP K 7 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 7)).mpr h7
    rcases hexc with hr | hr
    · exact caseFour_exception φ hφ S s t hs ht (by simpa only [hr] using hsact) htact
    · have hri : r⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by simpa only [mul_comm] using hr)
      exact caseFour_exception φ hφ S s⁻¹ t (hinv s hs) ht
        (by simpa only [hri] using hsinv) htact
  all_goals
    obtain ⟨c, hc, hlen, hsupport⟩ := caseFour_cycle φ hφ S s t hs ht
      r hr0 hr1 hrminus hsact htact
    let L : List (K × K) := [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)]
    have hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2 := by
      intro x hx
      rw [hsupport] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨(1,0), by simp [L], ?_⟩; simp
      · exact ⟨(1,1), by simp [L], fun z ↦ by simpa using htact z⟩
      · refine ⟨(r,1), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact]
      · refine ⟨(r,1+r), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact]; ring
      · refine ⟨(1,1+r), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact, hsinv]
        field_simp; ring
      · refine ⟨(1,r), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact, hsinv]
        field_simp
      · refine ⟨(r,r), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact]; ring
      · exact ⟨(r,0), by simp [L], fun z ↦ by simpa using hsact z⟩
      · refine ⟨(1,0), by simp [L], ?_⟩; simp
  · apply figureEight_of_affine_coordinate_intersection_general φ hφ S c 3 (by decide)
      hc (by simpa using hlen) L hvertices (s*t) (s*t) 1 r r r r
    · intro z; simp only [affine_mul_apply, hsact, htact]; ring
    · intro z; simp only [affine_mul_apply, hsact, htact]; ring
    · simp [hsupport]
    · simp [hsupport]
    · simp
    · exact fun p hp q hq heq ↦ caseFour_translate_plus r hr0 hr1 hrminus hrsq h2
        hplus.1 hplus.2.1 hplus.2.2.1 hplus.2.2.2 p q hp hq heq
  · have htinverse : ∀ z, φ t⁻¹ z = z-1 := by
      intro z
      simpa using affine_inv_apply φ one_ne_zero
        (fun z ↦ show φ t z = 1*z+1 by simpa using htact z) z
    apply figureEight_of_affine_coordinate_intersection_general φ hφ S c 3 (by decide)
      hc (by simpa using hlen) L hvertices (s*t⁻¹) s t r (-r) r 0
    · intro z; simp only [affine_mul_apply, hsact, htinverse]; ring
    · intro z; simpa using hsact z
    · simp [hsupport]
    · simp [hsupport]
    · group
    · exact fun p hp q hq heq ↦ caseFour_translate_minus r hr0 hr1 hrminus hrsq h2
        hminus.1 hminus.2.1 hminus.2.2.1 hminus.2.2.2 p q hp hq heq


end CayleyErdősGyárfás
