module

public import CayleyErdosGyarfas.Basic
public import CayleyErdosGyarfas.Lifting
public import Mathlib.Tactic

/-! Explicit affine cycles and their translates, following Case 3 of the manuscript. -/

public section

namespace CayleyErdősGyárfás

theorem affine_eq_coeffs {K : Type*} [Field K] {a b c d : K}
    (h : ∀ z, a*z+b = c*z+d) : a = c ∧ b = d := by
  have hzero := h 0
  have hone := h 1
  simp only [mul_zero, zero_add] at hzero
  simp only [mul_one] at hone
  exact ⟨add_right_cancel (hone.trans (congrArg (c + ·) hzero.symm)), hzero⟩

theorem affine_mul_apply {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (u v : G) (z : K) :
    φ (u*v) z = φ u (φ v z) := by simp

theorem affine_inv_apply {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) {u : G} {a b : K} (ha : a ≠ 0)
    (hu : ∀ z, φ u z = a*z+b) (z : K) :
    φ u⁻¹ z = a⁻¹ * (z-b) := by
  apply (φ u).injective
  simp only [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Equiv.Perm.one_apply]
  rw [hu]
  field_simp
  ring

private theorem caseThree_translate_plus {K : Type*} [Field K] (q : K)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqminus : q ≠ -1)
    (hqinv : q⁻¹ ≠ q) (h2 : (2:K) ≠ 0)
    (hbad1 : q ≠ -2) (hbad2 : 2*q ≠ -1)
    (x y : K × K)
    (hx : x ∈ [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)])
    (hy : y ∈ [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)])
    (heq : (y.1, 1+q+y.2) = x) : x = (1,1+q) := by
  have hqi1 : q⁻¹ ≠ 1 := by simpa using hq1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq] at heq ⊢ <;>
    simp only [true_and, false_and,
      hq1, hq1.symm, hqi1, hqi1.symm, hqinv, hqinv.symm] at heq <;>
    try contradiction <;> try rfl
  all_goals first
    | exact ⟨rfl, by linear_combination heq⟩
    | exact (hq0 (by linear_combination heq)).elim
    | exact (hqminus (by linear_combination heq)).elim
    | exact (h2 (by linear_combination heq)).elim
    | exact (hbad1 (by linear_combination heq)).elim
    | exact (hbad2 (by linear_combination heq)).elim
    | exact (hq0 (by linear_combination -heq)).elim
    | exact (hqminus (by linear_combination -heq)).elim
    | exact (h2 (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination -heq)).elim
    | exact (hbad2 (by linear_combination -heq)).elim
    | exact (h2 (by linear_combination 2*heq)).elim
    | exact (hqminus (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (hq0 (by apply mul_left_cancel₀ h2; linear_combination heq)).elim

private theorem caseThree_translate_minus {K : Type*} [Field K] (q : K)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqminus : q ≠ -1)
    (hqinv : q⁻¹ ≠ q) (h2 : (2:K) ≠ 0)
    (hbad1 : q ≠ 2) (hbad2 : 2*q ≠ 1)
    (x y : K × K)
    (hx : x ∈ [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)])
    (hy : y ∈ [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)])
    (heq : (y.1, 1-q+y.2) = x) : x = (1,1) := by
  have hqi1 : q⁻¹ ≠ 1 := by simpa using hq1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq] at heq ⊢ <;>
    simp only [true_and, false_and,
      hq1, hq1.symm, hqi1, hqi1.symm, hqinv, hqinv.symm] at heq <;>
    try contradiction <;> try rfl
  all_goals first
    | exact ⟨rfl, by linear_combination heq⟩
    | exact (hq0 (by linear_combination heq)).elim
    | exact (hqminus (by linear_combination heq)).elim
    | exact (h2 (by linear_combination heq)).elim
    | exact (hbad1 (by linear_combination heq)).elim
    | exact (hbad2 (by linear_combination heq)).elim
    | exact (hq0 (by linear_combination -heq)).elim
    | exact (hqminus (by linear_combination -heq)).elim
    | exact (h2 (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination -heq)).elim
    | exact (hbad2 (by linear_combination -heq)).elim
    | exact (h2 (by linear_combination 2*heq)).elim
    | exact (hqminus (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (hq0 (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (hq1 (by apply mul_left_cancel₀ h2; linear_combination -heq)).elim
    | exact (hq1 (by linear_combination -heq)).elim
    | exact (hq1 (by linear_combination heq)).elim
    | exact (hq0 (by apply mul_left_cancel₀ h2; linear_combination -heq)).elim

private theorem caseThree_good_translate {K : Type*} [Field K] (q : K)
    (h2 : (2:K) ≠ 0) (hsq : q^2 ≠ -1) :
    (q ≠ -2 ∧ 2*q ≠ -1) ∨ (q ≠ 2 ∧ 2*q ≠ 1) := by
  by_cases hplus1 : q ≠ -2
  · by_cases hplus2 : 2*q ≠ -1
    · exact Or.inl ⟨hplus1, hplus2⟩
    · push Not at hplus2
      right
      constructor
      · intro h
        apply hsq
        linear_combination q*h + hplus2
      · intro h
        apply h2
        linear_combination hplus2 - h
  · push Not at hplus1
    right
    constructor
    · intro h
      have hfour : (2:K)*2 = 0 := by linear_combination hplus1 - h
      exact (mul_ne_zero h2 h2) hfour
    · intro h
      apply hsq
      linear_combination q*hplus1 - h

set_option maxRecDepth 2000 in
private theorem caseThree_cycle {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (q : K) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqminus : q ≠ -1)
    (hqinv : q⁻¹ ≠ q)
    (hsact : ∀ z, φ s z = q⁻¹*z) (htact : ∀ z, φ t z = q⁻¹*z+1) :
    ∃ c : (SimpleGraph.mulCayley S).Walk 1 1,
      c.IsCycle ∧ c.length = 8 ∧
      c.support = [1, t, t*s⁻¹, t*s⁻¹*s⁻¹, t*s⁻¹*s⁻¹*t,
        t*s⁻¹*s⁻¹*t*s, s⁻¹*t, s⁻¹, 1] := by
  let f : ℕ → G
    | 0 => 1 | 1 => t | 2 => t*s⁻¹ | 3 => t*s⁻¹*s⁻¹
    | 4 => t*s⁻¹*s⁻¹*t | 5 => t*s⁻¹*s⁻¹*t*s
    | 6 => s⁻¹*t | 7 => s⁻¹ | _ => 1
  let v : ℕ → K × K
    | 0 => (1,0) | 1 => (q⁻¹,1) | 2 => (1,1) | 3 => (q,1)
    | 4 => (1,1+q) | 5 => (q⁻¹,1+q) | 6 => (1,q) | 7 => (q,0)
    | _ => (1,0)
  have hsinv : ∀ z, φ s⁻¹ z = q*z := by
    intro z
    simpa using affine_inv_apply φ (inv_ne_zero hq0)
      (fun z ↦ show φ s z = q⁻¹*z+0 by simpa using hsact z) z
  have htinverse : ∀ z, φ t⁻¹ z = q*(z-1) := by
    intro z
    simpa using affine_inv_apply φ (inv_ne_zero hq0) htact z
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
    have hqi1 : q⁻¹ ≠ 1 := by simpa using hq1
    interval_cases i <;> interval_cases j <;> try rfl
    all_goals simp only [v, Prod.mk.injEq] at hh
    all_goals simp only [hq1, hq1.symm, hqi1, hqi1.symm, hqinv, hqinv.symm,
      false_and, true_and, and_false, zero_ne_one, one_ne_zero] at hh
    all_goals first
      | contradiction
      | exact (hq0 (by linear_combination hh)).elim
      | exact (hq0 (by linear_combination -hh)).elim
      | exact (hq1 (by linear_combination hh)).elim
      | exact (hq1 (by linear_combination -hh)).elim
      | exact (hqminus (by linear_combination hh)).elim
      | exact (hqminus (by linear_combination -hh)).elim
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
    · exact ⟨s, hs, Or.inr (by simp [f])⟩
    · exact ⟨s, hs, Or.inr (by simp [f])⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · refine ⟨t, ht, Or.inr ?_⟩
      apply hφ
      ext z
      simp only [f, affine_mul_apply, hsinv, hsact, htact]
      field_simp
      ring
    · exact ⟨t, ht, Or.inr rfl⟩
    · exact ⟨s, hs, Or.inl (by simp [f])⟩
  obtain ⟨c, hc, hlen, hsupport⟩ := exists_cycle_of_sequence_with_support
    (n := 8) (by decide) f rfl hadj hinj
  refine ⟨c, hc, hlen, ?_⟩
  simpa [f, List.ofFn_succ] using hsupport

theorem figureEight_of_affine_coordinate_intersection
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (c : (SimpleGraph.mulCayley S).Walk 1 1)
    (n : ℕ) (hn : 1 ≤ n) (hc : c.IsCycle) (hlen : c.length = 2^n)
    (L : List (K × K))
    (hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2)
    (g w y : G) (d b : K)
    (hg : ∀ z, φ g z = z+d) (hw : ∀ z, φ w z = z+b)
    (hwmem : w ∈ c.support) (hymem : y ∈ c.support) (hgy : g*y = w)
    (hinter : ∀ p ∈ L, ∀ q ∈ L, (q.1,d+q.2) = p → p = (1,b)) :
    HasSymmetricFigureEight S := by
  apply hasSymmetricFigureEight_of_cycle_translate c n hn hc hlen g w
  intro x
  constructor
  · rintro ⟨hx, y', hy, hxy⟩
    obtain ⟨p, hp, hpx⟩ := hvertices x hx
    obtain ⟨q, hq, hqy⟩ := hvertices y' hy
    have heq : (q.1,d+q.2) = p := by
      have hcoeff : q.1 = p.1 ∧ d+q.2 = p.2 :=
        affine_eq_coeffs (a := q.1) (b := d+q.2) (c := p.1) (d := p.2)
          (fun z ↦ by
            rw [← hpx, ← hxy, affine_mul_apply, hqy, hg]
            ring)
      exact Prod.ext hcoeff.1 hcoeff.2
    have hpval := hinter p hp q hq heq
    apply hφ
    ext z
    rw [hpx, hpval, hw]
    simp
  · rintro rfl
    exact ⟨hwmem, y, hymem, hgy⟩

/-- The manuscript's third affine case: the two generators have the same
nontrivial linear part. The eight-cycle is the word `t s⁻² t s t⁻² s`.
The two candidate translates have offsets `1+q` and `1-q`, where `q` is
the inverse of the common scalar. -/
theorem affine_case_three {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (q : K) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqminus : q ≠ -1)
    (hqinv : q⁻¹ ≠ q) (h2 : (2:K) ≠ 0) (hsq : q^2 ≠ -1)
    (hsact : ∀ z, φ s z = q⁻¹*z) (htact : ∀ z, φ t z = q⁻¹*z+1) :
    HasSymmetricFigureEight S := by
  obtain ⟨c, hc, hlen, hsupport⟩ := caseThree_cycle φ hφ S s t hs ht
    q hq0 hq1 hqminus hqinv hsact htact
  let L : List (K × K) :=
    [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)]
  have hsinv : ∀ z, φ s⁻¹ z = q*z := by
    intro z
    simpa using affine_inv_apply φ (inv_ne_zero hq0)
      (fun z ↦ show φ s z = q⁻¹*z+0 by simpa using hsact z) z
  have hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2 := by
    intro x hx
    rw [hsupport] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨(1,0), by simp [L], ?_⟩
      simp
    · exact ⟨(q⁻¹,1), by simp [L], htact⟩
    · refine ⟨(1,1), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, htact]; field_simp <;> ring
    · refine ⟨(q,1), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, htact]; field_simp <;> ring
    · refine ⟨(1,1+q), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · refine ⟨(q⁻¹,1+q), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, hsact, htact]
      field_simp <;> ring
    · refine ⟨(1,q), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · exact ⟨(q,0), by simp [L], fun z ↦ by simpa using hsinv z⟩
    · refine ⟨(1,0), by simp [L], ?_⟩
      simp
  rcases caseThree_good_translate q h2 hsq with hplus | hminus
  · apply figureEight_of_affine_coordinate_intersection φ hφ S c 3 (by decide) hc
      (by simpa using hlen) L hvertices
      (t*s⁻¹*s⁻¹*t) (t*s⁻¹*s⁻¹*t) 1 (1+q) (1+q)
    · intro z
      simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · intro z
      simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · simp [hsupport]
    · simp [hsupport]
    · simp
    · intro p hp y hy heq
      exact caseThree_translate_plus q hq0 hq1 hqminus hqinv h2 hplus.1 hplus.2 p y hp hy heq
  · apply figureEight_of_affine_coordinate_intersection φ hφ S c 3 (by decide) hc
      (by simpa using hlen) L hvertices
      (t*s⁻¹*(s⁻¹*t)⁻¹) (t*s⁻¹) (s⁻¹*t) (1-q) 1
    · have htranslate (z : K) : φ (s⁻¹*t) z = 1*z+q := by
        simp only [affine_mul_apply, hsinv, htact]
        field_simp <;> ring
      have htranslateinv := affine_inv_apply φ (u := s⁻¹*t) one_ne_zero htranslate
      intro z
      simp only [affine_mul_apply, htranslateinv, inv_one, one_mul, hsinv, htact]
      field_simp <;> ring
    · intro z
      simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · simp [hsupport]
    · simp [hsupport]
    · group
    · intro p hp y hy heq
      exact caseThree_translate_minus q hq0 hq1 hqminus hqinv h2 hminus.1 hminus.2 p y hp hy heq


theorem figureEight_of_affine_coordinate_intersection_general
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (c : (SimpleGraph.mulCayley S).Walk 1 1)
    (n : ℕ) (hn : 1 ≤ n) (hc : c.IsCycle) (hlen : c.length = 2^n)
    (L : List (K × K))
    (hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2)
    (g w y : G) (a d e b : K)
    (hg : ∀ z, φ g z = a*z+d) (hw : ∀ z, φ w z = e*z+b)
    (hwmem : w ∈ c.support) (hymem : y ∈ c.support) (hgy : g*y = w)
    (hinter : ∀ p ∈ L, ∀ q ∈ L, (a*q.1,d+a*q.2) = p → p = (e,b)) :
    HasSymmetricFigureEight S := by
  apply hasSymmetricFigureEight_of_cycle_translate c n hn hc hlen g w
  intro x
  constructor
  · rintro ⟨hx, y', hy, hxy⟩
    obtain ⟨p, hp, hpx⟩ := hvertices x hx
    obtain ⟨q, hq, hqy⟩ := hvertices y' hy
    have heq : (a*q.1,d+a*q.2) = p := by
      have hcoeff : a*q.1 = p.1 ∧ d+a*q.2 = p.2 :=
        affine_eq_coeffs (a := a*q.1) (b := d+a*q.2) (c := p.1) (d := p.2)
          (fun z ↦ by
            rw [← hpx, ← hxy, affine_mul_apply, hqy, hg]
            ring)
      exact Prod.ext hcoeff.1 hcoeff.2
    have hpval := hinter p hp q hq heq
    apply hφ
    ext z
    rw [hpx, hpval, hw]
  · rintro rfl
    exact ⟨hwmem, y, hymem, hgy⟩


end CayleyErdősGyárfás
