module

public import CayleyErdosGyarfas.AffineCases

/-! Finite coordinate checks for the two sixteen-cycles in affine Case 2.
The scalar exclusions below are explicit polynomial identities checked by
`linear_combination`; every finite case is checked by the Lean kernel. -/

public section
namespace CayleyErdősGyárfás

@[expose] def caseTwoExponent : ℕ → ℕ
    | 0 => 0
    | 1 => 1
    | 2 => 3
    | 3 => 4
    | 4 => 0
    | 5 => 1
    | 6 => 4
    | 7 => 0
    | 8 => 2
    | 9 => 3
    | 10 => 1
    | 11 => 2
    | 12 => 3
    | 13 => 4
    | 14 => 1
    | 15 => 2
    | _ => 0
@[expose] def caseTwoOffset {K : Type*} [Field K] (r : K) : ℕ → K
    | 0 => 0
    | 1 => 0
    | 2 => r
    | 3 => r
    | 4 => r
    | 5 => r
    | 6 => -r^4 + r
    | 7 => -r^4 + r
    | 8 => -r^4 + r + 1
    | 9 => -r^4 + r + 1
    | 10 => 1 - r^4
    | 11 => 1 - r^4
    | 12 => 1 - r^4
    | 13 => 1 - r^4
    | 14 => 1
    | 15 => 1
    | _ => 0

set_option maxHeartbeats 2000000 in
/-- The sixteen affine coordinates are distinct and their translate by one
meets them only at the coordinate `(r,1)`. -/
theorem caseTwo_coordinates {K : Type*} [Field K] (r : K)
    (horder : orderOf r = 5)
    (hC : r^4+r^3+r^2+r+1 = 0) (h2 : (2:K) ≠ 0) (h5 : (5:K) ≠ 0)
    (hP : 19*r^2-r+19 ≠ 0) :
    Function.Injective (fun i : Fin 16 ↦ (r ^ caseTwoExponent i, caseTwoOffset r i)) ∧
    ∀ i j : Fin 16,
      (r ^ caseTwoExponent j, 1 + caseTwoOffset r j) =
        (r ^ caseTwoExponent i, caseTwoOffset r i) →
      (r ^ caseTwoExponent i, caseTwoOffset r i) = (r, 1) := by
  have hd0 : (-r : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1)*hC + (r^3 + r^2 + r + 1)*h
  have hd1 : (r^4 - r : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-3*r^3 + 2*r^2 - 3*r + 5)*hC + (3*r^3 + r^2 + 4*r + 2)*h
  have hd2 : (r^4 - 1 : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-r^3 - r^2 - r + 4)*hC + (r^3 + 2*r^2 + 3*r - 1)*h
  have hd3 : (-1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (0)*hC + (-1)*h
  have hd4 : (r^4 + r - 1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (-r^3 + r)*hC + (r^3 + r^2 - 1)*h
  have hd5 : (r^4 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1 - r)*hC + (r)*h
  have hd6 : (r : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1)*hC + (-r^3 - r^2 - r - 1)*h
  have hd7 : (r - 1 : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (1)*hC + (-r^3 - 2*r^2 - 3*r - 4)*h
  have hd8 : (-r^4 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1 - r)*hC + (-r)*h
  have hd9 : (-r^4 + r : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-3*r^3 + 2*r^2 - 3*r + 5)*hC + (-3*r^3 - r^2 - 4*r - 2)*h
  have hd10 : (1 - r^4 : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-r^3 - r^2 - r + 4)*hC + (-r^3 - 2*r^2 - 3*r + 1)*h
  have hd11 : (-r^4 - r + 1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (-r^3 + r)*hC + (-r^3 - r^2 + 1)*h
  have hd12 : (1 - r : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (1)*hC + (r^3 + 2*r^2 + 3*r + 4)*h
  have hd13 : (1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (0)*hC + (1)*h
  have hd14 : (-r - 1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1)*hC + (r^3 + r)*h
  have hd15 : (r^4 - r - 1 : K) ≠ 0 := by
    intro h
    apply hP
    linear_combination (-14*r^3 + 16*r^2 - 11*r + 21)*hC + (14*r^3 - 2*r^2 + 9*r + 2)*h
  have hd16 : (r^4 - 2 : K) ≠ 0 := by
    intro h
    apply hP
    linear_combination (-3*r^3 + 8*r^2 - 6*r + 7)*hC + (3*r^3 - 5*r^2 + r - 6)*h
  have hd17 : (-2 : K) ≠ 0 := by
    intro h
    apply h2
    linear_combination (0)*hC + (-1)*h
  have hd18 : (r^4 + r - 2 : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-r^3 + r + 1)*hC + (r^3 + r^2 - 2)*h
  have hd19 : (r - 2 : K) ≠ 0 := by
    intro h
    apply hP
    linear_combination (3)*hC + (-3*r^3 - 9*r^2 - 2*r - 8)*h
  have hd20 : (-r^4 - 1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (-r^3 + r^2 - r)*hC + (-r^3 - r - 1)*h
  have hd21 : (-r^4 + r - 1 : K) ≠ 0 := by
    intro h
    apply hP
    linear_combination (-14*r^3 + 2*r^2 + 7*r + 3)*hC + (-14*r^3 - 12*r^2 - 5*r - 16)*h
  have hd22 : (-r^4 - r : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (r^3 - r + 1)*hC + (r^3 + r^2)*h

  let e := caseTwoExponent
  let b := caseTwoOffset r
  have he_bound (i : ℕ) (hi : i < 16) : e i < 5 := by
    interval_cases i <;> norm_num [e, caseTwoExponent]
  constructor
  · intro i j hh
    change (r ^ e i, b i) = (r ^ e j, b j) at hh
    have hh := Prod.mk.inj hh
    have hexp : e i = e j := pow_injOn_Iio_orderOf
      (by simpa [horder] using he_bound i i.isLt)
      (by simpa [horder] using he_bound j j.isLt) hh.1
    have hoff := hh.2
    fin_cases i <;> fin_cases j <;> try norm_num [e, caseTwoExponent] at hexp
    all_goals try norm_num
    all_goals simp only [b, caseTwoOffset] at hoff
    all_goals first
      | (guard_hyp hoff : (0 : K) = (r : K)
         exact (hd0 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (0 : K) = (-r^4 + r : K)
         exact (hd1 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (0 : K) = (1 - r^4 : K)
         exact (hd2 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (0 : K) = (1 : K)
         exact (hd3 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (-r^4 + r + 1 : K)
         exact (hd2 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (1 - r^4 : K)
         exact (hd4 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (-r^4 + r : K)
         exact (hd5 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (0 : K)
         exact (hd6 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (1 : K)
         exact (hd7 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r : K) = (r : K)
         exact (hd8 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r : K) = (1 - r^4 : K)
         exact (hd7 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r : K) = (0 : K)
         exact (hd9 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r + 1 : K) = (1 - r^4 : K)
         exact (hd6 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r + 1 : K) = (1 : K)
         exact (hd9 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r + 1 : K) = (r : K)
         exact (hd10 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (0 : K)
         exact (hd10 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (r : K)
         exact (hd11 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (1 : K)
         exact (hd8 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (-r^4 + r + 1 : K)
         exact (hd0 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (-r^4 + r : K)
         exact (hd12 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 : K) = (0 : K)
         exact (hd13 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 : K) = (r : K)
         exact (hd12 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 : K) = (1 - r^4 : K)
         exact (hd5 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 : K) = (-r^4 + r + 1 : K)
         exact (hd1 (by linear_combination hoff)).elim)

  · intro i j heq
    change (r ^ e j, 1 + b j) = (r ^ e i, b i) at heq
    change (r ^ e i, b i) = (r, 1)
    simp only [Prod.mk.injEq] at heq
    have hexp : e i = e j := pow_injOn_Iio_orderOf
      (by simpa [horder] using he_bound i i.isLt)
      (by simpa [horder] using he_bound j j.isLt) heq.1.symm
    have hoff := heq.2
    fin_cases i <;> fin_cases j <;> try norm_num [e, caseTwoExponent] at hexp
    all_goals try norm_num [e, b, caseTwoExponent, caseTwoOffset]
    all_goals simp only [b, caseTwoOffset] at hoff
    all_goals first
      | (guard_hyp hoff : (1 : K) + (0 : K) = (0 : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (0 : K)
         exact (hd14 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r : K) = (0 : K)
         exact (hd15 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (0 : K)
         exact (hd16 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (0 : K)
         exact (hd17 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (r : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r + 1 : K) = (r : K)
         exact (hd16 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (r : K)
         exact (hd18 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r : K) = (r : K)
         exact (hd2 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (0 : K) = (r : K)
         exact (hd7 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (r : K)
         exact (hd19 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (-r^4 + r : K)
         exact (hd20 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r : K) = (-r^4 + r : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (-r^4 + r : K)
         exact (hd19 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (0 : K) = (-r^4 + r : K)
         exact (hd21 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r + 1 : K) = (-r^4 + r + 1 : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (-r^4 + r + 1 : K)
         exact (hd7 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (-r^4 + r + 1 : K)
         exact (hd21 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (-r^4 + r + 1 : K)
         exact (hd8 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (0 : K) = (1 - r^4 : K)
         exact (hd8 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (1 - r^4 : K)
         exact (hd22 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (1 - r^4 : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (1 - r^4 : K)
         exact (hd20 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r + 1 : K) = (1 - r^4 : K)
         exact (hd14 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r : K) = (1 - r^4 : K)
         exact (hd0 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (1 : K)
         exact (hd2 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (1 : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r + 1 : K) = (1 : K)
         exact (hd15 (by linear_combination -hoff)).elim)

end CayleyErdősGyárfás
