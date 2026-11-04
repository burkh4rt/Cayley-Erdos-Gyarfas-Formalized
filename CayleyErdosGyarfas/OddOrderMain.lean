module

public import CayleyErdosGyarfas.MainReduction
public import CayleyErdosGyarfas.AffineReduction
public import CayleyErdosGyarfas.CyclicNormalFieldModel
public import CayleyErdosGyarfas.AffineCaseTwo
public import CayleyErdosGyarfas.AffineCaseFour
public import OddOrder.FeitThompson

/-! Completion of the noncyclic odd-order figure-eight theorem. -/

public section

namespace CayleyErdősGyárfás

/-- The minimal nonabelian case: Feit–Thompson and the finite-field model
reduce the chosen generating pair to the quotient square or one of the
three explicit affine cycle constructions. -/
theorem minimal_nonabelian_case_has_symmetric_figure_eight
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (_hone : (1 : G) ∉ S) (hncomm : ¬ IsMulCommutative G)
    (hquot : ∀ (A : Subgroup G) [A.Normal] [IsMulCommutative A],
      A ≠ ⊥ → IsCyclic (G ⧸ A))
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hst : ¬ Commute s t)
    (hpair : Subgroup.closure ({s, t} : Set G) = ⊤) :
    HasSymmetricFigureEight S := by
  have : Group.IsSolvable G := OddOrder.feitThompson hodd
  obtain ⟨V, hVnormal, hVcomm, _, hVcyclic, p, hp, hpodd,
      K, hKfield, hKfinite, hKchar, φ, χ, hφ, hker, haffine⟩ :=
    exists_affine_model_of_cyclic_normal_quotients hodd hncomm hquot
  have h2 : (2 : K) ≠ 0 := by
    intro hzero
    have hpdvd := (CharP.cast_eq_zero_iff K p 2).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd with hp1 | hp2
    · exact hp.ne_one hp1
    · exact hpodd.not_two_dvd_nat (by simp [hp2])
  obtain hfigure | ⟨a, b, r, ψ, ha, hb, hψ, hr, hψa, hcases⟩ :=
    affine_pair_reduction S hodd hinv V φ hφ χ hker haffine hs ht hst hpair
  · exact hfigure
  rcases hcases with htranslation | hsame | ⟨hr5, hsquare⟩
  · exact affine_case_four hodd ψ hψ S hinv a b ha hb (r : K) r.ne_zero hr h2
      hψa htranslation
  · exact affine_case_three_of_odd_order hodd ψ hψ S a b ha hb r hr h2 hψa hsame
  · exact affine_case_two ψ hψ S a b ha hb (hinv a ha) r hr hr5 h2 hψa hsquare

/-- The stronger form established by the manuscript's main induction:
every noncyclic finite odd-order Cayley graph has a symmetric figure-eight. -/
theorem noncyclic_odd_order_symmetric_figure_eight
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S) (hgen : Subgroup.closure S = ⊤)
    (hncyclic : ¬ IsCyclic G) : HasSymmetricFigureEight S := by
  exact noncyclic_figure_eight_of_minimal_case
    (@minimal_nonabelian_case_has_symmetric_figure_eight)
    S hodd hinv hone hgen hncyclic

end CayleyErdősGyárfás
