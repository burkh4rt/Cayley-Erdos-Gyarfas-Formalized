module

public import CayleyErdosGyarfas.AffineModel
public import OddOrder.GroupTheory.RepresentationTheory.SingerField
public import OddOrder.Isaacs.Ch03_SplitExtensions.Basic
public import OddOrder.Isaacs.Ch03_SplitExtensions.CyclicExtensions

open scoped IsMulCommutative
public section

namespace CayleyErdősGyárfás

universe u

set_option backward.isDefEq.respectTransparency false

/-- A minimal normal elementary abelian subgroup, acted on irreducibly by
its cyclic complement, admits faithful finite-field scalar coordinates. -/
theorem exists_scalar_field_model
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V] [Nontrivial V]
    (hpow : ∀ v : V, v ^ p = 1)
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hminimal : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K)
      (_ : CharP K p)
      (e : Additive V ≃+ K) (μ : Subgroup.zpowers x →* Kˣ),
      Function.Injective μ ∧
      ∀ (c : Subgroup.zpowers x) (v : Additive V),
        e (Additive.ofMul (MulAut.conjNormal (H := V) (c : G) v.toMul)) =
          (μ c : K) * e v := by
  let := abelianKernelZModModule p V hpow
  let ρ : Representation (ZMod p) (Subgroup.zpowers x) (Additive V) :=
    normalConjugationRepresentation p V (Subgroup.zpowers x)
  have hfaithful : Function.Injective ρ :=
    normalConjugation_injective p V x hgenerate hcenter
  let : Module (MonoidAlgebra (ZMod p) (Subgroup.zpowers x)) (Additive V) :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  let : IsSimpleModule (MonoidAlgebra (ZMod p) (Subgroup.zpowers x)) (Additive V) :=
    normalConjugation_asModule_isSimple p V x hgenerate hminimal
  obtain ⟨data⟩ := OddOrder.RepresentationTheory.nonempty_singerFieldData
    (p := p) (C := Subgroup.zpowers x) (M := Additive V)
  have hequiv : ∀ (c : Subgroup.zpowers x) (v : Additive V),
      data.e ((ρ c).toFun v) = (data.μ c : data.K) * data.e v := by
    intro c v
    have h := data.compat c v
    convert h using 1
    congr 1
    exact ρ.asModuleEquiv_symm_map_rho c v
  have hchar : CharP data.K p := by
    apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    obtain ⟨v, hv⟩ := data.e.surjective 1
    have hvp : p • v = 0 := hpow v.toMul
    have hvp' := congrArg data.e hvp
    simpa [map_nsmul, hv] using hvp'
  refine ⟨data.K, data.field, data.fintype, hchar, data.e, data.μ, ?_, hequiv⟩
  intro c d hcd
  apply hfaithful
  apply LinearMap.ext
  intro v
  apply data.e.injective
  change data.e ((ρ c).toFun v) = data.e ((ρ d).toFun v)
  rw [hequiv, hequiv, hcd]



/-- The finite-field structure of the minimal odd-order counterexample. -/
theorem exists_affine_model_of_cyclic_normal_quotients
    {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) (hnonabelian : ¬ IsMulCommutative G)
    (hquot : ∀ (N : Subgroup G) [N.Normal] [IsMulCommutative N],
      N ≠ ⊥ → IsCyclic (G ⧸ N)) :
    ∃ (V : Subgroup G) (_ : V.Normal) (_ : IsMulCommutative V),
      V ≠ ⊥ ∧ IsCyclic (G ⧸ V) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧
      ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : CharP K p),
      ∃ (φ : G →* Equiv.Perm K) (χ : G →* Kˣ),
        Function.Injective φ ∧ χ.ker = V ∧
        ∀ g : G, ∃ a : K, ∀ z : K, φ g z = (χ g : K) * z + a := by
  have : Nontrivial G := by
    by_contra hn
    have := not_nontrivial_iff_subsingleton.mp hn
    exact hnonabelian inferInstance
  obtain ⟨V, hV, _⟩ := OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal
    (⊤ : Subgroup G) top_ne_bot
  have : V.Normal := hV.1
  have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV.2.1
  obtain ⟨p, hp, hEA⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hV
  have : Fact p.Prime := ⟨hp⟩
  have : IsMulCommutative V := ⟨⟨hEA.1⟩⟩
  have hcyclic := hquot V hV.2.1
  have hcenter := center_eq_bot_of_abelian_normal_quotients_cyclic hnonabelian hquot
  obtain ⟨x, hx⟩ := OddOrder.Isaacs.Ch03.cyclic_quotient_lift hcyclic
  obtain ⟨K, hKfield, hKfinite, hKchar, e, μ, hμ, hequiv⟩ :=
    exists_scalar_field_model p V hEA.2 x hx hcenter hV.2.2
  have hpne2 : p ≠ 2 := by
    intro hp2
    apply hV.2.1
    apply eq_bot_iff.mpr
    intro v hv
    have hvp := congrArg Subtype.val (hEA.2 (⟨v, hv⟩ : V))
    change v ^ p = 1 at hvp
    rw [hp2] at hvp
    exact hodd.coprime_two_right.pow_left_bijective.1 (by simpa using hvp)
  obtain ⟨φ, hφ, _, hφV, haffine⟩ := exists_faithful_affine_action V
    (Subgroup.zpowers x) (cyclic_lift_isComplement_abelian_kernel V x hx hcenter).symm
    e μ hμ hequiv
  obtain ⟨χ, hχ, hφχ⟩ := exists_scalar_hom_of_affine_action V e φ hφ hφV haffine
  exact ⟨V, inferInstance, inferInstance, hV.2.1, hcyclic, p, hp,
    hp.odd_of_ne_two hpne2, K, hKfield, hKfinite, hKchar, φ, χ, hφ, hχ, hφχ⟩


end CayleyErdősGyárfás
