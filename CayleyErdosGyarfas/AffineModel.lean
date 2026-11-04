module

public import CayleyErdosGyarfas.OddOrderReduction

/-! Faithful affine coordinates for a group with an abelian complement. -/

public section

namespace CayleyErdősGyárfás

open scoped IsMulCommutative

set_option backward.isDefEq.respectTransparency false in
/-- A scalar realization of the action on an abelian normal subgroup gives
faithful affine coordinates for the whole split extension. -/
theorem exists_faithful_affine_action
    {G K : Type*} [Group G] [Field K]
    (V C : Subgroup G) [V.Normal] [IsMulCommutative V]
    (hcomp : V.IsComplement' C)
    (e : Additive V ≃+ K) (μ : C →* Kˣ) (hμ : Function.Injective μ)
    (hequiv : ∀ (c : C) (v : Additive V),
      e (Additive.ofMul (MulAut.conjNormal (H := V) (c : G) v.toMul)) =
        (μ c : K) * e v) :
    ∃ φ : G →* Equiv.Perm K, Function.Injective φ ∧
      (∀ (c : C) (z : K), φ (c : G) z = (μ c : K) * z) ∧
      (∀ (v : V) (z : K), φ (v : G) z = z + e (Additive.ofMul v)) ∧
      ∀ g : G, ∃ (r : Kˣ) (a : K), ∀ z : K, φ g z = (r : K) * z + a := by
  let σ : C →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion (V.normalizer_eq_top ▸ le_top))
  have hσ (c : C) (v : V) :
      e (Additive.ofMul (σ c v)) = (μ c : K) * e (Additive.ofMul v) :=
    hequiv c (Additive.ofMul v)
  let ψ : V ⋊[σ] C →* Equiv.Perm K := {
    toFun d := {
      toFun z := (μ d.right : K) * z + e (Additive.ofMul d.left)
      invFun z := ((μ d.right)⁻¹ : Kˣ) * (z - e (Additive.ofMul d.left))
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
    map_one' := by ext z; simp
    map_mul' := by
      intro a b
      ext z
      change (μ (a.right * b.right) : K) * z +
        e (Additive.ofMul (a.left * σ a.right b.left)) =
        (μ a.right : K) * ((μ b.right : K) * z + e (Additive.ofMul b.left)) +
          e (Additive.ofMul a.left)
      rw [map_mul, Units.val_mul]
      change _ + e (Additive.ofMul a.left + Additive.ofMul (σ a.right b.left)) = _
      rw [map_add, hσ]
      ring }
  have hψ (d : V ⋊[σ] C) (z : K) :
      ψ d z = (μ d.right : K) * z + e (Additive.ofMul d.left) := rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have hleft : a.left = b.left := by
      have h0 := congrArg (fun f : Equiv.Perm K ↦ f 0) hab
      simp only [hψ, mul_zero, zero_add] at h0
      exact e.injective h0
    have hright : a.right = b.right := by
      apply hμ
      apply Units.ext
      have h1 := congrArg (fun f : Equiv.Perm K ↦ f 1) hab
      simp only [hψ, mul_one, hleft] at h1
      exact add_right_cancel h1
    exact SemidirectProduct.ext hleft hright
  let E : V ⋊[σ] C ≃* G := SemidirectProduct.mulEquivSubgroup hcomp
  let φ := ψ.comp E.symm.toMonoidHom
  refine ⟨φ, hψinj.comp E.symm.injective, ?_, ?_, ?_⟩
  · intro c z
    have hc : E (SemidirectProduct.inr c) = (c : G) := by
      change (1 : G) * (c : G) = (c : G)
      simp
    change ψ (E.symm (c : G)) z = _
    rw [← hc, E.symm_apply_apply, hψ]
    simp
  · intro v z
    have hv : E (SemidirectProduct.inl v) = (v : G) := by
      change (v : G) * (1 : G) = (v : G)
      simp
    change ψ (E.symm (v : G)) z = _
    rw [← hv, E.symm_apply_apply, hψ]
    simp
  · intro g
    exact ⟨μ (E.symm g).right, e (Additive.ofMul (E.symm g).left), fun _ ↦ rfl⟩

/-- Translate a fixed point of the first generator to zero and rescale the
nonzero translation part of the second generator to one. Noncommutation is
exactly what prevents that translation part from vanishing. -/
theorem normalize_two_affine_generators
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (s t : G) (r q : Kˣ) (a b : K)
    (hs : ∀ z : K, φ s z = (r : K) * z + a)
    (ht : ∀ z : K, φ t z = (q : K) * z + b)
    (hr : (r : K) ≠ 1) (hnoncomm : ¬ Commute s t) :
    ∃ ψ : G →* Equiv.Perm K, Function.Injective ψ ∧
      (∀ z : K, ψ s z = (r : K) * z) ∧
      ∀ z : K, ψ t z = (q : K) * z + 1 := by
  let c : K := a / (1 - (r : K))
  have hrc : (r : K) * c + a = c := by
    dsimp [c]
    field_simp
    ring
  let d : K := (q : K) * c + b - c
  have hd : d ≠ 0 := by
    intro hd
    have hqc : (q : K) * c + b = c := sub_eq_zero.mp hd
    have ha : a = c - (r : K) * c := by linear_combination hrc
    have hb : b = c - (q : K) * c := by linear_combination hqc
    apply hnoncomm
    apply hφ
    ext z
    simp only [map_mul, Equiv.Perm.mul_apply, hs, ht]
    rw [ha, hb]
    ring
  let E : Equiv.Perm K := {
    toFun z := d * z + c
    invFun z := d⁻¹ * (z - c)
    left_inv := by intro z; simp [hd]
    right_inv := by intro z; simp [hd] }
  let ψ := (MulAut.conj E⁻¹).toMonoidHom.comp φ
  have hψ (g : G) (z : K) : ψ g z = d⁻¹ * (φ g (d * z + c) - c) := rfl
  refine ⟨ψ, (MulAut.conj E⁻¹).injective.comp hφ, ?_, ?_⟩
  · intro z
    rw [hψ, hs]
    have hcalc : (r : K) * (d * z + c) + a - c = d * ((r : K) * z) := by
      linear_combination hrc
    rw [hcalc]
    simp [hd]
  · intro z
    rw [hψ, ht]
    have hcalc : (q : K) * (d * z + c) + b - c = d * ((q : K) * z + 1) := by
      dsimp [d]
      ring
    rw [hcalc]
    simp [hd]

/-- Powers of a generator acting by a scalar act by the corresponding scalar
power. -/
theorem scalar_action_pow
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (s : G) (r : K)
    (hs : ∀ z : K, φ s z = r * z) (n : ℕ) (z : K) :
    φ (s ^ n) z = r ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', map_mul, Equiv.Perm.mul_apply, hs, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

/-- A nonidentity scalar in a faithful action has no order coprime to the
order of the acting group. -/
theorem scalar_action_pow_ne_one
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (s : G) (r : K) (hs : ∀ z : K, φ s z = r * z)
    (hr : r ≠ 1) (n : ℕ) (hn : (Nat.card G).Coprime n) : r ^ n ≠ 1 := by
  intro hrn
  have hsn : s ^ n = 1 := by
    apply hφ
    ext z
    rw [scalar_action_pow φ s r hs, hrn]
    simp
  have hsone : s = 1 := hn.pow_left_bijective.1 (by simpa using hsn)
  have := hs 1
  rw [hsone, φ.map_one] at this
  exact hr (by simpa using this.symm)

/-- The scalar exclusions used by the explicit eight-cycle constructions. -/
theorem scalar_action_square_and_fourth_ne_one
    {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (s : G) (r : K) (hs : ∀ z : K, φ s z = r * z)
    (hr : r ≠ 1) : r ^ 2 ≠ 1 ∧ r ^ 4 ≠ 1 := by
  refine ⟨scalar_action_pow_ne_one φ hφ s r hs hr 2 hodd.coprime_two_right, ?_⟩
  exact scalar_action_pow_ne_one φ hφ s r hs hr 4
    (by simpa using hodd.coprime_two_right.pow_right 2)

/-- Extract the scalar homomorphism from faithful affine coordinates. Its
kernel is exactly the normal translation subgroup. -/
theorem exists_scalar_hom_of_affine_action
    {G K : Type*} [Group G] [Field K]
    (V : Subgroup G) [IsMulCommutative V]
    (e : Additive V ≃+ K)
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (hV : ∀ (v : V) (z : K), φ (v : G) z = z + e (Additive.ofMul v))
    (haffine : ∀ g : G, ∃ (r : Kˣ) (a : K), ∀ z : K, φ g z = (r : K) * z + a) :
    ∃ χ : G →* Kˣ, χ.ker = V ∧
      ∀ g : G, ∃ a : K, ∀ z : K, φ g z = (χ g : K) * z + a := by
  classical
  choose r a h using haffine
  have hcoeff (g : G) : (r g : K) = φ g 1 - φ g 0 := by
    rw [h, h]
    ring
  let χ : G →* Kˣ := {
    toFun := r
    map_one' := by
      apply Units.ext
      rw [hcoeff, φ.map_one]
      simp
    map_mul' := by
      intro g k
      apply Units.ext
      rw [hcoeff, φ.map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        h, h, h, h, Units.val_mul]
      ring }
  refine ⟨χ, ?_, fun g ↦ ⟨a g, h g⟩⟩
  ext g
  change χ g = 1 ↔ g ∈ V
  constructor
  · intro hg
    obtain ⟨v, hv⟩ := e.surjective (a g)
    have hgv : g = (v.toMul : G) := by
      apply hφ
      ext z
      rw [h, hV]
      change (r g : K) * z + a g = z + e v
      rw [hv]
      have hr : (r g : K) = 1 := congrArg Units.val hg
      rw [hr]
      simp
    rw [hgv]
    exact v.toMul.property
  · intro hg
    apply Units.ext
    change (r g : K) = 1
    rw [hcoeff, hV ⟨g, hg⟩, hV ⟨g, hg⟩]
    ring

/-- No power of a scalar coming from an odd-order group can equal minus one
in characteristic different from two. -/
theorem scalar_action_pow_ne_neg_one
    {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (s : G) (r : K) (hs : ∀ z : K, φ s z = r * z)
    (h2 : (2 : K) ≠ 0) (n : ℕ) : r ^ n ≠ -1 := by
  intro hn
  have hscalar (z : K) : φ (s ^ n) z = -z := by
    rw [scalar_action_pow φ s r hs, hn]
    simp
  have hsq : (s ^ n) ^ 2 = 1 := by
    apply hφ
    ext z
    simp only [pow_two, map_mul, Equiv.Perm.mul_apply, hscalar,
      neg_neg, map_one, Equiv.Perm.one_apply]
  have hsn : s ^ n = 1 := hodd.coprime_two_right.pow_left_bijective.1
    (by simpa using hsq)
  have h1 := hscalar 1
  rw [hsn, φ.map_one] at h1
  have hbad : (1 : K) = -1 := by simpa using h1
  apply h2
  linear_combination hbad

end CayleyErdősGyárfás
