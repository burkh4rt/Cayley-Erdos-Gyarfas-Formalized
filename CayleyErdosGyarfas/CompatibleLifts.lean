module

public import CayleyErdosGyarfas.Basic
public import CayleyErdosGyarfas.Lifting
public import CayleyErdosGyarfas.FigureEightLifting

/-! Compatible lifts of translated quotient cycles. -/

public section

namespace CayleyErdősGyárfás

open SimpleGraph
open scoped IsMulCommutative

/-- In a nonempty closed walk, deleting the repeated initial vertex does
not change the set of vertices. -/
theorem closed_walk_mem_support_tail_iff
    {V : Type*} {Γ : SimpleGraph V} {v x : V} (c : Γ.Walk v v) (hc : ¬ c.Nil) :
    x ∈ c.support.tail ↔ x ∈ c.support := by
  rw [c.mem_support_iff]
  constructor
  · exact Or.inr
  · rintro (rfl | h)
    · exact c.end_mem_tail_support hc
    · exact h

set_option backward.isDefEq.respectTransparency false in
/-- A symmetric figure-eight can be described by a single cycle based at
the identity and a translated support meeting it only at the identity. -/
theorem HasSymmetricFigureEight.exists_cycle_translate_based_one
    {Q : Type*} [Group Q] {T : Set Q} (hfigure : HasSymmetricFigureEight T) :
    ∃ (n : ℕ) (p : (mulCayley T).Walk 1 1) (g : Q),
      1 ≤ n ∧ p.IsCycle ∧ p.length = 2 ^ n ∧
      ∀ x : Q, (x ∈ p.support ∧ ∃ y ∈ p.support, g * y = x) ↔ x = 1 := by
  obtain ⟨n, v, α, β, hn, hα, hβ, hαlen, _, ⟨g, hrot⟩, hmeet⟩ := hfigure
  have hβsupport (x : Q) : x ∈ β.support ↔ ∃ y ∈ α.support, g * y = x := by
    rw [← closed_walk_mem_support_tail_iff β hβ.not_nil, ← hrot.mem_iff]
    simp only [List.mem_map, closed_walk_mem_support_tail_iff α hα.not_nil]
  have horiginal (x : Q) :
      (x ∈ α.support ∧ ∃ y ∈ α.support, g * y = x) ↔ x = v := by
    simpa only [hβsupport] using hmeet x
  let f := (cayleyLeftTranslation T v⁻¹).toHom
  let p : (mulCayley T).Walk 1 1 := (α.map f).copy (inv_mul_cancel v) (inv_mul_cancel v)
  have hpsupport (x : Q) : x ∈ p.support ↔ ∃ y ∈ α.support, v⁻¹ * y = x := by
    simp only [p, Walk.support_copy, Walk.support_map, List.mem_map]
    rfl
  refine ⟨n, p, v⁻¹ * g * v, Nat.le_trans (by decide : 1 ≤ 2) hn, ?_, by simpa [p] using hαlen, ?_⟩
  · rw [Walk.isCycle_copy]
    exact hα.map (fun _ _ h ↦ mul_left_cancel h)
  · intro x
    constructor
    · rintro ⟨hx, y, hy, heq⟩
      obtain ⟨u, hu, hux⟩ := (hpsupport x).mp hx
      obtain ⟨z, hz, hzy⟩ := (hpsupport y).mp hy
      have hgzu : g * z = u := by
        apply mul_left_cancel (a := v⁻¹)
        calc
          v⁻¹ * (g * z) = (v⁻¹ * g * v) * y := by rw [← hzy]; group
          _ = x := heq
          _ = v⁻¹ * u := hux.symm
      have huv : u = v := (horiginal u).mp ⟨hu, z, hz, hgzu⟩
      simpa [huv] using hux.symm
    · rintro rfl
      have hv := (horiginal v).mpr rfl
      obtain ⟨z, hz, hgz⟩ := hv.2
      refine ⟨p.start_mem_support, v⁻¹ * z, (hpsupport _).mpr ⟨z, hz, rfl⟩, ?_⟩
      calc
        (v⁻¹ * g * v) * (v⁻¹ * z) = v⁻¹ * (g * z) := by group
        _ = 1 := by rw [hgz]; simp

/-- A closed lift of a simple cycle is itself simple. -/
theorem closed_lift_isCycle
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    {S : Set G} {T : Set Q} {v : G} {q : Q}
    (p : (mulCayley T).Walk q q) (hp : p.IsCycle)
    (w : (mulCayley S).Walk v v)
    (hlen : w.length = p.length) (hmap : ∀ i, φ (w.getVert i) = p.getVert i) :
    w.IsCycle := by
  have hthree : 3 ≤ w.length := by simpa [hlen] using hp.three_le_length
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_, hthree⟩
  apply (Walk.IsPath.getVert_injOn_iff w.tail).mp
  intro i hi j hj hij
  simp only [Set.mem_ofPred_eq, Walk.length_tail] at hi hj
  have heq : p.getVert (i + 1) = p.getVert (j + 1) := by
    simpa only [Walk.getVert_tail, hmap] using congrArg φ hij
  have := hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) heq
  omega

/-- Concatenating two compatible lifts preserves the pointwise projection. -/
theorem append_lifts_getVert
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    {S : Set G} {T : Set Q} {a b c : G} {u v w : Q}
    (p : (mulCayley T).Walk u v) (r : (mulCayley T).Walk v w)
    (α : (mulCayley S).Walk a b) (β : (mulCayley S).Walk b c)
    (hlen : α.length = p.length)
    (hα : ∀ i, φ (α.getVert i) = p.getVert i)
    (hβ : ∀ i, φ (β.getVert i) = r.getVert i) :
    ∀ i, φ ((α.append β).getVert i) = (p.append r).getVert i := by
  intro i
  simp only [Walk.getVert_append, hlen]
  split <;> simp_all

/-- A closed lifted lobe and the translate coming from its lifted change
of basepoint already give a symmetric figure-eight. -/
theorem figureEight_of_closed_compatible_lift
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    {S : Set G} {T : Set Q}
    (p : (mulCayley T).Walk 1 1) (hp : p.IsCycle) (g : Q)
    (hmeet : ∀ x : Q, (x ∈ p.support ∧ ∃ y ∈ p.support, g * y = x) ↔ x = 1)
    (w : (mulCayley S).Walk 1 1)
    (hwlen : w.length = p.length) (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (u : G) (hu : u ∈ w.support) (hφu : φ u = g⁻¹)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) :
    HasSymmetricFigureEight S := by
  have hsupport : ∀ y ∈ w.support, φ y ∈ p.support := by
    intro y hy
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hy
    rw [hw]
    exact p.getVert_mem_support i
  apply hasSymmetricFigureEight_of_cycle_translate w n hn
    (closed_lift_isCycle φ p hp w hwlen hw) (hwlen.trans hplen) u⁻¹ 1
  intro x
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    have hφx : φ x = 1 := (hmeet (φ x)).mp
      ⟨hsupport x hx, φ y, hsupport y hy, by
        simpa [map_mul, map_inv, hφu] using congrArg φ hyx⟩
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have hpi : p.getVert i = 1 := by rw [← hw, hix, hφx]
    rcases (hp.getVert_endpoint_iff (by omega)).mp hpi with hi0 | hil
    · simpa [hi0] using hix.symm
    · rw [← hwlen] at hil
      simpa [hil] using hix.symm
  · rintro rfl
    exact ⟨w.start_mem_support, u, hu, inv_mul_cancel u⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lift the two lobes compatibly by lifting the two pieces of one lobe.
The second voltage is conjugate to the first. A trivial first voltage
already produces a symmetric figure-eight upstairs. -/
theorem compatible_lifts_or_figureEight
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q) (S : Set G)
    (p : (mulCayley (φ '' S)).Walk 1 1) (hp : p.IsCycle) (g : Q)
    (hmeet : ∀ x : Q, (x ∈ p.support ∧ ∃ y ∈ p.support, g * y = x) ↔ x = 1)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) :
    HasSymmetricFigureEight S ∨
    ∃ (r : (mulCayley (φ '' S)).Walk 1 1) (a b u : G)
      (w : (mulCayley S).Walk 1 a) (z : (mulCayley S).Walk 1 b),
      r.IsCycle ∧ r.length = p.length ∧
      (∀ q, (q ∈ p.support ∧ q ∈ r.support) ↔ q = 1) ∧
      a ≠ 1 ∧ b ≠ 1 ∧ φ a = 1 ∧ φ b = 1 ∧ u⁻¹ * a * u = b ∧
      w.length = p.length ∧ z.length = r.length ∧
      (∀ i, φ (w.getVert i) = p.getVert i) ∧
      (∀ i, φ (z.getVert i) = r.getVert i) := by
  classical
  have hginv : g⁻¹ ∈ p.support := by
    obtain ⟨q, hq, hgq⟩ := ((hmeet 1).mpr rfl).2
    rwa [eq_inv_of_mul_eq_one_right hgq] at hq
  let p₁ := p.takeUntil g⁻¹ hginv
  let p₂ := p.dropUntil g⁻¹ hginv
  obtain ⟨u, w₁, hw₁len, hw₁⟩ := cayley_walk_image_lift φ S p₁ 1 (map_one φ)
  have hφu : φ u = g⁻¹ := by
    have := hw₁ w₁.length
    rw [Walk.getVert_length, hw₁len, Walk.getVert_length] at this
    exact this
  obtain ⟨a, w₂, hw₂len, hw₂⟩ := cayley_walk_image_lift φ S p₂ u hφu
  have hφa : φ a = 1 := by
    have := hw₂ w₂.length
    rw [Walk.getVert_length, hw₂len, Walk.getVert_length] at this
    exact this
  let w := w₁.append w₂
  have hsplit : p₁.append p₂ = p := p.take_spec hginv
  have hwlen : w.length = p.length := by
    simp only [w, Walk.length_append, hw₁len, hw₂len]
    rw [← Walk.length_append, hsplit]
  have hw : ∀ i, φ (w.getVert i) = p.getVert i := by
    intro i
    rw [← hsplit]
    exact append_lifts_getVert φ p₁ p₂ w₁ w₂ hw₁len hw₁ hw₂ i
  by_cases ha : a = 1
  · subst a
    exact Or.inl (figureEight_of_closed_compatible_lift φ p hp g hmeet w hwlen hw
      u ((Walk.mem_support_append_iff w₁ w₂).mpr (Or.inl w₁.end_mem_support)) hφu n hn hplen)
  right
  let b := u⁻¹ * a * u
  let f := (cayleyLeftTranslation (φ '' S) g).toHom
  let r : (mulCayley (φ '' S)).Walk 1 1 :=
    ((p₂.append p₁).map f).copy (mul_inv_cancel g) (mul_inv_cancel g)
  let f₁ := (cayleyLeftTranslation S u⁻¹).toHom
  let f₂ := (cayleyLeftTranslation S (u⁻¹ * a)).toHom
  let z₁ : (mulCayley S).Walk 1 (u⁻¹ * a) :=
    (w₂.map f₁).copy (inv_mul_cancel u) rfl
  let z₂ : (mulCayley S).Walk (u⁻¹ * a) b :=
    (w₁.map f₂).copy (mul_one (u⁻¹ * a)) rfl
  let z := z₁.append z₂
  have hr : r.IsCycle := by
    change (((p.rotate g⁻¹ hginv).map f).copy _ _).IsCycle
    rw [Walk.isCycle_copy]
    exact (hp.rotate hginv).map (fun _ _ h ↦ mul_left_cancel h)
  have hrlen : r.length = p.length := by
    change (((p.rotate g⁻¹ hginv).map f).copy _ _).length = _
    simp
  have hrsupport (q : Q) : q ∈ r.support ↔ ∃ y ∈ p.support, g * y = q := by
    change q ∈ (((p.rotate g⁻¹ hginv).map f).copy _ _).support ↔ _
    simp only [Walk.support_copy, Walk.support_map, List.mem_map,
      Walk.mem_support_rotate_iff]
    rfl
  have hb : b ≠ 1 := by
    intro hb
    apply ha
    have := congrArg (fun y : G ↦ u * y * u⁻¹) hb
    simpa [b, mul_assoc] using this
  have hφb : φ b = 1 := by simp [b, map_mul, hφa]
  have hzlen : z.length = r.length := by
    simp only [z, z₁, z₂, Walk.length_append, Walk.length_copy, Walk.length_map,
      hw₁len, hw₂len]
    rw [hrlen, ← hsplit, Walk.length_append, Nat.add_comm]
  have hz : ∀ i, φ (z.getVert i) = r.getVert i := by
    intro i
    simp only [z, z₁, z₂, r, Walk.getVert_append, Walk.getVert_copy,
      Walk.getVert_map, Walk.length_copy, Walk.length_map, hw₂len,
      Walk.getVert_append]
    change φ (if i < p₂.length then u⁻¹ * w₂.getVert i
      else (u⁻¹ * a) * w₁.getVert (i - p₂.length)) =
      g * (if i < p₂.length then p₂.getVert i else p₁.getVert (i - p₂.length))
    split
    · simp only [map_mul, map_inv, hφu, inv_inv, hw₂]
    · simp only [map_mul, map_inv, hφu, hφa, inv_inv, mul_one, hw₁]
  exact ⟨r, a, b, u, w, z, hr, hrlen,
    (fun q ↦ by simpa only [hrsupport] using hmeet q),
    ha, hb, hφa, hφb, rfl, hwlen, hzlen, hw, hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 1.2, in a strengthened form: inverse closure, generation and
identity exclusion are not needed to lift an existing symmetric figure-eight. -/
theorem symmetric_figure_eight_lifts
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G))
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hfigure : HasSymmetricFigureEight
      ((QuotientGroup.mk (s := A)) '' S \ {1})) :
    HasSymmetricFigureEight S := by
  have himage : HasSymmetricFigureEight ((QuotientGroup.mk' A) '' S) := by
    unfold HasSymmetricFigureEight at hfigure ⊢
    rw [mulCayley_erase_one] at hfigure
    exact hfigure
  obtain ⟨n, p, g, hn, hp, hplen, hmeet⟩ := himage.exists_cycle_translate_based_one
  obtain h | ⟨r, a, b, u, w, z, hr, hrlen, hdisj, ha, hb, hφa, hφb,
      hconj, hwlen, hzlen, hw, hz⟩ :=
    compatible_lifts_or_figureEight (QuotientGroup.mk' A) S p hp g hmeet n hn hplen
  · exact h
  · have haA : a ∈ A := (QuotientGroup.eq_one_iff a).mp hφa
    have hbA : b ∈ A := (QuotientGroup.eq_one_iff b).mp hφb
    have hcomm : Commute a b := by
      exact congrArg Subtype.val (mul_comm (⟨a, haA⟩ : A) (⟨b, hbA⟩ : A))
    exact hasSymmetricFigureEight_of_nontrivial_compatible_lifts hodd
      (QuotientGroup.mk' A) p r hp hr hdisj ha hb hcomm hφa hφb hconj
      w z hwlen hzlen hw hz n hn hplen (hrlen.trans hplen)

end CayleyErdősGyárfás
