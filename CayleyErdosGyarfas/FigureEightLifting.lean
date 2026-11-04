module

public import CayleyErdosGyarfas.Lifting
public import CayleyErdosGyarfas.Basic

public section

namespace CayleyErdősGyárfás

/-- Squaring is injective in any group of finite odd cardinality. -/
theorem square_injective_of_odd_natCard {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) : Function.Injective (fun a : G ↦ a ^ 2) :=
  hodd.coprime_two_right.pow_left_bijective.1

/-- In a group of odd cardinality, only the identity is conjugate to its inverse. -/
theorem eq_one_of_conjugate_inv_of_odd_natCard {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a g : G} (h : g⁻¹ * a * g = a⁻¹) : a = 1 := by
  have hleft : a * g = g * a⁻¹ := calc
    a * g = g * (g⁻¹ * a * g) := by group
    _ = g * a⁻¹ := by rw [h]
  have hsq : (a * g) ^ 2 = g ^ 2 := calc
    (a * g) ^ 2 = (a * g) * a * g := by simp [pow_two, mul_assoc]
    _ = (g * a⁻¹) * a * g := by rw [hleft]
    _ = g ^ 2 := by simp [pow_two, mul_assoc]
  have := square_injective_of_odd_natCard hodd hsq
  exact mul_right_cancel (by simpa using this : a * g = 1 * g)

/-- The exceptional five-element configuration in the manuscript is impossible:
a nonidentity element cannot be conjugate to the inverse of its square if its
conjugate squares back to the original element. -/
theorem eq_one_of_conjugate_inverse_square {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a b g : G}
    (hconj : g⁻¹ * a * g = b) (hb : b = (a * a)⁻¹) (ha : b * b = a) : a = 1 := by
  let ψ : G ≃* G := MulAut.conj g⁻¹
  have hψ : ψ a = b := by simpa [ψ, MulAut.conj_apply, mul_assoc] using hconj
  have hψψ : ψ (ψ a) = a⁻¹ := by
    rw [hψ, hb, map_inv, map_mul, hψ, ha]
  apply eq_one_of_conjugate_inv_of_odd_natCard hodd (g := g * g)
  simpa [ψ, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hψψ

/-- The endpoint separation used to choose one of the two commutator figures in
Lemma 1.2. This formulation incorporates the odd-order conjugacy argument. -/
theorem conjugate_products_escape_inverse_set {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a b g : G} (ha : a ≠ 1) (hb : b ≠ 1)
    (hconj : g⁻¹ * a * g = b) :
    a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G) ∨
      a * b⁻¹ ∉ ({a, a⁻¹, b, b⁻¹} : Set G) := by
  by_contra! h
  rcases h with ⟨h₁, h₂⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  have h₁' : a * b = a⁻¹ ∨ a * b = b⁻¹ := by
    rcases h₁ with h | h | h | h
    · exact False.elim (hb (mul_left_cancel (by simpa using h : a * b = a * 1)))
    · exact Or.inl h
    · exact False.elim (ha (mul_right_cancel (by simpa using h : a * b = 1 * b)))
    · exact Or.inr h
  have h₂' : a * b⁻¹ = a⁻¹ ∨ a * b⁻¹ = b := by
    rcases h₂ with h | h | h | h
    · have : b⁻¹ = 1 := mul_left_cancel (by simpa using h : a * b⁻¹ = a * 1)
      exact False.elim (hb (by simpa using this))
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (ha (mul_right_cancel (by simpa using h : a * b⁻¹ = 1 * b⁻¹)))
  have h₁'' : b = (a * a)⁻¹ ∨ a = (b * b)⁻¹ := by
    rcases h₁' with h | h
    · left
      calc b = a⁻¹ * (a * b) := by group
           _ = a⁻¹ * a⁻¹ := by rw [h]
           _ = (a * a)⁻¹ := by group
    · right
      calc a = (a * b) * b⁻¹ := by group
           _ = b⁻¹ * b⁻¹ := by rw [h]
           _ = (b * b)⁻¹ := by group
  have h₂'' : b = a * a ∨ a = b * b := by
    rcases h₂' with h | h
    · left
      calc b = (a * b⁻¹)⁻¹ * a := by group
           _ = (a⁻¹)⁻¹ * a := by rw [h]
           _ = a * a := by simp
    · right
      calc a = (a * b⁻¹) * b := by group
           _ = b * b := by rw [h]
  rcases h₁'' with h₁ | h₁ <;> rcases h₂'' with h₂ | h₂
  · have hsq : a ^ 2 = (a⁻¹) ^ 2 := by simpa [pow_two, mul_inv_rev] using h₂.symm.trans h₁
    have hinv := square_injective_of_odd_natCard hodd hsq
    exact ha (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using hinv))
  · exact ha (eq_one_of_conjugate_inverse_square hodd hconj h₁ h₂.symm)
  · have hconj' : (g⁻¹)⁻¹ * b * g⁻¹ = a := by rw [← hconj]; group
    exact hb (eq_one_of_conjugate_inverse_square hodd hconj' h₁ h₂.symm)
  · have hsq : b ^ 2 = (b⁻¹) ^ 2 := by simpa [pow_two, mul_inv_rev] using h₂.symm.trans h₁
    have hinv := square_injective_of_odd_natCard hodd hsq
    exact hb (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using hinv))

/-- Distinct kernel translates of the half-open lift of a simple quotient cycle
have disjoint vertices. The endpoint is excluded to avoid counting it twice. -/
theorem translated_lift_vertex_eq_iff {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle)
    {a b : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    {u v : G} (hu : φ u = 1) (hv : φ v = 1)
    {i j : ℕ} (hi : i < p.length) (hj : j < p.length) :
    u * w.getVert i = v * w.getVert j ↔ i = j ∧ u = v := by
  constructor
  · intro heq
    have hproj : p.getVert i = p.getVert j := by
      simpa only [map_mul, hu, hv, one_mul, hw] using congrArg φ heq
    have hij : i = j := hp.getVert_injOn' (by exact Nat.le_pred_of_lt hi)
      (by exact Nat.le_pred_of_lt hj) hproj
    refine ⟨hij, ?_⟩
    subst j
    exact mul_right_cancel heq
  · rintro ⟨rfl, rfl⟩
    rfl

/-- For two lifted quotient cycles meeting only at their basepoint, kernel
translates can meet on their half-open vertex sequences only at the starts. -/
theorem translated_disjoint_lifts_vertex_eq_iff {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p r : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = q)
    {a b c : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (z : (SimpleGraph.mulCayley S).Walk a c)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    {u v : G} (hu : φ u = 1) (hv : φ v = 1)
    {i j : ℕ} (hi : i < p.length) (hj : j < r.length) :
    u * w.getVert i = v * z.getVert j ↔ i = 0 ∧ j = 0 ∧ u = v := by
  constructor
  · intro heq
    have hproj : p.getVert i = r.getVert j := by
      simpa only [map_mul, hu, hv, one_mul, hw, hz] using congrArg φ heq
    have hqi : p.getVert i = q := (hdisj _).mp
      ⟨p.getVert_mem_support i, hproj ▸ r.getVert_mem_support j⟩
    have hqj : r.getVert j = q := hproj.symm.trans hqi
    have hi0 : i = 0 := hp.getVert_injOn' (Nat.le_pred_of_lt hi)
      (by have := hp.three_le_length; simp only [Set.mem_ofPred_eq]; omega)
      (by simpa using hqi)
    have hj0 : j = 0 := hr.getVert_injOn' (Nat.le_pred_of_lt hj)
      (by have := hr.three_le_length; simp only [Set.mem_ofPred_eq]; omega)
      (by simpa using hqj)
    refine ⟨hi0, hj0, ?_⟩
    subst i; subst j
    exact mul_right_cancel (by simpa using heq : u * a = v * a)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- The only vertices of a lifted simple quotient cycle lying over its basepoint
are the two endpoints of the lift. -/
theorem lifted_cycle_basepoint_iff {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle)
    {a b : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (hlen : w.length = p.length) (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    {x : G} (hx : x ∈ w.support) : φ x = q ↔ x = a ∨ x = b := by
  obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  constructor
  · intro h
    have hi' : i = 0 ∨ i = p.length :=
      (hp.getVert_endpoint_iff (by omega)).mp (by simpa only [hw] using h)
    rcases hi' with rfl | hi'
    · simp
    · rw [← hlen] at hi'
      simp [hi']
  · intro h
    rcases h with h | h
    · rw [h]
      simpa using hw 0
    · rw [h]
      calc φ b = φ (w.getVert w.length) := by simp
           _ = p.getVert w.length := hw _
           _ = q := by rw [hlen]; simp

/-- A lift of a simple quotient cycle with distinct endpoints is a path. -/
theorem lifted_cycle_isPath_of_ne {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle)
    {a b : G} (w : (SimpleGraph.mulCayley S).Walk a b) (hab : a ≠ b)
    (hlen : w.length = p.length) (hw : ∀ i, φ (w.getVert i) = p.getVert i) :
    w.IsPath := by
  apply (SimpleGraph.Walk.IsPath.getVert_injOn_iff w).mp
  intro i hi j hj hij
  simp only [Set.mem_ofPred_eq] at hi hj
  have hproj : p.getVert i = p.getVert j := by simpa only [hw] using congrArg φ hij
  by_cases hil : i = w.length
  · subst i
    have hj' : j = 0 ∨ j = p.length :=
      (hp.getVert_endpoint_iff (by omega)).mp (by simpa only [hlen, SimpleGraph.Walk.getVert_length] using hproj.symm)
    rcases hj' with rfl | hj'
    · exact False.elim (hab (by simpa using hij.symm))
    · omega
  · by_cases hjl : j = w.length
    · subst j
      have hi' : i = 0 ∨ i = p.length :=
        (hp.getVert_endpoint_iff (by omega)).mp (by simpa only [hlen, SimpleGraph.Walk.getVert_length] using hproj)
      rcases hi' with rfl | hi'
      · exact False.elim (hab (by simpa using hij))
      · omega
    · exact hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hproj

/-- Two distinct kernel translates of a lifted lobe can meet only at endpoints. -/
theorem translated_lift_support_intersection {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle)
    {a b : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (hlen : w.length = p.length) (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    {u v x y : G} (hu : φ u = 1) (hv : φ v = 1) (huv : u ≠ v)
    (hx : x ∈ w.support) (hy : y ∈ w.support) (hxy : u * x = v * y) :
    (x = a ∨ x = b) ∧ (y = a ∨ y = b) := by
  have hproj : φ x = φ y := by simpa only [map_mul, hu, hv, one_mul] using congrArg φ hxy
  have hq : φ x = q := by
    by_contra hq
    obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
    have hil' : i < p.length := by
      have hne : i ≠ w.length := by
        intro heq
        apply hq
        rw [← hi, heq, hw, hlen]
        simp
      omega
    have hjl' : j < p.length := by
      have hne : j ≠ w.length := by
        intro heq
        apply hq
        rw [hproj, ← hj, heq, hw, hlen]
        simp
      omega
    have := (translated_lift_vertex_eq_iff φ p hp w hw hu hv hil' hjl').mp
      (by simpa only [hi, hj] using hxy)
    exact huv this.2
  exact ⟨(lifted_cycle_basepoint_iff φ p hp w hlen hw hx).mp hq,
    (lifted_cycle_basepoint_iff φ p hp w hlen hw hy).mp (hproj.symm.trans hq)⟩

/-- Translates of different lifted lobes of a quotient figure-eight can meet
only at endpoints. -/
theorem translated_disjoint_lifts_support_intersection {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p r : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = q)
    {a b c : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (z : (SimpleGraph.mulCayley S).Walk a c)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    {u v x y : G} (hu : φ u = 1) (hv : φ v = 1)
    (hx : x ∈ w.support) (hy : y ∈ z.support) (hxy : u * x = v * y) :
    (x = a ∨ x = b) ∧ (y = a ∨ y = c) := by
  have hproj : φ x = φ y := by simpa only [map_mul, hu, hv, one_mul] using congrArg φ hxy
  have hxq : φ x ∈ p.support := by
    obtain ⟨i, rfl, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    rw [hw]
    exact p.getVert_mem_support i
  have hyq : φ y ∈ r.support := by
    obtain ⟨i, rfl, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
    rw [hz]
    exact r.getVert_mem_support i
  have hq : φ x = q := (hdisj _).mp ⟨hxq, hproj ▸ hyq⟩
  exact ⟨(lifted_cycle_basepoint_iff φ p hp w hwlen hw hx).mp hq,
    (lifted_cycle_basepoint_iff φ r hr z hzlen hz hy).mp (hproj.symm.trans hq)⟩

/-- Append two paths meeting only at the common endpoint. -/
theorem isPath_append_of_support_intersection {V : Type*} {Γ : SimpleGraph V}
    {a b c : V} {p : Γ.Walk a b} {q : Γ.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (h : ∀ x, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  apply List.disjoint_left.mpr
  intro x hx hx'
  have hxb : x = b := h x hx (List.mem_of_mem_tail hx')
  subst x
  have hn : (b :: q.support.tail).Nodup := by
    rw [SimpleGraph.Walk.cons_tail_support]
    exact hq.support_nodup
  exact (List.nodup_cons.mp hn).1 hx'

/-- Two paths with the same endpoints and no other shared vertices form a cycle. -/
theorem isCycle_append_reverse_of_support_intersection {V : Type*} {Γ : SimpleGraph V}
    {a b : V} {p q : Γ.Walk a b} (hp : p.IsPath) (hq : q.IsPath)
    (h : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b)
    (hlen : 1 < p.length ∨ 1 < q.length) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse _ (by simpa using hlen)
  apply List.disjoint_left.mpr
  intro x hx hx'
  have hxa : x = a ∨ x = b := h x (List.mem_of_mem_tail hx)
    (by simpa using (List.mem_of_mem_tail hx' : x ∈ q.reverse.support))
  rcases hxa with hxa | hxb
  · subst x
    have hn : (a :: p.support.tail).Nodup := by
      rw [SimpleGraph.Walk.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hn).1 hx
  · subst x
    have hn : (b :: q.reverse.support.tail).Nodup := by
      rw [SimpleGraph.Walk.cons_tail_support]
      exact hq.reverse.support_nodup
    exact (List.nodup_cons.mp hn).1 hx'

/-- The equal nontrivial endpoint case of Lemma 1.2: the two lifted lobes,
followed in opposite directions, form a cycle whose inverse-endpoint translate
meets it exactly once. -/
theorem hasSymmetricFigureEight_of_equal_voltage_lifts
    {G Q : Type*} [Group G] [Group Q] (hodd : Odd (Nat.card G))
    (φ : G →* Q) {S : Set G} {T : Set Q}
    (p r : (SimpleGraph.mulCayley T).Walk 1 1) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = 1)
    {a : G} (ha : a ≠ 1) (hφa : φ a = 1)
    (w z : (SimpleGraph.mulCayley S).Walk 1 a)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) (hrlen : r.length = 2 ^ n) :
    HasSymmetricFigureEight S := by
  have hwpath := lifted_cycle_isPath_of_ne φ p hp w (Ne.symm ha) hwlen hw
  have hzpath := lifted_cycle_isPath_of_ne φ r hr z (Ne.symm ha) hzlen hz
  let c := w.append z.reverse
  have hc : c.IsCycle := isCycle_append_reverse_of_support_intersection hwpath hzpath
    (fun x hx hz' ↦ (translated_disjoint_lifts_support_intersection φ p r hp hr hdisj
      w z hwlen hzlen hw hz (u := 1) (v := 1) (by simp) (by simp) hx hz' rfl).1)
    (Or.inl (by have := hp.three_le_length; omega))
  have hclen : c.length = 2 ^ (n + 1) := by
    simp only [c, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      hwlen, hzlen, hplen, hrlen, pow_succ]
    omega
  apply hasSymmetricFigureEight_of_cycle_translate c (n + 1) (by omega) hc hclen a⁻¹ 1
  have hφai : φ a⁻¹ = 1 := by simp [hφa]
  have hne : (1 : G) ≠ a⁻¹ := by simpa using ha
  have hai : a⁻¹ ≠ a := by
    intro h
    exact ha (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using h.symm))
  have hsupport (x : G) : x ∈ c.support ↔ x ∈ w.support ∨ x ∈ z.support := by simp [c]
  intro x
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    rw [hsupport] at hx hy
    have he : (x = 1 ∨ x = a) ∧ (y = 1 ∨ y = a) := by
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact translated_lift_support_intersection φ p hp w hwlen hw
          (u := 1) (v := a⁻¹) (by simp) hφai hne hx hy (by simpa using hyx.symm)
      · exact translated_disjoint_lifts_support_intersection φ p r hp hr hdisj
          w z hwlen hzlen hw hz (u := 1) (v := a⁻¹) (by simp) hφai hx hy
          (by simpa using hyx.symm)
      · exact translated_disjoint_lifts_support_intersection φ r p hr hp
          (by intro x; simpa [and_comm] using hdisj x)
          z w hzlen hwlen hz hw (u := 1) (v := a⁻¹) (by simp) hφai hx hy
          (by simpa using hyx.symm)
      · exact translated_lift_support_intersection φ r hr z hzlen hz
          (u := 1) (v := a⁻¹) (by simp) hφai hne hx hy (by simpa using hyx.symm)
    rcases he with ⟨hx | hx, hy | hy⟩ <;> simp_all
  · rintro rfl
    refine ⟨by simp [c], a, ?_, by simp⟩
    rw [hsupport]
    exact Or.inl w.end_mem_support

set_option backward.isDefEq.respectTransparency false in
/-- The lifted commutator square is a simple cycle whenever its four corner
vertices are distinct. Its support is recorded for the figure-eight argument. -/
theorem commutator_cycle_of_lifts
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q) {S : Set G} {T : Set Q}
    (p r : (SimpleGraph.mulCayley T).Walk 1 1) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = 1)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (habi : a ≠ b⁻¹)
    (hcomm : Commute a b) (hφa : φ a = 1) (hφb : φ b = 1)
    (w : (SimpleGraph.mulCayley S).Walk 1 a)
    (z : (SimpleGraph.mulCayley S).Walk 1 b)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i) :
    ∃ c : (SimpleGraph.mulCayley S).Walk 1 1,
      c.IsCycle ∧ c.length = 2 * (w.length + z.length) ∧
      ∀ x, x ∈ c.support ↔
        (∃ u ∈ ({1, b} : Set G), ∃ y ∈ w.support, u * y = x) ∨
        (∃ u ∈ ({1, a} : Set G), ∃ y ∈ z.support, u * y = x) := by
  have hprod : a * b ≠ 1 := fun h ↦ habi (eq_inv_of_mul_eq_one_left h)
  have hprod' : b * a ≠ 1 := fun h ↦ hprod (hcomm.eq.trans h)
  have hcross {u v x y : G} := translated_disjoint_lifts_support_intersection φ p r hp hr hdisj
    w z hwlen hzlen hw hz (u := u) (v := v) (x := x) (y := y)
  have hcross' {u v x y : G} := translated_disjoint_lifts_support_intersection φ r p hr hp
    (by intro x; simpa [and_comm] using hdisj x) z w hzlen hwlen hz hw
    (u := u) (v := v) (x := x) (y := y)
  have hsamew {u v x y : G} := translated_lift_support_intersection φ p hp w hwlen hw
    (u := u) (v := v) (x := x) (y := y)
  have hsamez {u v x y : G} := translated_lift_support_intersection φ r hr z hzlen hz
    (u := u) (v := v) (x := x) (y := y)
  let az : (SimpleGraph.mulCayley S).Walk a (a * b) :=
    (z.map (cayleyLeftTranslation S a).toHom).copy (by simp [cayleyLeftTranslation]) rfl
  let bw : (SimpleGraph.mulCayley S).Walk b (a * b) :=
    (w.map (cayleyLeftTranslation S b).toHom).copy (by simp [cayleyLeftTranslation])
      (by simpa [cayleyLeftTranslation] using hcomm.eq.symm)
  have haz (x : G) : x ∈ az.support ↔ ∃ y ∈ z.support, a * y = x := by
    change x ∈ ((z.map (cayleyLeftTranslation S a).toHom).copy _ _).support ↔ _
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
    change x ∈ z.support.map (a * ·) ↔ _
    exact List.mem_map
  have hbw (x : G) : x ∈ bw.support ↔ ∃ y ∈ w.support, b * y = x := by
    change x ∈ ((w.map (cayleyLeftTranslation S b).toHom).copy _ _).support ↔ _
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
    change x ∈ w.support.map (b * ·) ↔ _
    exact List.mem_map
  have hwpath := lifted_cycle_isPath_of_ne φ p hp w (Ne.symm ha) hwlen hw
  have hzpath := lifted_cycle_isPath_of_ne φ r hr z (Ne.symm hb) hzlen hz
  have hazpath : az.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy ..).mpr
    exact hzpath.map (fun _ _ h ↦ mul_left_cancel h)
  have hbwpath : bw.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy ..).mpr
    exact hwpath.map (fun _ _ h ↦ mul_left_cancel h)
  let P := w.append az
  let R := z.append bw
  have hP : P.IsPath := isPath_append_of_support_intersection hwpath hazpath (by
    intro x hx hax
    obtain ⟨y, hy, hyx⟩ := (haz x).mp hax
    have he := hcross (u := 1) (v := a) (by simp) hφa hx hy (by simpa using hyx.symm)
    clear hcross hcross' hsamew hsamez
    rcases he with ⟨hx | hx, hy | hy⟩ <;> simp_all)
  have hR : R.IsPath := isPath_append_of_support_intersection hzpath hbwpath (by
    intro x hx hbx
    obtain ⟨y, hy, hyx⟩ := (hbw x).mp hbx
    have he := hcross' (u := 1) (v := b) (by simp) hφb hx hy (by simpa using hyx.symm)
    clear hcross hcross' hsamew hsamez
    rcases he with ⟨hx | hx, hy | hy⟩ <;> simp_all)
  have hPR : ∀ x, x ∈ P.support → x ∈ R.support → x = 1 ∨ x = a * b := by
    intro x hx hx'
    simp only [P, R, SimpleGraph.Walk.mem_support_append_iff, haz, hbw] at hx hx'
    rcases hx with hx | ⟨y, hy, hyx⟩ <;> rcases hx' with hx' | ⟨y', hy', hyx'⟩
    · have he := hcross (u := 1) (v := 1) (by simp) (by simp) hx hx' rfl
      clear hcross hcross' hsamew hsamez
      rcases he with ⟨hx | hx, hx' | hx'⟩ <;> simp_all
    · have he := hsamew (u := 1) (v := b) (by simp) hφb (Ne.symm hb) hx hy'
        (by simpa using hyx'.symm)
      clear hcross hcross' hsamew hsamez
      rcases he with ⟨hx | hx, hy' | hy'⟩ <;> simp_all
    · have he := hsamez (u := a) (v := 1) hφa (by simp) ha hy hx'
        (by simpa using hyx)
      clear hcross hcross' hsamew hsamez
      rcases he with ⟨hy | hy, hx' | hx'⟩ <;> simp_all
    · have he := hcross' (u := a) (v := b) hφa hφb hy hy' (hyx.trans hyx'.symm)
      clear hcross hcross' hsamew hsamez
      rcases he with ⟨hy | hy, hy' | hy'⟩ <;> simp_all
  refine ⟨P.append R.reverse, ?_, ?_, ?_⟩
  · exact isCycle_append_reverse_of_support_intersection hP hR hPR
      (Or.inl (by have := hp.three_le_length; simp [P]; omega))
  · simp [P, R, az, bw]
    omega
  · intro x
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse, P, R, haz, hbw, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ((hx | ⟨y, hy, rfl⟩) | (hx | ⟨y, hy, rfl⟩))
      · exact Or.inl ⟨1, Or.inl rfl, x, hx, by simp⟩
      · exact Or.inr ⟨a, Or.inr rfl, y, hy, rfl⟩
      · exact Or.inr ⟨1, Or.inl rfl, x, hx, by simp⟩
      · exact Or.inl ⟨b, Or.inr rfl, y, hy, rfl⟩
    · rintro (⟨u, hu, y, hy, rfl⟩ | ⟨u, hu, y, hy, rfl⟩) <;> rcases hu with rfl | rfl
      · simp [hy]
      · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
      · simp [hy]
      · exact Or.inl (Or.inr ⟨y, hy, rfl⟩)

/-- The corner sets of a commutator square and its opposite translate meet only
at the identity under the endpoint separation condition. -/
theorem commutator_corners_intersection {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a b x y : G}
    (ha : a ≠ 1) (hb : b ≠ 1) (habi : a ≠ b⁻¹) (hcomm : Commute a b)
    (hescape : a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G))
    (hx : x ∈ ({1, a, b, a * b} : Set G))
    (hy : y ∈ ({1, a, b, a * b} : Set G))
    (hxy : (a * b)⁻¹ * y = x) : x = 1 := by
  have hprod : a * b ≠ 1 := fun h ↦ habi (eq_inv_of_mul_eq_one_left h)
  have hga : (a * b)⁻¹ * a = b⁻¹ := by group
  have hgb : (a * b)⁻¹ * b = a⁻¹ := by rw [hcomm.eq]; group
  have hai : a⁻¹ ≠ a := by
    intro h
    exact ha (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using h.symm))
  have hbi : b⁻¹ ≠ b := by
    intro h
    exact hb (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using h.symm))
  have hpi : (a * b)⁻¹ ≠ a * b := by
    intro h
    exact hprod (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using h.symm))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx hy hescape
  obtain ⟨hea, heai, heb, hebi⟩ := hescape
  have hia : (a * b)⁻¹ ≠ a := by
    intro h
    apply heai
    simpa using congrArg Inv.inv h
  have hib : (a * b)⁻¹ ≠ b := by
    intro h
    apply hebi
    simpa using congrArg Inv.inv h
  have hi1 : (a * b)⁻¹ ≠ 1 := by
    intro h
    exact hprod (by simpa only [inv_inv, inv_one] using congrArg Inv.inv h)
  have hai1 : a⁻¹ ≠ 1 := by simpa using ha
  have hbi1 : b⁻¹ ≠ 1 := by simpa using hb
  have haiB : a⁻¹ ≠ b := by
    intro h
    apply habi
    simpa using congrArg Inv.inv h
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
    rw [hx, hy] at hxy <;> rw [hx] <;>
    simp only [mul_one, inv_mul_cancel, hga, hgb] at hxy <;> grind only

set_option backward.isDefEq.respectTransparency false in
/-- The generic commutator case of Lemma 1.2, including its translated second lobe. -/
theorem hasSymmetricFigureEight_of_commutator_lifts
    {G Q : Type*} [Group G] [Group Q] (hodd : Odd (Nat.card G))
    (φ : G →* Q) {S : Set G} {T : Set Q}
    (p r : (SimpleGraph.mulCayley T).Walk 1 1) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = 1)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (habi : a ≠ b⁻¹)
    (hcomm : Commute a b) (hφa : φ a = 1) (hφb : φ b = 1)
    (hescape : a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G))
    (w : (SimpleGraph.mulCayley S).Walk 1 a)
    (z : (SimpleGraph.mulCayley S).Walk 1 b)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) (hrlen : r.length = 2 ^ n) :
    HasSymmetricFigureEight S := by
  obtain ⟨c, hc, hclen, hsupport⟩ := commutator_cycle_of_lifts φ p r hp hr hdisj
    ha hb hab habi hcomm hφa hφb w z hwlen hzlen hw hz
  have hclen' : c.length = 2 ^ (n + 2) := by
    rw [hclen, hwlen, hzlen, hplen, hrlen, pow_add]
    ring
  let g := (a * b)⁻¹
  have hprod : a * b ≠ 1 := fun h ↦ habi (eq_inv_of_mul_eq_one_left h)
  have hga : g * a = b⁻¹ := by dsimp [g]; group
  have hgb : g * b = a⁻¹ := by dsimp [g]; rw [hcomm.eq]; group
  have hφg : φ g = 1 := by simp [g, map_mul, hφa, hφb]
  have hcornerW {u x : G} (hu : u ∈ ({1, b} : Set G)) (hx : x = 1 ∨ x = a) :
      u * x ∈ ({1, a, b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl <;> rcases hx with rfl | rfl <;> simp [hcomm.eq]
  have hcornerZ {u x : G} (hu : u ∈ ({1, a} : Set G)) (hx : x = 1 ∨ x = b) :
      u * x ∈ ({1, a, b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl <;> rcases hx with rfl | rfl <;> simp
  have hcoeffW {u v : G} (hu : u ∈ ({1, b} : Set G)) (hv : v ∈ ({1, b} : Set G)) :
      u ≠ g * v := by
    intro heq
    have hu' : u ∈ ({1, a, b, a * b} : Set G) := by
      simpa using hcornerW hu (Or.inl rfl : (1 : G) = 1 ∨ (1 : G) = a)
    have hv' : v ∈ ({1, a, b, a * b} : Set G) := by
      simpa using hcornerW hv (Or.inl rfl : (1 : G) = 1 ∨ (1 : G) = a)
    have hu1 := commutator_corners_intersection hodd ha hb habi hcomm hescape hu' hv' heq.symm
    rw [hu1] at heq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hprod ((inv_eq_one).mp (by simpa only [mul_one] using heq.symm))
    · exact ha ((inv_eq_one).mp (hgb.symm.trans heq.symm))
  have hcoeffZ {u v : G} (hu : u ∈ ({1, a} : Set G)) (hv : v ∈ ({1, a} : Set G)) :
      u ≠ g * v := by
    intro heq
    have hu' : u ∈ ({1, a, b, a * b} : Set G) := by
      simpa using hcornerZ hu (Or.inl rfl : (1 : G) = 1 ∨ (1 : G) = b)
    have hv' : v ∈ ({1, a, b, a * b} : Set G) := by
      simpa using hcornerZ hv (Or.inl rfl : (1 : G) = 1 ∨ (1 : G) = b)
    have hu1 := commutator_corners_intersection hodd ha hb habi hcomm hescape hu' hv' heq.symm
    rw [hu1] at heq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hprod ((inv_eq_one).mp (by simpa only [mul_one] using heq.symm))
    · exact hb ((inv_eq_one).mp (hga.symm.trans heq.symm))
  have hkerW {u : G} (hu : u ∈ ({1, b} : Set G)) : φ u = 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl <;> simp [hφb]
  have hkerZ {u : G} (hu : u ∈ ({1, a} : Set G)) : φ u = 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl <;> simp [hφa]
  apply hasSymmetricFigureEight_of_cycle_translate c (n + 2) (by omega) hc hclen' g 1
  intro x
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    have hcorners : x ∈ ({1, a, b, a * b} : Set G) ∧ y ∈ ({1, a, b, a * b} : Set G) := by
      rcases (hsupport x).mp hx with ⟨u, hu, s, hs, hus⟩ | ⟨u, hu, s, hs, hus⟩ <;>
        rcases (hsupport y).mp hy with ⟨v, hv, t, ht, hvt⟩ | ⟨v, hv, t, ht, hvt⟩
      all_goals
        have heq : u * s = (g * v) * t := by rw [mul_assoc, hvt, hxy, hus]
      · have he := translated_lift_support_intersection φ p hp w hwlen hw
          (hkerW hu) (by simp [map_mul, hφg, hkerW hv]) (hcoeffW hu hv) hs ht heq
        exact ⟨hus ▸ hcornerW hu he.1, hvt ▸ hcornerW hv he.2⟩
      · have he := translated_disjoint_lifts_support_intersection φ p r hp hr hdisj
          w z hwlen hzlen hw hz (hkerW hu) (by simp [map_mul, hφg, hkerZ hv]) hs ht heq
        exact ⟨hus ▸ hcornerW hu he.1, hvt ▸ hcornerZ hv he.2⟩
      · have he := translated_disjoint_lifts_support_intersection φ r p hr hp
          (by intro q; simpa [and_comm] using hdisj q) z w hzlen hwlen hz hw
          (hkerZ hu) (by simp [map_mul, hφg, hkerW hv]) hs ht heq
        exact ⟨hus ▸ hcornerZ hu he.1, hvt ▸ hcornerW hv he.2⟩
      · have he := translated_lift_support_intersection φ r hr z hzlen hz
          (hkerZ hu) (by simp [map_mul, hφg, hkerZ hv]) (hcoeffZ hu hv) hs ht heq
        exact ⟨hus ▸ hcornerZ hu he.1, hvt ▸ hcornerZ hv he.2⟩
    exact commutator_corners_intersection hodd ha hb habi hcomm hescape hcorners.1 hcorners.2 hxy
  · rintro rfl
    refine ⟨c.start_mem_support, a * b, ?_, by simp [g]⟩
    apply (hsupport (a * b)).mpr
    exact Or.inr ⟨a, by simp, b, z.end_mem_support, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Reverse a lifted quotient lobe and translate it back to the identity. The
new endpoint is the inverse of the original endpoint. -/
theorem exists_inverse_voltage_lift {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q}
    (r : (SimpleGraph.mulCayley T).Walk 1 1) {b : G} (hφb : φ b = 1)
    (z : (SimpleGraph.mulCayley S).Walk 1 b)
    (hzlen : z.length = r.length) (hz : ∀ i, φ (z.getVert i) = r.getVert i) :
    ∃ z' : (SimpleGraph.mulCayley S).Walk 1 b⁻¹,
      z'.length = r.reverse.length ∧ ∀ i, φ (z'.getVert i) = r.reverse.getVert i := by
  let z' : (SimpleGraph.mulCayley S).Walk 1 b⁻¹ :=
    (z.reverse.map (cayleyLeftTranslation S b⁻¹).toHom).copy
      (by simp [cayleyLeftTranslation]) (by simp [cayleyLeftTranslation])
  refine ⟨z', by simpa [z'] using hzlen, ?_⟩
  intro i
  simp only [z', SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_map,
    SimpleGraph.Walk.getVert_reverse]
  change φ (b⁻¹ * z.getVert (z.length - i)) = r.getVert (r.length - i)
  rw [map_mul, map_inv, hφb, inv_one, one_mul, hz, hzlen]

set_option backward.isDefEq.respectTransparency false in
/-- The nontrivial-voltage part of Lemma 1.2. A compatible pair of lifted lobes
with commuting, conjugate endpoints always produces a symmetric figure-eight. -/
theorem hasSymmetricFigureEight_of_nontrivial_compatible_lifts
    {G Q : Type*} [Group G] [Group Q] (hodd : Odd (Nat.card G))
    (φ : G →* Q) {S : Set G} {T : Set Q}
    (p r : (SimpleGraph.mulCayley T).Walk 1 1) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = 1)
    {a b u : G} (ha : a ≠ 1) (hb : b ≠ 1) (hcomm : Commute a b)
    (hφa : φ a = 1) (hφb : φ b = 1) (hconj : u⁻¹ * a * u = b)
    (w : (SimpleGraph.mulCayley S).Walk 1 a)
    (z : (SimpleGraph.mulCayley S).Walk 1 b)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) (hrlen : r.length = 2 ^ n) :
    HasSymmetricFigureEight S := by
  by_cases hab : a = b
  · clear hconj
    subst b
    exact hasSymmetricFigureEight_of_equal_voltage_lifts hodd φ p r hp hr hdisj ha hφa
      w z hwlen hzlen hw hz n hn hplen hrlen
  obtain ⟨z', hz'len, hz'⟩ := exists_inverse_voltage_lift φ r hφb z hzlen hz
  have hdisj' : ∀ x, (x ∈ p.support ∧ x ∈ r.reverse.support) ↔ x = 1 := by
    simpa using hdisj
  have hφbi : φ b⁻¹ = 1 := by simp [hφb]
  have hbi : b⁻¹ ≠ 1 := by simpa using hb
  have hrlen' : r.reverse.length = 2 ^ n := by simpa using hrlen
  by_cases habi : a = b⁻¹
  · clear hconj
    subst a
    exact hasSymmetricFigureEight_of_equal_voltage_lifts hodd φ p r.reverse hp hr.reverse
      hdisj' hbi hφbi w z' hwlen hz'len hw hz' n hn hplen hrlen'
  obtain hescape | hescape := conjugate_products_escape_inverse_set hodd ha hb hconj
  · exact hasSymmetricFigureEight_of_commutator_lifts hodd φ p r hp hr hdisj
      ha hb hab habi hcomm hφa hφb hescape w z hwlen hzlen hw hz n hn hplen hrlen
  · have hescape' : a * b⁻¹ ∉ ({a, a⁻¹, b⁻¹, (b⁻¹)⁻¹} : Set G) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_inv,
        or_assoc, or_left_comm, or_comm] using hescape
    exact hasSymmetricFigureEight_of_commutator_lifts hodd φ p r.reverse hp hr.reverse hdisj'
      ha hbi habi (by simpa using hab) hcomm.inv_right hφa hφbi hescape'
      w z' hwlen hz'len hw hz' n hn hplen hrlen'

end CayleyErdősGyárfás
