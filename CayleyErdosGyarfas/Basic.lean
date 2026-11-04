module

public import CayleyErdosGyarfas.Definitions

/-! Elementary, fully proved checks on the statement conventions. -/

@[expose] public section

namespace CayleyErdősGyárfás

/-- Mathlib's Cayley adjacency agrees with the manuscript's right-generator
convention when `S` is inverse-closed and does not contain the identity. -/
theorem cayley_adj_iff {G : Type*} [Group G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hone : (1 : G) ∉ S) (u v : G) :
    (SimpleGraph.mulCayley S).Adj u v ↔ u⁻¹ * v ∈ S := by
  rw [SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · simpa using hinv _ h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    exact hone (by simpa using h)

/-- Left translation preserves the right-generator Cayley graph. -/
def cayleyLeftTranslation {G : Type*} [Group G] (S : Set G) (g : G) :
    SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley S where
  toEquiv := Equiv.mulLeft g
  map_rel_iff' := SimpleGraph.mulCayley_adj_mul_iff_right

/-- Every symmetric figure-eight in the precise statement sense contains a
simple cycle of the required length. -/
theorem HasSymmetricFigureEight.contains_two_power_cycle
    {G : Type*} [Group G] {S : Set G} (h : HasSymmetricFigureEight S) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  rcases h with ⟨n, v, α, β, hn, hα, hβ, hlen, hlenβ, htranslate, hintersect⟩
  exact ⟨n, v, α, Nat.le_trans (by decide : 1 ≤ 2) hn, hα, hlen⟩

/-- A simple cycle of power-of-two length has at least four edges. -/
theorem two_power_cycle_exponent_ge_two
    {V : Type*} {Γ : SimpleGraph V} {v : V} {c : Γ.Walk v v} {n : ℕ}
    (hcycle : c.IsCycle) (hlen : c.length = 2 ^ n) : 2 ≤ n := by
  have hthree : 3 ≤ c.length :=
    (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mp hcycle).2
  rw [hlen] at hthree
  by_contra h
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl <;> norm_num at hthree

/-- The quotient generating set used in both lifting statements is
inverse-closed, with the identity coset deleted. -/
theorem quotient_generators_inverse_closed
    {G : Type*} [Group G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (N : Subgroup G) [N.Normal] :
    ∀ q ∈ (QuotientGroup.mk (s := N)) '' S \ {1},
      q⁻¹ ∈ (QuotientGroup.mk (s := N)) '' S \ {1} := by
  rintro q ⟨⟨s, hs, rfl⟩, hne⟩
  refine ⟨⟨s⁻¹, hinv s hs, ?_⟩, ?_⟩
  · simp
  · simpa only [Set.mem_singleton_iff, inv_eq_one] using hne

/-- A cycle and a left translate meeting at a unique vertex give the
manuscript's based symmetric figure-eight. This criterion lets constructive
proofs work with a single cycle and its translated vertex set. -/
theorem hasSymmetricFigureEight_of_cycle_translate
    {G : Type*} [Group G] {S : Set G} {v : G}
    (c : (SimpleGraph.mulCayley S).Walk v v) (n : ℕ)
    (_hn : 1 ≤ n) (hc : c.IsCycle) (hlen : c.length = 2 ^ n)
    (g w : G)
    (hintersect : ∀ x : G,
      (x ∈ c.support ∧ ∃ y ∈ c.support, g * y = x) ↔ x = w) :
    HasSymmetricFigureEight S := by
  classical
  let φ := (cayleyLeftTranslation S g).toHom
  let d := c.map φ
  have hw : w ∈ c.support := ((hintersect w).mpr rfl).1
  have hd (x : G) : x ∈ d.support ↔ ∃ y ∈ c.support, g * y = x := by
    change x ∈ (c.map φ).support ↔ _
    rw [SimpleGraph.Walk.support_map]
    change x ∈ c.support.map (g * ·) ↔ _
    exact List.mem_map
  have hwd : w ∈ d.support := (hd w).mpr ((hintersect w).mpr rfl).2
  refine ⟨n, w, c.rotate w hw, d.rotate w hwd, two_power_cycle_exponent_ge_two hc hlen,
    (SimpleGraph.Walk.isCycle_rotate hw).mpr hc, ?_,
    by simpa using hlen, ?_, ?_, ?_⟩
  · apply (SimpleGraph.Walk.isCycle_rotate hwd).mpr
    exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (f := φ) (fun _ _ h ↦ mul_left_cancel h)).mpr hc
  · simpa [d] using hlen
  · refine ⟨g, ?_⟩
    have hr := (c.support_rotate w hw).map (g * ·)
    have hdrot := (d.support_rotate w hwd).symm
    have heq : d.support.tail = c.support.tail.map (g * ·) := by
      change (c.map φ).support.tail = _
      rw [SimpleGraph.Walk.support_map, List.map_tail]
      rfl
    rw [heq] at hdrot
    exact hr.trans hdrot
  · intro x
    simpa only [SimpleGraph.Walk.mem_support_rotate_iff, hd] using hintersect x

end CayleyErdősGyárfás
