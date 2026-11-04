module

public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

/-! Compatibility with the pre-v4.35 explicit normality arguments. -/

theorem IsSimpleGroup.eq_bot_or_eq_top_of_normal_explicit
    {G : Type*} [Group G] [hG : IsSimpleGroup G]
    (H : Subgroup G) (hH : H.Normal) : H = ⊥ ∨ H = ⊤ :=
  @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hG H hH

theorem Subgroup.Normal.eq_bot_or_eq_top_explicit
    {G : Type*} [Group G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H.Normal) : H = ⊥ ∨ H = ⊤ :=
  @Subgroup.Normal.eq_bot_or_eq_top G _ _ H hH
