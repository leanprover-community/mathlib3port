import Mathbin.Data.Set.Intervals.Basic 
import Mathbin.Data.Set.Function

/-!
# Monotone surjective functions are surjective on intervals

A monotone surjective function sends any interval in the domain onto the interval with corresponding
endpoints in the range.  This is expressed in this file using `set.surj_on`, and provided for all
permutations of interval endpoints.
-/


variable {α : Type _} {β : Type _} [LinearOrderₓ α] [PartialOrderₓ β] {f : α → β}

open Set Function

open order_dual(toDual)

theorem surj_on_Ioo_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) :
  surj_on f (Ioo a b) (Ioo (f a) (f b)) :=
  by 
    classical 
    intro p hp 
    rcases h_surj p with ⟨x, rfl⟩
    refine' ⟨x, mem_Ioo.2 _, rfl⟩
    byContra h 
    cases' not_and_distrib.mp h with ha hb
    ·
      exact LT.lt.false (lt_of_lt_of_leₓ hp.1 (h_mono (not_lt.mp ha)))
    ·
      exact LT.lt.false (lt_of_le_of_ltₓ (h_mono (not_lt.mp hb)) hp.2)

-- error in Data.Set.Intervals.SurjOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem surj_on_Ico_of_monotone_surjective
(h_mono : monotone f)
(h_surj : function.surjective f)
(a b : α) : surj_on f (Ico a b) (Ico (f a) (f b)) :=
begin
  obtain [ident hab, "|", ident hab, ":=", expr lt_or_le a b],
  { intros [ident p, ident hp],
    rcases [expr mem_Ioo_or_eq_left_of_mem_Ico hp, "with", ident hp', "|", ident hp'],
    { rw [expr hp'] [],
      exact [expr ⟨a, left_mem_Ico.mpr hab, rfl⟩] },
    { have [] [] [":=", expr surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp'],
      cases [expr this] ["with", ident x, ident hx],
      exact [expr ⟨x, Ioo_subset_Ico_self hx.1, hx.2⟩] } },
  { rw [expr Ico_eq_empty (h_mono hab).not_lt] [],
    exact [expr surj_on_empty f _] }
end

theorem surj_on_Ioc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) :
  surj_on f (Ioc a b) (Ioc (f a) (f b)) :=
  by 
    simpa using surj_on_Ico_of_monotone_surjective h_mono.dual h_surj (to_dual b) (to_dual a)

-- error in Data.Set.Intervals.SurjOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem surj_on_Icc_of_monotone_surjective
(h_mono : monotone f)
(h_surj : function.surjective f)
{a b : α}
(hab : «expr ≤ »(a, b)) : surj_on f (Icc a b) (Icc (f a) (f b)) :=
begin
  rcases [expr lt_or_eq_of_le hab, "with", ident hab, "|", ident hab],
  { intros [ident p, ident hp],
    rcases [expr mem_Ioo_or_eq_endpoints_of_mem_Icc hp, "with", ident hp', "|", "⟨", ident hp', "|", ident hp', "⟩"],
    { rw [expr hp'] [],
      refine [expr ⟨a, left_mem_Icc.mpr (le_of_lt hab), rfl⟩] },
    { rw [expr hp'] [],
      refine [expr ⟨b, right_mem_Icc.mpr (le_of_lt hab), rfl⟩] },
    { have [] [] [":=", expr surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp'],
      cases [expr this] ["with", ident x, ident hx],
      exact [expr ⟨x, Ioo_subset_Icc_self hx.1, hx.2⟩] } },
  { simp [] [] ["only"] ["[", expr hab, ",", expr Icc_self, "]"] [] [],
    intros ["_", ident hp],
    exact [expr ⟨b, mem_singleton _, (mem_singleton_iff.mp hp).symm⟩] }
end

theorem surj_on_Ioi_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
  surj_on f (Ioi a) (Ioi (f a)) :=
  by 
    classical 
    intro p hp 
    rcases h_surj p with ⟨x, rfl⟩
    refine' ⟨x, _, rfl⟩
    simp only [mem_Ioi]
    byContra h 
    exact LT.lt.false (lt_of_lt_of_leₓ hp (h_mono (not_lt.mp h)))

theorem surj_on_Iio_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
  surj_on f (Iio a) (Iio (f a)) :=
  @surj_on_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

theorem surj_on_Ici_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
  surj_on f (Ici a) (Ici (f a)) :=
  by 
    intro p hp 
    rw [mem_Ici, le_iff_lt_or_eqₓ] at hp 
    rcases hp with (hp' | hp')
    ·
      cases' surj_on_Ioi_of_monotone_surjective h_mono h_surj a hp' with x hx 
      exact ⟨x, Ioi_subset_Ici_self hx.1, hx.2⟩
    ·
      rw [←hp']
      refine' ⟨a, left_mem_Ici, rfl⟩

theorem surj_on_Iic_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
  surj_on f (Iic a) (Iic (f a)) :=
  @surj_on_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

