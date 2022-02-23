/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
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

open OrderDual (toDual)

theorem surj_on_Ioo_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) :
    SurjOn f (Ioo a b) (Ioo (f a) (f b)) := by
  classical
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine' ⟨x, mem_Ioo.2 _, rfl⟩
  by_contra h
  cases' not_and_distrib.mp h with ha hb
  · exact LT.lt.false (lt_of_lt_of_leₓ hp.1 (h_mono (not_lt.mp ha)))
    
  · exact LT.lt.false (lt_of_le_of_ltₓ (h_mono (not_lt.mp hb)) hp.2)
    

theorem surj_on_Ico_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) :
    SurjOn f (Ico a b) (Ico (f a) (f b)) := by
  obtain hab | hab := lt_or_leₓ a b
  · intro p hp
    rcases mem_Ioo_or_eq_left_of_mem_Ico hp with (hp' | hp')
    · rw [hp']
      exact ⟨a, left_mem_Ico.mpr hab, rfl⟩
      
    · have := surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp'
      cases' this with x hx
      exact ⟨x, Ioo_subset_Ico_self hx.1, hx.2⟩
      
    
  · rw [Ico_eq_empty (h_mono hab).not_lt]
    exact surj_on_empty f _
    

theorem surj_on_Ioc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) :
    SurjOn f (Ioc a b) (Ioc (f a) (f b)) := by
  simpa using surj_on_Ico_of_monotone_surjective h_mono.dual h_surj (to_dual b) (to_dual a)

-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function
theorem surj_on_Icc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) {a b : α}
    (hab : a ≤ b) : SurjOn f (Icc a b) (Icc (f a) (f b)) := by
  rcases lt_or_eq_of_leₓ hab with (hab | hab)
  · intro p hp
    rcases mem_Ioo_or_eq_endpoints_of_mem_Icc hp with (hp' | ⟨hp' | hp'⟩)
    · rw [hp']
      refine' ⟨a, left_mem_Icc.mpr (le_of_ltₓ hab), rfl⟩
      
    · rw [hp']
      refine' ⟨b, right_mem_Icc.mpr (le_of_ltₓ hab), rfl⟩
      
    · have := surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp'
      cases' this with x hx
      exact ⟨x, Ioo_subset_Icc_self hx.1, hx.2⟩
      
    
  · simp only [hab, Icc_self]
    intro _ hp
    exact ⟨b, mem_singleton _, (mem_singleton_iff.mp hp).symm⟩
    

theorem surj_on_Ioi_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
    SurjOn f (Ioi a) (Ioi (f a)) := by
  classical
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine' ⟨x, _, rfl⟩
  simp only [mem_Ioi]
  by_contra h
  exact LT.lt.false (lt_of_lt_of_leₓ hp (h_mono (not_lt.mp h)))

theorem surj_on_Iio_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
    SurjOn f (Iio a) (Iio (f a)) :=
  @surj_on_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

theorem surj_on_Ici_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
    SurjOn f (Ici a) (Ici (f a)) := by
  intro p hp
  rw [mem_Ici, le_iff_lt_or_eqₓ] at hp
  rcases hp with (hp' | hp')
  · cases' surj_on_Ioi_of_monotone_surjective h_mono h_surj a hp' with x hx
    exact ⟨x, Ioi_subset_Ici_self hx.1, hx.2⟩
    
  · rw [← hp']
    refine' ⟨a, left_mem_Ici, rfl⟩
    

theorem surj_on_Iic_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
    SurjOn f (Iic a) (Iic (f a)) :=
  @surj_on_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

