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


variable {α : Type _} {β : Type _} [LinearOrder α] [PartialOrder β] {f : α → β}

open Set Function

open OrderDual (toDual)

theorem surj_on_Ioo_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) :
    SurjOn f (IooCat a b) (IooCat (f a) (f b)) := by
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine' ⟨x, mem_Ioo.2 _, rfl⟩
  contrapose! hp
  exact fun h => h.2.not_le (h_mono <| hp <| h_mono.reflect_lt h.1)

theorem surj_on_Ico_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) :
    SurjOn f (IcoCat a b) (IcoCat (f a) (f b)) := by
  obtain hab | hab := lt_or_le a b
  · intro p hp
    rcases eq_left_or_mem_Ioo_of_mem_Ico hp with (rfl | hp')
    · exact mem_image_of_mem f (left_mem_Ico.mpr hab)
      
    · have := surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp'
      exact image_subset f Ioo_subset_Ico_self this
      
    
  · rw [Ico_eq_empty (h_mono hab).not_lt]
    exact surj_on_empty f _
    

theorem surj_on_Ioc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) :
    SurjOn f (IocCat a b) (IocCat (f a) (f b)) := by
  simpa using surj_on_Ico_of_monotone_surjective h_mono.dual h_surj (to_dual b) (to_dual a)

-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function
theorem surj_on_Icc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) {a b : α}
    (hab : a ≤ b) : SurjOn f (IccCat a b) (IccCat (f a) (f b)) := by
  intro p hp
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with (rfl | rfl | hp')
  · exact ⟨a, left_mem_Icc.mpr hab, rfl⟩
    
  · exact ⟨b, right_mem_Icc.mpr hab, rfl⟩
    
  · have := surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp'
    exact image_subset f Ioo_subset_Icc_self this
    

theorem surj_on_Ioi_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
    SurjOn f (IoiCat a) (IoiCat (f a)) := by
  rw [← compl_Iic, ← compl_compl (Ioi (f a))]
  refine' maps_to.surj_on_compl _ h_surj
  exact fun x hx => (h_mono hx).not_lt

theorem surj_on_Iio_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
    SurjOn f (IioCat a) (IioCat (f a)) :=
  @surj_on_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

theorem surj_on_Ici_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
    SurjOn f (IciCat a) (IciCat (f a)) := by
  rw [← Ioi_union_left, ← Ioi_union_left]
  exact (surj_on_Ioi_of_monotone_surjective h_mono h_surj a).union_union (@image_singleton _ _ f a ▸ surj_on_image _ _)

theorem surj_on_Iic_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f) (a : α) :
    SurjOn f (IicCat a) (IicCat (f a)) :=
  @surj_on_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

