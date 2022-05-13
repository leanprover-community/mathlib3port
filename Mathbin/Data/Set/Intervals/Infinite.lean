/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathbin.Data.Set.Finite

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side.
-/


namespace Set

variable {α : Type _} [Preorderₓ α]

section Bounded

variable [DenselyOrdered α]

theorem Ioo.infinite {a b : α} (h : a < b) : Infinite (Ioo a b) := by
  rintro (f : finite (Ioo a b))
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m ∈ Ioo a b, ∀, ∀ x ∈ Ioo a b, ∀, ¬x < m := by
    simpa [h] using Finset.exists_minimal f.to_finset
  obtain ⟨z, hz₁, hz₂⟩ : ∃ z, a < z ∧ z < m := exists_between hm₁.1
  exact hm₂ z ⟨hz₁, lt_transₓ hz₂ hm₁.2⟩ hz₂

theorem Ico.infinite {a b : α} (h : a < b) : Infinite (Ico a b) :=
  (Ioo.infinite h).mono Ioo_subset_Ico_self

theorem Ioc.infinite {a b : α} (h : a < b) : Infinite (Ioc a b) :=
  (Ioo.infinite h).mono Ioo_subset_Ioc_self

theorem Icc.infinite {a b : α} (h : a < b) : Infinite (Icc a b) :=
  (Ioo.infinite h).mono Ioo_subset_Icc_self

end Bounded

section UnboundedBelow

variable [NoMinOrder α]

theorem Iio.infinite {b : α} : Infinite (Iio b) := by
  rintro (f : finite (Iio b))
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m < b, ∀, ∀ x < b, ∀, ¬x < m := by
    simpa using Finset.exists_minimal f.to_finset
  obtain ⟨z, hz⟩ : ∃ z, z < m := exists_lt _
  exact hm₂ z (lt_transₓ hz hm₁) hz

theorem Iic.infinite {b : α} : Infinite (Iic b) :=
  Iio.infinite.mono Iio_subset_Iic_self

end UnboundedBelow

section UnboundedAbove

variable [NoMaxOrder α]

theorem Ioi.infinite {a : α} : Infinite (Ioi a) :=
  @Iio.infinite αᵒᵈ _ _ _

theorem Ici.infinite {a : α} : Infinite (Ici a) :=
  Ioi.infinite.mono Ioi_subset_Ici_self

end UnboundedAbove

end Set

