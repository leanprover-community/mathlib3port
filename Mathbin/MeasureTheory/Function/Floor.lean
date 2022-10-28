/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability of `⌊x⌋` etc

In this file we prove that `int.floor`, `int.ceil`, `int.fract`, `nat.floor`, and `nat.ceil` are
measurable under some assumptions on the (semi)ring.
-/


open Set

section FloorRing

variable {α R : Type _} [MeasurableSpace α] [LinearOrderedRing R] [FloorRing R] [TopologicalSpace R] [OrderTopology R]
  [MeasurableSpace R]

theorem Int.measurableFloor [OpensMeasurableSpace R] : Measurable (Int.floor : R → ℤ) :=
  measurableToCountable fun x => by simpa only [Int.preimage_floor_singleton] using measurableSetIco

@[measurability]
theorem Measurable.floor [OpensMeasurableSpace R] {f : α → R} (hf : Measurable f) : Measurable fun x => ⌊f x⌋ :=
  Int.measurableFloor.comp hf

theorem Int.measurableCeil [OpensMeasurableSpace R] : Measurable (Int.ceil : R → ℤ) :=
  measurableToCountable fun x => by simpa only [Int.preimage_ceil_singleton] using measurableSetIoc

@[measurability]
theorem Measurable.ceil [OpensMeasurableSpace R] {f : α → R} (hf : Measurable f) : Measurable fun x => ⌈f x⌉ :=
  Int.measurableCeil.comp hf

theorem measurableFract [BorelSpace R] : Measurable (Int.fract : R → R) := by
  intro s hs
  rw [Int.preimage_fract]
  exact MeasurableSet.union fun z => measurable_id.sub_const _ (hs.inter measurableSetIco)

@[measurability]
theorem Measurable.fract [BorelSpace R] {f : α → R} (hf : Measurable f) : Measurable fun x => Int.fract (f x) :=
  measurableFract.comp hf

theorem MeasurableSet.imageFract [BorelSpace R] {s : Set R} (hs : MeasurableSet s) : MeasurableSet (Int.fract '' s) :=
  by
  simp only [Int.image_fract, sub_eq_add_neg, image_add_right']
  exact MeasurableSet.union fun m => (measurable_add_const _ hs).inter measurableSetIco

end FloorRing

section FloorSemiring

variable {α R : Type _} [MeasurableSpace α] [LinearOrderedSemiring R] [FloorSemiring R] [TopologicalSpace R]
  [OrderTopology R] [MeasurableSpace R] [OpensMeasurableSpace R] {f : α → R}

theorem Nat.measurableFloor : Measurable (Nat.floor : R → ℕ) :=
  measurableToCountable fun n => by cases eq_or_ne ⌊n⌋₊ 0 <;> simp [*, Nat.preimage_floor_of_ne_zero]

@[measurability]
theorem Measurable.natFloor (hf : Measurable f) : Measurable fun x => ⌊f x⌋₊ :=
  Nat.measurableFloor.comp hf

theorem Nat.measurableCeil : Measurable (Nat.ceil : R → ℕ) :=
  measurableToCountable fun n => by cases eq_or_ne ⌈n⌉₊ 0 <;> simp [*, Nat.preimage_ceil_of_ne_zero]

@[measurability]
theorem Measurable.natCeil (hf : Measurable f) : Measurable fun x => ⌈f x⌉₊ :=
  Nat.measurableCeil.comp hf

end FloorSemiring

