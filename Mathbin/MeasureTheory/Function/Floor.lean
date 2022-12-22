/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module measure_theory.function.floor
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability of `⌊x⌋` etc

In this file we prove that `int.floor`, `int.ceil`, `int.fract`, `nat.floor`, and `nat.ceil` are
measurable under some assumptions on the (semi)ring.
-/


open Set

section FloorRing

variable {α R : Type _} [MeasurableSpace α] [LinearOrderedRing R] [FloorRing R] [TopologicalSpace R]
  [OrderTopology R] [MeasurableSpace R]

theorem Int.measurableFloor [OpensMeasurableSpace R] : Measurable (Int.floor : R → ℤ) :=
  measurableToCountable fun x => by simpa only [Int.preimage_floor_singleton] using measurableSetIco
#align int.measurable_floor Int.measurableFloor

@[measurability]
theorem Measurable.floor [OpensMeasurableSpace R] {f : α → R} (hf : Measurable f) :
    Measurable fun x => ⌊f x⌋ :=
  Int.measurableFloor.comp hf
#align measurable.floor Measurable.floor

theorem Int.measurableCeil [OpensMeasurableSpace R] : Measurable (Int.ceil : R → ℤ) :=
  measurableToCountable fun x => by simpa only [Int.preimage_ceil_singleton] using measurableSetIoc
#align int.measurable_ceil Int.measurableCeil

@[measurability]
theorem Measurable.ceil [OpensMeasurableSpace R] {f : α → R} (hf : Measurable f) :
    Measurable fun x => ⌈f x⌉ :=
  Int.measurableCeil.comp hf
#align measurable.ceil Measurable.ceil

theorem measurableFract [BorelSpace R] : Measurable (Int.fract : R → R) := by
  intro s hs
  rw [Int.preimage_fract]
  exact MeasurableSet.union fun z => measurable_id.sub_const _ (hs.inter measurableSetIco)
#align measurable_fract measurableFract

@[measurability]
theorem Measurable.fract [BorelSpace R] {f : α → R} (hf : Measurable f) :
    Measurable fun x => Int.fract (f x) :=
  measurableFract.comp hf
#align measurable.fract Measurable.fract

theorem MeasurableSet.imageFract [BorelSpace R] {s : Set R} (hs : MeasurableSet s) :
    MeasurableSet (Int.fract '' s) := by
  simp only [Int.image_fract, sub_eq_add_neg, image_add_right']
  exact MeasurableSet.union fun m => (measurable_add_const _ hs).inter measurableSetIco
#align measurable_set.image_fract MeasurableSet.imageFract

end FloorRing

section FloorSemiring

variable {α R : Type _} [MeasurableSpace α] [LinearOrderedSemiring R] [FloorSemiring R]
  [TopologicalSpace R] [OrderTopology R] [MeasurableSpace R] [OpensMeasurableSpace R] {f : α → R}

theorem Nat.measurableFloor : Measurable (Nat.floor : R → ℕ) :=
  measurableToCountable fun n => by
    cases eq_or_ne ⌊n⌋₊ 0 <;> simp [*, Nat.preimage_floor_of_ne_zero]
#align nat.measurable_floor Nat.measurableFloor

@[measurability]
theorem Measurable.natFloor (hf : Measurable f) : Measurable fun x => ⌊f x⌋₊ :=
  Nat.measurableFloor.comp hf
#align measurable.nat_floor Measurable.natFloor

theorem Nat.measurableCeil : Measurable (Nat.ceil : R → ℕ) :=
  measurableToCountable fun n => by cases eq_or_ne ⌈n⌉₊ 0 <;> simp [*, Nat.preimage_ceil_of_ne_zero]
#align nat.measurable_ceil Nat.measurableCeil

@[measurability]
theorem Measurable.natCeil (hf : Measurable f) : Measurable fun x => ⌈f x⌉₊ :=
  Nat.measurableCeil.comp hf
#align measurable.nat_ceil Measurable.natCeil

end FloorSemiring

