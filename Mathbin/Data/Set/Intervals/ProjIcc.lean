/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot

! This file was ported from Lean 3 source module data.set.intervals.proj_Icc
! leanprover-community/mathlib commit 42e9a1fd3a99e10f82830349ba7f4f10e8961c2a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Function
import Mathbin.Data.Set.Intervals.Basic

/-!
# Projection of a line onto a closed interval

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a linearly ordered type `α`, in this file we define

* `set.proj_Icc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `set.Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Icc a b h`.

We also prove some trivial properties of these maps.
-/


variable {α β : Type _} [LinearOrder α]

open Function

namespace Set

#print Set.projIcc /-
/-- Projection of `α` to the closed interval `[a, b]`. -/
def projIcc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
  ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩
#align set.proj_Icc Set.projIcc
-/

variable {a b : α} (h : a ≤ b) {x : α}

#print Set.projIcc_of_le_left /-
theorem projIcc_of_le_left (hx : x ≤ a) : projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩ := by
  simp [proj_Icc, hx, hx.trans h]
#align set.proj_Icc_of_le_left Set.projIcc_of_le_left
-/

#print Set.projIcc_left /-
@[simp]
theorem projIcc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
  projIcc_of_le_left h le_rfl
#align set.proj_Icc_left Set.projIcc_left
-/

#print Set.projIcc_of_right_le /-
theorem projIcc_of_right_le (hx : b ≤ x) : projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩ := by
  simp [proj_Icc, hx, h]
#align set.proj_Icc_of_right_le Set.projIcc_of_right_le
-/

#print Set.projIcc_right /-
@[simp]
theorem projIcc_right : projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
  projIcc_of_right_le h le_rfl
#align set.proj_Icc_right Set.projIcc_right
-/

#print Set.projIcc_eq_left /-
theorem projIcc_eq_left (h : a < b) : projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x ≤ a :=
  by
  refine' ⟨fun h' => _, proj_Icc_of_le_left _⟩
  simp_rw [Subtype.ext_iff_val, proj_Icc, max_eq_left_iff, min_le_iff, h.not_le, false_or_iff] at h' 
  exact h'
#align set.proj_Icc_eq_left Set.projIcc_eq_left
-/

#print Set.projIcc_eq_right /-
theorem projIcc_eq_right (h : a < b) : projIcc a b h.le x = ⟨b, right_mem_Icc.mpr h.le⟩ ↔ b ≤ x :=
  by
  refine' ⟨fun h' => _, proj_Icc_of_right_le _⟩
  simp_rw [Subtype.ext_iff_val, proj_Icc] at h' 
  have := ((max_choice _ _).resolve_left (by simp [h.ne', h'])).symm.trans h'
  exact min_eq_left_iff.mp this
#align set.proj_Icc_eq_right Set.projIcc_eq_right
-/

#print Set.projIcc_of_mem /-
theorem projIcc_of_mem (hx : x ∈ Icc a b) : projIcc a b h x = ⟨x, hx⟩ := by
  simp [proj_Icc, hx.1, hx.2]
#align set.proj_Icc_of_mem Set.projIcc_of_mem
-/

#print Set.projIcc_val /-
@[simp]
theorem projIcc_val (x : Icc a b) : projIcc a b h x = x := by cases x; apply proj_Icc_of_mem
#align set.proj_Icc_coe Set.projIcc_val
-/

#print Set.projIcc_surjOn /-
theorem projIcc_surjOn : SurjOn (projIcc a b h) (Icc a b) univ := fun x _ =>
  ⟨x, x.2, projIcc_val h x⟩
#align set.proj_Icc_surj_on Set.projIcc_surjOn
-/

#print Set.projIcc_surjective /-
theorem projIcc_surjective : Surjective (projIcc a b h) := fun x => ⟨x, projIcc_val h x⟩
#align set.proj_Icc_surjective Set.projIcc_surjective
-/

#print Set.range_projIcc /-
@[simp]
theorem range_projIcc : range (projIcc a b h) = univ :=
  (projIcc_surjective h).range_eq
#align set.range_proj_Icc Set.range_projIcc
-/

#print Set.monotone_projIcc /-
theorem monotone_projIcc : Monotone (projIcc a b h) := fun x y hxy =>
  max_le_max le_rfl <| min_le_min le_rfl hxy
#align set.monotone_proj_Icc Set.monotone_projIcc
-/

#print Set.strictMonoOn_projIcc /-
theorem strictMonoOn_projIcc : StrictMonoOn (projIcc a b h) (Icc a b) := fun x hx y hy hxy => by
  simpa only [proj_Icc_of_mem, hx, hy]
#align set.strict_mono_on_proj_Icc Set.strictMonoOn_projIcc
-/

#print Set.IccExtend /-
/-- Extend a function `[a, b] → β` to a map `α → β`. -/
def IccExtend {a b : α} (h : a ≤ b) (f : Icc a b → β) : α → β :=
  f ∘ projIcc a b h
#align set.Icc_extend Set.IccExtend
-/

@[simp]
theorem IccExtend_range (f : Icc a b → β) : range (IccExtend h f) = range f := by
  simp only [Icc_extend, range_comp f, range_proj_Icc, range_id']
#align set.Icc_extend_range Set.IccExtend_range

theorem IccExtend_of_le_left (f : Icc a b → β) (hx : x ≤ a) :
    IccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
  congr_arg f <| projIcc_of_le_left h hx
#align set.Icc_extend_of_le_left Set.IccExtend_of_le_left

@[simp]
theorem IccExtend_left (f : Icc a b → β) : IccExtend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
  IccExtend_of_le_left h f le_rfl
#align set.Icc_extend_left Set.IccExtend_left

theorem IccExtend_of_right_le (f : Icc a b → β) (hx : b ≤ x) :
    IccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
  congr_arg f <| projIcc_of_right_le h hx
#align set.Icc_extend_of_right_le Set.IccExtend_of_right_le

@[simp]
theorem IccExtend_right (f : Icc a b → β) : IccExtend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
  IccExtend_of_right_le h f le_rfl
#align set.Icc_extend_right Set.IccExtend_right

theorem IccExtend_of_mem (f : Icc a b → β) (hx : x ∈ Icc a b) : IccExtend h f x = f ⟨x, hx⟩ :=
  congr_arg f <| projIcc_of_mem h hx
#align set.Icc_extend_of_mem Set.IccExtend_of_mem

@[simp]
theorem IccExtend_val (f : Icc a b → β) (x : Icc a b) : IccExtend h f x = f x :=
  congr_arg f <| projIcc_val h x
#align set.Icc_extend_coe Set.IccExtend_val

/-- If `f : α → β` is a constant both on $(-∞, a]$ and on $[b, +∞)$, then the extension of this
function from $[a, b]$ to the whole line is equal to the original function. -/
theorem IccExtend_eq_self (f : α → β) (ha : ∀ x < a, f x = f a) (hb : ∀ x, b < x → f x = f b) :
    IccExtend h (f ∘ coe) = f := by
  ext x
  cases' lt_or_le x a with hxa hax
  · simp [Icc_extend_of_le_left _ _ hxa.le, ha x hxa]
  · cases' le_or_lt x b with hxb hbx
    · lift x to Icc a b using ⟨hax, hxb⟩
      rw [Icc_extend_coe]
    · simp [Icc_extend_of_right_le _ _ hbx.le, hb x hbx]
#align set.Icc_extend_eq_self Set.IccExtend_eq_self

end Set

open Set

variable [Preorder β] {a b : α} (h : a ≤ b) {f : Icc a b → β}

theorem Monotone.IccExtend (hf : Monotone f) : Monotone (IccExtend h f) :=
  hf.comp <| monotone_projIcc h
#align monotone.Icc_extend Monotone.IccExtend

theorem StrictMono.strictMonoOn_IccExtend (hf : StrictMono f) :
    StrictMonoOn (IccExtend h f) (Icc a b) :=
  hf.comp_strictMonoOn (strictMonoOn_projIcc h)
#align strict_mono.strict_mono_on_Icc_extend StrictMono.strictMonoOn_IccExtend

