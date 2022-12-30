/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.category.Locale
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.FrameCat

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

/-- The category of locales. -/
def LocaleCat :=
  FrameCatᵒᵖderiving LargeCategory
#align Locale LocaleCat

namespace LocaleCat

instance : CoeSort LocaleCat (Type _) :=
  ⟨fun X => X.unop⟩

instance (X : LocaleCat) : Frame X :=
  X.unop.str

/-- Construct a bundled `Locale` from a `frame`. -/
def of (α : Type _) [Frame α] : LocaleCat :=
  op <| FrameCat.of α
#align Locale.of LocaleCat.of

@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α :=
  rfl
#align Locale.coe_of LocaleCat.coe_of

instance : Inhabited LocaleCat :=
  ⟨of PUnit⟩

end LocaleCat

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps]
def topToLocale : TopCat ⥤ LocaleCat :=
  topOpToFrame.rightOp
#align Top_to_Locale topToLocale

-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHausToLocale.faithful : Faithful (compHausToTop ⋙ topToLocale.{u}) :=
  ⟨fun X Y f g h => by
    dsimp at h
    exact opens.comap_injective (Quiver.Hom.op_inj h)⟩
#align CompHaus_to_Locale.faithful CompHausToLocale.faithful

