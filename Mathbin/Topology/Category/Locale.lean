/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.Category.Frm

#align_import topology.category.Locale from "leanprover-community/mathlib"@"2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe"

/-!
# The category of locales

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

#print Locale /-
/-- The category of locales. -/
def Locale :=
  Frmᵒᵖ
deriving LargeCategory
#align Locale Locale
-/

namespace Locale

instance : CoeSort Locale (Type _) :=
  ⟨fun X => X.unop⟩

instance (X : Locale) : Frame X :=
  X.unop.str

#print Locale.of /-
/-- Construct a bundled `Locale` from a `frame`. -/
def of (α : Type _) [Frame α] : Locale :=
  op <| Frm.of α
#align Locale.of Locale.of
-/

#print Locale.coe_of /-
@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α :=
  rfl
#align Locale.coe_of Locale.coe_of
-/

instance : Inhabited Locale :=
  ⟨of PUnit⟩

end Locale

#print topToLocale /-
/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps]
def topToLocale : TopCat ⥤ Locale :=
  topCatOpToFrm.rightOp
#align Top_to_Locale topToLocale
-/

#print CompHausToLocale.faithful /-
-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHausToLocale.faithful :
    CategoryTheory.Functor.Faithful (compHausToTop ⋙ topToLocale.{u}) :=
  ⟨fun X Y f g h => by dsimp at h; exact opens.comap_injective (Quiver.Hom.op_inj h)⟩
#align CompHaus_to_Locale.faithful CompHausToLocale.faithful
-/

