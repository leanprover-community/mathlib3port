/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import CategoryTheory.Category.Pointed
import Data.Pfun

#align_import category_theory.category.PartialFun from "leanprover-community/mathlib"@"1b089e3bdc3ce6b39cd472543474a0a137128c6c"

/-!
# The category of types with partial functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `PartialFun`, the category of types equipped with partial functions.

This category is classically equivalent to the category of pointed types. The reason it doesn't hold
constructively stems from the difference between `part` and `option`. Both can model partial
functions, but the latter forces a decidable domain.

Precisely, `PartialFun_to_Pointed` turns a partial function `α →. β` into a function
`option α → option β` by sending to `none` the undefined values (and `none` to `none`). But being
defined is (generally) undecidable while being sent to `none` is decidable. So it can't be
constructive.

## References

* [nLab, *The category of sets and partial functions*]
  (https://ncatlab.org/nlab/show/partial+function)
-/


open CategoryTheory Option

universe u

variable {α β : Type _}

#print PartialFun /-
/-- The category of types equipped with partial functions. -/
def PartialFun : Type _ :=
  Type _
#align PartialFun PartialFun
-/

namespace PartialFun

instance : CoeSort PartialFun (Type _) :=
  ⟨id⟩

#print PartialFun.of /-
/-- Turns a type into a `PartialFun`. -/
@[nolint has_nonempty_instance]
def of : Type _ → PartialFun :=
  id
#align PartialFun.of PartialFun.of
-/

@[simp]
theorem coe_of (X : Type _) : ↥(of X) = X :=
  rfl
#align PartialFun.coe_of PartialFun.coe_of

instance : Inhabited PartialFun :=
  ⟨Type _⟩

#print PartialFun.largeCategory /-
instance largeCategory : LargeCategory.{u} PartialFun
    where
  Hom := PFun
  id := PFun.id
  comp X Y Z f g := g.comp f
  id_comp' := @PFun.comp_id
  comp_id' := @PFun.id_comp
  assoc' W X Y Z _ _ _ := (PFun.comp_assoc _ _ _).symm
#align PartialFun.large_category PartialFun.largeCategory
-/

#print PartialFun.Iso.mk /-
/-- Constructs a partial function isomorphism between types from an equivalence between them. -/
@[simps]
def Iso.mk {α β : PartialFun.{u}} (e : α ≃ β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := (PFun.coe_comp _ _).symm.trans <| congr_arg coe e.symm_comp_self
  inv_hom_id' := (PFun.coe_comp _ _).symm.trans <| congr_arg coe e.self_comp_symm
#align PartialFun.iso.mk PartialFun.Iso.mk
-/

end PartialFun

#print typeToPartialFun /-
/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
def typeToPartialFun : Type u ⥤ PartialFun
    where
  obj := id
  map := @PFun.lift
  map_comp' _ _ _ _ _ := PFun.coe_comp _ _
#align Type_to_PartialFun typeToPartialFun
-/

instance : Faithful typeToPartialFun :=
  ⟨fun X Y => PFun.lift_injective⟩

#print pointedToPartialFun /-
/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This the computable part of the equivalence `PartialFun_equiv_Pointed`. -/
@[simps map]
def pointedToPartialFun : Pointed.{u} ⥤ PartialFun
    where
  obj X := { x : X // x ≠ X.point }
  map X Y f := PFun.toSubtype _ f.toFun ∘ Subtype.val
  map_id' X :=
    PFun.ext fun a b => PFun.mem_toSubtype_iff.trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp' X Y Z f g :=
    PFun.ext fun a c =>
      by
      refine' (pfun.mem_to_subtype_iff.trans _).trans part.mem_bind_iff.symm
      simp_rw [PFun.mem_toSubtype_iff, Subtype.exists]
      refine'
        ⟨fun h =>
          ⟨f.to_fun a, fun ha =>
            c.2 <| h.trans ((congr_arg g.to_fun ha : g.to_fun _ = _).trans g.map_point), rfl, h⟩,
          _⟩
      rintro ⟨b, _, rfl : b = _, h⟩
      exact h
#align Pointed_to_PartialFun pointedToPartialFun
-/

#print partialFunToPointed /-
/-- The functor which maps undefined values to a new point. This makes the maps total and creates
pointed types. This the noncomputable part of the equivalence `PartialFun_equiv_Pointed`. It can't
be computable because `= option.none` is decidable while the domain of a general `part` isn't. -/
@[simps map]
noncomputable def partialFunToPointed : PartialFun ⥤ Pointed := by classical
#align PartialFun_to_Pointed partialFunToPointed
-/

#print partialFunEquivPointed /-
/-- The equivalence induced by `PartialFun_to_Pointed` and `Pointed_to_PartialFun`.
`part.equiv_option` made functorial. -/
@[simps]
noncomputable def partialFunEquivPointed : PartialFun.{u} ≌ Pointed := by classical
#align PartialFun_equiv_Pointed partialFunEquivPointed
-/

#print typeToPartialFunIsoPartialFunToPointed /-
/-- Forgetting that maps are total and making them total again by adding a point is the same as just
adding a point. -/
@[simps]
noncomputable def typeToPartialFunIsoPartialFunToPointed :
    typeToPartialFun ⋙ partialFunToPointed ≅ typeToPointed :=
  NatIso.ofComponents
    (fun X =>
      { Hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩
        hom_inv_id' := rfl
        inv_hom_id' := rfl })
    fun X Y f =>
    Pointed.Hom.ext _ _ <|
      funext fun a => Option.recOn a rfl fun a => by convert Part.some_toOption _
#align Type_to_PartialFun_iso_PartialFun_to_Pointed typeToPartialFunIsoPartialFunToPointed
-/

