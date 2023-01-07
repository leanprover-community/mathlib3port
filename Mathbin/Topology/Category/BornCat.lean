/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.category.Born
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Topology.Bornology.Hom

/-!
# The category of bornologies

This defines `Born`, the category of bornologies.
-/


universe u

open CategoryTheory

/-- The category of bornologies. -/
def BornCat :=
  Bundled Bornology
#align Born BornCat

namespace BornCat

instance : CoeSort BornCat (Type _) :=
  bundled.has_coe_to_sort

instance (X : BornCat) : Bornology X :=
  X.str

/-- Construct a bundled `Born` from a `bornology`. -/
def of (α : Type _) [Bornology α] : BornCat :=
  Bundled.of α
#align Born.of BornCat.of

instance : Inhabited BornCat :=
  ⟨of PUnit⟩

instance : BundledHom @LocallyBoundedMap
    where
  toFun _ _ _ _ := coeFn
  id := @LocallyBoundedMap.id
  comp := @LocallyBoundedMap.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} BornCat :=
  BundledHom.category LocallyBoundedMap

instance : ConcreteCategory BornCat :=
  BundledHom.concreteCategory LocallyBoundedMap

end BornCat

