/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import CategoryTheory.ConcreteCategory.BundledHom
import Topology.Bornology.Hom

#align_import topology.category.Born from "leanprover-community/mathlib"@"1dac236edca9b4b6f5f00b1ad831e35f89472837"

/-!
# The category of bornologies

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `Born`, the category of bornologies.
-/


universe u

open CategoryTheory

#print Born /-
/-- The category of bornologies. -/
def Born :=
  Bundled Bornology
#align Born Born
-/

namespace Born

instance : CoeSort Born (Type _) :=
  Bundled.hasCoeToSort

instance (X : Born) : Bornology X :=
  X.str

#print Born.of /-
/-- Construct a bundled `Born` from a `bornology`. -/
def of (α : Type _) [Bornology α] : Born :=
  Bundled.of α
#align Born.of Born.of
-/

instance : Inhabited Born :=
  ⟨of PUnit⟩

instance : BundledHom @LocallyBoundedMap
    where
  toFun _ _ _ _ := coeFn
  id := @LocallyBoundedMap.id
  comp := @LocallyBoundedMap.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} Born :=
  BundledHom.category LocallyBoundedMap

instance : ConcreteCategory Born :=
  BundledHom.concreteCategory LocallyBoundedMap

end Born

