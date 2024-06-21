/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Algebra.PEmptyInstances
import Algebra.Group.Equiv.Basic
import CategoryTheory.ConcreteCategory.BundledHom
import CategoryTheory.Functor.ReflectsIso
import CategoryTheory.Elementwise

#align_import algebra.category.Semigroup.basic from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# Category instances for has_mul, has_add, semigroup and add_semigroup

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the bundled categories:
* `Magma`
* `AddMagma`
* `Semigroup`
* `AddSemigroup`
along with the relevant forgetful functors between them.

This closely follows `algebra.category.Mon.basic`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/


universe u v

open CategoryTheory

#print MagmaCat /-
/-- The category of magmas and magma morphisms. -/
@[to_additive AddMagmaCat]
def MagmaCat : Type (u + 1) :=
  Bundled Mul
#align Magma MagmaCat
#align AddMagma AddMagmaCat
-/

/-- The category of additive magmas and additive magma morphisms. -/
add_decl_doc AddMagmaCat

namespace MagmaCat

#print MagmaCat.bundledHom /-
@[to_additive]
instance bundledHom : BundledHom @MulHom :=
  ⟨@MulHom.toFun, @MulHom.id, @MulHom.comp, @DFunLike.coe_injective⟩
#align Magma.bundled_hom MagmaCat.bundledHom
#align AddMagma.bundled_hom AddMagmaCat.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for MagmaCat

attribute [to_additive] MagmaCat.largeCategory MagmaCat.concreteCategory

@[to_additive]
instance : CoeSort MagmaCat (Type _) :=
  Bundled.hasCoeToSort

#print MagmaCat.of /-
/-- Construct a bundled `Magma` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Mul M] : MagmaCat :=
  Bundled.of M
#align Magma.of MagmaCat.of
#align AddMagma.of AddMagmaCat.of
-/

/-- Construct a bundled `AddMagma` from the underlying type and typeclass. -/
add_decl_doc AddMagmaCat.of

#print MagmaCat.ofHom /-
/-- Typecheck a `mul_hom` as a morphism in `Magma`. -/
@[to_additive]
def ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Magma.of_hom MagmaCat.ofHom
#align AddMagma.of_hom AddMagmaCat.ofHom
-/

/-- Typecheck a `add_hom` as a morphism in `AddMagma`. -/
add_decl_doc AddMagmaCat.ofHom

#print MagmaCat.ofHom_apply /-
@[simp, to_additive]
theorem ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) : ofHom f x = f x :=
  rfl
#align Magma.of_hom_apply MagmaCat.ofHom_apply
#align AddMagma.of_hom_apply AddMagmaCat.ofHom_apply
-/

@[to_additive]
instance : Inhabited MagmaCat :=
  ⟨MagmaCat.of PEmpty⟩

@[to_additive]
instance (M : MagmaCat) : Mul M :=
  M.str

#print MagmaCat.coe_of /-
@[simp, to_additive]
theorem coe_of (R : Type u) [Mul R] : (MagmaCat.of R : Type u) = R :=
  rfl
#align Magma.coe_of MagmaCat.coe_of
#align AddMagma.coe_of AddMagmaCat.coe_of
-/

end MagmaCat

#print Semigrp /-
/-- The category of semigroups and semigroup morphisms. -/
@[to_additive AddSemigrp]
def Semigrp : Type (u + 1) :=
  Bundled Semigroup
#align Semigroup Semigrp
#align AddSemigroup AddSemigrp
-/

/-- The category of additive semigroups and semigroup morphisms. -/
add_decl_doc AddSemigrp

namespace Semigrp

@[to_additive]
instance : BundledHom.ParentProjection Semigroup.toHasMul :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for Semigrp

attribute [to_additive] Semigrp.largeCategory Semigrp.concreteCategory

@[to_additive]
instance : CoeSort Semigrp (Type _) :=
  Bundled.hasCoeToSort

#print Semigrp.of /-
/-- Construct a bundled `Semigroup` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Semigroup M] : Semigrp :=
  Bundled.of M
#align Semigroup.of Semigrp.of
#align AddSemigroup.of AddSemigrp.of
-/

/-- Construct a bundled `AddSemigroup` from the underlying type and typeclass. -/
add_decl_doc AddSemigrp.of

#print Semigrp.ofHom /-
/-- Typecheck a `mul_hom` as a morphism in `Semigroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Semigroup.of_hom Semigrp.ofHom
#align AddSemigroup.of_hom AddSemigrp.ofHom
-/

/-- Typecheck a `add_hom` as a morphism in `AddSemigroup`. -/
add_decl_doc AddSemigrp.ofHom

#print Semigrp.ofHom_apply /-
@[simp, to_additive]
theorem ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    ofHom f x = f x :=
  rfl
#align Semigroup.of_hom_apply Semigrp.ofHom_apply
#align AddSemigroup.of_hom_apply AddSemigrp.ofHom_apply
-/

@[to_additive]
instance : Inhabited Semigrp :=
  ⟨Semigrp.of PEmpty⟩

@[to_additive]
instance (M : Semigrp) : Semigroup M :=
  M.str

#print Semigrp.coe_of /-
@[simp, to_additive]
theorem coe_of (R : Type u) [Semigroup R] : (Semigrp.of R : Type u) = R :=
  rfl
#align Semigroup.coe_of Semigrp.coe_of
#align AddSemigroup.coe_of AddSemigrp.coe_of
-/

#print Semigrp.hasForgetToMagmaCat /-
@[to_additive has_forget_to_AddMagma]
instance hasForgetToMagmaCat : HasForget₂ Semigrp MagmaCat :=
  BundledHom.forget₂ _ _
#align Semigroup.has_forget_to_Magma Semigrp.hasForgetToMagmaCat
#align AddSemigroup.has_forget_to_AddMagma AddSemigrp.hasForgetToAddMagmaCat
-/

end Semigrp

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

#print MulEquiv.toMagmaCatIso /-
/-- Build an isomorphism in the category `Magma` from a `mul_equiv` between `has_mul`s. -/
@[to_additive AddEquiv.toAddMagmaCatIso
      "Build an isomorphism in the category `AddMagma` from\nan `add_equiv` between `has_add`s.",
  simps]
def MulEquiv.toMagmaCatIso (e : X ≃* Y) : MagmaCat.of X ≅ MagmaCat.of Y
    where
  Hom := e.toMulHom
  inv := e.symm.toMulHom
#align mul_equiv.to_Magma_iso MulEquiv.toMagmaCatIso
#align add_equiv.to_AddMagma_iso AddEquiv.toAddMagmaCatIso
-/

end

section

variable [Semigroup X] [Semigroup Y]

#print MulEquiv.toSemigrpIso /-
/-- Build an isomorphism in the category `Semigroup` from a `mul_equiv` between `semigroup`s. -/
@[to_additive AddEquiv.toAddSemigrpIso
      "Build an isomorphism in the category\n`AddSemigroup` from an `add_equiv` between `add_semigroup`s.",
  simps]
def MulEquiv.toSemigrpIso (e : X ≃* Y) : Semigrp.of X ≅ Semigrp.of Y
    where
  Hom := e.toMulHom
  inv := e.symm.toMulHom
#align mul_equiv.to_Semigroup_iso MulEquiv.toSemigrpIso
#align add_equiv.to_AddSemigroup_iso AddEquiv.toAddSemigrpIso
-/

end

namespace CategoryTheory.Iso

#print CategoryTheory.Iso.magmaCatIsoToMulEquiv /-
/-- Build a `mul_equiv` from an isomorphism in the category `Magma`. -/
@[to_additive AddMagma_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism in the category\n`AddMagma`."]
def magmaCatIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) : X ≃* Y
    where
  toFun := i.Hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := by simp
#align category_theory.iso.Magma_iso_to_mul_equiv CategoryTheory.Iso.magmaCatIsoToMulEquiv
#align category_theory.iso.AddMagma_iso_to_add_equiv CategoryTheory.Iso.addMagmaCatIsoToAddEquiv
-/

#print CategoryTheory.Iso.semigrpIsoToMulEquiv /-
/-- Build a `mul_equiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive "Build an `add_equiv` from an isomorphism in the category\n`AddSemigroup`."]
def semigrpIsoToMulEquiv {X Y : Semigrp} (i : X ≅ Y) : X ≃* Y
    where
  toFun := i.Hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := by simp
#align category_theory.iso.Semigroup_iso_to_mul_equiv CategoryTheory.Iso.semigrpIsoToMulEquiv
#align category_theory.iso.Semigroup_iso_to_add_equiv CategoryTheory.Iso.addSemigrpIsoToAddEquiv
-/

end CategoryTheory.Iso

#print mulEquivIsoMagmaIso /-
/-- multiplicative equivalences between `has_mul`s are the same as (isomorphic to) isomorphisms
in `Magma` -/
@[to_additive addEquivIsoAddMagmaIso
      "additive equivalences between `has_add`s are the same\nas (isomorphic to) isomorphisms in `AddMagma`"]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] : X ≃* Y ≅ MagmaCat.of X ≅ MagmaCat.of Y
    where
  Hom e := e.toMagmaCatIso
  inv i := i.magmaCatIsoToMulEquiv
#align mul_equiv_iso_Magma_iso mulEquivIsoMagmaIso
#align add_equiv_iso_AddMagma_iso addEquivIsoAddMagmaIso
-/

#print mulEquivIsoSemigrpIso /-
/-- multiplicative equivalences between `semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive addEquivIsoAddSemigrpIso
      "additive equivalences between `add_semigroup`s are\nthe same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mulEquivIsoSemigrpIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    X ≃* Y ≅ Semigrp.of X ≅ Semigrp.of Y
    where
  Hom e := e.toSemigrpIso
  inv i := i.semigrpIsoToMulEquiv
#align mul_equiv_iso_Semigroup_iso mulEquivIsoSemigrpIso
#align add_equiv_iso_AddSemigroup_iso addEquivIsoAddSemigrpIso
-/

#print MagmaCat.forgetReflectsIsos /-
@[to_additive]
instance MagmaCat.forgetReflectsIsos :
    CategoryTheory.Functor.ReflectsIsomorphisms (forget MagmaCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Magma_iso).1⟩
#align Magma.forget_reflects_isos MagmaCat.forgetReflectsIsos
#align AddMagma.forget_reflects_isos AddMagmaCat.forgetReflectsIsos
-/

#print Semigrp.forgetReflectsIsos /-
@[to_additive]
instance Semigrp.forgetReflectsIsos :
    CategoryTheory.Functor.ReflectsIsomorphisms (forget Semigrp.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget Semigrp).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Semigroup_iso).1⟩
#align Semigroup.forget_reflects_isos Semigrp.forgetReflectsIsos
#align AddSemigroup.forget_reflects_isos AddSemigrp.forgetReflectsIsos
-/

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/


example : CategoryTheory.Functor.ReflectsIsomorphisms (forget₂ Semigrp MagmaCat) := by
  infer_instance

