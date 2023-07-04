/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module algebra.category.Semigroup.basic
! leanprover-community/mathlib commit 728ef9dbb281241906f25cbeb30f90d83e0bb451
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.PemptyInstances
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms
import Mathbin.CategoryTheory.Elementwise

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
  ⟨@MulHom.toFun, @MulHom.id, @MulHom.comp, @MulHom.coe_inj⟩
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

#print SemigroupCat /-
/-- The category of semigroups and semigroup morphisms. -/
@[to_additive AddSemigroupCat]
def SemigroupCat : Type (u + 1) :=
  Bundled Semigroup
#align Semigroup SemigroupCat
#align AddSemigroup AddSemigroupCat
-/

/-- The category of additive semigroups and semigroup morphisms. -/
add_decl_doc AddSemigroupCat

namespace SemigroupCat

@[to_additive]
instance : BundledHom.ParentProjection Semigroup.toHasMul :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for SemigroupCat

attribute [to_additive] SemigroupCat.largeCategory SemigroupCat.concreteCategory

@[to_additive]
instance : CoeSort SemigroupCat (Type _) :=
  Bundled.hasCoeToSort

#print SemigroupCat.of /-
/-- Construct a bundled `Semigroup` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Semigroup M] : SemigroupCat :=
  Bundled.of M
#align Semigroup.of SemigroupCat.of
#align AddSemigroup.of AddSemigroupCat.of
-/

/-- Construct a bundled `AddSemigroup` from the underlying type and typeclass. -/
add_decl_doc AddSemigroupCat.of

#print SemigroupCat.ofHom /-
/-- Typecheck a `mul_hom` as a morphism in `Semigroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Semigroup.of_hom SemigroupCat.ofHom
#align AddSemigroup.of_hom AddSemigroupCat.ofHom
-/

/-- Typecheck a `add_hom` as a morphism in `AddSemigroup`. -/
add_decl_doc AddSemigroupCat.ofHom

#print SemigroupCat.ofHom_apply /-
@[simp, to_additive]
theorem ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    ofHom f x = f x :=
  rfl
#align Semigroup.of_hom_apply SemigroupCat.ofHom_apply
#align AddSemigroup.of_hom_apply AddSemigroupCat.ofHom_apply
-/

@[to_additive]
instance : Inhabited SemigroupCat :=
  ⟨SemigroupCat.of PEmpty⟩

@[to_additive]
instance (M : SemigroupCat) : Semigroup M :=
  M.str

#print SemigroupCat.coe_of /-
@[simp, to_additive]
theorem coe_of (R : Type u) [Semigroup R] : (SemigroupCat.of R : Type u) = R :=
  rfl
#align Semigroup.coe_of SemigroupCat.coe_of
#align AddSemigroup.coe_of AddSemigroupCat.coe_of
-/

#print SemigroupCat.hasForgetToMagmaCat /-
@[to_additive has_forget_to_AddMagma]
instance hasForgetToMagmaCat : HasForget₂ SemigroupCat MagmaCat :=
  BundledHom.forget₂ _ _
#align Semigroup.has_forget_to_Magma SemigroupCat.hasForgetToMagmaCat
#align AddSemigroup.has_forget_to_AddMagma AddSemigroupCat.hasForgetToAddMagmaCat
-/

end SemigroupCat

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

#print MulEquiv.toSemigroupCatIso /-
/-- Build an isomorphism in the category `Semigroup` from a `mul_equiv` between `semigroup`s. -/
@[to_additive AddEquiv.toAddSemigroupCatIso
      "Build an isomorphism in the category\n`AddSemigroup` from an `add_equiv` between `add_semigroup`s.",
  simps]
def MulEquiv.toSemigroupCatIso (e : X ≃* Y) : SemigroupCat.of X ≅ SemigroupCat.of Y
    where
  Hom := e.toMulHom
  inv := e.symm.toMulHom
#align mul_equiv.to_Semigroup_iso MulEquiv.toSemigroupCatIso
#align add_equiv.to_AddSemigroup_iso AddEquiv.toAddSemigroupCatIso
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

#print CategoryTheory.Iso.semigroupCatIsoToMulEquiv /-
/-- Build a `mul_equiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive "Build an `add_equiv` from an isomorphism in the category\n`AddSemigroup`."]
def semigroupCatIsoToMulEquiv {X Y : SemigroupCat} (i : X ≅ Y) : X ≃* Y
    where
  toFun := i.Hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := by simp
#align category_theory.iso.Semigroup_iso_to_mul_equiv CategoryTheory.Iso.semigroupCatIsoToMulEquiv
#align category_theory.iso.Semigroup_iso_to_add_equiv CategoryTheory.Iso.addSemigroupCatIsoToAddEquiv
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

#print mulEquivIsoSemigroupCatIso /-
/-- multiplicative equivalences between `semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive addEquivIsoAddSemigroupCatIso
      "additive equivalences between `add_semigroup`s are\nthe same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mulEquivIsoSemigroupCatIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    X ≃* Y ≅ SemigroupCat.of X ≅ SemigroupCat.of Y
    where
  Hom e := e.toSemigroupCatIso
  inv i := i.semigroupCatIsoToMulEquiv
#align mul_equiv_iso_Semigroup_iso mulEquivIsoSemigroupCatIso
#align add_equiv_iso_AddSemigroup_iso addEquivIsoAddSemigroupCatIso
-/

#print MagmaCat.forgetReflectsIsos /-
@[to_additive]
instance MagmaCat.forgetReflectsIsos : ReflectsIsomorphisms (forget MagmaCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Magma_iso).1⟩
#align Magma.forget_reflects_isos MagmaCat.forgetReflectsIsos
#align AddMagma.forget_reflects_isos AddMagmaCat.forgetReflectsIsos
-/

#print SemigroupCat.forgetReflectsIsos /-
@[to_additive]
instance SemigroupCat.forgetReflectsIsos : ReflectsIsomorphisms (forget SemigroupCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget SemigroupCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Semigroup_iso).1⟩
#align Semigroup.forget_reflects_isos SemigroupCat.forgetReflectsIsos
#align AddSemigroup.forget_reflects_isos AddSemigroupCat.forgetReflectsIsos
-/

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/


example : ReflectsIsomorphisms (forget₂ SemigroupCat MagmaCat) := by infer_instance

