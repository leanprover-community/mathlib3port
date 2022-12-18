/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module algebra.category.Semigroup.basic
! leanprover-community/mathlib commit c5c7e2760814660967bc27f0de95d190a22297f3
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

/-- The category of magmas and magma morphisms. -/
@[to_additive AddMagmaCat]
def MagmaCat : Type (u + 1) :=
  Bundled Mul
#align Magma MagmaCat

/-- The category of additive magmas and additive magma morphisms. -/
add_decl_doc AddMagmaCat

namespace MagmaCat

@[to_additive]
instance bundledHom : BundledHom @MulHom :=
  ⟨@MulHom.toFun, @MulHom.id, @MulHom.comp, @MulHom.coe_inj⟩
#align Magma.bundled_hom MagmaCat.bundledHom

deriving instance LargeCategory, ConcreteCategory for MagmaCat

attribute [to_additive] MagmaCat.largeCategory MagmaCat.concreteCategory

@[to_additive]
instance : CoeSort MagmaCat (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Magma` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Mul M] : MagmaCat :=
  Bundled.of M
#align Magma.of MagmaCat.of

/-- Construct a bundled `AddMagma` from the underlying type and typeclass. -/
add_decl_doc AddMagmaCat.of

/-- Typecheck a `mul_hom` as a morphism in `Magma`. -/
@[to_additive]
def ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Magma.of_hom MagmaCat.ofHom

/-- Typecheck a `add_hom` as a morphism in `AddMagma`. -/
add_decl_doc AddMagmaCat.ofHom

@[simp, to_additive]
theorem of_hom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) : ofHom f x = f x :=
  rfl
#align Magma.of_hom_apply MagmaCat.of_hom_apply

@[to_additive]
instance : Inhabited MagmaCat :=
  ⟨MagmaCat.of PEmpty⟩

@[to_additive]
instance (M : MagmaCat) : Mul M :=
  M.str

@[simp, to_additive]
theorem coe_of (R : Type u) [Mul R] : (MagmaCat.of R : Type u) = R :=
  rfl
#align Magma.coe_of MagmaCat.coe_of

end MagmaCat

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive AddSemigroupCat]
def SemigroupCat : Type (u + 1) :=
  Bundled Semigroup
#align Semigroup SemigroupCat

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
  bundled.has_coe_to_sort

/-- Construct a bundled `Semigroup` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Semigroup M] : SemigroupCat :=
  Bundled.of M
#align Semigroup.of SemigroupCat.of

/-- Construct a bundled `AddSemigroup` from the underlying type and typeclass. -/
add_decl_doc AddSemigroupCat.of

/-- Typecheck a `mul_hom` as a morphism in `Semigroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  f
#align Semigroup.of_hom SemigroupCat.ofHom

/-- Typecheck a `add_hom` as a morphism in `AddSemigroup`. -/
add_decl_doc AddSemigroupCat.ofHom

@[simp, to_additive]
theorem of_hom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    ofHom f x = f x :=
  rfl
#align Semigroup.of_hom_apply SemigroupCat.of_hom_apply

@[to_additive]
instance : Inhabited SemigroupCat :=
  ⟨SemigroupCat.of PEmpty⟩

@[to_additive]
instance (M : SemigroupCat) : Semigroup M :=
  M.str

@[simp, to_additive]
theorem coe_of (R : Type u) [Semigroup R] : (SemigroupCat.of R : Type u) = R :=
  rfl
#align Semigroup.coe_of SemigroupCat.coe_of

@[to_additive has_forget_to_AddMagma]
instance hasForgetToMagma : HasForget₂ SemigroupCat MagmaCat :=
  BundledHom.forget₂ _ _
#align Semigroup.has_forget_to_Magma SemigroupCat.hasForgetToMagma

end SemigroupCat

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `Magma` from a `mul_equiv` between `has_mul`s. -/
@[to_additive AddEquiv.toAddMagmaIso
      "Build an isomorphism in the category `AddMagma` from\nan `add_equiv` between `has_add`s.",
  simps]
def MulEquiv.toMagmaIso (e : X ≃* Y) :
    MagmaCat.of X ≅ MagmaCat.of Y where 
  Hom := e.toMulHom
  inv := e.symm.toMulHom
#align mul_equiv.to_Magma_iso MulEquiv.toMagmaIso

end

section

variable [Semigroup X] [Semigroup Y]

/-- Build an isomorphism in the category `Semigroup` from a `mul_equiv` between `semigroup`s. -/
@[to_additive AddEquiv.toAddSemigroupIso
      "Build an isomorphism in the category\n`AddSemigroup` from an `add_equiv` between `add_semigroup`s.",
  simps]
def MulEquiv.toSemigroupIso (e : X ≃* Y) :
    SemigroupCat.of X ≅ SemigroupCat.of
        Y where 
  Hom := e.toMulHom
  inv := e.symm.toMulHom
#align mul_equiv.to_Semigroup_iso MulEquiv.toSemigroupIso

end

namespace CategoryTheory.Iso

/-- Build a `mul_equiv` from an isomorphism in the category `Magma`. -/
@[to_additive AddMagma_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism in the category\n`AddMagma`."]
def magmaIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) :
    X ≃* Y where 
  toFun := i.Hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := by simp
#align category_theory.iso.Magma_iso_to_mul_equiv CategoryTheory.Iso.magmaIsoToMulEquiv

/-- Build a `mul_equiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive "Build an `add_equiv` from an isomorphism in the category\n`AddSemigroup`."]
def semigroupIsoToMulEquiv {X Y : SemigroupCat} (i : X ≅ Y) :
    X ≃* Y where 
  toFun := i.Hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := by simp
#align category_theory.iso.Semigroup_iso_to_mul_equiv CategoryTheory.Iso.semigroupIsoToMulEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `has_mul`s are the same as (isomorphic to) isomorphisms
in `Magma` -/
@[to_additive addEquivIsoAddMagmaIso
      "additive equivalences between `has_add`s are the same\nas (isomorphic to) isomorphisms in `AddMagma`"]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] :
    X ≃* Y ≅ MagmaCat.of X ≅
        MagmaCat.of Y where 
  Hom e := e.toMagmaIso
  inv i := i.magmaIsoToMulEquiv
#align mul_equiv_iso_Magma_iso mulEquivIsoMagmaIso

/-- multiplicative equivalences between `semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive addEquivIsoAddSemigroupIso
      "additive equivalences between `add_semigroup`s are\nthe same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mulEquivIsoSemigroupIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    X ≃* Y ≅ SemigroupCat.of X ≅
        SemigroupCat.of Y where 
  Hom e := e.toSemigroupIso
  inv i := i.semigroupIsoToMulEquiv
#align mul_equiv_iso_Semigroup_iso mulEquivIsoSemigroupIso

@[to_additive]
instance MagmaCat.forget_reflects_isos :
    ReflectsIsomorphisms
      (forget MagmaCat.{u}) where reflects X Y f _ := by
    skip
    let i := as_iso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Magma_iso).1⟩
#align Magma.forget_reflects_isos MagmaCat.forget_reflects_isos

@[to_additive]
instance SemigroupCat.forget_reflects_isos :
    ReflectsIsomorphisms
      (forget
        SemigroupCat.{u}) where reflects X Y f _ := by
    skip
    let i := as_iso ((forget SemigroupCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Semigroup_iso).1⟩
#align Semigroup.forget_reflects_isos SemigroupCat.forget_reflects_isos

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/


example : ReflectsIsomorphisms (forget₂ SemigroupCat MagmaCat) := by infer_instance

