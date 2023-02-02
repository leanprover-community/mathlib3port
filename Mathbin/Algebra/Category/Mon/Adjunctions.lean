/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module algebra.category.Mon.adjunctions
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.Algebra.Category.Semigroup.Basic
import Mathbin.Algebra.Group.WithOne.Basic
import Mathbin.Algebra.FreeMonoid.Basic

/-!
# Adjunctions regarding the category of monoids

This file proves the adjunction between adjoining a unit to a semigroup and the forgetful functor
from monoids to semigroups.

## TODO

* free-forgetful adjunction for monoids
* adjunctions related to commutative monoids
-/


universe u

open CategoryTheory

/-- The functor of adjoining a neutral element `one` to a semigroup.
 -/
@[to_additive "The functor of adjoining a neutral element `zero` to a semigroup", simps]
def adjoinOne : SemigroupCat.{u} ⥤ Mon.{u}
    where
  obj S := Mon.of (WithOne S)
  map X Y := WithOne.map
  map_id' X := WithOne.map_id
  map_comp' X Y Z := WithOne.map_comp
#align adjoin_one adjoinOne
#align adjoin_zero adjoinZero

@[to_additive hasForgetToAddSemigroup]
instance hasForgetToSemigroup : HasForget₂ Mon SemigroupCat
    where forget₂ :=
    { obj := fun M => SemigroupCat.of M
      map := fun M N => MonoidHom.toMulHom }
#align has_forget_to_Semigroup hasForgetToSemigroup
#align has_forget_to_AddSemigroup hasForgetToAddSemigroup

/-- The adjoin_one-forgetful adjunction from `Semigroup` to `Mon`.-/
@[to_additive "The adjoin_one-forgetful adjunction from `AddSemigroup` to `AddMon`"]
def adjoinOneAdj : adjoinOne ⊣ forget₂ Mon.{u} SemigroupCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun S M => WithOne.lift.symm
      homEquiv_naturality_left_symm' := by
        intro S T M f g
        ext
        simp only [Equiv.symm_symm, adjoinOne_map, coe_comp]
        simp_rw [WithOne.map]
        apply WithOne.cases_on x
        · rfl
        · simp }
#align adjoin_one_adj adjoinOneAdj
#align adjoin_zero_adj adjoin_zero_adj

/-- The free functor `Type u ⥤ Mon` sending a type `X` to the free monoid on `X`. -/
def free : Type u ⥤ Mon.{u} where
  obj α := Mon.of (FreeMonoid α)
  map X Y := FreeMonoid.map
  map_id' := by
    intros
    ext1
    rfl
  map_comp' := by
    intros
    ext1
    rfl
#align free free

/-- The free-forgetful adjunction for monoids. -/
def adj : free ⊣ forget Mon.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeMonoid.lift.symm
      homEquiv_naturality_left_symm' := fun X Y G f g =>
        by
        ext1
        rfl }
#align adj adj

instance : IsRightAdjoint (forget Mon.{u}) :=
  ⟨_, adj⟩

