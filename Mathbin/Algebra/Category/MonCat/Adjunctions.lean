/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Algebra.Category.MonCat.Basic
import Algebra.Category.Semigrp.Basic
import Algebra.Group.WithOne.Basic
import Algebra.FreeMonoid.Basic

#align_import algebra.category.Mon.adjunctions from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# Adjunctions regarding the category of monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the adjunction between adjoining a unit to a semigroup and the forgetful functor
from monoids to semigroups.

## TODO

* free-forgetful adjunction for monoids
* adjunctions related to commutative monoids
-/


universe u

open CategoryTheory

#print MonCat.adjoinOne /-
/-- The functor of adjoining a neutral element `one` to a semigroup.
 -/
@[to_additive "The functor of adjoining a neutral element `zero` to a semigroup", simps]
def MonCat.adjoinOne : Semigrp.{u} ⥤ MonCat.{u}
    where
  obj S := MonCat.of (WithOne S)
  map X Y := WithOne.map
  map_id' X := WithOne.map_id
  map_comp' X Y Z := WithOne.map_comp
#align adjoin_one MonCat.adjoinOne
#align adjoin_zero AddMonCat.adjoinZero
-/

#print MonCat.hasForgetToSemigroup /-
@[to_additive AddMonCat.hasForgetToAddSemigroup]
instance MonCat.hasForgetToSemigroup : HasForget₂ MonCat Semigrp
    where forget₂ :=
    { obj := fun M => Semigrp.of M
      map := fun M N => MonoidHom.toMulHom }
#align has_forget_to_Semigroup MonCat.hasForgetToSemigroup
#align has_forget_to_AddSemigroup AddMonCat.hasForgetToAddSemigroup
-/

#print MonCat.adjoinOneAdj /-
/-- The adjoin_one-forgetful adjunction from `Semigroup` to `Mon`.-/
@[to_additive "The adjoin_one-forgetful adjunction from `AddSemigroup` to `AddMon`"]
def MonCat.adjoinOneAdj : MonCat.adjoinOne ⊣ forget₂ MonCat.{u} Semigrp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun S M => WithOne.lift.symm
      homEquiv_naturality_left_symm := by
        intro S T M f g
        ext
        simp only [Equiv.symm_symm, adjoinOne_map, coe_comp]
        simp_rw [WithOne.map]
        apply WithOne.cases_on x
        · rfl
        · simp }
#align adjoin_one_adj MonCat.adjoinOneAdj
#align adjoin_zero_adj AddMonCat.adjoinZeroAdj
-/

#print MonCat.free /-
/-- The free functor `Type u ⥤ Mon` sending a type `X` to the free monoid on `X`. -/
def MonCat.free : Type u ⥤ MonCat.{u}
    where
  obj α := MonCat.of (FreeMonoid α)
  map X Y := FreeMonoid.map
  map_id' := by intros; ext1; rfl
  map_comp' := by intros; ext1; rfl
#align free MonCat.free
-/

#print MonCat.adj /-
/-- The free-forgetful adjunction for monoids. -/
def MonCat.adj : MonCat.free ⊣ forget MonCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeMonoid.lift.symm
      homEquiv_naturality_left_symm := fun X Y G f g => by ext1; rfl }
#align adj MonCat.adj
-/

instance : CategoryTheory.Functor.IsRightAdjoint (forget MonCat.{u}) :=
  ⟨_, MonCat.adj⟩

