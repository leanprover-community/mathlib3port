/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.Algebra.Category.Module.Basic

/-!
# Change Of Rings

## Main definitions

* `category_theory.Module.restrict_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`,
  then `restrict_scalars : Module S ⥤ Module R` is defined by `M ↦ M` where `M : S-module` is seen
  as `R-module` by `r • m := f r • m` and `S`-linear map `l : M ⟶ M'` is `R`-linear as well.
-/


namespace CategoryTheory.Module

universe v u₁ u₂

namespace RestrictScalars

variable {R : Type u₁} {S : Type u₂} [Ringₓ R] [Ringₓ S] (f : R →+* S)

variable (M : ModuleCat.{v} S)

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
    `r • m := f r • m` (`module.comp_hom`). This is called restriction of scalars. -/
def obj' : ModuleCat R where
  Carrier := M
  isModule := Module.compHom M f

/-- Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
def map' {M M' : ModuleCat.{v} S} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  { g with map_smul' := fun r => g.map_smul (f r) }

end RestrictScalars

/-- The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
def restrictScalars {R : Type u₁} {S : Type u₂} [Ringₓ R] [Ringₓ S] (f : R →+* S) :
    ModuleCat.{v} S ⥤ ModuleCat.{v} R where
  obj := RestrictScalars.obj' f
  map := fun _ _ => RestrictScalars.map' f
  map_id' := fun _ => LinearMap.ext fun m => rfl
  map_comp' := fun _ _ _ g h => LinearMap.ext fun m => rfl

@[simp]
theorem restrictScalars.map_apply {R : Type u₁} {S : Type u₂} [Ringₓ R] [Ringₓ S] (f : R →+* S) {M M' : ModuleCat.{v} S}
    (g : M ⟶ M') (x) : (restrictScalars f).map g x = g x :=
  rfl

@[simp]
theorem restrictScalars.smul_def {R : Type u₁} {S : Type u₂} [Ringₓ R] [Ringₓ S] (f : R →+* S) {M : ModuleCat.{v} S}
    (r : R) (m : (restrictScalars f).obj M) : r • m = (f r • m : M) :=
  rfl

@[simp]
theorem restrictScalars.smul_def' {R : Type u₁} {S : Type u₂} [Ringₓ R] [Ringₓ S] (f : R →+* S) {M : ModuleCat.{v} S}
    (r : R) (m : M) : (r • m : (restrictScalars f).obj M) = (f r • m : M) :=
  rfl

end CategoryTheory.Module

