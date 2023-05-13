/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebra.category.Module.change_of_rings
! leanprover-community/mathlib commit 403190b5419b3f03f1a2893ad9352ca7f7d8bff6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.RingTheory.TensorProduct

/-!
# Change Of Rings

## Main definitions

* `category_theory.Module.restrict_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`,
  then `restrict_scalars : Module S ⥤ Module R` is defined by `M ↦ M` where `M : S-module` is seen
  as `R-module` by `r • m := f r • m` and `S`-linear map `l : M ⟶ M'` is `R`-linear as well.

* `category_theory.Module.extend_scalars`: given **commutative** rings `R, S` and ring homomorphism
  `f : R ⟶ S`, then `extend_scalars : Module R ⥤ Module S` is defined by `M ↦ S ⨂ M` where the
  module structure is defined by `s • (s' ⊗ m) := (s * s') ⊗ m` and `R`-linear map `l : M ⟶ M'`
  is sent to `S`-linear map `s ⊗ m ↦ s ⊗ l m : S ⨂ M ⟶ S ⨂ M'`.

## Main results

* `category_theory.Module.extend_restrict_scalars_adj`: given commutative rings `R, S` and a ring
  homomorphism `f : R →+* S`, the extension and restriction of scalars by `f` are adjoint functors.

## List of notations
Let `R, S` be rings and `f : R →+* S`
* if `M` is an `R`-module, `s : S` and `m : M`, then `s ⊗ₜ[R, f] m` is the pure tensor
  `s ⊗ m : S ⊗[R, f] M`.
-/


namespace CategoryTheory.Module

universe v u₁ u₂

namespace RestrictScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

variable (M : ModuleCat.{v} S)

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
    `r • m := f r • m` (`module.comp_hom`). This is called restriction of scalars. -/
def obj' : ModuleCat R where
  carrier := M
  isModule := Module.compHom M f
#align category_theory.Module.restrict_scalars.obj' CategoryTheory.Module.RestrictScalars.obj'

/-- Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
def map' {M M' : ModuleCat.{v} S} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  { g with map_smul' := fun r => g.map_smul (f r) }
#align category_theory.Module.restrict_scalars.map' CategoryTheory.Module.RestrictScalars.map'

end RestrictScalars

/-- The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
def restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat.{v} S ⥤ ModuleCat.{v} R
    where
  obj := RestrictScalars.obj' f
  map _ _ := RestrictScalars.map' f
  map_id' _ := LinearMap.ext fun m => rfl
  map_comp' _ _ _ g h := LinearMap.ext fun m => rfl
#align category_theory.Module.restrict_scalars CategoryTheory.Module.restrictScalars

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    CategoryTheory.Faithful (restrictScalars.{v} f)
    where map_injective' _ _ _ _ h :=
    LinearMap.ext fun x => by simpa only using FunLike.congr_fun h x

@[simp]
theorem restrictScalars.map_apply {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M M' : ModuleCat.{v} S} (g : M ⟶ M') (x) : (restrictScalars f).map g x = g x :=
  rfl
#align category_theory.Module.restrict_scalars.map_apply CategoryTheory.Module.restrictScalars.map_apply

@[simp]
theorem restrictScalars.smul_def {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : (restrictScalars f).obj M) : r • m = (f r • m : M) :=
  rfl
#align category_theory.Module.restrict_scalars.smul_def CategoryTheory.Module.restrictScalars.smul_def

theorem restrictScalars.smul_def' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : M) : (r • m : (restrictScalars f).obj M) = (f r • m : M) :=
  rfl
#align category_theory.Module.restrict_scalars.smul_def' CategoryTheory.Module.restrictScalars.smul_def'

instance (priority := 100) sMulCommClass_mk {R : Type u₁} {S : Type u₂} [Ring R] [CommRing S]
    (f : R →+* S) (M : Type v) [AddCommGroup M] [Module S M] :
    @SMulCommClass R S M (RestrictScalars.obj' f (ModuleCat.mk M)).isModule.toSMul _
    where smul_comm r s m := (by simp [← mul_smul, mul_comm] : f r • s • m = s • f r • m)
#align category_theory.Module.smul_comm_class_mk CategoryTheory.Module.sMulCommClass_mk

namespace ExtendScalars

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

section Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

-- mathport name: «expr ⊗ₜ[ , ] »
-- This notation is necessary because we need to reason about `s ⊗ₜ m` where `s : S` and `m : M`;
-- without this notation, one need to work with `s : (restrict_scalars f).obj ⟨S⟩`.
scoped[ChangeOfRings]
  notation s "⊗ₜ[" R "," f "]" m => @TensorProduct.tmul R _ _ _ _ _ (Module.compHom _ f) _ s m

end Unbundled

open ChangeOfRings

variable (M : ModuleCat.{v} R)

/-- Extension of scalars turn an `R`-module into `S`-module by M ↦ S ⨂ M
-/
def obj' : ModuleCat S :=
  ⟨TensorProduct R ((restrictScalars f).obj ⟨S⟩) M⟩
#align category_theory.Module.extend_scalars.obj' CategoryTheory.Module.ExtendScalars.obj'

/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def map' {M1 M2 : ModuleCat.{v} R} (l : M1 ⟶ M2) : obj' f M1 ⟶ obj' f M2 :=
  by-- The "by apply" part makes this require 75% fewer heartbeats to process (#16371).
  apply @LinearMap.baseChange R S M1 M2 _ _ ((algebraMap S _).comp f).toAlgebra _ _ _ _ l
#align category_theory.Module.extend_scalars.map' CategoryTheory.Module.ExtendScalars.map'

theorem map'_id {M : ModuleCat.{v} R} : map' f (𝟙 M) = 𝟙 _ :=
  LinearMap.ext fun x : obj' f M =>
    by
    dsimp only [map', ModuleCat.id_apply]
    induction' x using TensorProduct.induction_on with _ _ m s ihx ihy
    · simp only [map_zero]
    · rw [LinearMap.baseChange_tmul, ModuleCat.id_apply]
    · rw [map_add, ihx, ihy]
#align category_theory.Module.extend_scalars.map'_id CategoryTheory.Module.ExtendScalars.map'_id

theorem map'_comp {M₁ M₂ M₃ : ModuleCat.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃) :
    map' f (l₁₂ ≫ l₂₃) = map' f l₁₂ ≫ map' f l₂₃ :=
  LinearMap.ext fun x : obj' f M₁ => by
    dsimp only [map']
    induction' x using TensorProduct.induction_on with _ _ x y ihx ihy
    · rfl
    · rfl
    · simp only [map_add, ihx, ihy]
#align category_theory.Module.extend_scalars.map'_comp CategoryTheory.Module.ExtendScalars.map'_comp

end ExtendScalars

/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def extendScalars {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    ModuleCat.{v} R ⥤ ModuleCat.{max v u₂} S
    where
  obj M := ExtendScalars.obj' f M
  map M1 M2 l := ExtendScalars.map' f l
  map_id' _ := ExtendScalars.map'_id f
  map_comp' _ _ _ := ExtendScalars.map'_comp f
#align category_theory.Module.extend_scalars CategoryTheory.Module.extendScalars

namespace ExtendScalars

open ChangeOfRings

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

@[simp]
protected theorem smul_tmul {M : ModuleCat.{v} R} (s s' : S) (m : M) :
    s • (s'⊗ₜ[R,f]m : (extendScalars f).obj M) = (s * s')⊗ₜ[R,f]m :=
  rfl
#align category_theory.Module.extend_scalars.smul_tmul CategoryTheory.Module.extendScalars.smul_tmul

@[simp]
theorem map_tmul {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M) :
    (extendScalars f).map g (s⊗ₜ[R,f]m) = s⊗ₜ[R,f]g m :=
  rfl
#align category_theory.Module.extend_scalars.map_tmul CategoryTheory.Module.extendScalars.map_tmul

end ExtendScalars

namespace ExtendRestrictScalarsAdj

open ChangeOfRings

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

/--
Given `R`-module X and `S`-module Y and a map `g : (extend_scalars f).obj X ⟶ Y`, i.e. `S`-linear
map `S ⨂ X → Y`, there is a `X ⟶ (restrict_scalars f).obj Y`, i.e. `R`-linear map `X ⟶ Y` by
`x ↦ g (1 ⊗ x)`.
-/
@[simps]
def HomEquiv.toRestrictScalars {X Y} (g : (extendScalars f).obj X ⟶ Y) :
    X ⟶ (restrictScalars f).obj Y
    where
  toFun x := g <| (1 : S)⊗ₜ[R,f]x
  map_add' _ _ := by rw [tmul_add, map_add]
  map_smul' r x := by
    letI : Module R S := Module.compHom S f
    letI : Module R Y := Module.compHom Y f
    rw [RingHom.id_apply, RestrictScalars.smul_def, ← LinearMap.map_smul, tmul_smul]
    congr
#align category_theory.Module.extend_restrict_scalars_adj.hom_equiv.to_restrict_scalars CategoryTheory.Module.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars

/--
Given `R`-module X and `S`-module Y and a map `X ⟶ (restrict_scalars f).obj Y`, i.e `R`-linear map
`X ⟶ Y`, there is a map `(extend_scalars f).obj X ⟶ Y`, i.e  `S`-linear map `S ⨂ X → Y` by
`s ⊗ x ↦ s • g x`.
-/
@[simps]
def HomEquiv.fromExtendScalars {X Y} (g : X ⟶ (restrictScalars f).obj Y) :
    (extendScalars f).obj X ⟶ Y :=
  by
  letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
  refine' ⟨fun z => TensorProduct.lift ⟨fun s => ⟨_, _, _⟩, _, _⟩ z, _, _⟩
  · exact fun x => s • g x
  · intros
    rw [map_add, smul_add]
  · intros
    rw [RingHom.id_apply, smul_comm, ← LinearMap.map_smul]
  · intros
    ext
    simp only [LinearMap.coe_mk, LinearMap.add_apply]
    rw [← add_smul]
  · intros
    ext
    simp only [LinearMap.coe_mk, RingHom.id_apply, LinearMap.smul_apply, RestrictScalars.smul_def,
      smul_eq_mul]
    convert mul_smul _ _ _
  · intros
    rw [map_add]
  · intro r z
    rw [RingHom.id_apply]
    induction' z using TensorProduct.induction_on with x y x y ih1 ih2
    · simp only [smul_zero, map_zero]
    · simp only [LinearMap.coe_mk, extend_scalars.smul_tmul, lift.tmul, ← mul_smul]
    · rw [smul_add, map_add, ih1, ih2, map_add, smul_add]
#align category_theory.Module.extend_restrict_scalars_adj.hom_equiv.from_extend_scalars CategoryTheory.Module.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars

/-- Given `R`-module X and `S`-module Y, `S`-linear linear maps `(extend_scalars f).obj X ⟶ Y`
bijectively correspond to `R`-linear maps `X ⟶ (restrict_scalars f).obj Y`.
-/
@[simps]
def homEquiv {X Y} : ((extendScalars f).obj X ⟶ Y) ≃ (X ⟶ (restrictScalars f).obj Y)
    where
  toFun := HomEquiv.toRestrictScalars f
  invFun := HomEquiv.fromExtendScalars f
  left_inv g := by
    ext z
    induction' z using TensorProduct.induction_on with x s z1 z2 ih1 ih2
    · simp only [map_zero]
    · erw [TensorProduct.lift.tmul]
      simp only [LinearMap.coe_mk]
      change S at x
      erw [← LinearMap.map_smul, extend_scalars.smul_tmul, mul_one x]
    · rw [map_add, map_add, ih1, ih2]
  right_inv g := by
    ext
    rw [hom_equiv.to_restrict_scalars_apply, hom_equiv.from_extend_scalars_apply, lift.tmul,
      LinearMap.coe_mk, LinearMap.coe_mk]
    convert one_smul _ _
#align category_theory.Module.extend_restrict_scalars_adj.hom_equiv CategoryTheory.Module.ExtendRestrictScalarsAdj.homEquiv

/--
For any `R`-module X, there is a natural `R`-linear map from `X` to `X ⨂ S` by sending `x ↦ x ⊗ 1`
-/
@[simps]
def Unit.map {X} : X ⟶ (extendScalars f ⋙ restrictScalars f).obj X
    where
  toFun x := (1 : S)⊗ₜ[R,f]x
  map_add' x x' := by rw [TensorProduct.tmul_add]
  map_smul' r x := by
    letI m1 : Module R S := Module.compHom S f
    tidy
#align category_theory.Module.extend_restrict_scalars_adj.unit.map CategoryTheory.Module.ExtendRestrictScalarsAdj.Unit.map

/--
The natural transformation from identity functor on `R`-module to the composition of extension and
restriction of scalars.
-/
@[simps]
def unit : 𝟭 (ModuleCat R) ⟶ extendScalars f ⋙ restrictScalars f
    where
  app _ := Unit.map f
  naturality' X X' g := by tidy
#align category_theory.Module.extend_restrict_scalars_adj.unit CategoryTheory.Module.ExtendRestrictScalarsAdj.unit

/-- For any `S`-module Y, there is a natural `R`-linear map from `S ⨂ Y` to `Y` by
`s ⊗ y ↦ s • y`
-/
@[simps]
def Counit.map {Y} : (restrictScalars f ⋙ extendScalars f).obj Y ⟶ Y :=
  by
  letI m1 : Module R S := Module.compHom S f
  letI m2 : Module R Y := Module.compHom Y f
  refine' ⟨TensorProduct.lift ⟨fun s : S => ⟨fun y : Y => s • y, smul_add _, _⟩, _, _⟩, _, _⟩
  · intros
    rw [RingHom.id_apply, RestrictScalars.smul_def, ← mul_smul, mul_comm, mul_smul,
      RestrictScalars.smul_def]
  · intros
    ext
    simp only [LinearMap.add_apply, LinearMap.coe_mk, add_smul]
  · intros
    ext
    simpa only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk,
      @RestrictScalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, mul_smul]
  · intros
    rw [map_add]
  · intro s z
    rw [RingHom.id_apply]
    induction' z using TensorProduct.induction_on with x s' z1 z2 ih1 ih2
    · simp only [smul_zero, map_zero]
    · simp only [extend_scalars.smul_tmul, LinearMap.coe_mk, TensorProduct.lift.tmul, mul_smul]
    · rw [smul_add, map_add, map_add, ih1, ih2, smul_add]
#align category_theory.Module.extend_restrict_scalars_adj.counit.map CategoryTheory.Module.ExtendRestrictScalarsAdj.Counit.map

/-- The natural transformation from the composition of restriction and extension of scalars to the
identity functor on `S`-module.
-/
@[simps]
def counit : restrictScalars f ⋙ extendScalars f ⟶ 𝟭 (ModuleCat S)
    where
  app _ := Counit.map f
  naturality' Y Y' g := by
    ext z; induction z using TensorProduct.induction_on
    · simp only [map_zero]
    ·
      simp only [CategoryTheory.Functor.comp_map, ModuleCat.coe_comp, Function.comp_apply,
        extend_scalars.map_tmul, restrict_scalars.map_apply, counit.map_apply, lift.tmul,
        LinearMap.coe_mk, CategoryTheory.Functor.id_map, LinearMap.map_smulₛₗ, RingHom.id_apply]
    · simp only [map_add, *]
#align category_theory.Module.extend_restrict_scalars_adj.counit CategoryTheory.Module.ExtendRestrictScalarsAdj.counit

end ExtendRestrictScalarsAdj

/-- Given commutative rings `R, S` and a ring hom `f : R →+* S`, the extension and restriction of
scalars by `f` are adjoint to each other.
-/
@[simps]
def extendRestrictScalarsAdj {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    extendScalars f ⊣ restrictScalars f
    where
  homEquiv _ _ := ExtendRestrictScalarsAdj.homEquiv f
  Unit := ExtendRestrictScalarsAdj.unit f
  counit := ExtendRestrictScalarsAdj.counit f
  homEquiv_unit X Y g := LinearMap.ext fun x => by simp
  homEquiv_counit X Y g :=
    LinearMap.ext fun x => by
      induction x using TensorProduct.induction_on
      · simp only [map_zero]
      ·
        simp only [extend_restrict_scalars_adj.hom_equiv_symm_apply, LinearMap.coe_mk,
          extend_restrict_scalars_adj.hom_equiv.from_extend_scalars_apply, TensorProduct.lift.tmul,
          extend_restrict_scalars_adj.counit_app, ModuleCat.coe_comp, Function.comp_apply,
          extend_scalars.map_tmul, extend_restrict_scalars_adj.counit.map_apply]
      · simp only [map_add, *]
#align category_theory.Module.extend_restrict_scalars_adj CategoryTheory.Module.extendRestrictScalarsAdj

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    CategoryTheory.IsLeftAdjoint (extendScalars f) :=
  ⟨_, extendRestrictScalarsAdj f⟩

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    CategoryTheory.IsRightAdjoint (restrictScalars f) :=
  ⟨_, extendRestrictScalarsAdj f⟩

end CategoryTheory.Module

