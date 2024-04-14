/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Algebra.Category.ModuleCat.Basic
import LinearAlgebra.TensorProduct.Tower

#align_import algebra.category.Module.change_of_rings from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# Change Of Rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `category_theory.Module.restrict_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`,
  then `restrict_scalars : Module S ⥤ Module R` is defined by `M ↦ M` where `M : S-module` is seen
  as `R-module` by `r • m := f r • m` and `S`-linear map `l : M ⟶ M'` is `R`-linear as well.

* `category_theory.Module.extend_scalars`: given **commutative** rings `R, S` and ring homomorphism
  `f : R ⟶ S`, then `extend_scalars : Module R ⥤ Module S` is defined by `M ↦ S ⨂ M` where the
  module structure is defined by `s • (s' ⊗ m) := (s * s') ⊗ m` and `R`-linear map `l : M ⟶ M'`
  is sent to `S`-linear map `s ⊗ m ↦ s ⊗ l m : S ⨂ M ⟶ S ⨂ M'`.

* `category_theory.Module.coextend_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`
  then `coextend_scalars : Module R ⥤ Module S` is defined by `M ↦ (S →ₗ[R] M)` where `S` is seen as
  `R-module` by restriction of scalars and `l ↦ l ∘ _`.

## Main results

* `category_theory.Module.extend_restrict_scalars_adj`: given commutative rings `R, S` and a ring
  homomorphism `f : R →+* S`, the extension and restriction of scalars by `f` are adjoint functors.
* `category_theory.Module.restrict_coextend_scalars_adj`: given rings `R, S` and a ring homomorphism
  `f : R ⟶ S` then `coextend_scalars f` is the right adjoint of `restrict_scalars f`.

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

#print ModuleCat.RestrictScalars.obj' /-
/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
    `r • m := f r • m` (`module.comp_hom`). This is called restriction of scalars. -/
def ModuleCat.RestrictScalars.obj' : ModuleCat R
    where
  carrier := M
  isModule := Module.compHom M f
#align category_theory.Module.restrict_scalars.obj' ModuleCat.RestrictScalars.obj'
-/

#print ModuleCat.RestrictScalars.map' /-
/-- Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
def ModuleCat.RestrictScalars.map' {M M' : ModuleCat.{v} S} (g : M ⟶ M') :
    ModuleCat.RestrictScalars.obj' f M ⟶ ModuleCat.RestrictScalars.obj' f M' :=
  { g with map_smul' := fun r => g.map_smul (f r) }
#align category_theory.Module.restrict_scalars.map' ModuleCat.RestrictScalars.map'
-/

end RestrictScalars

#print ModuleCat.restrictScalars /-
/-- The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
def ModuleCat.restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat.{v} S ⥤ ModuleCat.{v} R
    where
  obj := ModuleCat.RestrictScalars.obj' f
  map _ _ := ModuleCat.RestrictScalars.map' f
  map_id' _ := LinearMap.ext fun m => rfl
  map_comp' _ _ _ g h := LinearMap.ext fun m => rfl
#align category_theory.Module.restrict_scalars ModuleCat.restrictScalars
-/

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    CategoryTheory.Functor.Faithful (ModuleCat.restrictScalars.{v} f)
    where map_injective' _ _ _ _ h :=
    LinearMap.ext fun x => by simpa only using DFunLike.congr_fun h x

#print ModuleCat.restrictScalars.map_apply /-
@[simp]
theorem ModuleCat.restrictScalars.map_apply {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (f : R →+* S) {M M' : ModuleCat.{v} S} (g : M ⟶ M') (x) :
    (ModuleCat.restrictScalars f).map g x = g x :=
  rfl
#align category_theory.Module.restrict_scalars.map_apply ModuleCat.restrictScalars.map_apply
-/

#print ModuleCat.restrictScalars.smul_def /-
@[simp]
theorem ModuleCat.restrictScalars.smul_def {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (f : R →+* S) {M : ModuleCat.{v} S} (r : R) (m : (ModuleCat.restrictScalars f).obj M) :
    r • m = (f r • m : M) :=
  rfl
#align category_theory.Module.restrict_scalars.smul_def ModuleCat.restrictScalars.smul_def
-/

#print ModuleCat.restrictScalars.smul_def' /-
theorem ModuleCat.restrictScalars.smul_def' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (f : R →+* S) {M : ModuleCat.{v} S} (r : R) (m : M) :
    (r • m : (ModuleCat.restrictScalars f).obj M) = (f r • m : M) :=
  rfl
#align category_theory.Module.restrict_scalars.smul_def' ModuleCat.restrictScalars.smul_def'
-/

#print ModuleCat.sMulCommClass_mk /-
instance (priority := 100) ModuleCat.sMulCommClass_mk {R : Type u₁} {S : Type u₂} [Ring R]
    [CommRing S] (f : R →+* S) (M : Type v) [AddCommGroup M] [Module S M] :
    @SMulCommClass R S M (ModuleCat.RestrictScalars.obj' f (ModuleCat.mk M)).isModule.toSMul _
    where smul_comm r s m := (by simp [← mul_smul, mul_comm] : f r • s • m = s • f r • m)
#align category_theory.Module.smul_comm_class_mk ModuleCat.sMulCommClass_mk
-/

namespace ExtendScalars

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

section Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

-- This notation is necessary because we need to reason about `s ⊗ₜ m` where `s : S` and `m : M`;
-- without this notation, one need to work with `s : (restrict_scalars f).obj ⟨S⟩`.
scoped[ChangeOfRings]
  notation s "⊗ₜ[" R "," f "]" m => @TensorProduct.tmul R _ _ _ _ _ (Module.compHom _ f) _ s m

end Unbundled

open scoped ChangeOfRings

variable (M : ModuleCat.{v} R)

#print ModuleCat.ExtendScalars.obj' /-
/-- Extension of scalars turn an `R`-module into `S`-module by M ↦ S ⨂ M
-/
def ModuleCat.ExtendScalars.obj' : ModuleCat S :=
  ⟨TensorProduct R ((ModuleCat.restrictScalars f).obj ⟨S⟩) M⟩
#align category_theory.Module.extend_scalars.obj' ModuleCat.ExtendScalars.obj'
-/

#print ModuleCat.ExtendScalars.map' /-
/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def ModuleCat.ExtendScalars.map' {M1 M2 : ModuleCat.{v} R} (l : M1 ⟶ M2) :
    ModuleCat.ExtendScalars.obj' f M1 ⟶ ModuleCat.ExtendScalars.obj' f M2 :=
  by-- The "by apply" part makes this require 75% fewer heartbeats to process (#16371).
  apply @LinearMap.baseChange R S M1 M2 _ _ ((algebraMap S _).comp f).toAlgebra _ _ _ _ l
#align category_theory.Module.extend_scalars.map' ModuleCat.ExtendScalars.map'
-/

#print ModuleCat.ExtendScalars.map'_id /-
theorem ModuleCat.ExtendScalars.map'_id {M : ModuleCat.{v} R} :
    ModuleCat.ExtendScalars.map' f (𝟙 M) = 𝟙 _ :=
  LinearMap.ext fun x : ModuleCat.ExtendScalars.obj' f M =>
    by
    dsimp only [map', ModuleCat.id_apply]
    induction' x using TensorProduct.induction_on with _ _ m s ihx ihy
    · simp only [map_zero]
    · rw [LinearMap.baseChange_tmul, ModuleCat.id_apply]
    · rw [map_add, ihx, ihy]
#align category_theory.Module.extend_scalars.map'_id ModuleCat.ExtendScalars.map'_id
-/

#print ModuleCat.ExtendScalars.map'_comp /-
theorem ModuleCat.ExtendScalars.map'_comp {M₁ M₂ M₃ : ModuleCat.{v} R} (l₁₂ : M₁ ⟶ M₂)
    (l₂₃ : M₂ ⟶ M₃) :
    ModuleCat.ExtendScalars.map' f (l₁₂ ≫ l₂₃) =
      ModuleCat.ExtendScalars.map' f l₁₂ ≫ ModuleCat.ExtendScalars.map' f l₂₃ :=
  LinearMap.ext fun x : ModuleCat.ExtendScalars.obj' f M₁ =>
    by
    dsimp only [map']
    induction' x using TensorProduct.induction_on with _ _ x y ihx ihy
    · rfl
    · rfl
    · simp only [map_add, ihx, ihy]
#align category_theory.Module.extend_scalars.map'_comp ModuleCat.ExtendScalars.map'_comp
-/

end ExtendScalars

#print ModuleCat.extendScalars /-
/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def ModuleCat.extendScalars {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    ModuleCat.{v} R ⥤ ModuleCat.{max v u₂} S
    where
  obj M := ModuleCat.ExtendScalars.obj' f M
  map M1 M2 l := ModuleCat.ExtendScalars.map' f l
  map_id' _ := ModuleCat.ExtendScalars.map'_id f
  map_comp' _ _ _ := ModuleCat.ExtendScalars.map'_comp f
#align category_theory.Module.extend_scalars ModuleCat.extendScalars
-/

namespace ExtendScalars

open scoped ChangeOfRings

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

#print ModuleCat.ExtendScalars.smul_tmul /-
@[simp]
protected theorem ModuleCat.ExtendScalars.smul_tmul {M : ModuleCat.{v} R} (s s' : S) (m : M) :
    s • (s'⊗ₜ[R,f]m : (ModuleCat.extendScalars f).obj M) = (s * s')⊗ₜ[R,f]m :=
  rfl
#align category_theory.Module.extend_scalars.smul_tmul ModuleCat.ExtendScalars.smul_tmul
-/

#print ModuleCat.ExtendScalars.map_tmul /-
@[simp]
theorem ModuleCat.ExtendScalars.map_tmul {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M) :
    (ModuleCat.extendScalars f).map g (s⊗ₜ[R,f]m) = s⊗ₜ[R,f]g m :=
  rfl
#align category_theory.Module.extend_scalars.map_tmul ModuleCat.ExtendScalars.map_tmul
-/

end ExtendScalars

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

section Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

-- We use `S'` to denote `S` viewed as `R`-module, via the map `f`.
local notation "S'" => (ModuleCat.restrictScalars f).obj ⟨S⟩

#print ModuleCat.CoextendScalars.hasSMul /-
/-- Given an `R`-module M, consider Hom(S, M) -- the `R`-linear maps between S (as an `R`-module by
 means of restriction of scalars) and M. `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`
 -/
instance ModuleCat.CoextendScalars.hasSMul : SMul S <| S' →ₗ[R] M
    where smul s g :=
    { toFun := fun s' : S => g (s' * s : S)
      map_add' := fun x y : S => by simp [add_mul, map_add]
      map_smul' := fun r (t : S) => by
        rw [RingHom.id_apply, @RestrictScalars.smul_def _ _ _ _ f ⟨S⟩, ← LinearMap.map_smul,
          @RestrictScalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, smul_eq_mul, mul_assoc] }
#align category_theory.Module.coextend_scalars.has_smul ModuleCat.CoextendScalars.hasSMul
-/

#print ModuleCat.CoextendScalars.smul_apply' /-
@[simp]
theorem ModuleCat.CoextendScalars.smul_apply' (s : S) (g : S' →ₗ[R] M) (s' : S) :
    @SMul.smul _ _ (ModuleCat.CoextendScalars.hasSMul f _) s g s' = g (s' * s : S) :=
  rfl
#align category_theory.Module.coextend_scalars.smul_apply' ModuleCat.CoextendScalars.smul_apply'
-/

#print ModuleCat.CoextendScalars.mulAction /-
instance ModuleCat.CoextendScalars.mulAction : MulAction S <| S' →ₗ[R] M :=
  {
    ModuleCat.CoextendScalars.hasSMul f
      _ with
    one_smul := fun g => LinearMap.ext fun s : S => by simp
    hMul_smul := fun (s t : S) g => LinearMap.ext fun x : S => by simp [mul_assoc] }
#align category_theory.Module.coextend_scalars.mul_action ModuleCat.CoextendScalars.mulAction
-/

#print ModuleCat.CoextendScalars.distribMulAction /-
instance ModuleCat.CoextendScalars.distribMulAction : DistribMulAction S <| S' →ₗ[R] M :=
  {
    ModuleCat.CoextendScalars.mulAction f
      _ with
    smul_add := fun s g h => LinearMap.ext fun t : S => by simp
    smul_zero := fun s => LinearMap.ext fun t : S => by simp }
#align category_theory.Module.coextend_scalars.distrib_mul_action ModuleCat.CoextendScalars.distribMulAction
-/

#print ModuleCat.CoextendScalars.isModule /-
/-- `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`, this action defines an `S`-module structure on
Hom(S, M).
 -/
instance ModuleCat.CoextendScalars.isModule : Module S <| S' →ₗ[R] M :=
  {
    ModuleCat.CoextendScalars.distribMulAction f
      _ with
    add_smul := fun s1 s2 g => LinearMap.ext fun x : S => by simp [mul_add]
    zero_smul := fun g => LinearMap.ext fun x : S => by simp }
#align category_theory.Module.coextend_scalars.is_module ModuleCat.CoextendScalars.isModule
-/

end Unbundled

variable (M : ModuleCat.{v} R)

#print ModuleCat.CoextendScalars.obj' /-
/-- If `M` is an `R`-module, then the set of `R`-linear maps `S →ₗ[R] M` is an `S`-module with
scalar multiplication defined by `s • l := x ↦ l (x • s)`-/
def ModuleCat.CoextendScalars.obj' : ModuleCat S :=
  ⟨(ModuleCat.restrictScalars f).obj ⟨S⟩ →ₗ[R] M⟩
#align category_theory.Module.coextend_scalars.obj' ModuleCat.CoextendScalars.obj'
-/

instance : CoeFun (ModuleCat.CoextendScalars.obj' f M) fun g => S → M where coe g := g.toFun

#print ModuleCat.CoextendScalars.map' /-
/-- If `M, M'` are `R`-modules, then any `R`-linear map `g : M ⟶ M'` induces an `S`-linear map
`(S →ₗ[R] M) ⟶ (S →ₗ[R] M')` defined by `h ↦ g ∘ h`-/
@[simps]
def ModuleCat.CoextendScalars.map' {M M' : ModuleCat R} (g : M ⟶ M') :
    ModuleCat.CoextendScalars.obj' f M ⟶ ModuleCat.CoextendScalars.obj' f M'
    where
  toFun h := g.comp h
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' s h := LinearMap.ext fun t : S => by simpa only [smul_apply']
#align category_theory.Module.coextend_scalars.map' ModuleCat.CoextendScalars.map'
-/

end CoextendScalars

#print ModuleCat.coextendScalars /-
/--
For any rings `R, S` and a ring homomorphism `f : R →+* S`, there is a functor from `R`-module to
`S`-module defined by `M ↦ (S →ₗ[R] M)` where `S` is considered as an `R`-module via restriction of
scalars and `g : M ⟶ M'` is sent to `h ↦ g ∘ h`.
-/
def ModuleCat.coextendScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat R ⥤ ModuleCat S
    where
  obj := ModuleCat.CoextendScalars.obj' f
  map _ _ := ModuleCat.CoextendScalars.map' f
  map_id' M := LinearMap.ext fun h => LinearMap.ext fun x => rfl
  map_comp' _ _ _ g h := LinearMap.ext fun h => LinearMap.ext fun x => rfl
#align category_theory.Module.coextend_scalars ModuleCat.coextendScalars
-/

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

instance (M : ModuleCat R) : CoeFun ((ModuleCat.coextendScalars f).obj M) fun g => S → M :=
  (inferInstance : CoeFun (ModuleCat.CoextendScalars.obj' f M) _)

#print ModuleCat.CoextendScalars.smul_apply /-
theorem ModuleCat.CoextendScalars.smul_apply (M : ModuleCat R)
    (g : (ModuleCat.coextendScalars f).obj M) (s s' : S) : (s • g) s' = g (s' * s) :=
  rfl
#align category_theory.Module.coextend_scalars.smul_apply ModuleCat.CoextendScalars.smul_apply
-/

#print ModuleCat.CoextendScalars.map_apply /-
@[simp]
theorem ModuleCat.CoextendScalars.map_apply {M M' : ModuleCat R} (g : M ⟶ M') (x) (s : S) :
    (ModuleCat.coextendScalars f).map g x s = g (x s) :=
  rfl
#align category_theory.Module.coextend_scalars.map_apply ModuleCat.CoextendScalars.map_apply
-/

end CoextendScalars

namespace RestrictionCoextensionAdj

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

#print ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction /-
/-- Given `R`-module X and `S`-module Y, any `g : (restrict_of_scalars f).obj Y ⟶ X`
corresponds to `Y ⟶ (coextend_scalars f).obj X` by sending `y ↦ (s ↦ g (s • y))`
-/
@[simps]
def ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction {X Y}
    (g : (ModuleCat.restrictScalars f).obj Y ⟶ X) : Y ⟶ (ModuleCat.coextendScalars f).obj X
    where
  toFun := fun y : Y =>
    { toFun := fun s : S => g <| (s • y : Y)
      map_add' := fun s1 s2 : S => by simp [add_smul]
      map_smul' := fun r (s : S) => by
        rw [RingHom.id_apply, ← g.map_smul, @RestrictScalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul,
          mul_smul, @RestrictScalars.smul_def _ _ _ _ f Y] }
  map_add' := fun y1 y2 : Y =>
    LinearMap.ext fun s : S => by
      rw [LinearMap.add_apply, LinearMap.coe_mk, LinearMap.coe_mk, LinearMap.coe_mk, smul_add,
        map_add]
  map_smul' s y := LinearMap.ext fun t : S => by simp [mul_smul]
#align category_theory.Module.restriction_coextension_adj.hom_equiv.from_restriction ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction
-/

#print ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction /-
/-- Given `R`-module X and `S`-module Y, any `g : Y ⟶ (coextend_scalars f).obj X`
corresponds to `(restrict_scalars f).obj Y ⟶ X` by `y ↦ g y 1`
-/
@[simps]
def ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction {X Y}
    (g : Y ⟶ (ModuleCat.coextendScalars f).obj X) : (ModuleCat.restrictScalars f).obj Y ⟶ X
    where
  toFun := fun y : Y => (g y).toFun (1 : S)
  map_add' x y := by simp only [g.map_add, LinearMap.toFun_eq_coe, LinearMap.add_apply]
  map_smul' r (y : Y) := by
    rw [LinearMap.toFun_eq_coe, LinearMap.toFun_eq_coe, RingHom.id_apply, ← LinearMap.map_smul,
      RestrictScalars.smul_def f r y, @RestrictScalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, mul_one,
      LinearMap.map_smul, coextend_scalars.smul_apply, one_mul]
#align category_theory.Module.restriction_coextension_adj.hom_equiv.to_restriction ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction
-/

#print ModuleCat.RestrictionCoextensionAdj.unit' /-
/--
The natural transformation from identity functor to the composition of restriction and coextension
of scalars.
-/
@[simps]
protected def ModuleCat.RestrictionCoextensionAdj.unit' :
    𝟭 (ModuleCat S) ⟶ ModuleCat.restrictScalars f ⋙ ModuleCat.coextendScalars f
    where
  app Y :=
    { toFun := fun y : Y =>
        { toFun := fun s : S => (s • y : Y)
          map_add' := fun s s' => add_smul _ _ _
          map_smul' := fun r (s : S) => by
            rw [RingHom.id_apply, @RestrictScalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, mul_smul,
              RestrictScalars.smul_def f] }
      map_add' := fun y1 y2 =>
        LinearMap.ext fun s : S => by
          rw [LinearMap.add_apply, LinearMap.coe_mk, LinearMap.coe_mk, LinearMap.coe_mk, smul_add]
      map_smul' := fun s (y : Y) => LinearMap.ext fun t : S => by simp [mul_smul] }
  naturality' Y Y' g :=
    LinearMap.ext fun y : Y => LinearMap.ext fun s : S => by simp [coextend_scalars.map_apply]
#align category_theory.Module.restriction_coextension_adj.unit' ModuleCat.RestrictionCoextensionAdj.unit'
-/

#print ModuleCat.RestrictionCoextensionAdj.counit' /-
/-- The natural transformation from the composition of coextension and restriction of scalars to
identity functor.
-/
@[simps]
protected def ModuleCat.RestrictionCoextensionAdj.counit' :
    ModuleCat.coextendScalars f ⋙ ModuleCat.restrictScalars f ⟶ 𝟭 (ModuleCat R)
    where
  app X :=
    { toFun := fun g => g.toFun (1 : S)
      map_add' := fun x1 x2 => by simp [LinearMap.toFun_eq_coe]
      map_smul' :=
        fun r (g : (ModuleCat.restrictScalars f).obj ((ModuleCat.coextendScalars f).obj X)) =>
        by
        simp only [LinearMap.toFun_eq_coe, RingHom.id_apply]
        rw [RestrictScalars.smul_def f, coextend_scalars.smul_apply, one_mul, ← LinearMap.map_smul,
          @RestrictScalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, mul_one] }
  naturality' X X' g := LinearMap.ext fun h => by simp [coextend_scalars.map_apply]
#align category_theory.Module.restriction_coextension_adj.counit' ModuleCat.RestrictionCoextensionAdj.counit'
-/

end RestrictionCoextensionAdj

#print ModuleCat.restrictCoextendScalarsAdj /-
/-- Restriction of scalars is left adjoint to coextension of scalars. -/
@[simps]
def ModuleCat.restrictCoextendScalarsAdj {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (f : R →+* S) : ModuleCat.restrictScalars f ⊣ ModuleCat.coextendScalars f
    where
  homEquiv X Y :=
    { toFun := ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction f
      invFun := ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction f
      left_inv := fun g => LinearMap.ext fun x : X => by simp
      right_inv := fun g => LinearMap.ext fun x => LinearMap.ext fun s : S => by simp }
  Unit := ModuleCat.RestrictionCoextensionAdj.unit' f
  counit := ModuleCat.RestrictionCoextensionAdj.counit' f
  homEquiv_unit X Y g := LinearMap.ext fun y => rfl
  homEquiv_counit Y X g := LinearMap.ext fun y : Y => by simp
#align category_theory.Module.restrict_coextend_scalars_adj ModuleCat.restrictCoextendScalarsAdj
-/

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    CategoryTheory.IsLeftAdjoint (ModuleCat.restrictScalars f) :=
  ⟨_, ModuleCat.restrictCoextendScalarsAdj f⟩

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    CategoryTheory.IsRightAdjoint (ModuleCat.coextendScalars f) :=
  ⟨_, ModuleCat.restrictCoextendScalarsAdj f⟩

namespace ExtendRestrictScalarsAdj

open scoped ChangeOfRings

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

#print ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars /-
/--
Given `R`-module X and `S`-module Y and a map `g : (extend_scalars f).obj X ⟶ Y`, i.e. `S`-linear
map `S ⨂ X → Y`, there is a `X ⟶ (restrict_scalars f).obj Y`, i.e. `R`-linear map `X ⟶ Y` by
`x ↦ g (1 ⊗ x)`.
-/
@[simps]
def ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars {X Y}
    (g : (ModuleCat.extendScalars f).obj X ⟶ Y) : X ⟶ (ModuleCat.restrictScalars f).obj Y
    where
  toFun x := g <| (1 : S)⊗ₜ[R,f]x
  map_add' _ _ := by rw [tmul_add, map_add]
  map_smul' r x := by
    letI : Module R S := Module.compHom S f
    letI : Module R Y := Module.compHom Y f
    rw [RingHom.id_apply, RestrictScalars.smul_def, ← LinearMap.map_smul, tmul_smul]
    congr
#align category_theory.Module.extend_restrict_scalars_adj.hom_equiv.to_restrict_scalars ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
-/

#print ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars /-
/--
Given `R`-module X and `S`-module Y and a map `X ⟶ (restrict_scalars f).obj Y`, i.e `R`-linear map
`X ⟶ Y`, there is a map `(extend_scalars f).obj X ⟶ Y`, i.e  `S`-linear map `S ⨂ X → Y` by
`s ⊗ x ↦ s • g x`.
-/
@[simps]
def ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars {X Y}
    (g : X ⟶ (ModuleCat.restrictScalars f).obj Y) : (ModuleCat.extendScalars f).obj X ⟶ Y :=
  by
  letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
  refine' ⟨fun z => TensorProduct.lift ⟨fun s => ⟨_, _, _⟩, _, _⟩ z, _, _⟩
  · exact fun x => s • g x
  · intros; rw [map_add, smul_add]
  · intros; rw [RingHom.id_apply, smul_comm, ← LinearMap.map_smul]
  · intros; ext; simp only [LinearMap.coe_mk, LinearMap.add_apply]; rw [← add_smul]
  · intros; ext
    simp only [LinearMap.coe_mk, RingHom.id_apply, LinearMap.smul_apply, RestrictScalars.smul_def,
      smul_eq_mul]
    convert mul_smul _ _ _
  · intros; rw [map_add]
  · intro r z
    rw [RingHom.id_apply]
    induction' z using TensorProduct.induction_on with x y x y ih1 ih2
    · simp only [smul_zero, map_zero]
    · simp only [LinearMap.coe_mk, extend_scalars.smul_tmul, lift.tmul, ← mul_smul]
    · rw [smul_add, map_add, ih1, ih2, map_add, smul_add]
#align category_theory.Module.extend_restrict_scalars_adj.hom_equiv.from_extend_scalars ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
-/

#print ModuleCat.ExtendRestrictScalarsAdj.homEquiv /-
/-- Given `R`-module X and `S`-module Y, `S`-linear linear maps `(extend_scalars f).obj X ⟶ Y`
bijectively correspond to `R`-linear maps `X ⟶ (restrict_scalars f).obj Y`.
-/
@[simps]
def ModuleCat.ExtendRestrictScalarsAdj.homEquiv {X Y} :
    ((ModuleCat.extendScalars f).obj X ⟶ Y) ≃ (X ⟶ (ModuleCat.restrictScalars f).obj Y)
    where
  toFun := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars f
  invFun := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f
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
#align category_theory.Module.extend_restrict_scalars_adj.hom_equiv ModuleCat.ExtendRestrictScalarsAdj.homEquiv
-/

#print ModuleCat.ExtendRestrictScalarsAdj.Unit.map /-
/--
For any `R`-module X, there is a natural `R`-linear map from `X` to `X ⨂ S` by sending `x ↦ x ⊗ 1`
-/
@[simps]
def ModuleCat.ExtendRestrictScalarsAdj.Unit.map {X} :
    X ⟶ (ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f).obj X
    where
  toFun x := (1 : S)⊗ₜ[R,f]x
  map_add' x x' := by rw [TensorProduct.tmul_add]
  map_smul' r x := by letI m1 : Module R S := Module.compHom S f; tidy
#align category_theory.Module.extend_restrict_scalars_adj.unit.map ModuleCat.ExtendRestrictScalarsAdj.Unit.map
-/

#print ModuleCat.ExtendRestrictScalarsAdj.unit /-
/--
The natural transformation from identity functor on `R`-module to the composition of extension and
restriction of scalars.
-/
@[simps]
def ModuleCat.ExtendRestrictScalarsAdj.unit :
    𝟭 (ModuleCat R) ⟶ ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f
    where
  app _ := ModuleCat.ExtendRestrictScalarsAdj.Unit.map f
  naturality' X X' g := by tidy
#align category_theory.Module.extend_restrict_scalars_adj.unit ModuleCat.ExtendRestrictScalarsAdj.unit
-/

#print ModuleCat.ExtendRestrictScalarsAdj.Counit.map /-
/-- For any `S`-module Y, there is a natural `R`-linear map from `S ⨂ Y` to `Y` by
`s ⊗ y ↦ s • y`
-/
@[simps]
def ModuleCat.ExtendRestrictScalarsAdj.Counit.map {Y} :
    (ModuleCat.restrictScalars f ⋙ ModuleCat.extendScalars f).obj Y ⟶ Y :=
  by
  letI m1 : Module R S := Module.compHom S f
  letI m2 : Module R Y := Module.compHom Y f
  refine' ⟨TensorProduct.lift ⟨fun s : S => ⟨fun y : Y => s • y, smul_add _, _⟩, _, _⟩, _, _⟩
  · intros;
    rw [RingHom.id_apply, RestrictScalars.smul_def, ← mul_smul, mul_comm, mul_smul,
      RestrictScalars.smul_def]
  · intros; ext; simp only [LinearMap.add_apply, LinearMap.coe_mk, add_smul]
  · intros; ext
    simpa only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk,
      @RestrictScalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, mul_smul]
  · intros; rw [map_add]
  · intro s z
    rw [RingHom.id_apply]
    induction' z using TensorProduct.induction_on with x s' z1 z2 ih1 ih2
    · simp only [smul_zero, map_zero]
    · simp only [extend_scalars.smul_tmul, LinearMap.coe_mk, TensorProduct.lift.tmul, mul_smul]
    · rw [smul_add, map_add, map_add, ih1, ih2, smul_add]
#align category_theory.Module.extend_restrict_scalars_adj.counit.map ModuleCat.ExtendRestrictScalarsAdj.Counit.map
-/

#print ModuleCat.ExtendRestrictScalarsAdj.counit /-
/-- The natural transformation from the composition of restriction and extension of scalars to the
identity functor on `S`-module.
-/
@[simps]
def ModuleCat.ExtendRestrictScalarsAdj.counit :
    ModuleCat.restrictScalars f ⋙ ModuleCat.extendScalars f ⟶ 𝟭 (ModuleCat S)
    where
  app _ := ModuleCat.ExtendRestrictScalarsAdj.Counit.map f
  naturality' Y Y' g := by
    ext z; induction z using TensorProduct.induction_on
    · simp only [map_zero]
    ·
      simp only [CategoryTheory.Functor.comp_map, ModuleCat.coe_comp, Function.comp_apply,
        extend_scalars.map_tmul, restrict_scalars.map_apply, counit.map_apply, lift.tmul,
        LinearMap.coe_mk, CategoryTheory.Functor.id_map, LinearMap.map_smulₛₗ, RingHom.id_apply]
    · simp only [map_add, *]
#align category_theory.Module.extend_restrict_scalars_adj.counit ModuleCat.ExtendRestrictScalarsAdj.counit
-/

end ExtendRestrictScalarsAdj

#print ModuleCat.extendRestrictScalarsAdj /-
/-- Given commutative rings `R, S` and a ring hom `f : R →+* S`, the extension and restriction of
scalars by `f` are adjoint to each other.
-/
@[simps]
def ModuleCat.extendRestrictScalarsAdj {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (f : R →+* S) : ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f
    where
  homEquiv _ _ := ModuleCat.ExtendRestrictScalarsAdj.homEquiv f
  Unit := ModuleCat.ExtendRestrictScalarsAdj.unit f
  counit := ModuleCat.ExtendRestrictScalarsAdj.counit f
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
#align category_theory.Module.extend_restrict_scalars_adj ModuleCat.extendRestrictScalarsAdj
-/

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    CategoryTheory.IsLeftAdjoint (ModuleCat.extendScalars f) :=
  ⟨_, ModuleCat.extendRestrictScalarsAdj f⟩

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    CategoryTheory.IsRightAdjoint (ModuleCat.restrictScalars f) :=
  ⟨_, ModuleCat.extendRestrictScalarsAdj f⟩

end CategoryTheory.Module

