/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Nicolò Cavalleri
-/
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.Topology.ContinuousFunction.Ordered
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.UniformSpace.CompactConvergence
import Mathbin.Algebra.Algebra.Subalgebra
import Mathbin.Tactic.FieldSimp

/-!
# Algebraic structures over continuous functions

In this file we define instances of algebraic structures over the type `continuous_map α β`
(denoted `C(α, β)`) of **bundled** continuous maps from `α` to `β`. For example, `C(α, β)`
is a group when `β` is a group, a ring when `β` is a ring, etc.

For each type of algebraic structure, we also define an appropriate subobject of `α → β`
with carrier `{ f : α → β | continuous f }`. For example, when `β` is a group, a subgroup
`continuous_subgroup α β` of `α → β` is constructed with carrier `{ f : α → β | continuous f }`.

Note that, rather than using the derived algebraic structures on these subobjects
(for example, when `β` is a group, the derived group structure on `continuous_subgroup α β`),
one should use `C(α, β)` with the appropriate instance of the structure.
-/


attribute [local elabWithoutExpectedType] Continuous.comp

namespace ContinuousFunctions

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {f g : { f : α → β | Continuous f }}

instance : CoeFun { f : α → β | Continuous f } fun _ => α → β :=
  ⟨Subtype.val⟩

end ContinuousFunctions

namespace ContinuousMap

variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

@[to_additive]
instance hasMul [Mul β] [HasContinuousMul β] : Mul C(α, β) :=
  ⟨fun f g => ⟨f * g, continuous_mul.comp (f.Continuous.prod_mk g.Continuous : _)⟩⟩

@[simp, norm_cast, to_additive]
theorem coe_mul [Mul β] [HasContinuousMul β] (f g : C(α, β)) :
    ((f * g : C(α, β)) : α → β) = (f : α → β) * (g : α → β) :=
  rfl

@[simp, to_additive]
theorem mul_comp [Mul γ] [HasContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
    (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
  rfl

@[to_additive]
instance [One β] : One C(α, β) :=
  ⟨const (1 : β)⟩

@[simp, norm_cast, to_additive]
theorem coe_one [One β] : ((1 : C(α, β)) : α → β) = (1 : α → β) :=
  rfl

@[simp, to_additive]
theorem one_comp [One γ] (g : C(α, β)) : (1 : C(β, γ)).comp g = 1 :=
  rfl

instance hasNsmul [AddMonoidₓ β] [HasContinuousAdd β] : HasScalar ℕ C(α, β) :=
  ⟨fun n f => ⟨n • f, f.Continuous.nsmul n⟩⟩

@[to_additive has_nsmul]
instance hasPow [Monoidₓ β] [HasContinuousMul β] : Pow C(α, β) ℕ :=
  ⟨fun f n => ⟨f ^ n, f.Continuous.pow n⟩⟩

@[norm_cast, to_additive coe_nsmul]
theorem coe_pow [Monoidₓ β] [HasContinuousMul β] (f : C(α, β)) (n : ℕ) : ⇑(f ^ n) = f ^ n :=
  rfl

-- don't make `coe_nsmul` simp as the linter complains it's redundant WRT `coe_smul`
attribute [simp] coe_pow

@[to_additive nsmul_comp]
theorem pow_comp [Monoidₓ γ] [HasContinuousMul γ] (f : C(β, γ)) (n : ℕ) (g : C(α, β)) : (f ^ n).comp g = f.comp g ^ n :=
  rfl

-- don't make `nsmul_comp` simp as the linter complains it's redundant WRT `smul_comp`
attribute [simp] pow_comp

@[to_additive]
instance [Groupₓ β] [TopologicalGroup β] : Inv C(α, β) where
  inv := fun f => ⟨f⁻¹, f.Continuous.inv⟩

@[simp, norm_cast, to_additive]
theorem coe_inv [Groupₓ β] [TopologicalGroup β] (f : C(α, β)) : ⇑f⁻¹ = f⁻¹ :=
  rfl

@[simp, to_additive]
theorem inv_comp [Groupₓ γ] [TopologicalGroup γ] (f : C(β, γ)) (g : C(α, β)) : f⁻¹.comp g = (f.comp g)⁻¹ :=
  rfl

@[to_additive]
instance [Div β] [HasContinuousDiv β] : Div C(α, β) where
  div := fun f g => ⟨f / g, f.Continuous.div' g.Continuous⟩

@[simp, norm_cast, to_additive]
theorem coe_div [Div β] [HasContinuousDiv β] (f g : C(α, β)) : ⇑(f / g) = f / g :=
  rfl

@[simp, to_additive]
theorem div_comp [Div γ] [HasContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β)) : (f / g).comp h = f.comp h / g.comp h :=
  rfl

instance hasZsmul [AddGroupₓ β] [TopologicalAddGroup β] : HasScalar ℤ C(α, β) where
  smul := fun z f => ⟨z • f, f.Continuous.zsmul z⟩

@[to_additive]
instance hasZpow [Groupₓ β] [TopologicalGroup β] : Pow C(α, β) ℤ where
  pow := fun f z => ⟨f ^ z, f.Continuous.zpow z⟩

@[norm_cast, to_additive]
theorem coe_zpow [Groupₓ β] [TopologicalGroup β] (f : C(α, β)) (z : ℤ) : ⇑(f ^ z) = f ^ z :=
  rfl

-- don't make `coe_zsmul` simp as the linter complains it's redundant WRT `coe_smul`
attribute [simp] coe_zpow

@[to_additive]
theorem zpow_comp [Groupₓ γ] [TopologicalGroup γ] (f : C(β, γ)) (z : ℤ) (g : C(α, β)) : (f ^ z).comp g = f.comp g ^ z :=
  rfl

-- don't make `zsmul_comp` simp as the linter complains it's redundant WRT `smul_comp`
attribute [simp] zpow_comp

end ContinuousMap

section GroupStructure

/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/


section Subtype

/-- The `submonoid` of continuous maps `α → β`. -/
@[to_additive "The `add_submonoid` of continuous maps `α → β`. "]
def continuousSubmonoid (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] [Monoidₓ β]
    [HasContinuousMul β] : Submonoid (α → β) where
  Carrier := { f : α → β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' := fun f g fc gc => Continuous.comp HasContinuousMul.continuous_mul (Continuous.prod_mk fc gc : _)

/-- The subgroup of continuous maps `α → β`. -/
@[to_additive "The `add_subgroup` of continuous maps `α → β`. "]
def continuousSubgroup (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] [Groupₓ β]
    [TopologicalGroup β] : Subgroup (α → β) :=
  { continuousSubmonoid α β with inv_mem' := fun f fc => Continuous.comp (@TopologicalGroup.continuous_inv β _ _ _) fc }

end Subtype

namespace ContinuousMap

@[to_additive]
instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Semigroupₓ β] [HasContinuousMul β] :
    Semigroupₓ C(α, β) :=
  coe_injective.Semigroup _ coe_mul

@[to_additive]
instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommSemigroupₓ β] [HasContinuousMul β] :
    CommSemigroupₓ C(α, β) :=
  coe_injective.CommSemigroup _ coe_mul

@[to_additive]
instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [MulOneClassₓ β] [HasContinuousMul β] :
    MulOneClassₓ C(α, β) :=
  coe_injective.MulOneClass _ coe_one coe_mul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [MulZeroClassₓ β] [HasContinuousMul β] :
    MulZeroClassₓ C(α, β) :=
  coe_injective.MulZeroClass _ coe_zero coe_mul

@[to_additive]
instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Monoidₓ β] [HasContinuousMul β] :
    Monoidₓ C(α, β) :=
  coe_injective.monoidPow _ coe_one coe_mul coe_pow

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [MonoidWithZeroₓ β] [HasContinuousMul β] :
    MonoidWithZeroₓ C(α, β) :=
  { ContinuousMap.monoid, ContinuousMap.mulZeroClass with }

@[to_additive]
instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommMonoidₓ β] [HasContinuousMul β] :
    CommMonoidₓ C(α, β) :=
  { ContinuousMap.commSemigroup, ContinuousMap.monoid with }

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommMonoidWithZero β]
    [HasContinuousMul β] : CommMonoidWithZero C(α, β) :=
  { ContinuousMap.commMonoid, ContinuousMap.monoidWithZero with }

/-- Coercion to a function as an `monoid_hom`. Similar to `monoid_hom.coe_fn`. -/
@[to_additive "Coercion to a function as an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.", simps]
def coeFnMonoidHom {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Monoidₓ β]
    [HasContinuousMul β] : C(α, β) →* α → β where
  toFun := coeFn
  map_one' := coe_one
  map_mul' := coe_mul

/-- Composition on the left by a (continuous) homomorphism of topological monoids, as a
`monoid_hom`. Similar to `monoid_hom.comp_left`. -/
@[to_additive
      "Composition on the left by a (continuous) homomorphism of topological `add_monoid`s,\nas an `add_monoid_hom`. Similar to `add_monoid_hom.comp_left`.",
  simps]
protected def _root_.monoid_hom.comp_left_continuous (α : Type _) {β : Type _} {γ : Type _} [TopologicalSpace α]
    [TopologicalSpace β] [Monoidₓ β] [HasContinuousMul β] [TopologicalSpace γ] [Monoidₓ γ] [HasContinuousMul γ]
    (g : β →* γ) (hg : Continuous g) : C(α, β) →* C(α, γ) where
  toFun := fun f => (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun x => g.map_one
  map_mul' := fun f₁ f₂ => ext fun x => g.map_mul _ _

/-- Composition on the right as a `monoid_hom`. Similar to `monoid_hom.comp_hom'`. -/
@[to_additive "Composition on the right as an `add_monoid_hom`. Similar to\n`add_monoid_hom.comp_hom'`.", simps]
def compMonoidHom' {α : Type _} {β : Type _} {γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    [MulOneClassₓ γ] [HasContinuousMul γ] (g : C(α, β)) : C(β, γ) →* C(α, γ) where
  toFun := fun f => f.comp g
  map_one' := one_comp g
  map_mul' := fun f₁ f₂ => mul_comp f₁ f₂ g

open_locale BigOperators

@[simp, to_additive]
theorem coe_prod {α : Type _} {β : Type _} [CommMonoidₓ β] [TopologicalSpace α] [TopologicalSpace β]
    [HasContinuousMul β] {ι : Type _} (s : Finset ι) (f : ι → C(α, β)) : ⇑(∏ i in s, f i) = ∏ i in s, (f i : α → β) :=
  (coeFnMonoidHom : C(α, β) →* _).map_prod f s

@[to_additive]
theorem prod_apply {α : Type _} {β : Type _} [CommMonoidₓ β] [TopologicalSpace α] [TopologicalSpace β]
    [HasContinuousMul β] {ι : Type _} (s : Finset ι) (f : ι → C(α, β)) (a : α) : (∏ i in s, f i) a = ∏ i in s, f i a :=
  by
  simp

@[to_additive]
instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Groupₓ β] [TopologicalGroup β] :
    Groupₓ C(α, β) :=
  coe_injective.groupPow _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommGroupₓ β] [TopologicalGroup β] :
    CommGroupₓ C(α, β) :=
  { ContinuousMap.group, ContinuousMap.commMonoid with }

@[to_additive]
instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommGroupₓ β] [TopologicalGroup β] :
    TopologicalGroup C(α, β) where
  continuous_mul := by
    let this' : UniformSpace β := TopologicalGroup.toUniformSpace β
    have : UniformGroup β := topological_group_is_uniform
    rw [continuous_iff_continuous_at]
    rintro ⟨f, g⟩
    rw [ContinuousAt, tendsto_iff_forall_compact_tendsto_uniformly_on, nhds_prod_eq]
    exact fun K hK =>
      ((tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK).Prod
            (tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK)).comp'
        uniform_continuous_mul
  continuous_inv := by
    let this' : UniformSpace β := TopologicalGroup.toUniformSpace β
    have : UniformGroup β := topological_group_is_uniform
    rw [continuous_iff_continuous_at]
    intro f
    rw [ContinuousAt, tendsto_iff_forall_compact_tendsto_uniformly_on]
    exact fun K hK =>
      (tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK).comp' uniform_continuous_inv

end ContinuousMap

end GroupStructure

section RingStructure

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological ring `R` inherit
the structure of a ring.
-/


section Subtype

/-- The subsemiring of continuous maps `α → β`. -/
def continuousSubsemiring (α : Type _) (R : Type _) [TopologicalSpace α] [TopologicalSpace R] [Semiringₓ R]
    [TopologicalRing R] : Subsemiring (α → R) :=
  { continuousAddSubmonoid α R, continuousSubmonoid α R with }

/-- The subring of continuous maps `α → β`. -/
def continuousSubring (α : Type _) (R : Type _) [TopologicalSpace α] [TopologicalSpace R] [Ringₓ R]
    [TopologicalRing R] : Subring (α → R) :=
  { continuousSubsemiring α R, continuousAddSubgroup α R with }

end Subtype

namespace ContinuousMap

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Semiringₓ β] [TopologicalRing β] :
    Semiringₓ C(α, β) :=
  { ContinuousMap.addCommMonoid, ContinuousMap.monoidWithZero with
    left_distrib := fun a b c => by
      ext <;> exact left_distrib _ _ _,
    right_distrib := fun a b c => by
      ext <;> exact right_distrib _ _ _ }

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Ringₓ β] [TopologicalRing β] :
    Ringₓ C(α, β) :=
  { ContinuousMap.semiring, ContinuousMap.addCommGroup with }

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommSemiringₓ β] [TopologicalRing β] :
    CommSemiringₓ C(α, β) :=
  { ContinuousMap.semiring, ContinuousMap.commMonoid with }

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommRingₓ β] [TopologicalRing β] :
    CommRingₓ C(α, β) :=
  { ContinuousMap.commSemiring, ContinuousMap.ring with }

/-- Composition on the left by a (continuous) homomorphism of topological rings, as a `ring_hom`.
Similar to `ring_hom.comp_left`. -/
@[simps]
protected def _root_.ring_hom.comp_left_continuous (α : Type _) {β : Type _} {γ : Type _} [TopologicalSpace α]
    [TopologicalSpace β] [Semiringₓ β] [TopologicalRing β] [TopologicalSpace γ] [Semiringₓ γ] [TopologicalRing γ]
    (g : β →+* γ) (hg : Continuous g) : C(α, β) →+* C(α, γ) :=
  { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }

/-- Coercion to a function as a `ring_hom`. -/
@[simps]
def coeFnRingHom {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Ringₓ β] [TopologicalRing β] :
    C(α, β) →+* α → β :=
  { (coeFnMonoidHom : C(α, β) →* _), (coeFnAddMonoidHom : C(α, β) →+ _) with toFun := coeFn }

end ContinuousMap

end RingStructure

attribute [local ext] Subtype.eq

section ModuleStructure

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological module `M` over a
topological semiring `R` inherit the structure of a module.
-/


section Subtype

variable (α : Type _) [TopologicalSpace α]

variable (R : Type _) [Semiringₓ R]

variable (M : Type _) [TopologicalSpace M] [AddCommGroupₓ M]

variable [Module R M] [HasContinuousConstSmul R M] [TopologicalAddGroup M]

/-- The `R`-submodule of continuous maps `α → M`. -/
def continuousSubmodule : Submodule R (α → M) :=
  { continuousAddSubgroup α M with Carrier := { f : α → M | Continuous f }, smul_mem' := fun c f hf => hf.const_smul c }

end Subtype

namespace ContinuousMap

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {R R₁ : Type _} {M : Type _} [TopologicalSpace M]
  {M₂ : Type _} [TopologicalSpace M₂]

@[to_additive ContinuousMap.hasVadd]
instance [HasScalar R M] [HasContinuousConstSmul R M] : HasScalar R C(α, M) :=
  ⟨fun r f => ⟨r • f, f.Continuous.const_smul r⟩⟩

@[simp, to_additive, norm_cast]
theorem coe_smul [HasScalar R M] [HasContinuousConstSmul R M] (c : R) (f : C(α, M)) : ⇑(c • f) = c • f :=
  rfl

@[to_additive]
theorem smul_apply [HasScalar R M] [HasContinuousConstSmul R M] (c : R) (f : C(α, M)) (a : α) : (c • f) a = c • f a :=
  rfl

@[simp, to_additive]
theorem smul_comp [HasScalar R M] [HasContinuousConstSmul R M] (r : R) (f : C(β, M)) (g : C(α, β)) :
    (r • f).comp g = r • f.comp g :=
  rfl

@[to_additive]
instance [HasScalar R M] [HasContinuousConstSmul R M] [HasScalar R₁ M] [HasContinuousConstSmul R₁ M]
    [SmulCommClass R R₁ M] : SmulCommClass R R₁ C(α, M) where
  smul_comm := fun _ _ _ => ext fun _ => smul_comm _ _ _

instance [HasScalar R M] [HasContinuousConstSmul R M] [HasScalar R₁ M] [HasContinuousConstSmul R₁ M] [HasScalar R R₁]
    [IsScalarTower R R₁ M] : IsScalarTower R R₁ C(α, M) where
  smul_assoc := fun _ _ _ => ext fun _ => smul_assoc _ _ _

instance [HasScalar R M] [HasScalar Rᵐᵒᵖ M] [HasContinuousConstSmul R M] [IsCentralScalar R M] :
    IsCentralScalar R C(α, M) where
  op_smul_eq_smul := fun _ _ => ext fun _ => op_smul_eq_smul _ _

instance [Monoidₓ R] [MulAction R M] [HasContinuousConstSmul R M] : MulAction R C(α, M) :=
  Function.Injective.mulAction _ coe_injective coe_smul

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] [HasContinuousAdd M] [HasContinuousConstSmul R M] :
    DistribMulAction R C(α, M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]

variable [HasContinuousAdd M] [Module R M] [HasContinuousConstSmul R M]

variable [HasContinuousAdd M₂] [Module R M₂] [HasContinuousConstSmul R M₂]

instance module : Module R C(α, M) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul

variable (R)

/-- Composition on the left by a continuous linear map, as a `linear_map`.
Similar to `linear_map.comp_left`. -/
@[simps]
protected def _root_.continuous_linear_map.comp_left_continuous (α : Type _) [TopologicalSpace α] (g : M →L[R] M₂) :
    C(α, M) →ₗ[R] C(α, M₂) :=
  { g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.Continuous with
    map_smul' := fun c f => ext fun x => g.map_smul' c _ }

/-- Coercion to a function as a `linear_map`. -/
@[simps]
def coeFnLinearMap : C(α, M) →ₗ[R] α → M :=
  { (coeFnAddMonoidHom : C(α, M) →+ _) with toFun := coeFn, map_smul' := coe_smul }

end ContinuousMap

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `has_continuous_smul` and a `topological_ring`.-/


section Subtype

variable {α : Type _} [TopologicalSpace α] {R : Type _} [CommSemiringₓ R] {A : Type _} [TopologicalSpace A]
  [Semiringₓ A] [Algebra R A] [TopologicalRing A]

/-- The `R`-subalgebra of continuous maps `α → A`. -/
def continuousSubalgebra : Subalgebra R (α → A) :=
  { continuousSubsemiring α A with Carrier := { f : α → A | Continuous f },
    algebra_map_mem' := fun r => (continuous_const : Continuous fun x : α => algebraMap R A r) }

end Subtype

section ContinuousMap

variable {α : Type _} [TopologicalSpace α] {R : Type _} [CommSemiringₓ R] {A : Type _} [TopologicalSpace A]
  [Semiringₓ A] [Algebra R A] [TopologicalRing A] {A₂ : Type _} [TopologicalSpace A₂] [Semiringₓ A₂] [Algebra R A₂]
  [TopologicalRing A₂]

/-- Continuous constant functions as a `ring_hom`. -/
def ContinuousMap.c : R →+* C(α, A) where
  toFun := fun c : R => ⟨fun x : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by
    ext x <;> exact (algebraMap R A).map_one
  map_mul' := fun c₁ c₂ => by
    ext x <;> exact (algebraMap R A).map_mul _ _
  map_zero' := by
    ext x <;> exact (algebraMap R A).map_zero
  map_add' := fun c₁ c₂ => by
    ext x <;> exact (algebraMap R A).map_add _ _

@[simp]
theorem ContinuousMap.C_apply (r : R) (a : α) : ContinuousMap.c r a = algebraMap R A r :=
  rfl

variable [HasContinuousConstSmul R A] [HasContinuousConstSmul R A₂]

instance ContinuousMap.algebra : Algebra R C(α, A) where
  toRingHom := ContinuousMap.c
  commutes' := fun c f => by
    ext x <;> exact Algebra.commutes' _ _
  smul_def' := fun c f => by
    ext x <;> exact Algebra.smul_def' _ _

variable (R)

/-- Composition on the left by a (continuous) homomorphism of topological `R`-algebras, as an
`alg_hom`. Similar to `alg_hom.comp_left`. -/
@[simps]
protected def AlgHom.compLeftContinuous {α : Type _} [TopologicalSpace α] (g : A →ₐ[R] A₂) (hg : Continuous g) :
    C(α, A) →ₐ[R] C(α, A₂) :=
  { g.toRingHom.compLeftContinuous α hg with commutes' := fun c => ContinuousMap.ext fun _ => g.commutes' _ }

/-- Coercion to a function as an `alg_hom`. -/
@[simps]
def ContinuousMap.coeFnAlgHom : C(α, A) →ₐ[R] α → A where
  toFun := coeFn
  commutes' := fun r => rfl
  -- `..(continuous_map.coe_fn_ring_hom : C(α, A) →+* _)` times out for some reason
  map_zero' := ContinuousMap.coe_zero
  map_one' := ContinuousMap.coe_one
  map_add' := ContinuousMap.coe_add
  map_mul' := ContinuousMap.coe_mul

variable {R}

/-- A version of `separates_points` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
abbrev Subalgebra.SeparatesPoints (s : Subalgebra R C(α, A)) : Prop :=
  Set.SeparatesPoints ((fun f : C(α, A) => (f : α → A)) '' (s : Set C(α, A)))

theorem Subalgebra.separates_points_monotone : Monotone fun s : Subalgebra R C(α, A) => s.SeparatesPoints :=
  fun s s' r h x y n => by
  obtain ⟨f, m, w⟩ := h n
  rcases m with ⟨f, ⟨m, rfl⟩⟩
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩

@[simp]
theorem algebra_map_apply (k : R) (a : α) : algebraMap R C(α, A) k a = k • 1 := by
  rw [Algebra.algebra_map_eq_smul_one]
  rfl

variable {𝕜 : Type _} [TopologicalSpace 𝕜]

/-- A set of continuous maps "separates points strongly"
if for each pair of distinct points there is a function with specified values on them.

We give a slightly unusual formulation, where the specified values are given by some
function `v`, and we ask `f x = v x ∧ f y = v y`. This avoids needing a hypothesis `x ≠ y`.

In fact, this definition would work perfectly well for a set of non-continuous functions,
but as the only current use case is in the Stone-Weierstrass theorem,
writing it this way avoids having to deal with casts inside the set.
(This may need to change if we do Stone-Weierstrass on non-compact spaces,
where the functions would be continuous functions vanishing at infinity.)
-/
def Set.SeparatesPointsStrongly (s : Set C(α, 𝕜)) : Prop :=
  ∀ v : α → 𝕜 x y : α, ∃ f : s, (f x : 𝕜) = v x ∧ f y = v y

variable [Field 𝕜] [TopologicalRing 𝕜]

/-- Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f x = b`.
-/
theorem Subalgebra.SeparatesPoints.strongly {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints) :
    (s : Set C(α, 𝕜)).SeparatesPointsStrongly := fun v x y => by
  by_cases' n : x = y
  · subst n
    use (v x • 1 : C(α, 𝕜))
    · apply s.smul_mem
      apply s.one_mem
      
    · simp [coe_fn_coe_base']
      
    
  obtain ⟨f, ⟨f, ⟨m, rfl⟩⟩, w⟩ := h n
  replace w : f x - f y ≠ 0 := sub_ne_zero_of_ne w
  let a := v x
  let b := v y
  let f' := ((b - a) * (f x - f y)⁻¹) • (ContinuousMap.c (f x) - f) + ContinuousMap.c a
  refine' ⟨⟨f', _⟩, _, _⟩
  · simp only [f', SetLike.mem_coe, Subalgebra.mem_to_submodule]
    -- TODO should there be a tactic for this?
    -- We could add an attribute `@[subobject_mem]`, and a tactic
    -- ``def subobject_mem := `[solve_by_elim with subobject_mem { max_depth := 10 }]``
    solve_by_elim(config := { max_depth := 6 }) [Subalgebra.add_mem, Subalgebra.smul_mem, Subalgebra.sub_mem,
      Subalgebra.algebra_map_mem]
    
  · simp [f', coe_fn_coe_base']
    
  · simp [f', coe_fn_coe_base', inv_mul_cancel_right₀ w]
    

end ContinuousMap

-- TODO[gh-6025]: make this an instance once safe to do so
theorem ContinuousMap.subsingleton_subalgebra (α : Type _) [TopologicalSpace α] (R : Type _) [CommSemiringₓ R]
    [TopologicalSpace R] [TopologicalRing R] [Subsingleton α] : Subsingleton (Subalgebra R C(α, R)) := by
  fconstructor
  intro s₁ s₂
  by_cases' n : Nonempty α
  · obtain ⟨x⟩ := n
    ext f
    have h : f = algebraMap R C(α, R) (f x) := by
      ext x'
      simp only [mul_oneₓ, Algebra.id.smul_eq_mul, algebra_map_apply]
      congr
    rw [h]
    simp only [Subalgebra.algebra_map_mem]
    
  · ext f
    have h : f = 0 := by
      ext x'
      exact False.elim (n ⟨x'⟩)
    subst h
    simp only [Subalgebra.zero_mem]
    

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `R`. -/


namespace ContinuousMap

instance hasScalar' {α : Type _} [TopologicalSpace α] {R : Type _} [Semiringₓ R] [TopologicalSpace R] {M : Type _}
    [TopologicalSpace M] [AddCommMonoidₓ M] [Module R M] [HasContinuousSmul R M] : HasScalar C(α, R) C(α, M) :=
  ⟨fun f g => ⟨fun x => f x • g x, Continuous.smul f.2 g.2⟩⟩

instance module' {α : Type _} [TopologicalSpace α] (R : Type _) [Ringₓ R] [TopologicalSpace R] [TopologicalRing R]
    (M : Type _) [TopologicalSpace M] [AddCommMonoidₓ M] [HasContinuousAdd M] [Module R M] [HasContinuousSmul R M] :
    Module C(α, R) C(α, M) where
  smul := (· • ·)
  smul_add := fun c f g => by
    ext x <;> exact smul_add (c x) (f x) (g x)
  add_smul := fun c₁ c₂ f => by
    ext x <;> exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul := fun c₁ c₂ f => by
    ext x <;> exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul := fun f => by
    ext x <;> exact one_smul R (f x)
  zero_smul := fun f => by
    ext x <;> exact zero_smul _ _
  smul_zero := fun r => by
    ext x <;> exact smul_zero _

end ContinuousMap

end ModuleOverContinuousFunctions

/-!
We now provide formulas for `f ⊓ g` and `f ⊔ g`, where `f g : C(α, β)`,
in terms of `continuous_map.abs`.
-/


section

variable {R : Type _} [LinearOrderedField R]

-- TODO:
-- This lemma (and the next) could go all the way back in `algebra.order.field`,
-- except that it is tedious to prove without tactics.
-- Rather than stranding it at some intermediate location,
-- it's here, immediately prior to the point of use.
theorem min_eq_half_add_sub_abs_sub {x y : R} : min x y = 2⁻¹ * (x + y - abs (x - y)) := by
  cases' le_totalₓ x y with h h <;> field_simp [h, abs_of_nonneg, abs_of_nonpos, mul_two] <;> abel

theorem max_eq_half_add_add_abs_sub {x y : R} : max x y = 2⁻¹ * (x + y + abs (x - y)) := by
  cases' le_totalₓ x y with h h <;> field_simp [h, abs_of_nonneg, abs_of_nonpos, mul_two] <;> abel

end

namespace ContinuousMap

section Lattice

variable {α : Type _} [TopologicalSpace α]

variable {β : Type _} [LinearOrderedField β] [TopologicalSpace β] [OrderTopology β] [TopologicalRing β]

theorem inf_eq (f g : C(α, β)) : f⊓g = (2⁻¹ : β) • (f + g - abs (f - g)) :=
  ext fun x => by
    simpa using min_eq_half_add_sub_abs_sub

-- Not sure why this is grosser than `inf_eq`:
theorem sup_eq (f g : C(α, β)) : f⊔g = (2⁻¹ : β) • (f + g + abs (f - g)) :=
  ext fun x => by
    simpa [mul_addₓ] using @max_eq_half_add_add_abs_sub _ _ (f x) (g x)

end Lattice

end ContinuousMap

