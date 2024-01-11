/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Topology.ContinuousFunction.Bounded
import Topology.ContinuousFunction.CocompactMap

#align_import topology.continuous_function.zero_at_infty from "leanprover-community/mathlib"@"2a0ce625dbb0ffbc7d1316597de0b25c1ec75303"

/-!
# Continuous functions vanishing at infinity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The type of continuous functions vanishing at infinity. When the domain is compact
`C(α, β) ≃ C₀(α, β)` via the identity map. When the codomain is a metric space, every continuous
map which vanishes at infinity is a bounded continuous function. When the domain is a locally
compact space, this type has nice properties.

## TODO

* Create more intances of algebraic structures (e.g., `non_unital_semiring`) once the necessary
  type classes (e.g., `topological_ring`) are sufficiently generalized.
* Relate the unitization of `C₀(α, β)` to the Alexandroff compactification.
-/


universe u v w

variable {F : Type _} {α : Type u} {β : Type v} {γ : Type w} [TopologicalSpace α]

open scoped BoundedContinuousFunction Topology

open Filter Metric

#print ZeroAtInftyContinuousMap /-
/-- `C₀(α, β)` is the type of continuous functions `α → β` which vanish at infinity from a
topological space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : C₀(α, β))`,
you should parametrize over `(F : Type*) [zero_at_infty_continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `zero_at_infty_continuous_map_class`. -/
structure ZeroAtInftyContinuousMap (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] extends ContinuousMap α β : Type max u v where
  zero_at_infty' : Tendsto to_fun (cocompact α) (𝓝 0)
#align zero_at_infty_continuous_map ZeroAtInftyContinuousMap
-/

scoped[ZeroAtInfty] notation (priority := 2000) "C₀(" α ", " β ")" => ZeroAtInftyContinuousMap α β

scoped[ZeroAtInfty] notation α " →C₀ " β => ZeroAtInftyContinuousMap α β

section

#print ZeroAtInftyContinuousMapClass /-
/-- `zero_at_infty_continuous_map_class F α β` states that `F` is a type of continuous maps which
vanish at infinity.

You should also extend this typeclass when you extend `zero_at_infty_continuous_map`. -/
class ZeroAtInftyContinuousMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α]
    [Zero β] [TopologicalSpace β] extends ContinuousMapClass F α β where
  zero_at_infty (f : F) : Tendsto f (cocompact α) (𝓝 0)
#align zero_at_infty_continuous_map_class ZeroAtInftyContinuousMapClass
-/

end

export ZeroAtInftyContinuousMapClass (zero_at_infty)

namespace ZeroAtInftyContinuousMap

section Basics

variable [TopologicalSpace β] [Zero β] [ZeroAtInftyContinuousMapClass F α β]

instance : ZeroAtInftyContinuousMapClass C₀(α, β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
  map_continuous f := f.continuous_toFun
  zero_at_infty f := f.zero_at_infty'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun C₀(α, β) fun _ => α → β :=
  FunLike.hasCoeToFun

instance : CoeTC F C₀(α, β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      zero_at_infty' := zero_at_infty f }⟩

#print ZeroAtInftyContinuousMap.coe_toContinuousMap /-
@[simp]
theorem coe_toContinuousMap (f : C₀(α, β)) : (f.toContinuousMap : α → β) = f :=
  rfl
#align zero_at_infty_continuous_map.coe_to_continuous_fun ZeroAtInftyContinuousMap.coe_toContinuousMap
-/

#print ZeroAtInftyContinuousMap.ext /-
@[ext]
theorem ext {f g : C₀(α, β)} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align zero_at_infty_continuous_map.ext ZeroAtInftyContinuousMap.ext
-/

#print ZeroAtInftyContinuousMap.copy /-
/-- Copy of a `zero_at_infinity_continuous_map` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : C₀(α, β)) (f' : α → β) (h : f' = f) : C₀(α, β)
    where
  toFun := f'
  continuous_toFun := by rw [h]; exact f.continuous_to_fun
  zero_at_infty' := by simp_rw [h]; exact f.zero_at_infty'
#align zero_at_infty_continuous_map.copy ZeroAtInftyContinuousMap.copy
-/

#print ZeroAtInftyContinuousMap.coe_copy /-
@[simp]
theorem coe_copy (f : C₀(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align zero_at_infty_continuous_map.coe_copy ZeroAtInftyContinuousMap.coe_copy
-/

#print ZeroAtInftyContinuousMap.copy_eq /-
theorem copy_eq (f : C₀(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align zero_at_infty_continuous_map.copy_eq ZeroAtInftyContinuousMap.copy_eq
-/

#print ZeroAtInftyContinuousMap.eq_of_empty /-
theorem eq_of_empty [IsEmpty α] (f g : C₀(α, β)) : f = g :=
  ext <| IsEmpty.elim ‹_›
#align zero_at_infty_continuous_map.eq_of_empty ZeroAtInftyContinuousMap.eq_of_empty
-/

#print ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty /-
/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. -/
@[simps]
def ContinuousMap.liftZeroAtInfty [CompactSpace α] : C(α, β) ≃ C₀(α, β)
    where
  toFun f :=
    { toFun := f
      continuous_toFun := f.Continuous
      zero_at_infty' := by simp }
  invFun f := f
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
#align zero_at_infty_continuous_map.continuous_map.lift_zero_at_infty ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
-/

#print ZeroAtInftyContinuousMap.zeroAtInftyContinuousMapClass.ofCompact /-
/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. This is not an instance to avoid type class loops. -/
@[simps]
def zeroAtInftyContinuousMapClass.ofCompact {G : Type _} [ContinuousMapClass G α β]
    [CompactSpace α] : ZeroAtInftyContinuousMapClass G α β
    where
  coe g := g
  coe_injective' f g h := FunLike.coe_fn_eq.mp h
  map_continuous := map_continuous
  zero_at_infty := by simp
#align zero_at_infty_continuous_map.zero_at_infty_continuous_map_class.of_compact ZeroAtInftyContinuousMap.zeroAtInftyContinuousMapClass.ofCompact
-/

end Basics

/-! ### Algebraic structure

Whenever `β` has suitable algebraic structure and a compatible topological structure, then
`C₀(α, β)` inherits a corresponding algebraic structure. The primary exception to this is that
`C₀(α, β)` will not have a multiplicative identity.
-/


section AlgebraicStructure

variable [TopologicalSpace β] (x : α)

instance [Zero β] : Zero C₀(α, β) :=
  ⟨⟨0, tendsto_const_nhds⟩⟩

instance [Zero β] : Inhabited C₀(α, β) :=
  ⟨0⟩

#print ZeroAtInftyContinuousMap.coe_zero /-
@[simp]
theorem coe_zero [Zero β] : ⇑(0 : C₀(α, β)) = 0 :=
  rfl
#align zero_at_infty_continuous_map.coe_zero ZeroAtInftyContinuousMap.coe_zero
-/

#print ZeroAtInftyContinuousMap.zero_apply /-
theorem zero_apply [Zero β] : (0 : C₀(α, β)) x = 0 :=
  rfl
#align zero_at_infty_continuous_map.zero_apply ZeroAtInftyContinuousMap.zero_apply
-/

instance [MulZeroClass β] [ContinuousMul β] : Mul C₀(α, β) :=
  ⟨fun f g =>
    ⟨f * g, by simpa only [MulZeroClass.mul_zero] using (zero_at_infty f).mul (zero_at_infty g)⟩⟩

#print ZeroAtInftyContinuousMap.coe_mul /-
@[simp]
theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : ⇑(f * g) = f * g :=
  rfl
#align zero_at_infty_continuous_map.coe_mul ZeroAtInftyContinuousMap.coe_mul
-/

#print ZeroAtInftyContinuousMap.mul_apply /-
theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : (f * g) x = f x * g x :=
  rfl
#align zero_at_infty_continuous_map.mul_apply ZeroAtInftyContinuousMap.mul_apply
-/

instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C₀(α, β) :=
  FunLike.coe_injective.MulZeroClass _ coe_zero coe_mul

instance [SemigroupWithZero β] [ContinuousMul β] : SemigroupWithZero C₀(α, β) :=
  FunLike.coe_injective.SemigroupWithZero _ coe_zero coe_mul

instance [AddZeroClass β] [ContinuousAdd β] : Add C₀(α, β) :=
  ⟨fun f g => ⟨f + g, by simpa only [add_zero] using (zero_at_infty f).add (zero_at_infty g)⟩⟩

#print ZeroAtInftyContinuousMap.coe_add /-
@[simp]
theorem coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : ⇑(f + g) = f + g :=
  rfl
#align zero_at_infty_continuous_map.coe_add ZeroAtInftyContinuousMap.coe_add
-/

#print ZeroAtInftyContinuousMap.add_apply /-
theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : (f + g) x = f x + g x :=
  rfl
#align zero_at_infty_continuous_map.add_apply ZeroAtInftyContinuousMap.add_apply
-/

instance [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C₀(α, β) :=
  FunLike.coe_injective.AddZeroClass _ coe_zero coe_add

section AddMonoid

variable [AddMonoid β] [ContinuousAdd β] (f g : C₀(α, β))

#print ZeroAtInftyContinuousMap.coe_nsmulRec /-
@[simp]
theorem coe_nsmulRec : ∀ n, ⇑(nsmulRec n f) = n • f
  | 0 => by rw [nsmulRec, zero_smul, coe_zero]
  | n + 1 => by rw [nsmulRec, succ_nsmul, coe_add, coe_nsmul_rec]
#align zero_at_infty_continuous_map.coe_nsmul_rec ZeroAtInftyContinuousMap.coe_nsmulRec
-/

#print ZeroAtInftyContinuousMap.instNatSMul /-
instance instNatSMul : SMul ℕ C₀(α, β) :=
  ⟨fun n f => ⟨n • f, by simpa [coe_nsmul_rec] using zero_at_infty (nsmulRec n f)⟩⟩
#align zero_at_infty_continuous_map.has_nat_scalar ZeroAtInftyContinuousMap.instNatSMul
-/

instance : AddMonoid C₀(α, β) :=
  FunLike.coe_injective.AddMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

instance [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C₀(α, β) :=
  FunLike.coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => rfl

section AddGroup

variable [AddGroup β] [TopologicalAddGroup β] (f g : C₀(α, β))

instance : Neg C₀(α, β) :=
  ⟨fun f => ⟨-f, by simpa only [neg_zero] using (zero_at_infty f).neg⟩⟩

#print ZeroAtInftyContinuousMap.coe_neg /-
@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl
#align zero_at_infty_continuous_map.coe_neg ZeroAtInftyContinuousMap.coe_neg
-/

#print ZeroAtInftyContinuousMap.neg_apply /-
theorem neg_apply : (-f) x = -f x :=
  rfl
#align zero_at_infty_continuous_map.neg_apply ZeroAtInftyContinuousMap.neg_apply
-/

instance : Sub C₀(α, β) :=
  ⟨fun f g => ⟨f - g, by simpa only [sub_zero] using (zero_at_infty f).sub (zero_at_infty g)⟩⟩

#print ZeroAtInftyContinuousMap.coe_sub /-
@[simp]
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl
#align zero_at_infty_continuous_map.coe_sub ZeroAtInftyContinuousMap.coe_sub
-/

#print ZeroAtInftyContinuousMap.sub_apply /-
theorem sub_apply : (f - g) x = f x - g x :=
  rfl
#align zero_at_infty_continuous_map.sub_apply ZeroAtInftyContinuousMap.sub_apply
-/

#print ZeroAtInftyContinuousMap.coe_zsmulRec /-
@[simp]
theorem coe_zsmulRec : ∀ z, ⇑(zsmulRec z f) = z • f
  | Int.ofNat n => by rw [zsmulRec, Int.ofNat_eq_coe, coe_nsmul_rec, coe_nat_zsmul]
  | -[n+1] => by rw [zsmulRec, negSucc_zsmul, coe_neg, coe_nsmul_rec]
#align zero_at_infty_continuous_map.coe_zsmul_rec ZeroAtInftyContinuousMap.coe_zsmulRec
-/

#print ZeroAtInftyContinuousMap.instIntSMul /-
instance instIntSMul : SMul ℤ C₀(α, β) :=
  ⟨fun n f => ⟨n • f, by simpa using zero_at_infty (zsmulRec n f)⟩⟩
#align zero_at_infty_continuous_map.has_int_scalar ZeroAtInftyContinuousMap.instIntSMul
-/

instance : AddGroup C₀(α, β) :=
  FunLike.coe_injective.AddGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

instance [AddCommGroup β] [TopologicalAddGroup β] : AddCommGroup C₀(α, β) :=
  FunLike.coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

instance [Zero β] {R : Type _} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] :
    SMul R C₀(α, β) :=
  ⟨fun r f => ⟨r • f, by simpa [smul_zero] using (zero_at_infty f).const_smul r⟩⟩

#print ZeroAtInftyContinuousMap.coe_smul /-
@[simp]
theorem coe_smul [Zero β] {R : Type _} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] (r : R)
    (f : C₀(α, β)) : ⇑(r • f) = r • f :=
  rfl
#align zero_at_infty_continuous_map.coe_smul ZeroAtInftyContinuousMap.coe_smul
-/

#print ZeroAtInftyContinuousMap.smul_apply /-
theorem smul_apply [Zero β] {R : Type _} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
    (r : R) (f : C₀(α, β)) (x : α) : (r • f) x = r • f x :=
  rfl
#align zero_at_infty_continuous_map.smul_apply ZeroAtInftyContinuousMap.smul_apply
-/

instance [Zero β] {R : Type _} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
    [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScalar R C₀(α, β) :=
  ⟨fun r f => ext fun x => op_smul_eq_smul _ _⟩

instance [Zero β] {R : Type _} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] :
    SMulWithZero R C₀(α, β) :=
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ FunLike.coe_injective coe_smul

instance [Zero β] {R : Type _} [MonoidWithZero R] [MulActionWithZero R β]
    [ContinuousConstSMul R β] : MulActionWithZero R C₀(α, β) :=
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ FunLike.coe_injective coe_smul

instance [AddCommMonoid β] [ContinuousAdd β] {R : Type _} [Semiring R] [Module R β]
    [ContinuousConstSMul R β] : Module R C₀(α, β) :=
  Function.Injective.module R ⟨_, coe_zero, coe_add⟩ FunLike.coe_injective coe_smul

instance [NonUnitalNonAssocSemiring β] [TopologicalSemiring β] :
    NonUnitalNonAssocSemiring C₀(α, β) :=
  FunLike.coe_injective.NonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalSemiring β] [TopologicalSemiring β] : NonUnitalSemiring C₀(α, β) :=
  FunLike.coe_injective.NonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalCommSemiring β] [TopologicalSemiring β] : NonUnitalCommSemiring C₀(α, β) :=
  FunLike.coe_injective.NonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalNonAssocRing β] [TopologicalRing β] : NonUnitalNonAssocRing C₀(α, β) :=
  FunLike.coe_injective.NonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance [NonUnitalRing β] [TopologicalRing β] : NonUnitalRing C₀(α, β) :=
  FunLike.coe_injective.NonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

instance [NonUnitalCommRing β] [TopologicalRing β] : NonUnitalCommRing C₀(α, β) :=
  FunLike.coe_injective.NonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance {R : Type _} [Semiring R] [NonUnitalNonAssocSemiring β] [TopologicalSemiring β]
    [Module R β] [ContinuousConstSMul R β] [IsScalarTower R β β] : IsScalarTower R C₀(α, β) C₀(α, β)
    where smul_assoc r f g := by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]

instance {R : Type _} [Semiring R] [NonUnitalNonAssocSemiring β] [TopologicalSemiring β]
    [Module R β] [ContinuousConstSMul R β] [SMulCommClass R β β] : SMulCommClass R C₀(α, β) C₀(α, β)
    where smul_comm r f g := by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]

end AlgebraicStructure

section Uniform

variable [UniformSpace β] [UniformSpace γ] [Zero γ] [ZeroAtInftyContinuousMapClass F β γ]

#print ZeroAtInftyContinuousMap.uniformContinuous /-
theorem uniformContinuous (f : F) : UniformContinuous (f : β → γ) :=
  (map_continuous f).uniformContinuous_of_tendsto_cocompact (zero_at_infty f)
#align zero_at_infty_continuous_map.uniform_continuous ZeroAtInftyContinuousMap.uniformContinuous
-/

end Uniform

/-! ### Metric structure

When `β` is a metric space, then every element of `C₀(α, β)` is bounded, and so there is a natural
inclusion map `zero_at_infty_continuous_map.to_bcf : C₀(α, β) → (α →ᵇ β)`. Via this map `C₀(α, β)`
inherits a metric as the pullback of the metric on `α →ᵇ β`. Moreover, this map has closed range
in `α →ᵇ β` and consequently `C₀(α, β)` is a complete space whenever `β` is complete.
-/


section Metric

open Metric Set

variable [MetricSpace β] [Zero β] [ZeroAtInftyContinuousMapClass F α β]

#print ZeroAtInftyContinuousMap.bounded /-
protected theorem bounded (f : F) : ∃ C, ∀ x y : α, dist ((f : α → β) x) (f y) ≤ C :=
  by
  obtain ⟨K : Set α, hK₁, hK₂⟩ :=
    mem_cocompact.mp
      (tendsto_def.mp (zero_at_infty (f : F)) _ (closed_ball_mem_nhds (0 : β) zero_lt_one))
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).Bounded.subset_closedBall (0 : β)
  refine' ⟨max C 1 + max C 1, fun x y => _⟩
  have : ∀ x, f x ∈ closed_ball (0 : β) (max C 1) :=
    by
    intro x
    by_cases hx : x ∈ K
    · exact (mem_closed_ball.mp <| hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · exact (mem_closed_ball.mp <| mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _)
  exact
    (dist_triangle (f x) 0 (f y)).trans
      (add_le_add (mem_closed_ball.mp <| this x) (mem_closed_ball'.mp <| this y))
#align zero_at_infty_continuous_map.bounded ZeroAtInftyContinuousMap.bounded
-/

#print ZeroAtInftyContinuousMap.isBounded_range /-
theorem isBounded_range (f : C₀(α, β)) : Bounded (range f) :=
  isBounded_range_iff.2 f.Bounded
#align zero_at_infty_continuous_map.bounded_range ZeroAtInftyContinuousMap.isBounded_range
-/

#print ZeroAtInftyContinuousMap.isBounded_image /-
theorem isBounded_image (f : C₀(α, β)) (s : Set α) : Bounded (f '' s) :=
  f.isBounded_range.mono <| image_subset_range _ _
#align zero_at_infty_continuous_map.bounded_image ZeroAtInftyContinuousMap.isBounded_image
-/

instance (priority := 100) : BoundedContinuousMapClass F α β :=
  { ‹ZeroAtInftyContinuousMapClass F α β› with
    map_bounded := fun f => ZeroAtInftyContinuousMap.bounded f }

#print ZeroAtInftyContinuousMap.toBCF /-
/-- Construct a bounded continuous function from a continuous function vanishing at infinity. -/
@[simps]
def toBCF (f : C₀(α, β)) : α →ᵇ β :=
  ⟨f, map_bounded f⟩
#align zero_at_infty_continuous_map.to_bcf ZeroAtInftyContinuousMap.toBCF
-/

section

variable (α) (β)

#print ZeroAtInftyContinuousMap.toBCF_injective /-
theorem toBCF_injective : Function.Injective (toBCF : C₀(α, β) → α →ᵇ β) := fun f g h => by ext;
  simpa only using FunLike.congr_fun h x
#align zero_at_infty_continuous_map.to_bcf_injective ZeroAtInftyContinuousMap.toBCF_injective
-/

end

variable {C : ℝ} {f g : C₀(α, β)}

/-- The type of continuous functions vanishing at infinity, with the uniform distance induced by the
inclusion `zero_at_infinity_continuous_map.to_bcf`, is a metric space. -/
noncomputable instance : MetricSpace C₀(α, β) :=
  MetricSpace.induced _ (toBCF_injective α β) (by infer_instance)

#print ZeroAtInftyContinuousMap.dist_toBCF_eq_dist /-
@[simp]
theorem dist_toBCF_eq_dist {f g : C₀(α, β)} : dist f.toBCF g.toBCF = dist f g :=
  rfl
#align zero_at_infty_continuous_map.dist_to_bcf_eq_dist ZeroAtInftyContinuousMap.dist_toBCF_eq_dist
-/

open BoundedContinuousFunction

#print ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly /-
/-- Convergence in the metric on `C₀(α, β)` is uniform convergence. -/
theorem tendsto_iff_tendstoUniformly {ι : Type _} {F : ι → C₀(α, β)} {f : C₀(α, β)} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l := by
  simpa only [Metric.tendsto_nhds] using
    @BoundedContinuousFunction.tendsto_iff_tendstoUniformly _ _ _ _ _ (fun i => (F i).toBCF)
      f.to_bcf l
#align zero_at_infty_continuous_map.tendsto_iff_tendsto_uniformly ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly
-/

#print ZeroAtInftyContinuousMap.isometry_toBCF /-
theorem isometry_toBCF : Isometry (toBCF : C₀(α, β) → α →ᵇ β) := by tauto
#align zero_at_infty_continuous_map.isometry_to_bcf ZeroAtInftyContinuousMap.isometry_toBCF
-/

#print ZeroAtInftyContinuousMap.closed_range_toBCF /-
theorem closed_range_toBCF : IsClosed (range (toBCF : C₀(α, β) → α →ᵇ β)) :=
  by
  refine' is_closed_iff_cluster_pt.mpr fun f hf => _
  rw [clusterPt_principal_iff] at hf 
  have : tendsto f (cocompact α) (𝓝 0) :=
    by
    refine' metric.tendsto_nhds.mpr fun ε hε => _
    obtain ⟨_, hg, g, rfl⟩ := hf (ball f (ε / 2)) (ball_mem_nhds f <| half_pos hε)
    refine'
      (metric.tendsto_nhds.mp (zero_at_infty g) (ε / 2) (half_pos hε)).mp
        (eventually_of_forall fun x hx => _)
    calc
      dist (f x) 0 ≤ dist (g.to_bcf x) (f x) + dist (g x) 0 := dist_triangle_left _ _ _
      _ < dist g.to_bcf f + ε / 2 := (add_lt_add_of_le_of_lt (dist_coe_le_dist x) hx)
      _ < ε := by simpa [add_halves ε] using add_lt_add_right hg (ε / 2)
  exact ⟨⟨f.to_continuous_map, this⟩, by ext; rfl⟩
#align zero_at_infty_continuous_map.closed_range_to_bcf ZeroAtInftyContinuousMap.closed_range_toBCF
-/

/-- Continuous functions vanishing at infinity taking values in a complete space form a
complete space. -/
instance [CompleteSpace β] : CompleteSpace C₀(α, β) :=
  (completeSpace_iff_isComplete_range isometry_toBCF.UniformInducing).mpr
    closed_range_toBCF.IsComplete

end Metric

section Norm

/-! ### Normed space

The norm structure on `C₀(α, β)` is the one induced by the inclusion `to_bcf : C₀(α, β) → (α →ᵇ b)`,
viewed as an additive monoid homomorphism. Then `C₀(α, β)` is naturally a normed space over a normed
field `𝕜` whenever `β` is as well.
-/


section NormedSpace

variable [NormedAddCommGroup β] {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 β]

noncomputable instance : NormedAddCommGroup C₀(α, β) :=
  NormedAddCommGroup.induced C₀(α, β) (α →ᵇ β) (⟨toBCF, rfl, fun x y => rfl⟩ : C₀(α, β) →+ α →ᵇ β)
    (toBCF_injective α β)

#print ZeroAtInftyContinuousMap.norm_toBCF_eq_norm /-
@[simp]
theorem norm_toBCF_eq_norm {f : C₀(α, β)} : ‖f.toBCF‖ = ‖f‖ :=
  rfl
#align zero_at_infty_continuous_map.norm_to_bcf_eq_norm ZeroAtInftyContinuousMap.norm_toBCF_eq_norm
-/

instance : NormedSpace 𝕜 C₀(α, β) where norm_smul_le k f := (norm_smul_le k f.toBCF : _)

end NormedSpace

section NormedRing

variable [NonUnitalNormedRing β]

noncomputable instance : NonUnitalNormedRing C₀(α, β) :=
  { ZeroAtInftyContinuousMap.nonUnitalRing, ZeroAtInftyContinuousMap.normedAddCommGroup with
    norm_hMul := fun f g => norm_mul_le f.toBCF g.toBCF }

end NormedRing

end Norm

section Star

/-! ### Star structure

It is possible to equip `C₀(α, β)` with a pointwise `star` operation whenever there is a continuous
`star : β → β` for which `star (0 : β) = 0`. We don't have quite this weak a typeclass, but
`star_add_monoid` is close enough.

The `star_add_monoid` and `normed_star_group` classes on `C₀(α, β)` are inherited from their
counterparts on `α →ᵇ β`. Ultimately, when `β` is a C⋆-ring, then so is `C₀(α, β)`.
-/


variable [TopologicalSpace β] [AddMonoid β] [StarAddMonoid β] [ContinuousStar β]

instance : Star C₀(α, β)
    where unit f :=
    { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).unit
      zero_at_infty' := by
        simpa only [star_zero] using (continuous_star.tendsto (0 : β)).comp (zero_at_infty f) }

#print ZeroAtInftyContinuousMap.coe_star /-
@[simp]
theorem coe_star (f : C₀(α, β)) : ⇑(star f) = star f :=
  rfl
#align zero_at_infty_continuous_map.coe_star ZeroAtInftyContinuousMap.coe_star
-/

#print ZeroAtInftyContinuousMap.star_apply /-
theorem star_apply (f : C₀(α, β)) (x : α) : (star f) x = star (f x) :=
  rfl
#align zero_at_infty_continuous_map.star_apply ZeroAtInftyContinuousMap.star_apply
-/

instance [ContinuousAdd β] : StarAddMonoid C₀(α, β)
    where
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

end Star

section NormedStar

variable [NormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

instance : NormedStarGroup C₀(α, β) where norm_star f := (norm_star f.toBCF : _)

end NormedStar

section StarModule

variable {𝕜 : Type _} [Zero 𝕜] [Star 𝕜] [AddMonoid β] [StarAddMonoid β] [TopologicalSpace β]
  [ContinuousStar β] [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] [StarModule 𝕜 β]

instance : StarModule 𝕜 C₀(α, β) where star_smul k f := ext fun x => star_smul k (f x)

end StarModule

section StarRing

variable [NonUnitalSemiring β] [StarRing β] [TopologicalSpace β] [ContinuousStar β]
  [TopologicalSemiring β]

instance : StarRing C₀(α, β) :=
  { ZeroAtInftyContinuousMap.starAddMonoid with
    star_hMul := fun f g => ext fun x => star_hMul (f x) (g x) }

end StarRing

section CstarRing

instance [NonUnitalNormedRing β] [StarRing β] [CstarRing β] : CstarRing C₀(α, β)
    where norm_star_hMul_self f := @CstarRing.norm_star_hMul_self _ _ _ _ f.toBCF

end CstarRing

/-! ### C₀ as a functor

For each `β` with sufficient structure, there is a contravariant functor `C₀(-, β)` from the
category of topological spaces with morphisms given by `cocompact_map`s.
-/


variable {δ : Type _} [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

local notation α " →co " β => CocompactMap α β

section

variable [Zero δ]

#print ZeroAtInftyContinuousMap.comp /-
/-- Composition of a continuous function vanishing at infinity with a cocompact map yields another
continuous function vanishing at infinity. -/
def comp (f : C₀(γ, δ)) (g : β →co γ) : C₀(β, δ)
    where
  toContinuousMap := (f : C(γ, δ)).comp g
  zero_at_infty' := (zero_at_infty f).comp (cocompact_tendsto g)
#align zero_at_infty_continuous_map.comp ZeroAtInftyContinuousMap.comp
-/

#print ZeroAtInftyContinuousMap.coe_comp_to_continuous_fun /-
@[simp]
theorem coe_comp_to_continuous_fun (f : C₀(γ, δ)) (g : β →co γ) :
    ((f.comp g).toContinuousMap : β → δ) = f ∘ g :=
  rfl
#align zero_at_infty_continuous_map.coe_comp_to_continuous_fun ZeroAtInftyContinuousMap.coe_comp_to_continuous_fun
-/

#print ZeroAtInftyContinuousMap.comp_id /-
@[simp]
theorem comp_id (f : C₀(γ, δ)) : f.comp (CocompactMap.id γ) = f :=
  ext fun x => rfl
#align zero_at_infty_continuous_map.comp_id ZeroAtInftyContinuousMap.comp_id
-/

#print ZeroAtInftyContinuousMap.comp_assoc /-
@[simp]
theorem comp_assoc (f : C₀(γ, δ)) (g : β →co γ) (h : α →co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align zero_at_infty_continuous_map.comp_assoc ZeroAtInftyContinuousMap.comp_assoc
-/

#print ZeroAtInftyContinuousMap.zero_comp /-
@[simp]
theorem zero_comp (g : β →co γ) : (0 : C₀(γ, δ)).comp g = 0 :=
  rfl
#align zero_at_infty_continuous_map.zero_comp ZeroAtInftyContinuousMap.zero_comp
-/

end

#print ZeroAtInftyContinuousMap.compAddMonoidHom /-
/-- Composition as an additive monoid homomorphism. -/
def compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β →co γ) : C₀(γ, δ) →+ C₀(β, δ)
    where
  toFun f := f.comp g
  map_zero' := zero_comp g
  map_add' f₁ f₂ := rfl
#align zero_at_infty_continuous_map.comp_add_monoid_hom ZeroAtInftyContinuousMap.compAddMonoidHom
-/

#print ZeroAtInftyContinuousMap.compMulHom /-
/-- Composition as a semigroup homomorphism. -/
def compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β →co γ) : C₀(γ, δ) →ₙ* C₀(β, δ)
    where
  toFun f := f.comp g
  map_mul' f₁ f₂ := rfl
#align zero_at_infty_continuous_map.comp_mul_hom ZeroAtInftyContinuousMap.compMulHom
-/

#print ZeroAtInftyContinuousMap.compLinearMap /-
/-- Composition as a linear map. -/
def compLinearMap [AddCommMonoid δ] [ContinuousAdd δ] {R : Type _} [Semiring R] [Module R δ]
    [ContinuousConstSMul R δ] (g : β →co γ) : C₀(γ, δ) →ₗ[R] C₀(β, δ)
    where
  toFun f := f.comp g
  map_add' f₁ f₂ := rfl
  map_smul' r f := rfl
#align zero_at_infty_continuous_map.comp_linear_map ZeroAtInftyContinuousMap.compLinearMap
-/

#print ZeroAtInftyContinuousMap.compNonUnitalAlgHom /-
/-- Composition as a non-unital algebra homomorphism. -/
def compNonUnitalAlgHom {R : Type _} [Semiring R] [NonUnitalNonAssocSemiring δ]
    [TopologicalSemiring δ] [Module R δ] [ContinuousConstSMul R δ] (g : β →co γ) :
    C₀(γ, δ) →ₙₐ[R] C₀(β, δ) where
  toFun f := f.comp g
  map_smul' r f := rfl
  map_zero' := rfl
  map_add' f₁ f₂ := rfl
  map_mul' f₁ f₂ := rfl
#align zero_at_infty_continuous_map.comp_non_unital_alg_hom ZeroAtInftyContinuousMap.compNonUnitalAlgHom
-/

end ZeroAtInftyContinuousMap

