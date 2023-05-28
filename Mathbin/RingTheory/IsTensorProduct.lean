/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.is_tensor_product
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.TensorProduct
import Mathbin.Algebra.Module.Ulift

/-!
# The characteristice predicate of tensor product

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

- `is_tensor_product`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `is_base_change`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being a
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.
- `algebra.is_pushout`: A predicate on the following diagram of scalar towers
  ```
    R  →  S
    ↓     ↓
    R' →  S'
  ```
    asserting that is a pushout diagram (i.e. `S' = S ⊗[R] R'`)

## Main results
- `tensor_product.is_base_change`: `S ⊗[R] M` is the base change of `M` along `R → S`.

-/


universe u v₁ v₂ v₃ v₄

open TensorProduct

open TensorProduct

section IsTensorProduct

variable {R : Type _} [CommRing R]

variable {M₁ M₂ M M' : Type _}

variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M] [AddCommMonoid M']

variable [Module R M₁] [Module R M₂] [Module R M] [Module R M']

variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M)

variable {N₁ N₂ N : Type _} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N]

variable [Module R N₁] [Module R N₂] [Module R N]

variable {g : N₁ →ₗ[R] N₂ →ₗ[R] N}

#print IsTensorProduct /-
/-- Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `is_tensor_product f` means that
`M` is the tensor product of `M₁` and `M₂` via `f`.
This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be bijective.
-/
def IsTensorProduct : Prop :=
  Function.Bijective (TensorProduct.lift f)
#align is_tensor_product IsTensorProduct
-/

variable (R M N) {f}

/- warning: tensor_product.is_tensor_product -> TensorProduct.isTensorProduct is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (M : Type.{u2}) [_inst_4 : AddCommMonoid.{u2} M] [_inst_8 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_4] (N : Type.{u3}) [_inst_12 : AddCommMonoid.{u3} N] [_inst_15 : Module.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_12], IsTensorProduct.{u1, u2, u3, max u2 u3} R _inst_1 M N (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N _inst_4 _inst_12 _inst_8 _inst_15) _inst_4 _inst_12 (TensorProduct.addCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N _inst_4 _inst_12 _inst_8 _inst_15) _inst_8 _inst_15 (TensorProduct.module.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N _inst_4 _inst_12 _inst_8 _inst_15) (TensorProduct.mk.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N _inst_4 _inst_12 _inst_8 _inst_15)
but is expected to have type
  forall (R : Type.{u3}) [_inst_1 : CommRing.{u3} R] (M : Type.{u2}) [_inst_4 : AddCommMonoid.{u2} M] [_inst_8 : Module.{u3, u2} R M (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) _inst_4] (N : Type.{u1}) [_inst_12 : AddCommMonoid.{u1} N] [_inst_15 : Module.{u3, u1} R N (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) _inst_12], IsTensorProduct.{u3, u2, u1, max u2 u1} R _inst_1 M N (TensorProduct.{u3, u2, u1} R (CommRing.toCommSemiring.{u3} R _inst_1) M N _inst_4 _inst_12 _inst_8 _inst_15) _inst_4 _inst_12 (TensorProduct.addCommMonoid.{u3, u2, u1} R (CommRing.toCommSemiring.{u3} R _inst_1) M N _inst_4 _inst_12 _inst_8 _inst_15) _inst_8 _inst_15 (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u3, u2, u1} R (CommRing.toCommSemiring.{u3} R _inst_1) M N _inst_4 _inst_12 _inst_8 _inst_15) (TensorProduct.mk.{u3, u2, u1} R (CommRing.toCommSemiring.{u3} R _inst_1) M N _inst_4 _inst_12 _inst_8 _inst_15)
Case conversion may be inaccurate. Consider using '#align tensor_product.is_tensor_product TensorProduct.isTensorProductₓ'. -/
theorem TensorProduct.isTensorProduct : IsTensorProduct (TensorProduct.mk R M N) :=
  by
  delta IsTensorProduct
  convert_to Function.Bijective LinearMap.id using 2
  · apply TensorProduct.ext'; simp
  · exact Function.bijective_id
#align tensor_product.is_tensor_product TensorProduct.isTensorProduct

variable {R M N}

#print IsTensorProduct.equiv /-
/-- If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ ⊗[R] M₂`. -/
@[simps apply]
noncomputable def IsTensorProduct.equiv (h : IsTensorProduct f) : M₁ ⊗[R] M₂ ≃ₗ[R] M :=
  LinearEquiv.ofBijective _ h
#align is_tensor_product.equiv IsTensorProduct.equiv
-/

/- warning: is_tensor_product.equiv_to_linear_map -> IsTensorProduct.equiv_toLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_tensor_product.equiv_to_linear_map IsTensorProduct.equiv_toLinearMapₓ'. -/
@[simp]
theorem IsTensorProduct.equiv_toLinearMap (h : IsTensorProduct f) :
    h.Equiv.toLinearMap = TensorProduct.lift f :=
  rfl
#align is_tensor_product.equiv_to_linear_map IsTensorProduct.equiv_toLinearMap

/- warning: is_tensor_product.equiv_symm_apply -> IsTensorProduct.equiv_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_tensor_product.equiv_symm_apply IsTensorProduct.equiv_symm_applyₓ'. -/
@[simp]
theorem IsTensorProduct.equiv_symm_apply (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂) :
    h.Equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ :=
  by
  apply h.equiv.injective
  refine' (h.equiv.apply_symm_apply _).trans _
  simp
#align is_tensor_product.equiv_symm_apply IsTensorProduct.equiv_symm_apply

#print IsTensorProduct.lift /-
/-- If `M` is the tensor product of `M₁` and `M₂`, we may lift a bilinear map `M₁ →ₗ[R] M₂ →ₗ[R] M'`
to a `M →ₗ[R] M'`. -/
noncomputable def IsTensorProduct.lift (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') :
    M →ₗ[R] M' :=
  (TensorProduct.lift f').comp h.Equiv.symm.toLinearMap
#align is_tensor_product.lift IsTensorProduct.lift
-/

/- warning: is_tensor_product.lift_eq -> IsTensorProduct.lift_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_tensor_product.lift_eq IsTensorProduct.lift_eqₓ'. -/
theorem IsTensorProduct.lift_eq (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') (x₁ : M₁)
    (x₂ : M₂) : h.lift f' (f x₁ x₂) = f' x₁ x₂ :=
  by
  delta IsTensorProduct.lift
  simp
#align is_tensor_product.lift_eq IsTensorProduct.lift_eq

#print IsTensorProduct.map /-
/-- The tensor product of a pair of linear maps between modules. -/
noncomputable def IsTensorProduct.map (hf : IsTensorProduct f) (hg : IsTensorProduct g)
    (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) : M →ₗ[R] N :=
  hg.Equiv.toLinearMap.comp ((TensorProduct.map i₁ i₂).comp hf.Equiv.symm.toLinearMap)
#align is_tensor_product.map IsTensorProduct.map
-/

/- warning: is_tensor_product.map_eq -> IsTensorProduct.map_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_tensor_product.map_eq IsTensorProduct.map_eqₓ'. -/
theorem IsTensorProduct.map_eq (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁)
    (i₂ : M₂ →ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x₁) (i₂ x₂) :=
  by
  delta IsTensorProduct.map
  simp
#align is_tensor_product.map_eq IsTensorProduct.map_eq

/- warning: is_tensor_product.induction_on -> IsTensorProduct.inductionOn is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_tensor_product.induction_on IsTensorProduct.inductionOnₓ'. -/
theorem IsTensorProduct.inductionOn (h : IsTensorProduct f) {C : M → Prop} (m : M) (h0 : C 0)
    (htmul : ∀ x y, C (f x y)) (hadd : ∀ x y, C x → C y → C (x + y)) : C m :=
  by
  rw [← h.equiv.right_inv m]
  generalize h.equiv.inv_fun m = y
  change C (TensorProduct.lift f y)
  induction y using TensorProduct.induction_on
  · rwa [map_zero]
  · rw [TensorProduct.lift.tmul]; apply htmul
  · rw [map_add]; apply hadd <;> assumption
#align is_tensor_product.induction_on IsTensorProduct.inductionOn

end IsTensorProduct

section IsBaseChange

variable {R : Type _} {M : Type v₁} {N : Type v₂} (S : Type v₃)

variable [AddCommMonoid M] [AddCommMonoid N] [CommRing R]

variable [CommRing S] [Algebra R S] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]

variable (f : M →ₗ[R] N)

include f

#print IsBaseChange /-
/-- Given an `R`-algebra `S` and an `R`-module `M`, an `S`-module `N` together with a map
`f : M →ₗ[R] N` is the base change of `M` to `S` if the map `S × M → N, (s, m) ↦ s • f m` is the
tensor product. -/
def IsBaseChange : Prop :=
  IsTensorProduct
    (((Algebra.ofId S <| Module.End S (M →ₗ[R] N)).toLinearMap.flip f).restrictScalars R)
#align is_base_change IsBaseChange
-/

variable {S f} (h : IsBaseChange S f)

variable {P Q : Type _} [AddCommMonoid P] [Module R P]

variable [AddCommMonoid Q] [Module S Q]

section

variable [Module R Q] [IsScalarTower R S Q]

#print IsBaseChange.lift /-
/-- Suppose `f : M →ₗ[R] N` is the base change of `M` along `R → S`. Then any `R`-linear map from
`M` to an `S`-module factors thorugh `f`. -/
noncomputable def IsBaseChange.lift (g : M →ₗ[R] Q) : N →ₗ[S] Q :=
  {
    h.lift
      (((Algebra.ofId S <| Module.End S (M →ₗ[R] Q)).toLinearMap.flip g).restrictScalars R) with
    map_smul' := fun r x =>
      by
      let F := ((Algebra.ofId S <| Module.End S (M →ₗ[R] Q)).toLinearMap.flip g).restrictScalars R
      have hF : ∀ (s : S) (m : M), h.lift F (s • f m) = s • g m := h.lift_eq F
      change h.lift F (r • x) = r • h.lift F x
      apply h.induction_on x
      · rw [smul_zero, map_zero, smul_zero]
      · intro s m
        change h.lift F (r • s • f m) = r • h.lift F (s • f m)
        rw [← mul_smul, hF, hF, mul_smul]
      · intro x₁ x₂ e₁ e₂; rw [map_add, smul_add, map_add, smul_add, e₁, e₂] }
#align is_base_change.lift IsBaseChange.lift
-/

/- warning: is_base_change.lift_eq -> IsBaseChange.lift_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.lift_eq IsBaseChange.lift_eqₓ'. -/
theorem IsBaseChange.lift_eq (g : M →ₗ[R] Q) (x : M) : h.lift g (f x) = g x :=
  by
  have hF : ∀ (s : S) (m : M), h.lift g (s • f m) = s • g m := h.lift_eq _
  convert hF 1 x <;> rw [one_smul]
#align is_base_change.lift_eq IsBaseChange.lift_eq

/- warning: is_base_change.lift_comp -> IsBaseChange.lift_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.lift_comp IsBaseChange.lift_compₓ'. -/
theorem IsBaseChange.lift_comp (g : M →ₗ[R] Q) : ((h.lift g).restrictScalars R).comp f = g :=
  LinearMap.ext (h.liftEq g)
#align is_base_change.lift_comp IsBaseChange.lift_comp

end

include h

/- warning: is_base_change.induction_on -> IsBaseChange.inductionOn is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.induction_on IsBaseChange.inductionOnₓ'. -/
@[elab_as_elim]
theorem IsBaseChange.inductionOn (x : N) (P : N → Prop) (h₁ : P 0) (h₂ : ∀ m : M, P (f m))
    (h₃ : ∀ (s : S) (n), P n → P (s • n)) (h₄ : ∀ n₁ n₂, P n₁ → P n₂ → P (n₁ + n₂)) : P x :=
  h.inductionOn x h₁ (fun s y => h₃ _ _ (h₂ _)) h₄
#align is_base_change.induction_on IsBaseChange.inductionOn

/- warning: is_base_change.alg_hom_ext -> IsBaseChange.alg_hom_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.alg_hom_ext IsBaseChange.alg_hom_extₓ'. -/
theorem IsBaseChange.alg_hom_ext (g₁ g₂ : N →ₗ[S] Q) (e : ∀ x, g₁ (f x) = g₂ (f x)) : g₁ = g₂ :=
  by
  ext x
  apply h.induction_on x
  · rw [map_zero, map_zero]
  · assumption
  · intro s n e'; rw [g₁.map_smul, g₂.map_smul, e']
  · intro x y e₁ e₂; rw [map_add, map_add, e₁, e₂]
#align is_base_change.alg_hom_ext IsBaseChange.alg_hom_ext

/- warning: is_base_change.alg_hom_ext' -> IsBaseChange.alg_hom_ext' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.alg_hom_ext' IsBaseChange.alg_hom_ext'ₓ'. -/
theorem IsBaseChange.alg_hom_ext' [Module R Q] [IsScalarTower R S Q] (g₁ g₂ : N →ₗ[S] Q)
    (e : (g₁.restrictScalars R).comp f = (g₂.restrictScalars R).comp f) : g₁ = g₂ :=
  h.alg_hom_ext g₁ g₂ (LinearMap.congr_fun e)
#align is_base_change.alg_hom_ext' IsBaseChange.alg_hom_ext'

variable (R M N S)

omit h f

/- warning: tensor_product.is_base_change -> TensorProduct.isBaseChange is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align tensor_product.is_base_change TensorProduct.isBaseChangeₓ'. -/
theorem TensorProduct.isBaseChange : IsBaseChange S (TensorProduct.mk R S M 1) :=
  by
  delta IsBaseChange
  convert TensorProduct.isTensorProduct R S M using 1
  ext (s x)
  change s • 1 ⊗ₜ x = s ⊗ₜ x
  rw [TensorProduct.smul_tmul']
  congr 1
  exact mul_one _
#align tensor_product.is_base_change TensorProduct.isBaseChange

variable {R M N S}

#print IsBaseChange.equiv /-
/-- The base change of `M` along `R → S` is linearly equivalent to `S ⊗[R] M`. -/
noncomputable def IsBaseChange.equiv : S ⊗[R] M ≃ₗ[S] N :=
  { h.Equiv with
    map_smul' := fun r x => by
      change h.equiv (r • x) = r • h.equiv x
      apply TensorProduct.induction_on x
      · rw [smul_zero, map_zero, smul_zero]
      · intro x y; simp [smul_tmul', Algebra.ofId_apply]
      · intro x y hx hy; rw [map_add, smul_add, map_add, smul_add, hx, hy] }
#align is_base_change.equiv IsBaseChange.equiv
-/

/- warning: is_base_change.equiv_tmul -> IsBaseChange.equiv_tmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.equiv_tmul IsBaseChange.equiv_tmulₓ'. -/
theorem IsBaseChange.equiv_tmul (s : S) (m : M) : h.Equiv (s ⊗ₜ m) = s • f m :=
  TensorProduct.lift.tmul s m
#align is_base_change.equiv_tmul IsBaseChange.equiv_tmul

/- warning: is_base_change.equiv_symm_apply -> IsBaseChange.equiv_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.equiv_symm_apply IsBaseChange.equiv_symm_applyₓ'. -/
theorem IsBaseChange.equiv_symm_apply (m : M) : h.Equiv.symm (f m) = 1 ⊗ₜ m := by
  rw [h.equiv.symm_apply_eq, h.equiv_tmul, one_smul]
#align is_base_change.equiv_symm_apply IsBaseChange.equiv_symm_apply

variable (f)

/- warning: is_base_change.of_lift_unique -> IsBaseChange.of_lift_unique is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.of_lift_unique IsBaseChange.of_lift_uniqueₓ'. -/
theorem IsBaseChange.of_lift_unique
    (h :
      ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
        ∀ [Module R Q] [Module S Q],
          ∀ [IsScalarTower R S Q],
            ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g) :
    IsBaseChange S f :=
  by
  obtain ⟨g, hg, -⟩ :=
    h (ULift.{v₂} <| S ⊗[R] M)
      (ulift.module_equiv.symm.to_linear_map.comp <| TensorProduct.mk R S M 1)
  let f' : S ⊗[R] M →ₗ[R] N := _; change Function.Bijective f'
  let f'' : S ⊗[R] M →ₗ[S] N :=
    by
    refine'
      { f' with
        toFun := f'
        map_smul' := fun s x =>
          TensorProduct.induction_on x _ (fun s' y => smul_assoc s s' _) fun x y hx hy => _ }
    · rw [map_zero, smul_zero, map_zero, smul_zero]
    · rw [smul_add, map_add, map_add, smul_add, hx, hy]
  simp_rw [FunLike.ext_iff, LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hg
  let fe : S ⊗[R] M ≃ₗ[S] N :=
    LinearEquiv.ofLinear f'' (ulift.module_equiv.to_linear_map.comp g) _ _
  · exact fe.bijective
  · rw [← LinearMap.cancel_left (ULift.moduleEquiv : ULift.{max v₁ v₃} N ≃ₗ[S] N).symm.Injective]
    refine' (h (ULift.{max v₁ v₃} N) <| ulift.module_equiv.symm.to_linear_map.comp f).unique _ rfl
    · infer_instance
    ext x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hg]
    apply one_smul
  · ext x; change (g <| (1 : S) • f x).down = _; rw [one_smul, hg]; rfl
#align is_base_change.of_lift_unique IsBaseChange.of_lift_unique

variable {f}

/- warning: is_base_change.iff_lift_unique -> IsBaseChange.iff_lift_unique is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.iff_lift_unique IsBaseChange.iff_lift_uniqueₓ'. -/
theorem IsBaseChange.iff_lift_unique :
    IsBaseChange S f ↔
      ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
        ∀ [Module R Q] [Module S Q],
          ∀ [IsScalarTower R S Q],
            ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g :=
  ⟨fun h => by
    intros
    exact ⟨h.lift g, h.lift_comp g, fun g' e => h.alg_hom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩,
    IsBaseChange.of_lift_unique f⟩
#align is_base_change.iff_lift_unique IsBaseChange.iff_lift_unique

/- warning: is_base_change.of_equiv -> IsBaseChange.ofEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u3}} {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} M] [_inst_2 : AddCommMonoid.{u2} N] [_inst_3 : CommRing.{u3} R] [_inst_6 : Module.{u3, u1} R M (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)) _inst_1] [_inst_7 : Module.{u3, u2} R N (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)) _inst_2] (e : LinearEquiv.{u3, u3, u1, u2} R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)) (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)))) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)))) (RingHomInvPair.ids.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3))) (RingHomInvPair.ids.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3))) M N _inst_1 _inst_2 _inst_6 _inst_7), IsBaseChange.{u1, u2, u3, u3} R M N R _inst_1 _inst_2 _inst_3 _inst_3 (Algebra.id.{u3} R (CommRing.toCommSemiring.{u3} R _inst_3)) _inst_6 _inst_7 _inst_7 (IsScalarTower.left.{u3, u2} R N (Ring.toMonoid.{u3} R (CommRing.toRing.{u3} R _inst_3)) (MulActionWithZero.toMulAction.{u3, u2} R N (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3))) (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N (AddCommMonoid.toAddMonoid.{u2} N _inst_2))) (Module.toMulActionWithZero.{u3, u2} R N (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)) _inst_2 _inst_7))) (LinearEquiv.toLinearMap.{u3, u3, u1, u2} R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)) (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)))) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3)))) (RingHomInvPair.ids.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3))) (RingHomInvPair.ids.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_3))) M N _inst_1 _inst_2 _inst_6 _inst_7 e)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} M] [_inst_2 : AddCommMonoid.{u3} N] [_inst_3 : CommRing.{u1} R] [_inst_6 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) _inst_1] [_inst_7 : Module.{u1, u3} R N (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) _inst_2] (e : LinearEquiv.{u1, u1, u2, u3} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3))) M N _inst_1 _inst_2 _inst_6 _inst_7), IsBaseChange.{u2, u3, u1, u1} R M N R _inst_1 _inst_2 _inst_3 _inst_3 (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) _inst_6 _inst_7 _inst_7 (IsScalarTower.left.{u1, u3} R N (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)))) (MulActionWithZero.toMulAction.{u1, u3} R N (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3))) (AddMonoid.toZero.{u3} N (AddCommMonoid.toAddMonoid.{u3} N _inst_2)) (Module.toMulActionWithZero.{u1, u3} R N (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) _inst_2 _inst_7))) (LinearEquiv.toLinearMap.{u1, u1, u2, u3} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3))) (RingHomInvPair.ids.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3))) M N _inst_1 _inst_2 _inst_6 _inst_7 e)
Case conversion may be inaccurate. Consider using '#align is_base_change.of_equiv IsBaseChange.ofEquivₓ'. -/
theorem IsBaseChange.ofEquiv (e : M ≃ₗ[R] N) : IsBaseChange R e.toLinearMap :=
  by
  apply IsBaseChange.of_lift_unique
  intro Q I₁ I₂ I₃ I₄ g
  have : I₂ = I₃ := by
    ext (r q)
    rw [← one_smul R q, smul_smul, ← smul_assoc, smul_eq_mul, mul_one]
  cases this
  refine' ⟨g.comp e.symm.to_linear_map, by ext; simp, _⟩
  rintro y (rfl : _ = _)
  ext
  simp
#align is_base_change.of_equiv IsBaseChange.ofEquiv

variable {T O : Type _} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

variable [AddCommMonoid O] [Module R O] [Module S O] [Module T O] [IsScalarTower S T O]

variable [IsScalarTower R S O] [IsScalarTower R T O]

/- warning: is_base_change.comp -> IsBaseChange.comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_base_change.comp IsBaseChange.compₓ'. -/
theorem IsBaseChange.comp {f : M →ₗ[R] N} (hf : IsBaseChange S f) {g : N →ₗ[S] O}
    (hg : IsBaseChange T g) : IsBaseChange T ((g.restrictScalars R).comp f) :=
  by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ i
  letI := Module.compHom Q (algebraMap S T)
  haveI : IsScalarTower S T Q := ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower R S Q := by
    refine' ⟨fun x y z => _⟩
    change (IsScalarTower.toAlgHom R S T) (x • y) • z = x • algebraMap S T y • z
    rw [AlgHom.map_smul, smul_assoc]
    rfl
  refine' ⟨hg.lift (hf.lift i), by ext; simp [IsBaseChange.lift_eq], _⟩
  rintro g' (e : _ = _)
  refine' hg.alg_hom_ext' _ _ (hf.alg_hom_ext' _ _ _)
  rw [IsBaseChange.lift_comp, IsBaseChange.lift_comp, ← e]
  ext
  rfl
#align is_base_change.comp IsBaseChange.comp

variable {R' S' : Type _} [CommRing R'] [CommRing S']

variable [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']

variable [IsScalarTower R R' S'] [IsScalarTower R S S']

open IsScalarTower (toAlgHom)

variable (R S R' S')

#print Algebra.IsPushout /-
/-- A type-class stating that the following diagram of scalar towers
R  →  S
↓     ↓
R' →  S'
is a pushout diagram (i.e. `S' = S ⊗[R] R'`)
-/
@[mk_iff]
class Algebra.IsPushout : Prop where
  out : IsBaseChange S (toAlgHom R R' S').toLinearMap
#align algebra.is_pushout Algebra.IsPushout
-/

variable {R S R' S'}

/- warning: algebra.is_pushout.symm -> Algebra.IsPushout.symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.is_pushout.symm Algebra.IsPushout.symmₓ'. -/
theorem Algebra.IsPushout.symm (h : Algebra.IsPushout R S R' S') : Algebra.IsPushout R R' S S' :=
  by
  letI := (Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗ R').toRingHom.toAlgebra
  let e : R' ⊗[R] S ≃ₗ[R'] S' :=
    by
    refine' { (TensorProduct.comm R R' S).trans <| h.1.Equiv.restrictScalars R with map_smul' := _ }
    intro r x
    change
      h.1.Equiv (TensorProduct.comm R R' S (r • x)) = r • h.1.Equiv (TensorProduct.comm R R' S x)
    apply TensorProduct.induction_on x
    · simp only [smul_zero, map_zero]
    · intro x y
      simp [smul_tmul', Algebra.smul_def, RingHom.algebraMap_toAlgebra, h.1.equiv_tmul]
      ring
    · intro x y hx hy; simp only [map_add, smul_add, hx, hy]
  have :
    (to_alg_hom R S S').toLinearMap =
      (e.to_linear_map.restrict_scalars R).comp (TensorProduct.mk R R' S 1) :=
    by ext; simp [e, h.1.equiv_tmul, Algebra.smul_def]
  constructor
  rw [this]
  exact (TensorProduct.isBaseChange R S R').comp (IsBaseChange.ofEquiv e)
#align algebra.is_pushout.symm Algebra.IsPushout.symm

variable (R S R' S')

/- warning: algebra.is_pushout.comm -> Algebra.IsPushout.comm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.is_pushout.comm Algebra.IsPushout.commₓ'. -/
theorem Algebra.IsPushout.comm : Algebra.IsPushout R S R' S' ↔ Algebra.IsPushout R R' S S' :=
  ⟨Algebra.IsPushout.symm, Algebra.IsPushout.symm⟩
#align algebra.is_pushout.comm Algebra.IsPushout.comm

variable {R S R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- warning: tensor_product.is_pushout -> TensorProduct.isPushout is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {T : Type.{u3}} [_inst_33 : CommRing.{u1} R] [_inst_34 : CommRing.{u2} S] [_inst_35 : CommRing.{u3} T] [_inst_36 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34))] [_inst_37 : Algebra.{u1, u3} R T (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35))], Algebra.IsPushout.{u2, u1, u3, max u2 u3} R S _inst_33 _inst_34 _inst_36 T (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_33) S T (AddCommGroup.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toAddCommGroup.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_34))))) (AddCommGroup.toAddCommMonoid.{u3} T (NonUnitalNonAssocRing.toAddCommGroup.{u3} T (NonAssocRing.toNonUnitalNonAssocRing.{u3} T (Ring.toNonAssocRing.{u3} T (CommRing.toRing.{u3} T _inst_35))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36) (Algebra.toModule.{u1, u3} R T (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35)) _inst_37)) _inst_35 (Algebra.TensorProduct.TensorProduct.commRing.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) _inst_37 (Algebra.TensorProduct.leftAlgebra.{u1, u2, u3, u2} R (CommRing.toCommSemiring.{u1} R _inst_33) S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36 T (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35)) _inst_37 S (CommRing.toCommSemiring.{u2} S _inst_34) _inst_36 (Algebra.id.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) (IsScalarTower.right.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36)) (Algebra.TensorProduct.rightAlgebra.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) (Algebra.TensorProduct.TensorProduct.algebra.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_33) S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36 T (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35)) _inst_37) (Algebra.TensorProduct.right_isScalarTower.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) (Algebra.TensorProduct.TensorProduct.isScalarTower.{u1, u2, u3, u2} R (CommRing.toCommSemiring.{u1} R _inst_33) S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36 T (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35)) _inst_37 S (CommRing.toCommSemiring.{u2} S _inst_34) _inst_36 (Algebra.id.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) (IsScalarTower.right.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {T : Type.{u3}} [_inst_33 : CommRing.{u1} R] [_inst_34 : CommRing.{u2} S] [_inst_35 : CommRing.{u3} T] [_inst_36 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34))] [_inst_37 : Algebra.{u1, u3} R T (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35))], Algebra.IsPushout.{u2, u1, u3, max u3 u2} R S _inst_33 _inst_34 _inst_36 T (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_33) S T (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_34))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} T (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} T (NonAssocRing.toNonUnitalNonAssocRing.{u3} T (Ring.toNonAssocRing.{u3} T (CommRing.toRing.{u3} T _inst_35))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36) (Algebra.toModule.{u1, u3} R T (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35)) _inst_37)) _inst_35 (Algebra.TensorProduct.instCommRingTensorProductToCommSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingToRingToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingToRingToModuleToSemiringToCommSemiringToModuleToSemiringToCommSemiring.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) _inst_37 (Algebra.TensorProduct.leftAlgebra.{u1, u2, u3, u2} R (CommRing.toCommSemiring.{u1} R _inst_33) S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36 T (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35)) _inst_37 S (CommRing.toCommSemiring.{u2} S _inst_34) _inst_36 (Algebra.id.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) (IsScalarTower.right.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36)) (Algebra.TensorProduct.rightAlgebra.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) (Algebra.TensorProduct.instAlgebraTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModuleInstSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_33) S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36 T (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35)) _inst_37) (Algebra.TensorProduct.right_isScalarTower.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) (Algebra.TensorProduct.instIsScalarTowerTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModuleToSMulToSemiringLeftHasSMulToMonoidToMonoidWithZeroToDistribMulActionToModuleTo_smulCommClassInstSMulTensorProduct.{u1, u2, u3, u2} R (CommRing.toCommSemiring.{u1} R _inst_33) S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36 T (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35)) _inst_37 S (CommRing.toCommSemiring.{u2} S _inst_34) _inst_36 (Algebra.id.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) (IsScalarTower.right.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36))
Case conversion may be inaccurate. Consider using '#align tensor_product.is_pushout TensorProduct.isPushoutₓ'. -/
instance TensorProduct.isPushout {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R S T (TensorProduct R S T) :=
  ⟨TensorProduct.isBaseChange R T S⟩
#align tensor_product.is_pushout TensorProduct.isPushout

/- warning: tensor_product.is_pushout' -> TensorProduct.isPushout' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {T : Type.{u3}} [_inst_33 : CommRing.{u1} R] [_inst_34 : CommRing.{u2} S] [_inst_35 : CommRing.{u3} T] [_inst_36 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34))] [_inst_37 : Algebra.{u1, u3} R T (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35))], Algebra.IsPushout.{u3, u1, u2, max u2 u3} R T _inst_33 _inst_35 _inst_37 S (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_33) S T (AddCommGroup.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toAddCommGroup.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_34))))) (AddCommGroup.toAddCommMonoid.{u3} T (NonUnitalNonAssocRing.toAddCommGroup.{u3} T (NonAssocRing.toNonUnitalNonAssocRing.{u3} T (Ring.toNonAssocRing.{u3} T (CommRing.toRing.{u3} T _inst_35))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36) (Algebra.toModule.{u1, u3} R T (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35)) _inst_37)) _inst_34 (Algebra.TensorProduct.TensorProduct.commRing.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) _inst_36 (Algebra.TensorProduct.rightAlgebra.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) (Algebra.TensorProduct.leftAlgebra.{u1, u2, u3, u2} R (CommRing.toCommSemiring.{u1} R _inst_33) S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36 T (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35)) _inst_37 S (CommRing.toCommSemiring.{u2} S _inst_34) _inst_36 (Algebra.id.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) (IsScalarTower.right.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36)) (Algebra.TensorProduct.TensorProduct.algebra.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_33) S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36 T (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35)) _inst_37) (Algebra.TensorProduct.TensorProduct.isScalarTower.{u1, u2, u3, u2} R (CommRing.toCommSemiring.{u1} R _inst_33) S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36 T (Ring.toSemiring.{u3} T (CommRing.toRing.{u3} T _inst_35)) _inst_37 S (CommRing.toCommSemiring.{u2} S _inst_34) _inst_36 (Algebra.id.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) (IsScalarTower.right.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_34)) _inst_36)) (Algebra.TensorProduct.right_isScalarTower.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {T : Type.{u3}} [_inst_33 : CommRing.{u1} R] [_inst_34 : CommRing.{u2} S] [_inst_35 : CommRing.{u3} T] [_inst_36 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34))] [_inst_37 : Algebra.{u1, u3} R T (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35))], Algebra.IsPushout.{u3, u1, u2, max u3 u2} R T _inst_33 _inst_35 _inst_37 S (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_33) S T (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_34))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} T (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} T (NonAssocRing.toNonUnitalNonAssocRing.{u3} T (Ring.toNonAssocRing.{u3} T (CommRing.toRing.{u3} T _inst_35))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36) (Algebra.toModule.{u1, u3} R T (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35)) _inst_37)) _inst_34 (Algebra.TensorProduct.instCommRingTensorProductToCommSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingToRingToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingToRingToModuleToSemiringToCommSemiringToModuleToSemiringToCommSemiring.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) _inst_36 (Algebra.TensorProduct.rightAlgebra.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37) (Algebra.TensorProduct.leftAlgebra.{u1, u2, u3, u2} R (CommRing.toCommSemiring.{u1} R _inst_33) S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36 T (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35)) _inst_37 S (CommRing.toCommSemiring.{u2} S _inst_34) _inst_36 (Algebra.id.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) (IsScalarTower.right.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36)) (Algebra.TensorProduct.instAlgebraTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModuleInstSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_33) S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36 T (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35)) _inst_37) (Algebra.TensorProduct.instIsScalarTowerTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModuleToSMulToSemiringLeftHasSMulToMonoidToMonoidWithZeroToDistribMulActionToModuleTo_smulCommClassInstSMulTensorProduct.{u1, u2, u3, u2} R (CommRing.toCommSemiring.{u1} R _inst_33) S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36 T (CommSemiring.toSemiring.{u3} T (CommRing.toCommSemiring.{u3} T _inst_35)) _inst_37 S (CommRing.toCommSemiring.{u2} S _inst_34) _inst_36 (Algebra.id.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) (IsScalarTower.right.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_33) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_34)) _inst_36)) (Algebra.TensorProduct.right_isScalarTower.{u1, u2, u3} R _inst_33 S _inst_34 _inst_36 T _inst_35 _inst_37)
Case conversion may be inaccurate. Consider using '#align tensor_product.is_pushout' TensorProduct.isPushout'ₓ'. -/
instance TensorProduct.isPushout' {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R T S (TensorProduct R S T) :=
  Algebra.IsPushout.symm inferInstance
#align tensor_product.is_pushout' TensorProduct.isPushout'

/- warning: algebra.pushout_desc -> Algebra.pushoutDesc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.pushout_desc Algebra.pushoutDescₓ'. -/
/-- If `S' = S ⊗[R] R'`, then any pair of `R`-algebra homomorphisms `f : S → A` and `g : R' → A`
such that `f x` and `g y` commutes for all `x, y` descends to a (unique) homomoprhism `S' → A`.
-/
@[simps (config := lemmasOnly) apply]
noncomputable def Algebra.pushoutDesc [H : Algebra.IsPushout R S R' S'] {A : Type _} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (hf : ∀ x y, f x * g y = g y * f x) :
    S' →ₐ[R] A := by
  letI := Module.compHom A f.to_ring_hom
  haveI : IsScalarTower R S A :=
    {
      smul_assoc := fun r s a =>
        show f (r • s) * a = r • (f s * a) by rw [f.map_smul, smul_mul_assoc] }
  haveI : IsScalarTower S A A := { smul_assoc := fun r a b => mul_assoc _ _ _ }
  have : ∀ x, H.out.lift g.to_linear_map (algebraMap R' S' x) = g x := H.out.lift_eq _
  refine' AlgHom.ofLinearMap ((H.out.lift g.to_linear_map).restrictScalars R) _ _
  · dsimp only [LinearMap.restrictScalars_apply]
    rw [← (algebraMap R' S').map_one, this, g.map_one]
  · intro x y
    apply H.out.induction_on x
    · rw [MulZeroClass.zero_mul, map_zero, MulZeroClass.zero_mul]
    rotate_left
    · intro s s' e; dsimp only [LinearMap.restrictScalars_apply] at e⊢
      rw [LinearMap.map_smul, smul_mul_assoc, LinearMap.map_smul, e, smul_mul_assoc]
    · intro s s' e₁ e₂; dsimp only [LinearMap.restrictScalars_apply] at e₁ e₂⊢
      rw [add_mul, map_add, map_add, add_mul, e₁, e₂]
    intro x; dsimp; rw [this]; apply H.out.induction_on y
    · rw [MulZeroClass.mul_zero, map_zero, MulZeroClass.mul_zero]
    · intro y; dsimp; rw [← _root_.map_mul, this, this, _root_.map_mul]
    · intro s s' e
      rw [mul_comm, smul_mul_assoc, LinearMap.map_smul, LinearMap.map_smul, mul_comm, e]
      change f s * (g x * _) = g x * (f s * _)
      rw [← mul_assoc, ← mul_assoc, hf]
    · intro s s' e₁ e₂; rw [mul_add, map_add, map_add, mul_add, e₁, e₂]
#align algebra.pushout_desc Algebra.pushoutDesc

/- warning: algebra.pushout_desc_left -> Algebra.pushoutDesc_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.pushout_desc_left Algebra.pushoutDesc_leftₓ'. -/
@[simp]
theorem Algebra.pushoutDesc_left [H : Algebra.IsPushout R S R' S'] {A : Type _} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : S) :
    Algebra.pushoutDesc S' f g H (algebraMap S S' x) = f x :=
  by
  rw [Algebra.pushoutDesc_apply, Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, ←
    Algebra.pushoutDesc_apply S' f g H, _root_.map_one]
  exact mul_one (f x)
#align algebra.pushout_desc_left Algebra.pushoutDesc_left

/- warning: algebra.lift_alg_hom_comp_left -> Algebra.lift_algHom_comp_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.lift_alg_hom_comp_left Algebra.lift_algHom_comp_leftₓ'. -/
theorem Algebra.lift_algHom_comp_left [H : Algebra.IsPushout R S R' S'] {A : Type _} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R S S') = f :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_left S' f g H x : _)
#align algebra.lift_alg_hom_comp_left Algebra.lift_algHom_comp_left

/- warning: algebra.pushout_desc_right -> Algebra.pushoutDesc_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.pushout_desc_right Algebra.pushoutDesc_rightₓ'. -/
@[simp]
theorem Algebra.pushoutDesc_right [H : Algebra.IsPushout R S R' S'] {A : Type _} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : R') :
    Algebra.pushoutDesc S' f g H (algebraMap R' S' x) = g x := by
  apply (config := { instances := false }) @IsBaseChange.lift_eq
#align algebra.pushout_desc_right Algebra.pushoutDesc_right

/- warning: algebra.lift_alg_hom_comp_right -> Algebra.lift_algHom_comp_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.lift_alg_hom_comp_right Algebra.lift_algHom_comp_rightₓ'. -/
theorem Algebra.lift_algHom_comp_right [H : Algebra.IsPushout R S R' S'] {A : Type _} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R R' S') = g :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_right S' f g H x : _)
#align algebra.lift_alg_hom_comp_right Algebra.lift_algHom_comp_right

/- warning: algebra.is_pushout.alg_hom_ext -> Algebra.IsPushout.algHom_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.is_pushout.alg_hom_ext Algebra.IsPushout.algHom_extₓ'. -/
@[ext]
theorem Algebra.IsPushout.algHom_ext [H : Algebra.IsPushout R S R' S'] {A : Type _} [Semiring A]
    [Algebra R A] {f g : S' →ₐ[R] A} (h₁ : f.comp (toAlgHom R R' S') = g.comp (toAlgHom R R' S'))
    (h₂ : f.comp (toAlgHom R S S') = g.comp (toAlgHom R S S')) : f = g :=
  by
  ext x
  apply H.1.inductionOn x
  · simp only [map_zero]
  · exact AlgHom.congr_fun h₁
  · intro s s' e; rw [Algebra.smul_def, f.map_mul, g.map_mul, e]
    congr 1; exact (AlgHom.congr_fun h₂ s : _)
  · intro s₁ s₂ e₁ e₂; rw [map_add, map_add, e₁, e₂]
#align algebra.is_pushout.alg_hom_ext Algebra.IsPushout.algHom_ext

end IsBaseChange

