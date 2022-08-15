/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.TensorProduct
import Mathbin.Algebra.Module.Ulift
import Mathbin.Logic.Equiv.TransferInstance

/-!
# The characteristice predicate of tensor product

## Main definitions

- `is_tensor_product`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `is_base_change`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being a
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.

## Main results
- `tensor_product.is_base_change`: `S ⊗[R] M` is the base change of `M` along `R → S`.

-/


universe u v₁ v₂ v₃ v₄

open TensorProduct

open TensorProduct

section IsTensorProduct

variable {R : Type _} [CommRingₓ R]

variable {M₁ M₂ M M' : Type _}

variable [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M] [AddCommMonoidₓ M']

variable [Module R M₁] [Module R M₂] [Module R M] [Module R M']

variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M)

variable {N₁ N₂ N : Type _} [AddCommMonoidₓ N₁] [AddCommMonoidₓ N₂] [AddCommMonoidₓ N]

variable [Module R N₁] [Module R N₂] [Module R N]

variable {g : N₁ →ₗ[R] N₂ →ₗ[R] N}

/-- Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `is_tensor_product f` means that
`M` is the tensor product of `M₁` and `M₂` via `f`.
This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be bijective.
-/
def IsTensorProduct : Prop :=
  Function.Bijective (TensorProduct.lift f)

variable (R M N) {f}

theorem TensorProduct.is_tensor_product : IsTensorProduct (TensorProduct.mk R M N) := by
  delta' IsTensorProduct
  convert_to Function.Bijective LinearMap.id using 2
  · apply TensorProduct.ext'
    simp
    
  · exact Function.bijective_id
    

variable {R M N}

/-- If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ ⊗[R] M₂`. -/
@[simps apply]
noncomputable def IsTensorProduct.equiv (h : IsTensorProduct f) : M₁ ⊗[R] M₂ ≃ₗ[R] M :=
  LinearEquiv.ofBijective _ h.1 h.2

@[simp]
theorem IsTensorProduct.equiv_to_linear_map (h : IsTensorProduct f) : h.Equiv.toLinearMap = TensorProduct.lift f :=
  rfl

@[simp]
theorem IsTensorProduct.equiv_symm_apply (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂) :
    h.Equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ := by
  apply h.equiv.injective
  refine' (h.equiv.apply_symm_apply _).trans _
  simp

/-- If `M` is the tensor product of `M₁` and `M₂`, we may lift a bilinear map `M₁ →ₗ[R] M₂ →ₗ[R] M'`
to a `M →ₗ[R] M'`. -/
noncomputable def IsTensorProduct.lift (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') : M →ₗ[R] M' :=
  (TensorProduct.lift f').comp h.Equiv.symm.toLinearMap

theorem IsTensorProduct.lift_eq (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') (x₁ : M₁) (x₂ : M₂) :
    h.lift f' (f x₁ x₂) = f' x₁ x₂ := by
  delta' IsTensorProduct.lift
  simp

/-- The tensor product of a pair of linear maps between modules. -/
noncomputable def IsTensorProduct.map (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁)
    (i₂ : M₂ →ₗ[R] N₂) : M →ₗ[R] N :=
  hg.Equiv.toLinearMap.comp ((TensorProduct.map i₁ i₂).comp hf.Equiv.symm.toLinearMap)

theorem IsTensorProduct.map_eq (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂)
    (x₁ : M₁) (x₂ : M₂) : hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x₁) (i₂ x₂) := by
  delta' IsTensorProduct.map
  simp

theorem IsTensorProduct.induction_on (h : IsTensorProduct f) {C : M → Prop} (m : M) (h0 : C 0)
    (htmul : ∀ x y, C (f x y)) (hadd : ∀ x y, C x → C y → C (x + y)) : C m := by
  rw [← h.equiv.right_inv m]
  generalize h.equiv.inv_fun m = y
  change C (TensorProduct.lift f y)
  induction y using TensorProduct.induction_on
  · rwa [map_zero]
    
  · rw [TensorProduct.lift.tmul]
    apply htmul
    
  · rw [map_add]
    apply hadd <;> assumption
    

end IsTensorProduct

section IsBaseChange

variable {R : Type _} {M : Type v₁} {N : Type v₂} (S : Type v₃)

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [CommRingₓ R]

variable [CommRingₓ S] [Algebra R S] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]

variable (f : M →ₗ[R] N)

include f

/-- Given an `R`-algebra `S` and an `R`-module `M`, an `S`-module `N` together with a map
`f : M →ₗ[R] N` is the base change of `M` to `S` if the map `S × M → N, (s, m) ↦ s • f m` is the
tensor product. -/
def IsBaseChange : Prop :=
  IsTensorProduct (((Algebra.ofId S <| Module.End S (M →ₗ[R] N)).toLinearMap.flip f).restrictScalars R)

variable {S f} (h : IsBaseChange S f)

variable {P Q : Type _} [AddCommMonoidₓ P] [Module R P]

variable [AddCommMonoidₓ Q] [Module S Q]

section

variable [Module R Q] [IsScalarTower R S Q]

/-- Suppose `f : M →ₗ[R] N` is the base change of `M` along `R → S`. Then any `R`-linear map from
`M` to an `S`-module factors thorugh `f`. -/
noncomputable def IsBaseChange.lift (g : M →ₗ[R] Q) : N →ₗ[S] Q :=
  { h.lift (((Algebra.ofId S <| Module.End S (M →ₗ[R] Q)).toLinearMap.flip g).restrictScalars R) with
    map_smul' := fun r x => by
      let F := ((Algebra.ofId S <| Module.End S (M →ₗ[R] Q)).toLinearMap.flip g).restrictScalars R
      have hF : ∀ (s : S) (m : M), h.lift F (s • f m) = s • g m := h.lift_eq F
      change h.lift F (r • x) = r • h.lift F x
      apply h.induction_on x
      · rw [smul_zero, map_zero, smul_zero]
        
      · intro s m
        change h.lift F (r • s • f m) = r • h.lift F (s • f m)
        rw [← mul_smul, hF, hF, mul_smul]
        
      · intro x₁ x₂ e₁ e₂
        rw [map_add, smul_add, map_add, smul_add, e₁, e₂]
         }

theorem IsBaseChange.lift_eq (g : M →ₗ[R] Q) (x : M) : h.lift g (f x) = g x := by
  have hF : ∀ (s : S) (m : M), h.lift g (s • f m) = s • g m := h.lift_eq _
  convert hF 1 x <;> rw [one_smul]

theorem IsBaseChange.lift_comp (g : M →ₗ[R] Q) : ((h.lift g).restrictScalars R).comp f = g :=
  LinearMap.ext (h.liftEq g)

end

include h

@[elabAsElim]
theorem IsBaseChange.induction_on (x : N) (P : N → Prop) (h₁ : P 0) (h₂ : ∀ m : M, P (f m))
    (h₃ : ∀ (s : S) (n), P n → P (s • n)) (h₄ : ∀ n₁ n₂, P n₁ → P n₂ → P (n₁ + n₂)) : P x :=
  h.induction_on x h₁ (fun s y => h₃ _ _ (h₂ _)) h₄

theorem IsBaseChange.alg_hom_ext (g₁ g₂ : N →ₗ[S] Q) (e : ∀ x, g₁ (f x) = g₂ (f x)) : g₁ = g₂ := by
  ext x
  apply h.induction_on x
  · rw [map_zero, map_zero]
    
  · assumption
    
  · intro s n e'
    rw [g₁.map_smul, g₂.map_smul, e']
    
  · intro x y e₁ e₂
    rw [map_add, map_add, e₁, e₂]
    

theorem IsBaseChange.alg_hom_ext' [Module R Q] [IsScalarTower R S Q] (g₁ g₂ : N →ₗ[S] Q)
    (e : (g₁.restrictScalars R).comp f = (g₂.restrictScalars R).comp f) : g₁ = g₂ :=
  h.alg_hom_ext g₁ g₂ (LinearMap.congr_fun e)

variable (R M N S)

omit h f

theorem TensorProduct.is_base_change : IsBaseChange S (TensorProduct.mk R S M 1) := by
  delta' IsBaseChange
  convert TensorProduct.is_tensor_product R S M using 1
  ext s x
  change s • 1 ⊗ₜ x = s ⊗ₜ x
  rw [TensorProduct.smul_tmul']
  congr 1
  exact mul_oneₓ _

variable {R M N S}

/-- The base change of `M` along `R → S` is linearly equivalent to `S ⊗[R] M`. -/
noncomputable def IsBaseChange.equiv : S ⊗[R] M ≃ₗ[R] N :=
  h.Equiv

theorem IsBaseChange.equiv_tmul (s : S) (m : M) : h.Equiv (s ⊗ₜ m) = s • f m :=
  TensorProduct.lift.tmul s m

theorem IsBaseChange.equiv_symm_apply (m : M) : h.Equiv.symm (f m) = 1 ⊗ₜ m := by
  rw [h.equiv.symm_apply_eq, h.equiv_tmul, one_smul]

variable (f)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
theorem IsBaseChange.of_lift_unique
    (h :
      ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoidₓ Q],
        ∀ [Module R Q] [Module S Q],
          ∀ [IsScalarTower R S Q], ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g) :
    IsBaseChange S f := by
  delta' IsBaseChange IsTensorProduct
  obtain ⟨g, hg, hg'⟩ :=
    h (ULift.{v₂} <| S ⊗[R] M) (ulift.module_equiv.symm.to_linear_map.comp <| TensorProduct.mk R S M 1)
  let f' : S ⊗[R] M →ₗ[R] N := _
  change Function.Bijective f'
  let f'' : S ⊗[R] M →ₗ[S] N := by
    refine' { f' with map_smul' := fun r x => _ }
    apply TensorProduct.induction_on x
    · simp only [← map_zero, ← smul_zero, ← LinearMap.to_fun_eq_coe]
      
    · intro x y
      simp only [← Algebra.of_id_apply, ← Algebra.id.smul_eq_mul, ← AlgHom.to_linear_map_apply, ← LinearMap.mul_apply, ←
        TensorProduct.lift.tmul', ← LinearMap.smul_apply, ← RingHom.id_apply, ← Module.algebra_map_End_apply, ← f', ←
        _root_.map_mul, ← TensorProduct.smul_tmul', ← LinearMap.coe_restrict_scalars_eq_coe, ← LinearMap.flip_apply]
      
    · intro x y hx hy
      dsimp'  at hx hy⊢
      simp only [← hx, ← hy, ← smul_add, ← map_add]
      
  change Function.Bijective f''
  constructor
  · apply Function.HasLeftInverse.injective
    refine' ⟨ulift.module_equiv.to_linear_map.comp g, fun x => _⟩
    apply TensorProduct.induction_on x
    · simp only [← map_zero]
      
    · intro x y
      have := (congr_arg (fun a => x • a) (LinearMap.congr_fun hg y)).trans (ulift.module_equiv.symm.map_smul x _).symm
      apply (ULift.moduleEquiv : ULift.{v₂} (S ⊗ M) ≃ₗ[S] S ⊗ M).toEquiv.apply_eq_iff_eq_symm_apply.mpr
      any_goals {
      }
      simpa only [← Algebra.of_id_apply, ← smul_tmul', ← Algebra.id.smul_eq_mul, ← lift.tmul', ←
        LinearMap.coe_restrict_scalars_eq_coe, ← LinearMap.flip_apply, ← AlgHom.to_linear_map_apply, ←
        Module.algebra_map_End_apply, ← LinearMap.smul_apply, ← LinearMap.coe_mk, ← LinearMap.map_smulₛₗ, ← mk_apply, ←
        mul_oneₓ] using this
      
    · intro x y hx hy
      simp only [← map_add, ← hx, ← hy]
      
    
  · apply Function.HasRightInverse.surjective
    refine' ⟨ulift.module_equiv.to_linear_map.comp g, fun x => _⟩
    obtain ⟨g', hg₁, hg₂⟩ := h (ULift.{max v₁ v₃} N) (ulift.module_equiv.symm.to_linear_map.comp f)
    have : g' = ulift.module_equiv.symm.to_linear_map := by
      refine' (hg₂ _ _).symm
      rfl
    subst this
    apply (ULift.moduleEquiv : ULift.{max v₁ v₃} N ≃ₗ[S] N).symm.Injective
    simp_rw [← LinearEquiv.coe_to_linear_map, ← LinearMap.comp_apply]
    congr 1
    apply hg₂
    ext y
    have := LinearMap.congr_fun hg y
    dsimp' [← ULift.moduleEquiv]  at this⊢
    rw [this]
    simp only [← lift.tmul, ← LinearMap.coe_restrict_scalars_eq_coe, ← LinearMap.flip_apply, ←
      AlgHom.to_linear_map_apply, ← _root_.map_one, ← LinearMap.one_apply]
    

variable {f}

theorem IsBaseChange.iff_lift_unique :
    IsBaseChange S f ↔
      ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoidₓ Q],
        ∀ [Module R Q] [Module S Q],
          ∀ [IsScalarTower R S Q], ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g :=
  ⟨fun h => by
    intros
    exact ⟨h.lift g, h.lift_comp g, fun g' e => h.alg_hom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩,
    IsBaseChange.of_lift_unique f⟩

theorem IsBaseChange.of_equiv (e : M ≃ₗ[R] N) : IsBaseChange R e.toLinearMap := by
  apply IsBaseChange.of_lift_unique
  intro Q I₁ I₂ I₃ I₄ g
  have : I₂ = I₃ := by
    ext r q
    rw [← one_smul R q, smul_smul, ← smul_assoc, smul_eq_mul, mul_oneₓ]
  cases this
  refine'
    ⟨g.comp e.symm.to_linear_map, by
      ext
      simp , _⟩
  rintro y (rfl : _ = _)
  ext
  simp

variable {T O : Type _} [CommRingₓ T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

variable [AddCommMonoidₓ O] [Module R O] [Module S O] [Module T O] [IsScalarTower S T O]

variable [IsScalarTower R S O] [IsScalarTower R T O]

theorem IsBaseChange.comp {f : M →ₗ[R] N} (hf : IsBaseChange S f) {g : N →ₗ[S] O} (hg : IsBaseChange T g) :
    IsBaseChange T ((g.restrictScalars R).comp f) := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ i
  letI := Module.compHom Q (algebraMap S T)
  haveI : IsScalarTower S T Q :=
    ⟨fun x y z => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have : IsScalarTower R S Q := by
    refine' ⟨fun x y z => _⟩
    change (IsScalarTower.toAlgHom R S T) (x • y) • z = x • algebraMap S T y • z
    rw [AlgHom.map_smul, smul_assoc]
    rfl
  refine'
    ⟨hg.lift (hf.lift i), by
      ext
      simp [← IsBaseChange.lift_eq], _⟩
  rintro g' (e : _ = _)
  refine' hg.alg_hom_ext' _ _ (hf.alg_hom_ext' _ _ _)
  rw [IsBaseChange.lift_comp, IsBaseChange.lift_comp, ← e]
  ext
  rfl

variable {R' S' : Type _} [CommRingₓ R'] [CommRingₓ S']

variable [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']

variable [IsScalarTower R R' S'] [IsScalarTower R S S']

theorem IsBaseChange.symm (h : IsBaseChange S (IsScalarTower.toAlgHom R R' S').toLinearMap) :
    IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap := by
  letI := (Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗ R').toRingHom.toAlgebra
  let e : R' ⊗[R] S ≃ₗ[R'] S' := by
    refine' { (TensorProduct.comm R R' S).trans <| h.equiv.restrict_scalars R with map_smul' := _ }
    intro r x
    change h.equiv (TensorProduct.comm R R' S (r • x)) = r • h.equiv (TensorProduct.comm R R' S x)
    apply TensorProduct.induction_on x
    · simp only [← smul_zero, ← map_zero]
      
    · intro x y
      simp [← smul_tmul', ← Algebra.smul_def, ← RingHom.algebra_map_to_algebra, ← h.equiv_tmul]
      ring
      
    · intro x y hx hy
      simp only [← map_add, ← smul_add, ← hx, ← hy]
      
  have :
    (IsScalarTower.toAlgHom R S S').toLinearMap =
      (e.to_linear_map.restrict_scalars R).comp (TensorProduct.mk R R' S 1) :=
    by
    ext
    simp [← e, ← h.equiv_tmul, ← Algebra.smul_def]
  rw [this]
  exact (TensorProduct.is_base_change R S R').comp (IsBaseChange.of_equiv e)

variable (R S R' S')

theorem IsBaseChange.comm :
    IsBaseChange S (IsScalarTower.toAlgHom R R' S').toLinearMap ↔
      IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap :=
  ⟨IsBaseChange.symm, IsBaseChange.symm⟩

end IsBaseChange

