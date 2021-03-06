/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.Data.Complex.IsROrC

/-!
# Extending a continuous `β`-linear map to a continuous `π`-linear map

In this file we provide a way to extend a continuous `β`-linear map to a continuous `π`-linear map
in a way that bounds the norm by the norm of the original map, when `π` is either `β` (the
extension is trivial) or `β`. We formulate the extension uniformly, by assuming `is_R_or_C π`.

We motivate the form of the extension as follows. Note that `fc : F ββ[π] π` is determined fully by
`Re fc`: for all `x : F`, `fc (I β’ x) = I * fc x`, so `Im (fc x) = -Re (fc (I β’ x))`. Therefore,
given an `fr : F ββ[β] β`, we define `fc x = fr x - fr (I β’ x) * I`.

## Main definitions

* `linear_map.extend_to_π`
* `continuous_linear_map.extend_to_π`

## Implementation details

For convenience, the main definitions above operate in terms of `restrict_scalars β π F`.
Alternate forms which operate on `[is_scalar_tower β π F]` instead are provided with a primed name.

-/


open IsROrC

variable {π : Type _} [IsROrC π] {F : Type _} [SemiNormedGroup F] [NormedSpace π F]

-- mathport name: Β«exprabsπΒ»
local notation "absπ" => @IsROrC.abs π _

/-- Extend `fr : F ββ[β] β` to `F ββ[π] π` in a way that will also be continuous and have its norm
bounded by `β₯frβ₯` if `fr` is continuous. -/
noncomputable def LinearMap.extendToπ' [Module β F] [IsScalarTower β π F] (fr : F ββ[β] β) : F ββ[π] π := by
  let fc : F β π := fun x => (fr x : π) - (I : π) * fr ((I : π) β’ x)
  have add : β x y : F, fc (x + y) = fc x + fc y := by
    intro x y
    simp only [β fc]
    simp only [β smul_add, β LinearMap.map_add, β of_real_add]
    rw [mul_addβ]
    abel
  have A : β (c : β) (x : F), (fr ((c : π) β’ x) : π) = (c : π) * (fr x : π) := by
    intro c x
    rw [β of_real_mul]
    congr 1
    rw [IsROrC.of_real_alg, smul_assoc, fr.map_smul, Algebra.id.smul_eq_mul, one_smul]
  have smul_β : β (c : β) (x : F), fc ((c : π) β’ x) = (c : π) * fc x := by
    intro c x
    simp only [β fc, β A]
    rw [A c x]
    rw [smul_smul, mul_comm I (c : π), β smul_smul, A, mul_sub]
    ring
  have smul_I : β x : F, fc ((I : π) β’ x) = (I : π) * fc x := by
    intro x
    simp only [β fc]
    cases' @I_mul_I_ax π _ with h h
    Β· simp [β h]
      
    rw [mul_sub, β mul_assoc, smul_smul, h]
    simp only [β neg_mul, β LinearMap.map_neg, β one_mulβ, β one_smul, β mul_neg, β of_real_neg, β neg_smul, β
      sub_neg_eq_add, β add_commβ]
  have smul_π : β (c : π) (x : F), fc (c β’ x) = c β’ fc x := by
    intro c x
    rw [β re_add_im c, add_smul, add_smul, add, smul_β, β smul_smul, smul_β, smul_I, β mul_assoc]
    rfl
  exact { toFun := fc, map_add' := add, map_smul' := smul_π }

theorem LinearMap.extend_to_π'_apply [Module β F] [IsScalarTower β π F] (fr : F ββ[β] β) (x : F) :
    fr.extendToπ' x = (fr x : π) - (i : π) * fr ((i : π) β’ x) :=
  rfl

/-- The norm of the extension is bounded by `β₯frβ₯`. -/
theorem norm_bound [NormedSpace β F] [IsScalarTower β π F] (fr : F βL[β] β) (x : F) :
    β₯(fr.toLinearMap.extendToπ' x : π)β₯ β€ β₯frβ₯ * β₯xβ₯ := by
  let lm : F ββ[π] π := fr.to_linear_map.extend_to_π'
  -- We aim to find a `t : π` such that
  -- * `lm (t β’ x) = fr (t β’ x)` (so `lm (t β’ x) = t * lm x β β`)
  -- * `β₯lm xβ₯ = β₯lm (t β’ x)β₯` (so `t.abs` must be 1)
  -- If `lm x β  0`, `(lm x)β»ΒΉ` satisfies the first requirement, and after normalizing, it
  -- satisfies the second.
  -- (If `lm x = 0`, the goal is trivial.)
  classical
  by_cases' h : lm x = 0
  Β· rw [h, norm_zero]
    apply mul_nonneg <;> exact norm_nonneg _
    
  let fx := (lm x)β»ΒΉ
  let t := fx / (absπ fx : π)
  have ht : absπ t = 1 := by
    field_simp [β abs_of_real, β of_real_inv, β IsROrC.abs_inv, β IsROrC.abs_div, β IsROrC.abs_abs, β h]
  have h1 : (fr (t β’ x) : π) = lm (t β’ x) := by
    apply ext
    Β· simp only [β lm, β of_real_re, β LinearMap.extend_to_π'_apply, β mul_re, β I_re, β of_real_im, β zero_mul, β
        AddMonoidHom.map_sub, β sub_zero, β mul_zero]
      rfl
      
    Β· symm
      calc im (lm (t β’ x)) = im (t * lm x) := by
          rw [lm.map_smul, smul_eq_mul]_ = im ((lm x)β»ΒΉ / absπ (lm x)β»ΒΉ * lm x) :=
          rfl _ = im (1 / (absπ (lm x)β»ΒΉ : π)) := by
          rw [div_mul_eq_mul_div, inv_mul_cancel h]_ = 0 := by
          rw [β of_real_one, β of_real_div, of_real_im]_ = im (fr (t β’ x) : π) := by
          rw [of_real_im]
      
  calc β₯lm xβ₯ = absπ t * β₯lm xβ₯ := by
      rw [ht, one_mulβ]_ = β₯t * lm xβ₯ := by
      rw [β norm_eq_abs, norm_mul]_ = β₯lm (t β’ x)β₯ := by
      rw [β smul_eq_mul, lm.map_smul]_ = β₯(fr (t β’ x) : π)β₯ := by
      rw [h1]_ = β₯fr (t β’ x)β₯ := by
      rw [norm_eq_abs, abs_of_real, norm_eq_abs, abs_to_real]_ β€ β₯frβ₯ * β₯t β’ xβ₯ :=
      ContinuousLinearMap.le_op_norm _ _ _ = β₯frβ₯ * (β₯tβ₯ * β₯xβ₯) := by
      rw [norm_smul]_ β€ β₯frβ₯ * β₯xβ₯ := by
      rw [norm_eq_abs, ht, one_mulβ]

/-- Extend `fr : F βL[β] β` to `F βL[π] π`. -/
noncomputable def ContinuousLinearMap.extendToπ' [NormedSpace β F] [IsScalarTower β π F] (fr : F βL[β] β) : F βL[π] π :=
  LinearMap.mkContinuous _ β₯frβ₯ (norm_bound _)

theorem ContinuousLinearMap.extend_to_π'_apply [NormedSpace β F] [IsScalarTower β π F] (fr : F βL[β] β) (x : F) :
    fr.extendToπ' x = (fr x : π) - (i : π) * fr ((i : π) β’ x) :=
  rfl

/-- Extend `fr : restrict_scalars β π F ββ[β] β` to `F ββ[π] π`. -/
noncomputable def LinearMap.extendToπ (fr : RestrictScalars β π F ββ[β] β) : F ββ[π] π :=
  fr.extendToπ'

theorem LinearMap.extend_to_π_apply (fr : RestrictScalars β π F ββ[β] β) (x : F) :
    fr.extendToπ x = (fr x : π) - (i : π) * fr ((i : π) β’ x : _) :=
  rfl

/-- Extend `fr : restrict_scalars β π F βL[β] β` to `F βL[π] π`. -/
noncomputable def ContinuousLinearMap.extendToπ (fr : RestrictScalars β π F βL[β] β) : F βL[π] π :=
  fr.extendToπ'

theorem ContinuousLinearMap.extend_to_π_apply (fr : RestrictScalars β π F βL[β] β) (x : F) :
    fr.extendToπ x = (fr x : π) - (i : π) * fr ((i : π) β’ x : _) :=
  rfl

