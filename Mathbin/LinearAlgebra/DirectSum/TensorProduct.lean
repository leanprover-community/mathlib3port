import Mathbin.LinearAlgebra.TensorProduct 
import Mathbin.Algebra.DirectSum.Module

/-!
# Tensor products of direct sums

This file shows that taking `tensor_product`s commutes with taking `direct_sum`s in both arguments.
-/


section Ringₓ

namespace TensorProduct

open_locale TensorProduct

open_locale DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable(R : Type _)[CommRingₓ R]

variable(ι₁ : Type _)(ι₂ : Type _)

variable[DecidableEq ι₁][DecidableEq ι₂]

variable(M₁ : ι₁ → Type _)(M₂ : ι₂ → Type _)

variable[∀ i₁, AddCommGroupₓ (M₁ i₁)][∀ i₂, AddCommGroupₓ (M₂ i₂)]

variable[∀ i₁, Module R (M₁ i₁)][∀ i₂, Module R (M₂ i₂)]

-- error in LinearAlgebra.DirectSum.TensorProduct: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
def direct_sum : «expr ≃ₗ[ ] »(«expr ⊗[ ] »(«expr⨁ , »((i₁), M₁ i₁), R, «expr⨁ , »((i₂), M₂ i₂)), R, «expr⨁ , »((i : «expr × »(ι₁, ι₂)), «expr ⊗[ ] »(M₁ i.1, R, M₂ i.2))) :=
begin
  refine [expr linear_equiv.of_linear «expr $ »(lift, «expr $ »(direct_sum.to_module R _ _, λ
     i₁, «expr $ »(flip, «expr $ »(direct_sum.to_module R _ _, λ
       i₂, «expr $ »(flip, «expr $ »(curry, direct_sum.lof R «expr × »(ι₁, ι₂) (λ
          i, «expr ⊗[ ] »(M₁ i.1, R, M₂ i.2)) (i₁, i₂))))))) «expr $ »(direct_sum.to_module R _ _, λ
    i, map (direct_sum.lof R _ _ _) (direct_sum.lof R _ _ _)) _ _]; [ext [] ["⟨", ident i₁, ",", ident i₂, "⟩", ident x₁, ident x₂] [":", 4], ext [] [ident i₁, ident i₂, ident x₁, ident x₂] [":", 5]],
  repeat { rw [expr compr₂_apply] [] <|> rw [expr comp_apply] [] <|> rw [expr id_apply] [] <|> rw [expr mk_apply] [] <|> rw [expr direct_sum.to_module_lof] [] <|> rw [expr map_tmul] [] <|> rw [expr lift.tmul] [] <|> rw [expr flip_apply] [] <|> rw [expr curry_apply] [] }
end

@[simp]
theorem direct_sum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
  DirectSum R ι₁ ι₂ M₁ M₂ (DirectSum.lof R ι₁ M₁ i₁ m₁ ⊗ₜ DirectSum.lof R ι₂ M₂ i₂ m₂) =
    DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂) :=
  by 
    simp [DirectSum]

end TensorProduct

end Ringₓ

