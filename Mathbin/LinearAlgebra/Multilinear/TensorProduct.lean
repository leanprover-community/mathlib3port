import Mathbin.LinearAlgebra.Multilinear.Basic 
import Mathbin.LinearAlgebra.TensorProduct

/-!
# Constructions relating multilinear maps and tensor products.
-/


namespace MultilinearMap

section DomCoprod

open_locale TensorProduct

variable{R ι₁ ι₂ ι₃ ι₄ : Type _}

variable[CommSemiringₓ R]

variable[DecidableEq ι₁][DecidableEq ι₂][DecidableEq ι₃][DecidableEq ι₄]

variable{N₁ : Type _}[AddCommMonoidₓ N₁][Module R N₁]

variable{N₂ : Type _}[AddCommMonoidₓ N₂][Module R N₂]

variable{N : Type _}[AddCommMonoidₓ N][Module R N]

-- error in LinearAlgebra.Multilinear.TensorProduct: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given two multilinear maps `(ι₁ → N) → N₁` and `(ι₂ → N) → N₂`, this produces the map
`(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂` by taking the coproduct of the domain and the tensor product
of the codomain.

This can be thought of as combining `equiv.sum_arrow_equiv_prod_arrow.symm` with
`tensor_product.map`, noting that the two operations can't be separated as the intermediate result
is not a `multilinear_map`.

While this can be generalized to work for dependent `Π i : ι₁, N'₁ i` instead of `ι₁ → N`, doing so
introduces `sum.elim N'₁ N'₂` types in the result which are difficult to work with and not defeq
to the simple case defined here. See [this zulip thread](
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Instances.20on.20.60sum.2Eelim.20A.20B.20i.60/near/218484619).
-/
@[simps #[ident apply]]
def dom_coprod
(a : multilinear_map R (λ _ : ι₁, N) N₁)
(b : multilinear_map R (λ _ : ι₂, N) N₂) : multilinear_map R (λ _ : «expr ⊕ »(ι₁, ι₂), N) «expr ⊗[ ] »(N₁, R, N₂) :=
{ to_fun := λ v, «expr ⊗ₜ »(a (λ i, v (sum.inl i)), b (λ i, v (sum.inr i))),
  map_add' := λ
  v
  i
  p
  q, by cases [expr i] []; simp [] [] [] ["[", expr tensor_product.add_tmul, ",", expr tensor_product.tmul_add, "]"] [] [],
  map_smul' := λ
  v
  i
  c
  p, by cases [expr i] []; simp [] [] [] ["[", expr tensor_product.smul_tmul', ",", expr tensor_product.tmul_smul, "]"] [] [] }

-- error in LinearAlgebra.Multilinear.TensorProduct: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A more bundled version of `multilinear_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def dom_coprod' : «expr →ₗ[ ] »(«expr ⊗[ ] »(multilinear_map R (λ
   _ : ι₁, N) N₁, R, multilinear_map R (λ
   _ : ι₂, N) N₂), R, multilinear_map R (λ _ : «expr ⊕ »(ι₁, ι₂), N) «expr ⊗[ ] »(N₁, R, N₂)) :=
«expr $ »(tensor_product.lift, linear_map.mk₂ R dom_coprod (λ m₁ m₂ n, by { ext [] [] [],
    simp [] [] ["only"] ["[", expr dom_coprod_apply, ",", expr tensor_product.add_tmul, ",", expr add_apply, "]"] [] [] }) (λ
  c m n, by { ext [] [] [],
    simp [] [] ["only"] ["[", expr dom_coprod_apply, ",", expr tensor_product.smul_tmul', ",", expr smul_apply, "]"] [] [] }) (λ
  m n₁ n₂, by { ext [] [] [],
    simp [] [] ["only"] ["[", expr dom_coprod_apply, ",", expr tensor_product.tmul_add, ",", expr add_apply, "]"] [] [] }) (λ
  c m n, by { ext [] [] [],
    simp [] [] ["only"] ["[", expr dom_coprod_apply, ",", expr tensor_product.tmul_smul, ",", expr smul_apply, "]"] [] [] }))

-- error in LinearAlgebra.Multilinear.TensorProduct: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem dom_coprod'_apply
(a : multilinear_map R (λ _ : ι₁, N) N₁)
(b : multilinear_map R (λ _ : ι₂, N) N₂) : «expr = »(dom_coprod' «expr ⊗ₜ[ ] »(a, R, b), dom_coprod a b) :=
rfl

-- error in LinearAlgebra.Multilinear.TensorProduct: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- When passed an `equiv.sum_congr`, `multilinear_map.dom_dom_congr` distributes over
`multilinear_map.dom_coprod`. -/
theorem dom_coprod_dom_dom_congr_sum_congr
(a : multilinear_map R (λ _ : ι₁, N) N₁)
(b : multilinear_map R (λ _ : ι₂, N) N₂)
(σa : «expr ≃ »(ι₁, ι₃))
(σb : «expr ≃ »(ι₂, ι₄)) : «expr = »((a.dom_coprod b).dom_dom_congr (σa.sum_congr σb), (a.dom_dom_congr σa).dom_coprod (b.dom_dom_congr σb)) :=
rfl

end DomCoprod

end MultilinearMap

