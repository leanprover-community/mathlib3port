import Mathbin.Analysis.InnerProductSpace.Projection 
import Mathbin.Analysis.NormedSpace.Dual

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`to_dual_map`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element
`x` of the space to `λ y, ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `to_dual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `to_dual_map`.  This is the Fréchet-Riesz representation theorem: every element of
the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/


noncomputable theory

open_locale Classical

universe u v

namespace InnerProductSpace

open IsROrC ContinuousLinearMap

variable (𝕜 : Type _)

variable (E : Type _) [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

local postfix:90 "†" => starRingAut

-- error in Analysis.InnerProductSpace.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An element `x` of an inner product space `E` induces an element of the dual space `dual 𝕜 E`,
the map `λ y, ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric embedding of `E`
into `dual 𝕜 E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `to_dual`.
-/ def to_dual_map : «expr →ₗᵢ⋆[ ] »(E, 𝕜, normed_space.dual 𝕜 E) :=
{ to_fun := λ
  x, linear_map.mk_continuous { to_fun := λ y, «expr⟪ , ⟫»(x, y),
    map_add' := λ _ _, inner_add_right,
    map_smul' := λ
    _
    _, inner_smul_right } «expr∥ ∥»(x) (λ y, by { rw ["[", expr is_R_or_C.norm_eq_abs, "]"] [],
     exact [expr abs_inner_le_norm _ _] }),
  map_add' := λ x y, by { ext [] [ident z] [],
    simp [] [] [] ["[", expr inner_add_left, "]"] [] [] },
  map_smul' := λ c y, by { ext [] [ident z] [],
    simp [] [] [] ["[", expr inner_smul_left, "]"] [] [] },
  norm_map' := λ x, begin
    refine [expr le_antisymm _ _],
    { exact [expr linear_map.mk_continuous_norm_le _ (norm_nonneg _) _] },
    { cases [expr eq_or_lt_of_le (norm_nonneg x)] ["with", ident h, ident h],
      { have [] [":", expr «expr = »(x, 0)] [":=", expr norm_eq_zero.mp (eq.symm h)],
        simp [] [] [] ["[", expr this, "]"] [] [] },
      { refine [expr (mul_le_mul_right h).mp _],
        calc
          «expr = »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(x)), «expr ^ »(«expr∥ ∥»(x), 2)) : by ring []
          «expr = »(..., re «expr⟪ , ⟫»(x, x)) : norm_sq_eq_inner _
          «expr ≤ »(..., abs «expr⟪ , ⟫»(x, x)) : re_le_abs _
          «expr = »(..., «expr∥ ∥»(linear_map.mk_continuous _ _ _ x)) : by simp [] [] [] ["[", expr norm_eq_abs, "]"] [] []
          «expr ≤ »(..., «expr * »(«expr∥ ∥»(linear_map.mk_continuous _ _ _), «expr∥ ∥»(x))) : le_op_norm _ x } }
  end }

variable {E}

@[simp]
theorem to_dual_map_apply {x y : E} : to_dual_map 𝕜 E x y = ⟪x, y⟫ :=
  rfl

variable (E) [CompleteSpace E]

-- error in Analysis.InnerProductSpace.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual_map` is surjective.
-/ def to_dual : «expr ≃ₗᵢ⋆[ ] »(E, 𝕜, normed_space.dual 𝕜 E) :=
linear_isometry_equiv.of_surjective (to_dual_map 𝕜 E) (begin
   intros [ident ℓ],
   set [] [ident Y] [] [":="] [expr ker ℓ] ["with", ident hY],
   by_cases [expr htriv, ":", expr «expr = »(Y, «expr⊤»())],
   { have [ident hℓ] [":", expr «expr = »(ℓ, 0)] [],
     { have [ident h'] [] [":=", expr linear_map.ker_eq_top.mp htriv],
       rw ["[", "<-", expr coe_zero, "]"] ["at", ident h'],
       apply [expr coe_injective],
       exact [expr h'] },
     exact [expr ⟨0, by simp [] [] [] ["[", expr hℓ, "]"] [] []⟩] },
   { rw ["[", "<-", expr submodule.orthogonal_eq_bot_iff, "]"] ["at", ident htriv],
     change [expr «expr ≠ »(«expr ᗮ»(Y), «expr⊥»())] [] ["at", ident htriv],
     rw ["[", expr submodule.ne_bot_iff, "]"] ["at", ident htriv],
     obtain ["⟨", ident z, ":", expr E, ",", ident hz, ":", expr «expr ∈ »(z, «expr ᗮ»(Y)), ",", ident z_ne_0, ":", expr «expr ≠ »(z, 0), "⟩", ":=", expr htriv],
     refine [expr ⟨«expr • »(«expr / »(«expr †»(ℓ z), «expr⟪ , ⟫»(z, z)), z), _⟩],
     ext [] [ident x] [],
     have [ident h₁] [":", expr «expr ∈ »(«expr - »(«expr • »(ℓ z, x), «expr • »(ℓ x, z)), Y)] [],
     { rw ["[", expr mem_ker, ",", expr map_sub, ",", expr map_smul, ",", expr map_smul, ",", expr algebra.id.smul_eq_mul, ",", expr algebra.id.smul_eq_mul, ",", expr mul_comm, "]"] [],
       exact [expr sub_self «expr * »(ℓ x, ℓ z)] },
     have [ident h₂] [":", expr «expr = »(«expr * »(ℓ z, «expr⟪ , ⟫»(z, x)), «expr * »(ℓ x, «expr⟪ , ⟫»(z, z)))] [],
     { have [ident h₃] [] [":=", expr calc
          «expr = »(0, «expr⟪ , ⟫»(z, «expr - »(«expr • »(ℓ z, x), «expr • »(ℓ x, z)))) : by { rw ["[", expr (Y.mem_orthogonal' z).mp hz, "]"] [],
            exact [expr h₁] }
          «expr = »(..., «expr - »(«expr⟪ , ⟫»(z, «expr • »(ℓ z, x)), «expr⟪ , ⟫»(z, «expr • »(ℓ x, z)))) : by rw ["[", expr inner_sub_right, "]"] []
          «expr = »(..., «expr - »(«expr * »(ℓ z, «expr⟪ , ⟫»(z, x)), «expr * »(ℓ x, «expr⟪ , ⟫»(z, z)))) : by simp [] [] [] ["[", expr inner_smul_right, "]"] [] []],
       exact [expr sub_eq_zero.mp (eq.symm h₃)] },
     have [ident h₄] [] [":=", expr calc
        «expr = »(«expr⟪ , ⟫»(«expr • »(«expr / »(«expr †»(ℓ z), «expr⟪ , ⟫»(z, z)), z), x), «expr * »(«expr / »(ℓ z, «expr⟪ , ⟫»(z, z)), «expr⟪ , ⟫»(z, x))) : by simp [] [] [] ["[", expr inner_smul_left, ",", expr ring_equiv.map_div, ",", expr conj_conj, "]"] [] []
        «expr = »(..., «expr / »(«expr * »(ℓ z, «expr⟪ , ⟫»(z, x)), «expr⟪ , ⟫»(z, z))) : by rw ["[", "<-", expr div_mul_eq_mul_div, "]"] []
        «expr = »(..., «expr / »(«expr * »(ℓ x, «expr⟪ , ⟫»(z, z)), «expr⟪ , ⟫»(z, z))) : by rw ["[", expr h₂, "]"] []
        «expr = »(..., ℓ x) : begin
          have [] [":", expr «expr ≠ »(«expr⟪ , ⟫»(z, z), 0)] [],
          { change [expr «expr = »(z, 0) → false] [] ["at", ident z_ne_0],
            rwa ["<-", expr inner_self_eq_zero] ["at", ident z_ne_0] },
          field_simp [] ["[", expr this, "]"] [] []
        end],
     exact [expr h₄] }
 end)

variable {E}

@[simp]
theorem to_dual_apply {x y : E} : to_dual 𝕜 E x y = ⟪x, y⟫ :=
  rfl

@[simp]
theorem to_dual_symm_apply {x : E} {y : NormedSpace.Dual 𝕜 E} : ⟪(to_dual 𝕜 E).symm y, x⟫ = y x :=
  by 
    rw [←to_dual_apply]
    simp only [LinearIsometryEquiv.apply_symm_apply]

end InnerProductSpace

