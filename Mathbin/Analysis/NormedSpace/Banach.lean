import Mathbin.Topology.MetricSpace.Baire 
import Mathbin.Analysis.NormedSpace.OperatorNorm 
import Mathbin.Analysis.NormedSpace.AffineIsometry

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/


open Function Metric Set Filter Finset

open_locale Classical TopologicalSpace BigOperators Nnreal

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] (f : E →L[𝕜] F)

include 𝕜

namespace ContinuousLinearMap

/-- A (possibly nonlinear) right inverse to a continuous linear map, which doesn't have to be
linear itself but which satisfies a bound `∥inverse x∥ ≤ C * ∥x∥`. A surjective continuous linear
map doesn't always have a continuous linear right inverse, but it always has a nonlinear inverse
in this sense, by Banach's open mapping theorem. -/
structure nonlinear_right_inverse where 
  toFun : F → E 
  nnnorm :  ℝ≥0 
  bound' : ∀ y, ∥to_fun y∥ ≤ nnnorm*∥y∥
  right_inv' : ∀ y, f (to_fun y) = y

instance : CoeFun (nonlinear_right_inverse f) fun _ => F → E :=
  ⟨fun fsymm => fsymm.to_fun⟩

@[simp]
theorem nonlinear_right_inverse.right_inv {f : E →L[𝕜] F} (fsymm : nonlinear_right_inverse f) (y : F) :
  f (fsymm y) = y :=
  fsymm.right_inv' y

theorem nonlinear_right_inverse.bound {f : E →L[𝕜] F} (fsymm : nonlinear_right_inverse f) (y : F) :
  ∥fsymm y∥ ≤ fsymm.nnnorm*∥y∥ :=
  fsymm.bound' y

end ContinuousLinearMap

/-- Given a continuous linear equivalence, the inverse is in particular an instance of
`nonlinear_right_inverse` (which turns out to be linear). -/
noncomputable def ContinuousLinearEquiv.toNonlinearRightInverse (f : E ≃L[𝕜] F) :
  ContinuousLinearMap.NonlinearRightInverse (f : E →L[𝕜] F) :=
  { toFun := f.inv_fun, nnnorm := nnnorm (f.symm : F →L[𝕜] E),
    bound' := fun y => ContinuousLinearMap.le_op_norm (f.symm : F →L[𝕜] E) _, right_inv' := f.apply_symm_apply }

noncomputable instance (f : E ≃L[𝕜] F) : Inhabited (ContinuousLinearMap.NonlinearRightInverse (f : E →L[𝕜] F)) :=
  ⟨f.to_nonlinear_right_inverse⟩

/-! ### Proof of the Banach open mapping theorem -/


variable [CompleteSpace F]

-- error in Analysis.NormedSpace.Banach: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
First step of the proof of the Banach open mapping theorem (using completeness of `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached by
images of elements of norm at most `C * ∥y∥`.
For further use, we will only need such an element whose image
is within distance `∥y∥/2` of `y`, to apply an iterative process. -/
theorem exists_approx_preimage_norm_le
(surj : surjective f) : «expr∃ , »((C «expr ≥ » 0), ∀
 y, «expr∃ , »((x), «expr ∧ »(«expr ≤ »(dist (f x) y, «expr * »(«expr / »(1, 2), «expr∥ ∥»(y))), «expr ≤ »(«expr∥ ∥»(x), «expr * »(C, «expr∥ ∥»(y)))))) :=
begin
  have [ident A] [":", expr «expr = »(«expr⋃ , »((n : exprℕ()), closure «expr '' »(f, ball 0 n)), univ)] [],
  { refine [expr subset.antisymm (subset_univ _) (λ y hy, _)],
    rcases [expr surj y, "with", "⟨", ident x, ",", ident hx, "⟩"],
    rcases [expr exists_nat_gt «expr∥ ∥»(x), "with", "⟨", ident n, ",", ident hn, "⟩"],
    refine [expr mem_Union.2 ⟨n, subset_closure _⟩],
    refine [expr (mem_image _ _ _).2 ⟨x, ⟨_, hx⟩⟩],
    rwa ["[", expr mem_ball, ",", expr dist_eq_norm, ",", expr sub_zero, "]"] [] },
  have [] [":", expr «expr∃ , »((n : exprℕ())
    (x), «expr ∈ »(x, interior (closure «expr '' »(f, ball 0 n))))] [":=", expr nonempty_interior_of_Union_of_closed (λ
    n, is_closed_closure) A],
  simp [] [] ["only"] ["[", expr mem_interior_iff_mem_nhds, ",", expr metric.mem_nhds_iff, "]"] [] ["at", ident this],
  rcases [expr this, "with", "⟨", ident n, ",", ident a, ",", ident ε, ",", "⟨", ident εpos, ",", ident H, "⟩", "⟩"],
  rcases [expr normed_field.exists_one_lt_norm 𝕜, "with", "⟨", ident c, ",", ident hc, "⟩"],
  refine [expr ⟨«expr * »(«expr * »(«expr * »(«expr ⁻¹»(«expr / »(ε, 2)), «expr∥ ∥»(c)), 2), n), _, λ y, _⟩],
  { refine [expr mul_nonneg (mul_nonneg (mul_nonneg _ (norm_nonneg _)) (by norm_num [] [])) _],
    exacts ["[", expr inv_nonneg.2 (div_nonneg (le_of_lt εpos) (by norm_num [] [])), ",", expr n.cast_nonneg, "]"] },
  { by_cases [expr hy, ":", expr «expr = »(y, 0)],
    { use [expr 0],
      simp [] [] [] ["[", expr hy, "]"] [] [] },
    { rcases [expr rescale_to_shell hc (half_pos εpos) hy, "with", "⟨", ident d, ",", ident hd, ",", ident ydlt, ",", ident leyd, ",", ident dinv, "⟩"],
      let [ident δ] [] [":=", expr «expr / »(«expr * »(«expr∥ ∥»(d), «expr∥ ∥»(y)), 4)],
      have [ident δpos] [":", expr «expr < »(0, δ)] [":=", expr div_pos (mul_pos (norm_pos_iff.2 hd) (norm_pos_iff.2 hy)) (by norm_num [] [])],
      have [] [":", expr «expr ∈ »(«expr + »(a, «expr • »(d, y)), ball a ε)] [],
      by simp [] [] [] ["[", expr dist_eq_norm, ",", expr lt_of_le_of_lt ydlt.le (half_lt_self εpos), "]"] [] [],
      rcases [expr metric.mem_closure_iff.1 (H this) _ δpos, "with", "⟨", ident z₁, ",", ident z₁im, ",", ident h₁, "⟩"],
      rcases [expr (mem_image _ _ _).1 z₁im, "with", "⟨", ident x₁, ",", ident hx₁, ",", ident xz₁, "⟩"],
      rw ["<-", expr xz₁] ["at", ident h₁],
      rw ["[", expr mem_ball, ",", expr dist_eq_norm, ",", expr sub_zero, "]"] ["at", ident hx₁],
      have [] [":", expr «expr ∈ »(a, ball a ε)] [],
      by { simp [] [] [] [] [] [],
        exact [expr εpos] },
      rcases [expr metric.mem_closure_iff.1 (H this) _ δpos, "with", "⟨", ident z₂, ",", ident z₂im, ",", ident h₂, "⟩"],
      rcases [expr (mem_image _ _ _).1 z₂im, "with", "⟨", ident x₂, ",", ident hx₂, ",", ident xz₂, "⟩"],
      rw ["<-", expr xz₂] ["at", ident h₂],
      rw ["[", expr mem_ball, ",", expr dist_eq_norm, ",", expr sub_zero, "]"] ["at", ident hx₂],
      let [ident x] [] [":=", expr «expr - »(x₁, x₂)],
      have [ident I] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(f x, «expr • »(d, y))), «expr * »(2, δ))] [":=", expr calc
         «expr = »(«expr∥ ∥»(«expr - »(f x, «expr • »(d, y))), «expr∥ ∥»(«expr - »(«expr - »(f x₁, «expr + »(a, «expr • »(d, y))), «expr - »(f x₂, a)))) : by { congr' [1] [],
           simp [] [] ["only"] ["[", expr x, ",", expr f.map_sub, "]"] [] [],
           abel [] [] [] }
         «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr - »(f x₁, «expr + »(a, «expr • »(d, y)))), «expr∥ ∥»(«expr - »(f x₂, a)))) : norm_sub_le _ _
         «expr ≤ »(..., «expr + »(δ, δ)) : begin
           apply [expr add_le_add],
           { rw ["[", "<-", expr dist_eq_norm, ",", expr dist_comm, "]"] [],
             exact [expr le_of_lt h₁] },
           { rw ["[", "<-", expr dist_eq_norm, ",", expr dist_comm, "]"] [],
             exact [expr le_of_lt h₂] }
         end
         «expr = »(..., «expr * »(2, δ)) : (two_mul _).symm],
      have [ident J] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(f «expr • »(«expr ⁻¹»(d), x), y)), «expr * »(«expr / »(1, 2), «expr∥ ∥»(y)))] [":=", expr calc
         «expr = »(«expr∥ ∥»(«expr - »(f «expr • »(«expr ⁻¹»(d), x), y)), «expr∥ ∥»(«expr - »(«expr • »(«expr ⁻¹»(d), f x), «expr • »(«expr * »(«expr ⁻¹»(d), d), y)))) : by rwa ["[", expr f.map_smul _, ",", expr inv_mul_cancel, ",", expr one_smul, "]"] []
         «expr = »(..., «expr∥ ∥»(«expr • »(«expr ⁻¹»(d), «expr - »(f x, «expr • »(d, y))))) : by rw ["[", expr mul_smul, ",", expr smul_sub, "]"] []
         «expr = »(..., «expr * »(«expr ⁻¹»(«expr∥ ∥»(d)), «expr∥ ∥»(«expr - »(f x, «expr • »(d, y))))) : by rw ["[", expr norm_smul, ",", expr normed_field.norm_inv, "]"] []
         «expr ≤ »(..., «expr * »(«expr ⁻¹»(«expr∥ ∥»(d)), «expr * »(2, δ))) : begin
           apply [expr mul_le_mul_of_nonneg_left I],
           rw [expr inv_nonneg] [],
           exact [expr norm_nonneg _]
         end
         «expr = »(..., «expr / »(«expr * »(«expr * »(«expr ⁻¹»(«expr∥ ∥»(d)), «expr∥ ∥»(d)), «expr∥ ∥»(y)), 2)) : by { simp [] [] ["only"] ["[", expr δ, "]"] [] [],
           ring [] }
         «expr = »(..., «expr / »(«expr∥ ∥»(y), 2)) : by { rw ["[", expr inv_mul_cancel, ",", expr one_mul, "]"] [],
           simp [] [] [] ["[", expr norm_eq_zero, ",", expr hd, "]"] [] [] }
         «expr = »(..., «expr * »(«expr / »(1, 2), «expr∥ ∥»(y))) : by ring []],
      rw ["<-", expr dist_eq_norm] ["at", ident J],
      have [ident K] [":", expr «expr ≤ »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(d), x)), «expr * »(«expr * »(«expr * »(«expr * »(«expr ⁻¹»(«expr / »(ε, 2)), «expr∥ ∥»(c)), 2), «expr↑ »(n)), «expr∥ ∥»(y)))] [":=", expr calc
         «expr = »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(d), x)), «expr * »(«expr ⁻¹»(«expr∥ ∥»(d)), «expr∥ ∥»(«expr - »(x₁, x₂)))) : by rw ["[", expr norm_smul, ",", expr normed_field.norm_inv, "]"] []
         «expr ≤ »(..., «expr * »(«expr * »(«expr * »(«expr ⁻¹»(«expr / »(ε, 2)), «expr∥ ∥»(c)), «expr∥ ∥»(y)), «expr + »(n, n))) : begin
           refine [expr mul_le_mul dinv _ (norm_nonneg _) _],
           { exact [expr le_trans (norm_sub_le _ _) (add_le_add (le_of_lt hx₁) (le_of_lt hx₂))] },
           { apply [expr mul_nonneg (mul_nonneg _ (norm_nonneg _)) (norm_nonneg _)],
             exact [expr inv_nonneg.2 (le_of_lt (half_pos εpos))] }
         end
         «expr = »(..., «expr * »(«expr * »(«expr * »(«expr * »(«expr ⁻¹»(«expr / »(ε, 2)), «expr∥ ∥»(c)), 2), «expr↑ »(n)), «expr∥ ∥»(y))) : by ring []],
      exact [expr ⟨«expr • »(«expr ⁻¹»(d), x), J, K⟩] } }
end

variable [CompleteSpace E]

-- error in Analysis.NormedSpace.Banach: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Banach open mapping theorem: if a bounded linear map between Banach spaces is onto, then
any point has a preimage with controlled norm. -/
theorem exists_preimage_norm_le
(surj : surjective f) : «expr∃ , »((C «expr > » 0), ∀
 y, «expr∃ , »((x), «expr ∧ »(«expr = »(f x, y), «expr ≤ »(«expr∥ ∥»(x), «expr * »(C, «expr∥ ∥»(y)))))) :=
begin
  obtain ["⟨", ident C, ",", ident C0, ",", ident hC, "⟩", ":=", expr exists_approx_preimage_norm_le f surj],
  choose [] [ident g] [ident hg] ["using", expr hC],
  let [ident h] [] [":=", expr λ y, «expr - »(y, f (g y))],
  have [ident hle] [":", expr ∀ y, «expr ≤ »(«expr∥ ∥»(h y), «expr * »(«expr / »(1, 2), «expr∥ ∥»(y)))] [],
  { assume [binders (y)],
    rw ["[", "<-", expr dist_eq_norm, ",", expr dist_comm, "]"] [],
    exact [expr (hg y).1] },
  refine [expr ⟨«expr + »(«expr * »(2, C), 1), by linarith [] [] [], λ y, _⟩],
  have [ident hnle] [":", expr ∀
   n : exprℕ(), «expr ≤ »(«expr∥ ∥»(«expr ^[ ]»(h, n) y), «expr * »(«expr ^ »(«expr / »(1, 2), n), «expr∥ ∥»(y)))] [],
  { assume [binders (n)],
    induction [expr n] [] ["with", ident n, ident IH] [],
    { simp [] [] ["only"] ["[", expr one_div, ",", expr nat.nat_zero_eq_zero, ",", expr one_mul, ",", expr iterate_zero_apply, ",", expr pow_zero, "]"] [] [] },
    { rw ["[", expr iterate_succ', "]"] [],
      apply [expr le_trans (hle _) _],
      rw ["[", expr pow_succ, ",", expr mul_assoc, "]"] [],
      apply [expr mul_le_mul_of_nonneg_left IH],
      norm_num [] [] } },
  let [ident u] [] [":=", expr λ n, g («expr ^[ ]»(h, n) y)],
  have [ident ule] [":", expr ∀
   n, «expr ≤ »(«expr∥ ∥»(u n), «expr * »(«expr ^ »(«expr / »(1, 2), n), «expr * »(C, «expr∥ ∥»(y))))] [],
  { assume [binders (n)],
    apply [expr le_trans (hg _).2 _],
    calc
      «expr ≤ »(«expr * »(C, «expr∥ ∥»(«expr ^[ ]»(h, n) y)), «expr * »(C, «expr * »(«expr ^ »(«expr / »(1, 2), n), «expr∥ ∥»(y)))) : mul_le_mul_of_nonneg_left (hnle n) C0
      «expr = »(..., «expr * »(«expr ^ »(«expr / »(1, 2), n), «expr * »(C, «expr∥ ∥»(y)))) : by ring [] },
  have [ident sNu] [":", expr summable (λ n, «expr∥ ∥»(u n))] [],
  { refine [expr summable_of_nonneg_of_le (λ n, norm_nonneg _) ule _],
    exact [expr summable.mul_right _ (summable_geometric_of_lt_1 (by norm_num [] []) (by norm_num [] []))] },
  have [ident su] [":", expr summable u] [":=", expr summable_of_summable_norm sNu],
  let [ident x] [] [":=", expr tsum u],
  have [ident x_ineq] [":", expr «expr ≤ »(«expr∥ ∥»(x), «expr * »(«expr + »(«expr * »(2, C), 1), «expr∥ ∥»(y)))] [":=", expr calc
     «expr ≤ »(«expr∥ ∥»(x), «expr∑' , »((n), «expr∥ ∥»(u n))) : norm_tsum_le_tsum_norm sNu
     «expr ≤ »(..., «expr∑' , »((n), «expr * »(«expr ^ »(«expr / »(1, 2), n), «expr * »(C, «expr∥ ∥»(y))))) : tsum_le_tsum ule sNu (summable.mul_right _ summable_geometric_two)
     «expr = »(..., «expr * »(«expr∑' , »((n), «expr ^ »(«expr / »(1, 2), n)), «expr * »(C, «expr∥ ∥»(y)))) : tsum_mul_right
     «expr = »(..., «expr * »(«expr * »(2, C), «expr∥ ∥»(y))) : by rw ["[", expr tsum_geometric_two, ",", expr mul_assoc, "]"] []
     «expr ≤ »(..., «expr + »(«expr * »(«expr * »(2, C), «expr∥ ∥»(y)), «expr∥ ∥»(y))) : le_add_of_nonneg_right (norm_nonneg y)
     «expr = »(..., «expr * »(«expr + »(«expr * »(2, C), 1), «expr∥ ∥»(y))) : by ring []],
  have [ident fsumeq] [":", expr ∀
   n : exprℕ(), «expr = »(f «expr∑ in , »((i), range n, u i), «expr - »(y, «expr ^[ ]»(h, n) y))] [],
  { assume [binders (n)],
    induction [expr n] [] ["with", ident n, ident IH] [],
    { simp [] [] [] ["[", expr f.map_zero, "]"] [] [] },
    { rw ["[", expr sum_range_succ, ",", expr f.map_add, ",", expr IH, ",", expr iterate_succ', ",", expr sub_add, "]"] [] } },
  have [] [":", expr tendsto (λ
    n, «expr∑ in , »((i), range n, u i)) at_top (expr𝓝() x)] [":=", expr su.has_sum.tendsto_sum_nat],
  have [ident L₁] [":", expr tendsto (λ
    n, f «expr∑ in , »((i), range n, u i)) at_top (expr𝓝() (f x))] [":=", expr (f.continuous.tendsto _).comp this],
  simp [] [] ["only"] ["[", expr fsumeq, "]"] [] ["at", ident L₁],
  have [ident L₂] [":", expr tendsto (λ n, «expr - »(y, «expr ^[ ]»(h, n) y)) at_top (expr𝓝() «expr - »(y, 0))] [],
  { refine [expr tendsto_const_nhds.sub _],
    rw [expr tendsto_iff_norm_tendsto_zero] [],
    simp [] [] ["only"] ["[", expr sub_zero, "]"] [] [],
    refine [expr squeeze_zero (λ _, norm_nonneg _) hnle _],
    rw ["[", "<-", expr zero_mul «expr∥ ∥»(y), "]"] [],
    refine [expr (tendsto_pow_at_top_nhds_0_of_lt_1 _ _).mul tendsto_const_nhds]; norm_num [] [] },
  have [ident feq] [":", expr «expr = »(f x, «expr - »(y, 0))] [":=", expr tendsto_nhds_unique L₁ L₂],
  rw [expr sub_zero] ["at", ident feq],
  exact [expr ⟨x, feq, x_ineq⟩]
end

-- error in Analysis.NormedSpace.Banach: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Banach open mapping theorem: a surjective bounded linear map between Banach spaces is
open. -/ theorem open_mapping (surj : surjective f) : is_open_map f :=
begin
  assume [binders (s hs)],
  rcases [expr exists_preimage_norm_le f surj, "with", "⟨", ident C, ",", ident Cpos, ",", ident hC, "⟩"],
  refine [expr is_open_iff.2 (λ y yfs, _)],
  rcases [expr mem_image_iff_bex.1 yfs, "with", "⟨", ident x, ",", ident xs, ",", ident fxy, "⟩"],
  rcases [expr is_open_iff.1 hs x xs, "with", "⟨", ident ε, ",", ident εpos, ",", ident hε, "⟩"],
  refine [expr ⟨«expr / »(ε, C), div_pos εpos Cpos, λ z hz, _⟩],
  rcases [expr hC «expr - »(z, y), "with", "⟨", ident w, ",", ident wim, ",", ident wnorm, "⟩"],
  have [] [":", expr «expr = »(f «expr + »(x, w), z)] [],
  by { rw ["[", expr f.map_add, ",", expr wim, ",", expr fxy, ",", expr add_sub_cancel'_right, "]"] [] },
  rw ["<-", expr this] [],
  have [] [":", expr «expr ∈ »(«expr + »(x, w), ball x ε)] [":=", expr calc
     «expr = »(dist «expr + »(x, w) x, «expr∥ ∥»(w)) : by { rw [expr dist_eq_norm] [],
       simp [] [] [] [] [] [] }
     «expr ≤ »(..., «expr * »(C, «expr∥ ∥»(«expr - »(z, y)))) : wnorm
     «expr < »(..., «expr * »(C, «expr / »(ε, C))) : begin
       apply [expr mul_lt_mul_of_pos_left _ Cpos],
       rwa ["[", expr mem_ball, ",", expr dist_eq_norm, "]"] ["at", ident hz]
     end
     «expr = »(..., ε) : mul_div_cancel' _ (ne_of_gt Cpos)],
  exact [expr set.mem_image_of_mem _ (hε this)]
end

theorem open_mapping_affine {P Q : Type _} [MetricSpace P] [NormedAddTorsor E P] [MetricSpace Q] [NormedAddTorsor F Q]
  {f : P →ᵃ[𝕜] Q} (hf : Continuous f) (surj : surjective f) : IsOpenMap f :=
  by 
    rw [←AffineMap.is_open_map_linear_iff]
    exact
      open_mapping { f.linear with cont := affine_map.continuous_linear_iff.mpr hf }
        (f.surjective_iff_linear_surjective.mpr surj)

/-! ### Applications of the Banach open mapping theorem -/


namespace ContinuousLinearMap

theorem exists_nonlinear_right_inverse_of_surjective (f : E →L[𝕜] F) (hsurj : f.range = ⊤) :
  ∃ fsymm : nonlinear_right_inverse f, 0 < fsymm.nnnorm :=
  by 
    choose C hC fsymm h using exists_preimage_norm_le _ (linear_map.range_eq_top.mp hsurj)
    use { toFun := fsymm, nnnorm := ⟨C, hC.lt.le⟩, bound' := fun y => (h y).2, right_inv' := fun y => (h y).1 }
    exact hC

/-- A surjective continuous linear map between Banach spaces admits a (possibly nonlinear)
controlled right inverse. In general, it is not possible to ensure that such a right inverse
is linear (take for instance the map from `E` to `E/F` where `F` is a closed subspace of `E`
without a closed complement. Then it doesn't have a continuous linear right inverse.) -/
@[irreducible]
noncomputable def nonlinear_right_inverse_of_surjective (f : E →L[𝕜] F) (hsurj : f.range = ⊤) :
  nonlinear_right_inverse f :=
  Classical.some (exists_nonlinear_right_inverse_of_surjective f hsurj)

theorem nonlinear_right_inverse_of_surjective_nnnorm_pos (f : E →L[𝕜] F) (hsurj : f.range = ⊤) :
  0 < (nonlinear_right_inverse_of_surjective f hsurj).nnnorm :=
  by 
    rw [nonlinear_right_inverse_of_surjective]
    exact Classical.some_spec (exists_nonlinear_right_inverse_of_surjective f hsurj)

end ContinuousLinearMap

namespace LinearEquiv

/-- If a bounded linear map is a bijection, then its inverse is also a bounded linear map. -/
@[continuity]
theorem continuous_symm (e : E ≃ₗ[𝕜] F) (h : Continuous e) : Continuous e.symm :=
  by 
    rw [continuous_def]
    intro s hs 
    rw [←e.image_eq_preimage]
    rw [←e.coe_coe] at h⊢
    exact open_mapping ⟨«expr↑ » e, h⟩ e.surjective s hs

/-- Associating to a linear equivalence between Banach spaces a continuous linear equivalence when
the direct map is continuous, thanks to the Banach open mapping theorem that ensures that the
inverse map is also continuous. -/
def to_continuous_linear_equiv_of_continuous (e : E ≃ₗ[𝕜] F) (h : Continuous e) : E ≃L[𝕜] F :=
  { e with continuous_to_fun := h, continuous_inv_fun := e.continuous_symm h }

@[simp]
theorem coe_fn_to_continuous_linear_equiv_of_continuous (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
  «expr⇑ » (e.to_continuous_linear_equiv_of_continuous h) = e :=
  rfl

@[simp]
theorem coe_fn_to_continuous_linear_equiv_of_continuous_symm (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
  «expr⇑ » (e.to_continuous_linear_equiv_of_continuous h).symm = e.symm :=
  rfl

end LinearEquiv

namespace ContinuousLinearEquiv

/-- Convert a bijective continuous linear map `f : E →L[𝕜] F` between two Banach spaces
to a continuous linear equivalence. -/
noncomputable def of_bijective (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) : E ≃L[𝕜] F :=
  (LinearEquiv.ofBijective («expr↑ » f) (LinearMap.ker_eq_bot.mp hinj)
        (LinearMap.range_eq_top.mp hsurj)).toContinuousLinearEquivOfContinuous
    f.continuous

@[simp]
theorem coe_fn_of_bijective (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
  «expr⇑ » (of_bijective f hinj hsurj) = f :=
  rfl

theorem coe_of_bijective (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
  «expr↑ » (of_bijective f hinj hsurj) = f :=
  by 
    ext 
    rfl

@[simp]
theorem of_bijective_symm_apply_apply (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) (x : E) :
  (of_bijective f hinj hsurj).symm (f x) = x :=
  (of_bijective f hinj hsurj).symm_apply_apply x

@[simp]
theorem of_bijective_apply_symm_apply (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) (y : F) :
  f ((of_bijective f hinj hsurj).symm y) = y :=
  (of_bijective f hinj hsurj).apply_symm_apply y

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- Intermediate definition used to show
`continuous_linear_map.closed_complemented_range_of_is_compl_of_ker_eq_bot`.

This is `f.coprod G.subtypeL` as an `continuous_linear_equiv`. -/
noncomputable def coprod_subtypeL_equiv_of_is_compl (f : E →L[𝕜] F) {G : Submodule 𝕜 F} (h : IsCompl f.range G)
  [CompleteSpace G] (hker : f.ker = ⊥) : (E × G) ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by 
      rw [ker_coprod_of_disjoint_range]
      ·
        rw [hker, Submodule.ker_subtypeL, Submodule.prod_bot]
      ·
        rw [Submodule.range_subtypeL]
        exact h.disjoint)
    (by 
      simp only [range_coprod, h.sup_eq_top, Submodule.range_subtypeL])

theorem range_eq_map_coprod_subtypeL_equiv_of_is_compl (f : E →L[𝕜] F) {G : Submodule 𝕜 F} (h : IsCompl f.range G)
  [CompleteSpace G] (hker : f.ker = ⊥) :
  f.range =
    ((⊤ : Submodule 𝕜 E).Prod (⊥ : Submodule 𝕜 G)).map (f.coprod_subtypeL_equiv_of_is_compl h hker : E × G →ₗ[𝕜] F) :=
  by 
    rw [coprod_subtypeL_equiv_of_is_compl, _root_.coe_coe, ContinuousLinearEquiv.coe_of_bijective, coe_coprod,
      LinearMap.coprod_map_prod, Submodule.map_bot, sup_bot_eq, Submodule.map_top, range]

-- error in Analysis.NormedSpace.Banach: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem closed_complemented_range_of_is_compl_of_ker_eq_bot
(f : «expr →L[ ] »(E, 𝕜, F))
(G : submodule 𝕜 F)
(h : is_compl f.range G)
(hG : is_closed (G : set F))
(hker : «expr = »(f.ker, «expr⊥»())) : is_closed (f.range : set F) :=
begin
  haveI [] [":", expr complete_space G] [":=", expr complete_space_coe_iff_is_complete.2 hG.is_complete],
  let [ident g] [] [":=", expr coprod_subtypeL_equiv_of_is_compl f h hker],
  rw [expr congr_arg coe (range_eq_map_coprod_subtypeL_equiv_of_is_compl f h hker)] [],
  apply [expr g.to_homeomorph.is_closed_image.2],
  exact [expr is_closed_univ.prod is_closed_singleton]
end

end ContinuousLinearMap

