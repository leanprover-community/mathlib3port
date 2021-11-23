import Mathbin.Analysis.Calculus.Deriv 
import Mathbin.Analysis.Calculus.MeanValue 
import Mathbin.Analysis.Convex.Topology

/-!
# Symmetry of the second derivative

We show that, over the reals, the second derivative is symmetric.

The most precise result is `convex.second_derivative_within_at_symmetric`. It asserts that,
if a function is differentiable inside a convex set `s` with nonempty interior, and has a second
derivative within `s` at a point `x`, then this second derivative at `x` is symmetric. Note that
this result does not require continuity of the first derivative.

The following particular cases of this statement are especially relevant:

`second_derivative_symmetric_of_eventually` asserts that, if a function is differentiable on a
neighborhood of `x`, and has a second derivative at `x`, then this second derivative is symmetric.

`second_derivative_symmetric` asserts that, if a function is differentiable, and has a second
derivative at `x`, then this second derivative is symmetric.

## Implementation note

For the proof, we obtain an asymptotic expansion to order two of `f (x + v + w) - f (x + v)`, by
using the mean value inequality applied to a suitable function along the
segment `[x + v, x + v + w]`. This expansion involves `f'' ⬝ w` as we move along a segment directed
by `w` (see `convex.taylor_approx_two_segment`).

Consider the alternate sum `f (x + v + w) + f x - f (x + v) - f (x + w)`, corresponding to the
values of `f` along a rectangle based at `x` with sides `v` and `w`. One can write it using the two
sides directed by `w`, as `(f (x + v + w) - f (x + v)) - (f (x + w) - f x)`. Together with the
previous asymptotic expansion, one deduces that it equals `f'' v w + o(1)` when `v, w` tends to `0`.
Exchanging the roles of `v` and `w`, one instead gets an asymptotic expansion `f'' w v`, from which
the equality `f'' v w = f'' w v` follows.

In our most general statement, we only assume that `f` is differentiable inside a convex set `s`, so
a few modifications have to be made. Since we don't assume continuity of `f` at `x`, we consider
instead the rectangle based at `x + v + w` with sides `v` and `w`,
in `convex.is_o_alternate_sum_square`, but the argument is essentially the same. It only works
when `v` and `w` both point towards the interior of `s`, to make sure that all the sides of the
rectangle are contained in `s` by convexity. The general case follows by linearity, though.
-/


open Asymptotics Set

open_locale TopologicalSpace

variable{E F :
    Type
      _}[NormedGroup
      E][NormedSpace ℝ
      E][NormedGroup
      F][NormedSpace ℝ
      F]{s :
    Set
      E}(s_conv :
    Convex ℝ
      s){f :
    E →
      F}{f' :
    E →
      E →L[ℝ]
        F}{f'' :
    E →L[ℝ]
      E →L[ℝ]
        F}(hf :
    ∀ x _ : x ∈ Interior s, HasFderivAt f (f' x) x){x : E}(xs : x ∈ s)(hx : HasFderivWithinAt f' f'' (Interior s) x)

include s_conv xs hx hf

-- error in Analysis.Calculus.FderivSymmetric: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Assume that `f` is differentiable inside a convex set `s`, and that its derivative `f'` is
differentiable at a point `x`. Then, given two vectors `v` and `w` pointing inside `s`, one can
Taylor-expand to order two the function `f` on the segment `[x + h v, x + h (v + w)]`, giving a
bilinear estimate for `f (x + hv + hw) - f (x + hv)` in terms of `f' w` and of `f'' ⬝ w`, up to
`o(h^2)`.

This is a technical statement used to show that the second derivative is symmetric.
-/
theorem convex.taylor_approx_two_segment
{v w : E}
(hv : «expr ∈ »(«expr + »(x, v), interior s))
(hw : «expr ∈ »(«expr + »(«expr + »(x, v), w), interior s)) : is_o (λ
 h : exprℝ(), «expr - »(«expr - »(«expr - »(«expr - »(f «expr + »(«expr + »(x, «expr • »(h, v)), «expr • »(h, w)), f «expr + »(x, «expr • »(h, v))), «expr • »(h, f' x w)), «expr • »(«expr ^ »(h, 2), f'' v w)), «expr • »(«expr / »(«expr ^ »(h, 2), 2), f'' w w))) (λ
 h, «expr ^ »(h, 2)) «expr𝓝[ ] »(Ioi (0 : exprℝ()), 0) :=
begin
  apply [expr is_o.trans_is_O (is_o_iff.2 (λ
     ε εpos, _)) (is_O_const_mul_self «expr * »(«expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w)), «expr∥ ∥»(w)) _ _)],
  rw ["[", expr has_fderiv_within_at, ",", expr has_fderiv_at_filter, ",", expr is_o_iff, "]"] ["at", ident hx],
  rcases [expr metric.mem_nhds_within_iff.1 (hx εpos), "with", "⟨", ident δ, ",", ident δpos, ",", ident sδ, "⟩"],
  have [ident E1] [":", expr «expr∀ᶠ in , »((h), «expr𝓝[ ] »(Ioi (0 : exprℝ()), 0), «expr < »(«expr * »(h, «expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w))), δ))] [],
  { have [] [":", expr filter.tendsto (λ
      h, «expr * »(h, «expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w)))) «expr𝓝[ ] »(Ioi (0 : exprℝ()), 0) (expr𝓝() «expr * »(0, «expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w))))] [":=", expr (continuous_id.mul continuous_const).continuous_within_at],
    apply [expr (tendsto_order.1 this).2 δ],
    simpa [] [] ["only"] ["[", expr zero_mul, "]"] [] ["using", expr δpos] },
  have [ident E2] [":", expr «expr∀ᶠ in , »((h), «expr𝓝[ ] »(Ioi (0 : exprℝ()), 0), «expr < »((h : exprℝ()), 1))] [":=", expr mem_nhds_within_Ioi_iff_exists_Ioo_subset.2 ⟨(1 : exprℝ()), by simp [] [] ["only"] ["[", expr mem_Ioi, ",", expr zero_lt_one, "]"] [] [], λ
    x hx, hx.2⟩],
  filter_upwards ["[", expr E1, ",", expr E2, ",", expr self_mem_nhds_within, "]"] [],
  assume [binders (h hδ h_lt_1 hpos)],
  replace [ident hpos] [":", expr «expr < »(0, h)] [":=", expr hpos],
  have [ident xt_mem] [":", expr ∀
   t «expr ∈ » Icc (0 : exprℝ()) 1, «expr ∈ »(«expr + »(«expr + »(x, «expr • »(h, v)), «expr • »(«expr * »(t, h), w)), interior s)] [],
  { assume [binders (t ht)],
    have [] [":", expr «expr ∈ »(«expr + »(x, «expr • »(h, v)), interior s)] [":=", expr s_conv.add_smul_mem_interior xs hv ⟨hpos, h_lt_1.le⟩],
    rw ["[", "<-", expr smul_smul, "]"] [],
    apply [expr s_conv.interior.add_smul_mem this _ ht],
    rw [expr add_assoc] ["at", ident hw],
    convert [] [expr s_conv.add_smul_mem_interior xs hw ⟨hpos, h_lt_1.le⟩] ["using", 1],
    simp [] [] ["only"] ["[", expr add_assoc, ",", expr smul_add, "]"] [] [] },
  let [ident g] [] [":=", expr λ
   t, «expr - »(«expr - »(«expr - »(f «expr + »(«expr + »(x, «expr • »(h, v)), «expr • »(«expr * »(t, h), w)), «expr • »(«expr * »(t, h), f' x w)), «expr • »(«expr * »(t, «expr ^ »(h, 2)), f'' v w)), «expr • »(«expr / »(«expr ^ »(«expr * »(t, h), 2), 2), f'' w w))],
  set [] [ident g'] [] [":="] [expr λ
   t, «expr - »(«expr - »(«expr - »(f' «expr + »(«expr + »(x, «expr • »(h, v)), «expr • »(«expr * »(t, h), w)) «expr • »(h, w), «expr • »(h, f' x w)), «expr • »(«expr ^ »(h, 2), f'' v w)), «expr • »(«expr * »(t, «expr ^ »(h, 2)), f'' w w))] ["with", ident hg'],
  have [ident g_deriv] [":", expr ∀ t «expr ∈ » Icc (0 : exprℝ()) 1, has_deriv_within_at g (g' t) (Icc 0 1) t] [],
  { assume [binders (t ht)],
    apply_rules ["[", expr has_deriv_within_at.sub, ",", expr has_deriv_within_at.add, "]"],
    { refine [expr (hf _ _).comp_has_deriv_within_at _ _],
      { exact [expr xt_mem t ht] },
      apply_rules ["[", expr has_deriv_at.has_deriv_within_at, ",", expr has_deriv_at.const_add, ",", expr has_deriv_at.smul_const, ",", expr has_deriv_at_mul_const, "]"] },
    { apply_rules ["[", expr has_deriv_at.has_deriv_within_at, ",", expr has_deriv_at.smul_const, ",", expr has_deriv_at_mul_const, "]"] },
    { apply_rules ["[", expr has_deriv_at.has_deriv_within_at, ",", expr has_deriv_at.smul_const, ",", expr has_deriv_at_mul_const, "]"] },
    { suffices [ident H] [":", expr has_deriv_within_at (λ
        u, «expr • »(«expr / »(«expr ^ »(«expr * »(u, h), 2), 2), f'' w w)) «expr • »(«expr / »(«expr * »(«expr * »(((2 : exprℕ()) : exprℝ()), «expr ^ »(«expr * »(t, h), «expr - »(2, 1))), «expr * »(1, h)), 2), f'' w w) (Icc 0 1) t],
      { convert [] [expr H] ["using", 2],
        simp [] [] ["only"] ["[", expr one_mul, ",", expr nat.cast_bit0, ",", expr pow_one, ",", expr nat.cast_one, "]"] [] [],
        ring [] },
      apply_rules ["[", expr has_deriv_at.has_deriv_within_at, ",", expr has_deriv_at.smul_const, ",", expr has_deriv_at_id', ",", expr has_deriv_at.pow, ",", expr has_deriv_at.mul_const, "]"] } },
  have [ident g'_bound] [":", expr ∀
   t «expr ∈ » Ico (0 : exprℝ()) 1, «expr ≤ »(«expr∥ ∥»(g' t), «expr * »(«expr * »(ε, «expr * »(«expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w)), «expr∥ ∥»(w))), «expr ^ »(h, 2)))] [],
  { assume [binders (t ht)],
    have [ident I] [":", expr «expr ≤ »(«expr∥ ∥»(«expr + »(«expr • »(h, v), «expr • »(«expr * »(t, h), w))), «expr * »(h, «expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w))))] [":=", expr calc
       «expr ≤ »(«expr∥ ∥»(«expr + »(«expr • »(h, v), «expr • »(«expr * »(t, h), w))), «expr + »(«expr∥ ∥»(«expr • »(h, v)), «expr∥ ∥»(«expr • »(«expr * »(t, h), w)))) : norm_add_le _ _
       «expr = »(..., «expr + »(«expr * »(h, «expr∥ ∥»(v)), «expr * »(t, «expr * »(h, «expr∥ ∥»(w))))) : by simp [] [] ["only"] ["[", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr hpos.le, ",", expr abs_of_nonneg, ",", expr abs_mul, ",", expr ht.left, ",", expr mul_assoc, "]"] [] []
       «expr ≤ »(..., «expr + »(«expr * »(h, «expr∥ ∥»(v)), «expr * »(1, «expr * »(h, «expr∥ ∥»(w))))) : add_le_add (le_refl _) (mul_le_mul_of_nonneg_right ht.2.le (mul_nonneg hpos.le (norm_nonneg _)))
       «expr = »(..., «expr * »(h, «expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w)))) : by ring []],
    calc
      «expr = »(«expr∥ ∥»(g' t), «expr∥ ∥»(«expr - »(«expr - »(f' «expr + »(«expr + »(x, «expr • »(h, v)), «expr • »(«expr * »(t, h), w)), f' x), f'' «expr + »(«expr • »(h, v), «expr • »(«expr * »(t, h), w))) «expr • »(h, w))) : begin
        rw [expr hg'] [],
        have [] [":", expr «expr = »(«expr * »(h, «expr * »(t, h)), «expr * »(t, «expr * »(h, h)))] [],
        by ring [],
        simp [] [] ["only"] ["[", expr continuous_linear_map.coe_sub', ",", expr continuous_linear_map.map_add, ",", expr pow_two, ",", expr continuous_linear_map.add_apply, ",", expr pi.smul_apply, ",", expr smul_sub, ",", expr smul_add, ",", expr smul_smul, ",", "<-", expr sub_sub, ",", expr continuous_linear_map.coe_smul', ",", expr pi.sub_apply, ",", expr continuous_linear_map.map_smul, ",", expr this, "]"] [] []
      end
      «expr ≤ »(..., «expr * »(«expr∥ ∥»(«expr - »(«expr - »(f' «expr + »(«expr + »(x, «expr • »(h, v)), «expr • »(«expr * »(t, h), w)), f' x), f'' «expr + »(«expr • »(h, v), «expr • »(«expr * »(t, h), w)))), «expr∥ ∥»(«expr • »(h, w)))) : continuous_linear_map.le_op_norm _ _
      «expr ≤ »(..., «expr * »(«expr * »(ε, «expr∥ ∥»(«expr + »(«expr • »(h, v), «expr • »(«expr * »(t, h), w)))), «expr∥ ∥»(«expr • »(h, w)))) : begin
        apply [expr mul_le_mul_of_nonneg_right _ (norm_nonneg _)],
        have [ident H] [":", expr «expr ∈ »(«expr + »(«expr + »(x, «expr • »(h, v)), «expr • »(«expr * »(t, h), w)), «expr ∩ »(metric.ball x δ, interior s))] [],
        { refine [expr ⟨_, xt_mem t ⟨ht.1, ht.2.le⟩⟩],
          rw ["[", expr add_assoc, ",", expr add_mem_ball_iff_norm, "]"] [],
          exact [expr I.trans_lt hδ] },
        have [] [] [":=", expr sδ H],
        simp [] [] ["only"] ["[", expr mem_set_of_eq, "]"] [] ["at", ident this],
        convert [] [expr this] []; abel [] [] []
      end
      «expr ≤ »(..., «expr * »(«expr * »(ε, «expr + »(«expr∥ ∥»(«expr • »(h, v)), «expr∥ ∥»(«expr • »(h, w)))), «expr∥ ∥»(«expr • »(h, w)))) : begin
        apply [expr mul_le_mul_of_nonneg_right _ (norm_nonneg _)],
        apply [expr mul_le_mul_of_nonneg_left _ εpos.le],
        apply [expr (norm_add_le _ _).trans],
        refine [expr add_le_add (le_refl _) _],
        simp [] [] ["only"] ["[", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_mul, ",", expr abs_of_nonneg, ",", expr ht.1, ",", expr hpos.le, ",", expr mul_assoc, "]"] [] [],
        exact [expr mul_le_of_le_one_left (mul_nonneg hpos.le (norm_nonneg _)) ht.2.le]
      end
      «expr = »(..., «expr * »(«expr * »(ε, «expr * »(«expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w)), «expr∥ ∥»(w))), «expr ^ »(h, 2))) : by { simp [] [] ["only"] ["[", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_mul, ",", expr abs_of_nonneg, ",", expr hpos.le, "]"] [] [],
        ring [] } },
  have [ident I] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(g 1, g 0)), «expr * »(«expr * »(ε, «expr * »(«expr + »(«expr∥ ∥»(v), «expr∥ ∥»(w)), «expr∥ ∥»(w))), «expr ^ »(h, 2)))] [],
  by simpa [] [] ["only"] ["[", expr mul_one, ",", expr sub_zero, "]"] [] ["using", expr norm_image_sub_le_of_norm_deriv_le_segment' g_deriv g'_bound 1 (right_mem_Icc.2 zero_le_one)],
  convert [] [expr I] ["using", 1],
  { congr' [1] [],
    dsimp ["only"] ["[", expr g, "]"] [] [],
    simp [] [] ["only"] ["[", expr nat.one_ne_zero, ",", expr add_zero, ",", expr one_mul, ",", expr zero_div, ",", expr zero_mul, ",", expr sub_zero, ",", expr zero_smul, ",", expr ne.def, ",", expr not_false_iff, ",", expr bit0_eq_zero, ",", expr zero_pow', "]"] [] [],
    abel [] [] [] },
  { simp [] [] ["only"] ["[", expr real.norm_eq_abs, ",", expr abs_mul, ",", expr add_nonneg (norm_nonneg v) (norm_nonneg w), ",", expr abs_of_nonneg, ",", expr mul_assoc, ",", expr pow_bit0_abs, ",", expr norm_nonneg, ",", expr abs_pow, "]"] [] [] }
end

-- error in Analysis.Calculus.FderivSymmetric: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- One can get `f'' v w` as the limit of `h ^ (-2)` times the alternate sum of the values of `f`
along the vertices of a quadrilateral with sides `h v` and `h w` based at `x`.
In a setting where `f` is not guaranteed to be continuous at `f`, we can still
get this if we use a quadrilateral based at `h v + h w`. -/
theorem convex.is_o_alternate_sum_square
{v w : E}
(h4v : «expr ∈ »(«expr + »(x, «expr • »((4 : exprℝ()), v)), interior s))
(h4w : «expr ∈ »(«expr + »(x, «expr • »((4 : exprℝ()), w)), interior s)) : is_o (λ
 h : exprℝ(), «expr - »(«expr - »(«expr - »(«expr + »(f «expr + »(x, «expr • »(h, «expr + »(«expr • »(2, v), «expr • »(2, w)))), f «expr + »(x, «expr • »(h, «expr + »(v, w)))), f «expr + »(x, «expr • »(h, «expr + »(«expr • »(2, v), w)))), f «expr + »(x, «expr • »(h, «expr + »(v, «expr • »(2, w))))), «expr • »(«expr ^ »(h, 2), f'' v w))) (λ
 h, «expr ^ »(h, 2)) «expr𝓝[ ] »(Ioi (0 : exprℝ()), 0) :=
begin
  have [ident A] [":", expr «expr ∈ »(«expr / »((1 : exprℝ()), 2), Ioc (0 : exprℝ()) 1)] [":=", expr ⟨by norm_num [] [], by norm_num [] []⟩],
  have [ident B] [":", expr «expr ∈ »(«expr / »((1 : exprℝ()), 2), Icc (0 : exprℝ()) 1)] [":=", expr ⟨by norm_num [] [], by norm_num [] []⟩],
  have [ident C] [":", expr ∀
   w : E, «expr = »(«expr • »((2 : exprℝ()), w), «expr • »(2, w))] [":=", expr λ
   w, by simp [] [] ["only"] ["[", expr two_smul, "]"] [] []],
  have [ident h2v2w] [":", expr «expr ∈ »(«expr + »(«expr + »(x, «expr • »((2 : exprℝ()), v)), «expr • »((2 : exprℝ()), w)), interior s)] [],
  { convert [] [expr s_conv.interior.add_smul_sub_mem h4v h4w B] ["using", 1],
    simp [] [] ["only"] ["[", expr smul_sub, ",", expr smul_smul, ",", expr one_div, ",", expr add_sub_add_left_eq_sub, ",", expr mul_add, ",", expr add_smul, "]"] [] [],
    norm_num [] [],
    simp [] [] ["only"] ["[", expr show «expr = »((4 : exprℝ()), «expr + »((2 : exprℝ()), (2 : exprℝ()))), by norm_num [] [], ",", expr add_smul, "]"] [] [],
    abel [] [] [] },
  have [ident h2vww] [":", expr «expr ∈ »(«expr + »(«expr + »(x, «expr + »(«expr • »(2, v), w)), w), interior s)] [],
  { convert [] [expr h2v2w] ["using", 1],
    simp [] [] ["only"] ["[", expr two_smul, "]"] [] [],
    abel [] [] [] },
  have [ident h2v] [":", expr «expr ∈ »(«expr + »(x, «expr • »((2 : exprℝ()), v)), interior s)] [],
  { convert [] [expr s_conv.add_smul_sub_mem_interior xs h4v A] ["using", 1],
    simp [] [] ["only"] ["[", expr smul_smul, ",", expr one_div, ",", expr add_sub_cancel', ",", expr add_right_inj, "]"] [] [],
    norm_num [] [] },
  have [ident h2w] [":", expr «expr ∈ »(«expr + »(x, «expr • »((2 : exprℝ()), w)), interior s)] [],
  { convert [] [expr s_conv.add_smul_sub_mem_interior xs h4w A] ["using", 1],
    simp [] [] ["only"] ["[", expr smul_smul, ",", expr one_div, ",", expr add_sub_cancel', ",", expr add_right_inj, "]"] [] [],
    norm_num [] [] },
  have [ident hvw] [":", expr «expr ∈ »(«expr + »(x, «expr + »(v, w)), interior s)] [],
  { convert [] [expr s_conv.add_smul_sub_mem_interior xs h2v2w A] ["using", 1],
    simp [] [] ["only"] ["[", expr smul_smul, ",", expr one_div, ",", expr add_sub_cancel', ",", expr add_right_inj, ",", expr smul_add, ",", expr smul_sub, "]"] [] [],
    norm_num [] [],
    abel [] [] [] },
  have [ident h2vw] [":", expr «expr ∈ »(«expr + »(x, «expr + »(«expr • »(2, v), w)), interior s)] [],
  { convert [] [expr s_conv.interior.add_smul_sub_mem h2v h2v2w B] ["using", 1],
    simp [] [] ["only"] ["[", expr smul_add, ",", expr smul_sub, ",", expr smul_smul, ",", "<-", expr C, "]"] [] [],
    norm_num [] [],
    abel [] [] [] },
  have [ident hvww] [":", expr «expr ∈ »(«expr + »(«expr + »(x, «expr + »(v, w)), w), interior s)] [],
  { convert [] [expr s_conv.interior.add_smul_sub_mem h2w h2v2w B] ["using", 1],
    simp [] [] ["only"] ["[", expr one_div, ",", expr add_sub_cancel', ",", expr inv_smul_smul₀, ",", expr add_sub_add_right_eq_sub, ",", expr ne.def, ",", expr not_false_iff, ",", expr bit0_eq_zero, ",", expr one_ne_zero, "]"] [] [],
    rw [expr two_smul] [],
    abel [] [] [] },
  have [ident TA1] [] [":=", expr s_conv.taylor_approx_two_segment hf xs hx h2vw h2vww],
  have [ident TA2] [] [":=", expr s_conv.taylor_approx_two_segment hf xs hx hvw hvww],
  convert [] [expr TA1.sub TA2] [],
  ext [] [ident h] [],
  simp [] [] ["only"] ["[", expr two_smul, ",", expr smul_add, ",", "<-", expr add_assoc, ",", expr continuous_linear_map.map_add, ",", expr continuous_linear_map.add_apply, ",", expr pi.smul_apply, ",", expr continuous_linear_map.coe_smul', ",", expr continuous_linear_map.map_smul, "]"] [] [],
  abel [] [] []
end

-- error in Analysis.Calculus.FderivSymmetric: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Assume that `f` is differentiable inside a convex set `s`, and that its derivative `f'` is
differentiable at a point `x`. Then, given two vectors `v` and `w` pointing inside `s`, one
has `f'' v w = f'' w v`. Superseded by `convex.second_derivative_within_at_symmetric`, which
removes the assumption that `v` and `w` point inside `s`.
-/
theorem convex.second_derivative_within_at_symmetric_of_mem_interior
{v w : E}
(h4v : «expr ∈ »(«expr + »(x, «expr • »((4 : exprℝ()), v)), interior s))
(h4w : «expr ∈ »(«expr + »(x, «expr • »((4 : exprℝ()), w)), interior s)) : «expr = »(f'' w v, f'' v w) :=
begin
  have [ident A] [":", expr is_o (λ
    h : exprℝ(), «expr • »(«expr ^ »(h, 2), «expr - »(f'' w v, f'' v w))) (λ
    h, «expr ^ »(h, 2)) «expr𝓝[ ] »(Ioi (0 : exprℝ()), 0)] [],
  { convert [] [expr (s_conv.is_o_alternate_sum_square hf xs hx h4v h4w).sub (s_conv.is_o_alternate_sum_square hf xs hx h4w h4v)] [],
    ext [] [ident h] [],
    simp [] [] ["only"] ["[", expr add_comm, ",", expr smul_add, ",", expr smul_sub, "]"] [] [],
    abel [] [] [] },
  have [ident B] [":", expr is_o (λ
    h : exprℝ(), «expr - »(f'' w v, f'' v w)) (λ h, (1 : exprℝ())) «expr𝓝[ ] »(Ioi (0 : exprℝ()), 0)] [],
  { have [] [":", expr is_O (λ
      h : exprℝ(), «expr / »(1, «expr ^ »(h, 2))) (λ
      h, «expr / »(1, «expr ^ »(h, 2))) «expr𝓝[ ] »(Ioi (0 : exprℝ()), 0)] [":=", expr is_O_refl _ _],
    have [ident C] [] [":=", expr this.smul_is_o A],
    apply [expr C.congr' _ _],
    { filter_upwards ["[", expr self_mem_nhds_within, "]"] [],
      assume [binders (h hpos)],
      rw ["[", "<-", expr one_smul exprℝ() «expr - »(f'' w v, f'' v w), ",", expr smul_smul, ",", expr smul_smul, "]"] [],
      congr' [1] [],
      field_simp [] ["[", expr has_lt.lt.ne' hpos, "]"] [] [] },
    { filter_upwards ["[", expr self_mem_nhds_within, "]"] [],
      assume [binders (h hpos)],
      field_simp [] ["[", expr has_lt.lt.ne' hpos, ",", expr has_scalar.smul, "]"] [] [] } },
  simpa [] [] ["only"] ["[", expr sub_eq_zero, "]"] [] ["using", expr (is_o_const_const_iff (@one_ne_zero exprℝ() _ _)).1 B]
end

omit s_conv xs hx hf

-- error in Analysis.Calculus.FderivSymmetric: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is differentiable inside a convex set with nonempty interior, and has a second
derivative at a point of this convex set, then this second derivative is symmetric. -/
theorem convex.second_derivative_within_at_symmetric
{s : set E}
(s_conv : convex exprℝ() s)
(hne : (interior s).nonempty)
{f : E → F}
{f' : E → «expr →L[ ] »(E, exprℝ(), F)}
{f'' : «expr →L[ ] »(E, exprℝ(), «expr →L[ ] »(E, exprℝ(), F))}
(hf : ∀ x «expr ∈ » interior s, has_fderiv_at f (f' x) x)
{x : E}
(xs : «expr ∈ »(x, s))
(hx : has_fderiv_within_at f' f'' (interior s) x)
(v w : E) : «expr = »(f'' v w, f'' w v) :=
begin
  rcases [expr hne, "with", "⟨", ident y, ",", ident hy, "⟩"],
  obtain ["⟨", ident z, ",", ident hz, "⟩", ":", expr «expr∃ , »((z), «expr = »(z, «expr • »(«expr / »((1 : exprℝ()), 4), «expr - »(y, x)))), ":=", expr ⟨«expr • »(«expr / »((1 : exprℝ()), 4), «expr - »(y, x)), rfl⟩],
  have [ident A] [":", expr ∀
   m : E, filter.tendsto (λ
    t : exprℝ(), «expr + »(x, «expr • »((4 : exprℝ()), «expr + »(z, «expr • »(t, m))))) (expr𝓝() 0) (expr𝓝() y)] [],
  { assume [binders (m)],
    have [] [":", expr «expr = »(«expr + »(x, «expr • »((4 : exprℝ()), «expr + »(z, «expr • »((0 : exprℝ()), m)))), y)] [],
    by simp [] [] [] ["[", expr hz, "]"] [] [],
    rw ["<-", expr this] [],
    refine [expr tendsto_const_nhds.add _],
    refine [expr tendsto_const_nhds.smul _],
    refine [expr tendsto_const_nhds.add _],
    exact [expr continuous_at_id.smul continuous_at_const] },
  have [ident B] [":", expr ∀
   m : E, «expr∀ᶠ in , »((t), «expr𝓝[ ] »(Ioi (0 : exprℝ()), (0 : exprℝ())), «expr ∈ »(«expr + »(x, «expr • »((4 : exprℝ()), «expr + »(z, «expr • »(t, m)))), interior s))] [],
  { assume [binders (m)],
    apply [expr nhds_within_le_nhds],
    apply [expr A m],
    rw ["[", expr mem_interior_iff_mem_nhds, "]"] ["at", ident hy],
    exact [expr interior_mem_nhds.2 hy] },
  choose [] [ident t] [ident ts, ident tpos] ["using", expr λ m, ((B m).and self_mem_nhds_within).exists],
  have [ident C] [":", expr ∀ m : E, «expr = »(f'' m z, f'' z m)] [],
  { assume [binders (m)],
    have [] [":", expr «expr = »(f'' «expr + »(z, «expr • »(t m, m)) «expr + »(z, «expr • »(t 0, 0)), f'' «expr + »(z, «expr • »(t 0, 0)) «expr + »(z, «expr • »(t m, m)))] [":=", expr s_conv.second_derivative_within_at_symmetric_of_mem_interior hf xs hx (ts 0) (ts m)],
    simp [] [] ["only"] ["[", expr continuous_linear_map.map_add, ",", expr continuous_linear_map.map_smul, ",", expr add_right_inj, ",", expr continuous_linear_map.add_apply, ",", expr pi.smul_apply, ",", expr continuous_linear_map.coe_smul', ",", expr add_zero, ",", expr continuous_linear_map.zero_apply, ",", expr smul_zero, ",", expr continuous_linear_map.map_zero, "]"] [] ["at", ident this],
    exact [expr smul_right_injective F (tpos m).ne' this] },
  have [] [":", expr «expr = »(f'' «expr + »(z, «expr • »(t v, v)) «expr + »(z, «expr • »(t w, w)), f'' «expr + »(z, «expr • »(t w, w)) «expr + »(z, «expr • »(t v, v)))] [":=", expr s_conv.second_derivative_within_at_symmetric_of_mem_interior hf xs hx (ts w) (ts v)],
  simp [] [] ["only"] ["[", expr continuous_linear_map.map_add, ",", expr continuous_linear_map.map_smul, ",", expr smul_add, ",", expr smul_smul, ",", expr continuous_linear_map.add_apply, ",", expr pi.smul_apply, ",", expr continuous_linear_map.coe_smul', ",", expr C, "]"] [] ["at", ident this],
  rw ["<-", expr sub_eq_zero] ["at", ident this],
  abel [] [] ["at", ident this],
  simp [] [] ["only"] ["[", expr one_zsmul, ",", expr neg_smul, ",", expr sub_eq_zero, ",", expr mul_comm, ",", "<-", expr sub_eq_add_neg, "]"] [] ["at", ident this],
  apply [expr smul_right_injective F _ this],
  simp [] [] [] ["[", expr (tpos v).ne', ",", expr (tpos w).ne', "]"] [] []
end

-- error in Analysis.Calculus.FderivSymmetric: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is differentiable around `x`, and has two derivatives at `x`, then the second
derivative is symmetric. -/
theorem second_derivative_symmetric_of_eventually
{f : E → F}
{f' : E → «expr →L[ ] »(E, exprℝ(), F)}
{f'' : «expr →L[ ] »(E, exprℝ(), «expr →L[ ] »(E, exprℝ(), F))}
(hf : «expr∀ᶠ in , »((y), expr𝓝() x, has_fderiv_at f (f' y) y))
(hx : has_fderiv_at f' f'' x)
(v w : E) : «expr = »(f'' v w, f'' w v) :=
begin
  rcases [expr metric.mem_nhds_iff.1 hf, "with", "⟨", ident ε, ",", ident εpos, ",", ident hε, "⟩"],
  have [ident A] [":", expr (interior (metric.ball x ε)).nonempty] [],
  by rwa ["[", expr metric.is_open_ball.interior_eq, ",", expr metric.nonempty_ball, "]"] [],
  exact [expr convex.second_derivative_within_at_symmetric (convex_ball x ε) A (λ
    y hy, hε (interior_subset hy)) (metric.mem_ball_self εpos) hx.has_fderiv_within_at v w]
end

/-- If a function is differentiable, and has two derivatives at `x`, then the second
derivative is symmetric. -/
theorem second_derivative_symmetric {f : E → F} {f' : E → E →L[ℝ] F} {f'' : E →L[ℝ] E →L[ℝ] F}
  (hf : ∀ y, HasFderivAt f (f' y) y) (hx : HasFderivAt f' f'' x) (v w : E) : f'' v w = f'' w v :=
  second_derivative_symmetric_of_eventually (Filter.eventually_of_forall hf) hx v w

