import Mathbin.Analysis.BoxIntegral.Basic 
import Mathbin.Analysis.BoxIntegral.Partition.Additive 
import Mathbin.Analysis.Calculus.Fderiv

/-!
# Divergence integral for Henstock-Kurzweil integral

In this file we prove the Divergence Theorem for a Henstock-Kurzweil style integral. The theorem
says the following. Let `f : ℝⁿ → Eⁿ` be a function differentiable on a closed rectangular box
`I` with derivative `f' x : ℝⁿ →L[ℝ] Eⁿ` at `x ∈ I`. Then the divergence `λ x, ∑ k, f' x eₖ k`,
where `eₖ = pi.single k 1` is the `k`-th basis vector, is integrable on `I`, and its integral is
equal to the sum of integrals of `f` over the faces of `I` taken with appropriate signs.

To make the proof work, we had to ban tagged partitions with “long and thin” boxes. More precisely,
we use the following generalization of one-dimensional Henstock-Kurzweil integral to functions
defined on a box in `ℝⁿ` (it corresponds to the value `⊥` of `box_integral.integration_params` in
the definition of `box_integral.has_integral`).

We say that `f : ℝⁿ → E` has integral `y : E` over a box `I ⊆ ℝⁿ` if for an arbitrarily small
positive `ε` and an arbitrarily large `c`, there exists a function `r : ℝⁿ → (0, ∞)` such that for
any tagged partition `π` of `I` such that

* `π` is a Henstock partition, i.e., each tag belongs to its box;
* `π` is subordinate to `r`;
* for every box of `π`, the maximum of the ratios of its sides is less than or equal to `c`,

the integral sum of `f` over `π` is `ε`-close to `y`. In case of dimension one, the last condition
trivially holds for any `c ≥ 1`, so this definition is equivalent to the standard definition of
Henstock-Kurzweil integral.

## Tags

Henstock-Kurzweil integral, integral, Stokes theorem, divergence theorem
-/


open_locale Classical BigOperators Nnreal Ennreal TopologicalSpace BoxIntegral

open continuous_linear_map(lsmul)

open Filter Set Finset Metric

noncomputable theory

universe u

variable{E : Type u}[NormedGroup E][NormedSpace ℝ E]{n : ℕ}

namespace BoxIntegral

local notation "ℝⁿ" => Finₓ n → ℝ

local notation "ℝⁿ⁺¹" => Finₓ (n+1) → ℝ

local notation "Eⁿ⁺¹" => Finₓ (n+1) → E

variable[CompleteSpace E](I : box (Finₓ (n+1))){i : Finₓ (n+1)}

open MeasureTheory

-- error in Analysis.BoxIntegral.DivergenceTheorem: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Auxiliary lemma for the divergence theorem. -/
theorem norm_volume_sub_integral_face_upper_sub_lower_smul_le
{f : «exprℝⁿ⁺¹»() → E}
{f' : «expr →L[ ] »(«exprℝⁿ⁺¹»(), exprℝ(), E)}
(hfc : continuous_on f I.Icc)
{x : «exprℝⁿ⁺¹»()}
(hxI : «expr ∈ »(x, I.Icc))
{a : E}
{ε : exprℝ()}
(h0 : «expr < »(0, ε))
(hε : ∀
 y «expr ∈ » I.Icc, «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f y, a), f' «expr - »(y, x))), «expr * »(ε, «expr∥ ∥»(«expr - »(y, x)))))
{c : «exprℝ≥0»()}
(hc : «expr ≤ »(I.distortion, c)) : «expr ≤ »(«expr∥ ∥»(«expr - »(«expr • »(«expr∏ , »((j), «expr - »(I.upper j, I.lower j)), f' (pi.single i 1)), «expr - »(integral (I.face i) «expr⊥»() «expr ∘ »(f, i.insert_nth (I.upper i)) box_additive_map.volume, integral (I.face i) «expr⊥»() «expr ∘ »(f, i.insert_nth (I.lower i)) box_additive_map.volume))), «expr * »(«expr * »(«expr * »(2, ε), c), «expr∏ , »((j), «expr - »(I.upper j, I.lower j)))) :=
begin
  have [ident Hl] [":", expr «expr ∈ »(I.lower i, Icc (I.lower i) (I.upper i))] [":=", expr set.left_mem_Icc.2 (I.lower_le_upper i)],
  have [ident Hu] [":", expr «expr ∈ »(I.upper i, Icc (I.lower i) (I.upper i))] [":=", expr set.right_mem_Icc.2 (I.lower_le_upper i)],
  have [ident Hi] [":", expr ∀
   x «expr ∈ » Icc (I.lower i) (I.upper i), integrable.{0, u, u} (I.face i) «expr⊥»() «expr ∘ »(f, i.insert_nth x) box_additive_map.volume] [],
  from [expr λ x hx, integrable_of_continuous_on _ (box.continuous_on_face_Icc hfc hx) volume],
  have [] [":", expr ∀
   y «expr ∈ » (I.face i).Icc, «expr ≤ »(«expr∥ ∥»(«expr - »(f' (pi.single i «expr - »(I.upper i, I.lower i)), «expr - »(f (i.insert_nth (I.upper i) y), f (i.insert_nth (I.lower i) y)))), «expr * »(«expr * »(2, ε), diam I.Icc))] [],
  { intros [ident y, ident hy],
    set [] [ident g] [] [":="] [expr λ y, «expr - »(«expr - »(f y, a), f' «expr - »(y, x))] ["with", ident hg],
    change [expr ∀
     y «expr ∈ » I.Icc, «expr ≤ »(«expr∥ ∥»(g y), «expr * »(ε, «expr∥ ∥»(«expr - »(y, x))))] [] ["at", ident hε],
    clear_value [ident g],
    obtain [ident rfl, ":", expr «expr = »(f, λ y, «expr + »(«expr + »(a, f' «expr - »(y, x)), g y))],
    by simp [] [] [] ["[", expr hg, "]"] [] [],
    convert_to [expr «expr ≤ »(«expr∥ ∥»(«expr - »(g (i.insert_nth (I.lower i) y), g (i.insert_nth (I.upper i) y))), _)] [],
    { congr' [1] [],
      have [] [] [":=", expr fin.insert_nth_sub_same i (I.upper i) (I.lower i) y],
      simp [] [] ["only"] ["[", "<-", expr this, ",", expr f'.map_sub, "]"] [] [],
      abel [] [] [] },
    { have [] [":", expr ∀ z «expr ∈ » Icc (I.lower i) (I.upper i), «expr ∈ »(i.insert_nth z y, I.Icc)] [],
      from [expr λ z hz, I.maps_to_insert_nth_face_Icc hz hy],
      replace [ident hε] [":", expr ∀ y «expr ∈ » I.Icc, «expr ≤ »(«expr∥ ∥»(g y), «expr * »(ε, diam I.Icc))] [],
      { intros [ident y, ident hy],
        refine [expr (hε y hy).trans (mul_le_mul_of_nonneg_left _ h0.le)],
        rw ["<-", expr dist_eq_norm] [],
        exact [expr dist_le_diam_of_mem I.is_compact_Icc.bounded hy hxI] },
      rw ["[", expr two_mul, ",", expr add_mul, "]"] [],
      exact [expr norm_sub_le_of_le (hε _ (this _ Hl)) (hε _ (this _ Hu))] } },
  calc
    «expr = »(«expr∥ ∥»(«expr - »(«expr • »(«expr∏ , »((j), «expr - »(I.upper j, I.lower j)), f' (pi.single i 1)), «expr - »(integral (I.face i) «expr⊥»() «expr ∘ »(f, i.insert_nth (I.upper i)) box_additive_map.volume, integral (I.face i) «expr⊥»() «expr ∘ »(f, i.insert_nth (I.lower i)) box_additive_map.volume))), «expr∥ ∥»(integral.{0, u, u} (I.face i) «expr⊥»() (λ
       x : fin n → exprℝ(), «expr - »(f' (pi.single i «expr - »(I.upper i, I.lower i)), «expr - »(f (i.insert_nth (I.upper i) x), f (i.insert_nth (I.lower i) x)))) box_additive_map.volume)) : begin
      rw ["[", "<-", expr integral_sub (Hi _ Hu) (Hi _ Hl), ",", "<-", expr box.volume_face_mul i, ",", expr mul_smul, ",", "<-", expr box.volume_apply, ",", "<-", expr box_additive_map.to_smul_apply, ",", "<-", expr integral_const, ",", "<-", expr box_additive_map.volume, ",", "<-", expr integral_sub (integrable_const _) ((Hi _ Hu).sub (Hi _ Hl)), "]"] [],
      simp [] [] ["only"] ["[", expr («expr ∘ »), ",", expr pi.sub_def, ",", "<-", expr f'.map_smul, ",", "<-", expr pi.single_smul', ",", expr smul_eq_mul, ",", expr mul_one, "]"] [] []
    end
    «expr ≤ »(..., «expr * »((volume (I.face i : set «exprℝⁿ»())).to_real, «expr * »(«expr * »(«expr * »(2, ε), c), «expr - »(I.upper i, I.lower i)))) : begin
      refine [expr norm_integral_le_of_le_const (λ y hy, (this y hy).trans _) volume],
      rw [expr mul_assoc «expr * »(2, ε)] [],
      exact [expr mul_le_mul_of_nonneg_left (I.diam_Icc_le_of_distortion_le i hc) (mul_nonneg zero_le_two h0.le)]
    end
    «expr = »(..., «expr * »(«expr * »(«expr * »(2, ε), c), «expr∏ , »((j), «expr - »(I.upper j, I.lower j)))) : begin
      rw ["[", "<-", expr measure.to_box_additive_apply, ",", expr box.volume_apply, ",", "<-", expr I.volume_face_mul i, "]"] [],
      ac_refl
    end
end

-- error in Analysis.BoxIntegral.DivergenceTheorem: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f : ℝⁿ⁺¹ → E` is differentiable on a closed rectangular box `I` with derivative `f'`, then
the partial derivative `λ x, f' x (pi.single i 1)` is Henstock-Kurzweil integrable with integral
equal to the difference of integrals of `f` over the faces `x i = I.upper i` and `x i = I.lower i`.

More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
we allow `f` to be non-differentiable (but still continuous) at a countable set of points.

TODO: If `n > 0`, then the condition at `x ∈ s` can be replaced by a much weaker estimate but this
requires either better integrability theorems, or usage of a filter depending on the countable set
`s` (we need to ensure that none of the faces of a partition contain a point from `s`). -/
theorem has_integral_bot_pderiv
(f : «exprℝⁿ⁺¹»() → E)
(f' : «exprℝⁿ⁺¹»() → «expr →L[ ] »(«exprℝⁿ⁺¹»(), exprℝ(), E))
(s : set «exprℝⁿ⁺¹»())
(hs : countable s)
(Hs : ∀ x «expr ∈ » s, continuous_within_at f I.Icc x)
(Hd : ∀ x «expr ∈ » «expr \ »(I.Icc, s), has_fderiv_within_at f (f' x) I.Icc x)
(i : fin «expr + »(n, 1)) : has_integral.{0, u, u} I «expr⊥»() (λ
 x, f' x (pi.single i 1)) box_additive_map.volume «expr - »(integral.{0, u, u} (I.face i) «expr⊥»() (λ
  x, f (i.insert_nth (I.upper i) x)) box_additive_map.volume, integral.{0, u, u} (I.face i) «expr⊥»() (λ
  x, f (i.insert_nth (I.lower i) x)) box_additive_map.volume) :=
begin
  have [ident Hc] [":", expr continuous_on f I.Icc] [],
  { intros [ident x, ident hx],
    by_cases [expr hxs, ":", expr «expr ∈ »(x, s)],
    exacts ["[", expr Hs x hxs, ",", expr (Hd x ⟨hx, hxs⟩).continuous_within_at, "]"] },
  set [] [ident fI] [":", expr exprℝ() → box (fin n) → E] [":="] [expr λ
   y J, integral.{0, u, u} J «expr⊥»() (λ x, f (i.insert_nth y x)) box_additive_map.volume] [],
  set [] [ident fb] [":", expr Icc (I.lower i) (I.upper i) → «expr →ᵇᵃ[ ] »(fin n, «expr↑ »(I.face i), E)] [":="] [expr λ
   x, (integrable_of_continuous_on «expr⊥»() (box.continuous_on_face_Icc Hc x.2) volume).to_box_additive] [],
  set [] [ident F] [":", expr «expr →ᵇᵃ[ ] »(fin «expr + »(n, 1), I, E)] [":="] [expr box_additive_map.upper_sub_lower I i fI fb (λ
    x hx J, rfl)] [],
  change [expr has_integral I «expr⊥»() (λ x, f' x (pi.single i 1)) _ (F I)] [] [],
  refine [expr has_integral_of_le_Henstock_of_forall_is_o bot_le _ _ _ s hs _ _],
  { exact [expr (volume : measure «exprℝⁿ⁺¹»()).to_box_additive.restrict _ le_top] },
  { exact [expr λ J, ennreal.to_real_nonneg] },
  { intros [ident c, ident x, ident hx, ident ε, ident ε0],
    have [] [":", expr «expr∀ᶠ in , »((δ), «expr𝓝[ ] »(Ioi 0, (0 : exprℝ())), «expr ∧ »(«expr ∈ »(δ, Ioc (0 : exprℝ()) «expr / »(1, 2)), «expr ∧ »(∀
        y₁
        y₂ «expr ∈ » «expr ∩ »(closed_ball x δ, I.Icc), «expr ≤ »(«expr∥ ∥»(«expr - »(f y₁, f y₂)), «expr / »(ε, 2)), «expr ≤ »(«expr * »(«expr ^ »(«expr * »(2, δ), «expr + »(n, 1)), «expr∥ ∥»(f' x (pi.single i 1))), «expr / »(ε, 2)))))] [],
    { refine [expr eventually.and _ (eventually.and _ _)],
      { exact [expr Ioc_mem_nhds_within_Ioi ⟨le_rfl, one_half_pos⟩] },
      { rcases [expr ((nhds_within_has_basis nhds_basis_closed_ball _).tendsto_iff nhds_basis_closed_ball).1 (Hs x hx.2) _ «expr $ »(half_pos, half_pos ε0), "with", "⟨", ident δ₁, ",", ident δ₁0, ",", ident hδ₁, "⟩"],
        filter_upwards ["[", expr Ioc_mem_nhds_within_Ioi ⟨le_rfl, δ₁0⟩, "]"] [],
        rintro [ident δ, ident hδ, ident y₁, ident y₂, ident hy₁, ident hy₂],
        have [] [":", expr «expr ⊆ »(«expr ∩ »(closed_ball x δ, I.Icc), «expr ∩ »(closed_ball x δ₁, I.Icc))] [],
        from [expr inter_subset_inter_left _ (closed_ball_subset_closed_ball hδ.2)],
        rw ["<-", expr dist_eq_norm] [],
        calc
          «expr ≤ »(dist (f y₁) (f y₂), «expr + »(dist (f y₁) (f x), dist (f y₂) (f x))) : dist_triangle_right _ _ _
          «expr ≤ »(..., «expr + »(«expr / »(«expr / »(ε, 2), 2), «expr / »(«expr / »(ε, 2), 2))) : add_le_add «expr $ »(hδ₁ _, this hy₁) «expr $ »(hδ₁ _, this hy₂)
          «expr = »(..., «expr / »(ε, 2)) : add_halves _ },
      { have [] [":", expr continuous_within_at (λ
          δ, «expr * »(«expr ^ »(«expr * »(2, δ), «expr + »(n, 1)), «expr∥ ∥»(f' x (pi.single i 1)))) (Ioi (0 : exprℝ())) 0] [":=", expr ((continuous_within_at_id.const_mul _).pow _).mul_const _],
        refine [expr this.eventually (ge_mem_nhds _)],
        simpa [] [] [] [] [] ["using", expr half_pos ε0] } },
    rcases [expr this.exists, "with", "⟨", ident δ, ",", "⟨", ident hδ0, ",", ident hδ12, "⟩", ",", ident hdfδ, ",", ident hδ, "⟩"],
    refine [expr ⟨δ, hδ0, λ J hJI hJδ hxJ hJc, «expr ▸ »(add_halves ε, _)⟩],
    have [ident Hl] [":", expr «expr ∈ »(J.lower i, Icc (J.lower i) (J.upper i))] [":=", expr set.left_mem_Icc.2 (J.lower_le_upper i)],
    have [ident Hu] [":", expr «expr ∈ »(J.upper i, Icc (J.lower i) (J.upper i))] [":=", expr set.right_mem_Icc.2 (J.lower_le_upper i)],
    have [ident Hi] [":", expr ∀
     x «expr ∈ » Icc (J.lower i) (J.upper i), integrable.{0, u, u} (J.face i) «expr⊥»() (λ
      y, f (i.insert_nth x y)) box_additive_map.volume] [],
    from [expr λ
     x
     hx, integrable_of_continuous_on _ (box.continuous_on_face_Icc «expr $ »(Hc.mono, box.le_iff_Icc.1 hJI) hx) volume],
    have [ident hJδ'] [":", expr «expr ⊆ »(J.Icc, «expr ∩ »(closed_ball x δ, I.Icc))] [],
    from [expr subset_inter hJδ (box.le_iff_Icc.1 hJI)],
    have [ident Hmaps] [":", expr ∀
     z «expr ∈ » Icc (J.lower i) (J.upper i), maps_to (i.insert_nth z) (J.face i).Icc «expr ∩ »(closed_ball x δ, I.Icc)] [],
    from [expr λ z hz, (J.maps_to_insert_nth_face_Icc hz).mono subset.rfl hJδ'],
    simp [] [] ["only"] ["[", expr dist_eq_norm, ",", expr F, ",", expr fI, "]"] [] [],
    dsimp [] [] [] [],
    rw ["[", "<-", expr integral_sub (Hi _ Hu) (Hi _ Hl), "]"] [],
    refine [expr (norm_sub_le _ _).trans (add_le_add _ _)],
    { simp_rw ["[", expr box_additive_map.volume_apply, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_prod, "]"] [],
      refine [expr «expr $ »(mul_le_mul_of_nonneg_right _, norm_nonneg _).trans hδ],
      have [] [":", expr ∀ j, «expr ≤ »(«expr| |»(«expr - »(J.upper j, J.lower j)), «expr * »(2, δ))] [],
      { intro [ident j],
        calc
          «expr ≤ »(dist (J.upper j) (J.lower j), dist J.upper J.lower) : dist_le_pi_dist _ _ _
          «expr ≤ »(..., «expr + »(dist J.upper x, dist J.lower x)) : dist_triangle_right _ _ _
          «expr ≤ »(..., «expr + »(δ, δ)) : add_le_add (hJδ J.upper_mem_Icc) (hJδ J.lower_mem_Icc)
          «expr = »(..., «expr * »(2, δ)) : (two_mul δ).symm },
      calc
        «expr ≤ »(«expr∏ , »((j), «expr| |»(«expr - »(J.upper j, J.lower j))), «expr∏ , »((j : fin «expr + »(n, 1)), «expr * »(2, δ))) : prod_le_prod (λ
         _ _, abs_nonneg _) (λ j hj, this j)
        «expr = »(..., «expr ^ »(«expr * »(2, δ), «expr + »(n, 1))) : by simp [] [] [] [] [] [] },
    { refine [expr (norm_integral_le_of_le_const (λ y hy, hdfδ _ _ (Hmaps _ Hu hy) (Hmaps _ Hl hy)) _).trans _],
      refine [expr (mul_le_mul_of_nonneg_right _ (half_pos ε0).le).trans_eq (one_mul _)],
      rw ["[", expr box.coe_eq_pi, ",", expr real.volume_pi_Ioc_to_real (box.lower_le_upper _), "]"] [],
      refine [expr prod_le_one (λ _ _, «expr $ »(sub_nonneg.2, box.lower_le_upper _ _)) (λ j hj, _)],
      calc
        «expr ≤ »(«expr - »(J.upper (i.succ_above j), J.lower (i.succ_above j)), dist (J.upper (i.succ_above j)) (J.lower (i.succ_above j))) : le_abs_self _
        «expr ≤ »(..., dist J.upper J.lower) : dist_le_pi_dist J.upper J.lower (i.succ_above j)
        «expr ≤ »(..., «expr + »(dist J.upper x, dist J.lower x)) : dist_triangle_right _ _ _
        «expr ≤ »(..., «expr + »(δ, δ)) : add_le_add (hJδ J.upper_mem_Icc) (hJδ J.lower_mem_Icc)
        «expr ≤ »(..., «expr + »(«expr / »(1, 2), «expr / »(1, 2))) : add_le_add hδ12 hδ12
        «expr = »(..., 1) : add_halves 1 } },
  { intros [ident c, ident x, ident hx, ident ε, ident ε0],
    rcases [expr exists_pos_mul_lt ε0 «expr * »(2, c), "with", "⟨", ident ε', ",", ident ε'0, ",", ident hlt, "⟩"],
    rcases [expr (nhds_within_has_basis nhds_basis_closed_ball _).mem_iff.1 ((Hd x hx).def ε'0), "with", "⟨", ident δ, ",", ident δ0, ",", ident Hδ, "⟩"],
    refine [expr ⟨δ, δ0, λ J hle hJδ hxJ hJc, _⟩],
    simp [] [] ["only"] ["[", expr box_additive_map.volume_apply, ",", expr box.volume_apply, ",", expr dist_eq_norm, "]"] [] [],
    refine [expr (norm_volume_sub_integral_face_upper_sub_lower_smul_le _ «expr $ »(Hc.mono, box.le_iff_Icc.1 hle) hxJ ε'0 (λ
       y hy, Hδ _) (hJc rfl)).trans _],
    { exact [expr ⟨hJδ hy, box.le_iff_Icc.1 hle hy⟩] },
    { rw ["[", expr mul_right_comm (2 : exprℝ()), ",", "<-", expr box.volume_apply, "]"] [],
      exact [expr mul_le_mul_of_nonneg_right hlt.le ennreal.to_real_nonneg] } }
end

/-- Divergence theorem for a Henstock-Kurzweil style integral.

If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a closed rectangular box `I` with derivative `f'`, then
the divergence `∑ i, f' x (pi.single i 1) i` is Henstock-Kurzweil integrable with integral equal to
the sum of integrals of `f` over the faces of `I` taken with appropriate signs.

More precisely, we use a non-standard generalization of the Henstock-Kurzweil integral and
we allow `f` to be non-differentiable (but still continuous) at a countable set of points. -/
theorem has_integral_bot_divergence_of_forall_has_deriv_within_at (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹)
  (s : Set ℝⁿ⁺¹) (hs : countable s) (Hs : ∀ x (_ : x ∈ s), ContinuousWithinAt f I.Icc x)
  (Hd : ∀ x (_ : x ∈ I.Icc \ s), HasFderivWithinAt f (f' x) I.Icc x) :
  has_integral.{0, u, u} I ⊥ (fun x => ∑i, f' x (Pi.single i 1) i) box_additive_map.volume
    (∑i,
      integral.{0, u, u} (I.face i) ⊥ (fun x => f (i.insert_nth (I.upper i) x) i) box_additive_map.volume -
        integral.{0, u, u} (I.face i) ⊥ (fun x => f (i.insert_nth (I.lower i) x) i) box_additive_map.volume) :=
  by 
    refine' has_integral_sum fun i hi => _ 
    clear hi 
    simp only [has_fderiv_within_at_pi', continuous_within_at_pi] at Hd Hs 
    convert has_integral_bot_pderiv I _ _ s hs (fun x hx => Hs x hx i) (fun x hx => Hd x hx i) i

end BoxIntegral

