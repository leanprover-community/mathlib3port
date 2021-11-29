import Mathbin.Analysis.Calculus.TimesContDiff 
import Mathbin.Tactic.RingExp 
import Mathbin.Analysis.NormedSpace.Banach 
import Mathbin.Topology.LocalHomeomorph

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `has_strict_deriv_at.to_local_homeomorph` that repacks a function `f`
with a `hf : has_strict_fderiv_at f f' a`, `f' : E ≃L[𝕜] F`, into a `local_homeomorph`.
The `to_fun` of this `local_homeomorph` is `defeq` to `f`, so one can apply theorems
about `local_homeomorph` to `hf.to_local_homeomorph f`, and get statements about `f`.

Then we define `has_strict_fderiv_at.local_inverse` to be the `inv_fun` of this `local_homeomorph`,
and prove two versions of the inverse function theorem:

* `has_strict_fderiv_at.to_local_inverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.local_inverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `has_strict_fderiv_at.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

In the one-dimensional case we reformulate these theorems in terms of `has_strict_deriv_at` and
`f'⁻¹`.

We also reformulate the theorems in terms of `times_cont_diff`, to give that `C^k` (respectively,
smooth) inputs give `C^k` (smooth) inverses.  These versions require that continuous
differentiability implies strict differentiability; this is false over a general field, true over
`ℝ` or `ℂ` and implemented here assuming `is_R_or_C 𝕂`.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in `fderiv.lean`, `deriv.lean`, and `times_cont_diff.lean`.

## Notations

In the section about `approximates_linear_on` we introduce some `local notation` to make formulas
shorter:

* by `N` we denote `∥f'⁻¹∥`;
* by `g` we denote the auxiliary contracting map `x ↦ x + f'.symm (y - f x)` used to prove that
  `{x | f x = y}` is nonempty.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/


open Function Set Filter Metric

open_locale TopologicalSpace Classical Nnreal

noncomputable theory

variable{𝕜 : Type _}[NondiscreteNormedField 𝕜]

variable{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]

variable{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]

variable{G : Type _}[NormedGroup G][NormedSpace 𝕜 G]

variable{G' : Type _}[NormedGroup G'][NormedSpace 𝕜 G']

variable{ε : ℝ}

open Asymptotics Filter Metric Set

open continuous_linear_map(id)

/-!
### Non-linear maps close to affine maps

In this section we study a map `f` such that `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` on an open set
`s`, where `f' : E →L[𝕜] F` is a continuous linear map and `c` is suitably small. Maps of this type
behave like `f a + f' (x - a)` near each `a ∈ s`.

When `f'` is onto, we show that `f` is locally onto.

When `f'` is a continuous linear equiv, we show that `f` is a homeomorphism
between `s` and `f '' s`. More precisely, we define `approximates_linear_on.to_local_homeomorph` to
be a `local_homeomorph` with `to_fun = f`, `source = s`, and `target = f '' s`.

Maps of this type naturally appear in the proof of the inverse function theorem (see next section),
and `approximates_linear_on.to_local_homeomorph` will imply that the locally inverse function
exists.

We define this auxiliary notion to split the proof of the inverse function theorem into small
lemmas. This approach makes it possible

- to prove a lower estimate on the size of the domain of the inverse function;

- to reuse parts of the proofs in the case if a function is not strictly differentiable. E.g., for a
  function `f : E × F → G` with estimates on `f x y₁ - f x y₂` but not on `f x₁ y - f x₂ y`.
-/


/-- We say that `f` approximates a continuous linear map `f'` on `s` with constant `c`,
if `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` whenever `x, y ∈ s`.

This predicate is defined to facilitate the splitting of the inverse function theorem into small
lemmas. Some of these lemmas can be useful, e.g., to prove that the inverse function is defined
on a specific set. -/
def ApproximatesLinearOn (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (c :  ℝ≥0 ) : Prop :=
  ∀ x (_ : x ∈ s) y (_ : y ∈ s), ∥f x - f y - f' (x - y)∥ ≤ c*∥x - y∥

namespace ApproximatesLinearOn

variable[cs : CompleteSpace E]{f : E → F}

/-! First we prove some properties of a function that `approximates_linear_on` a (not necessarily
invertible) continuous linear map. -/


section 

variable{f' : E →L[𝕜] F}{s t : Set E}{c c' :  ℝ≥0 }

theorem mono_num (hc : c ≤ c') (hf : ApproximatesLinearOn f f' s c) : ApproximatesLinearOn f f' s c' :=
  fun x hx y hy => le_transₓ (hf x hx y hy) (mul_le_mul_of_nonneg_right hc$ norm_nonneg _)

theorem mono_set (hst : s ⊆ t) (hf : ApproximatesLinearOn f f' t c) : ApproximatesLinearOn f f' s c :=
  fun x hx y hy => hf x (hst hx) y (hst hy)

-- error in Analysis.Calculus.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem lipschitz_sub (hf : approximates_linear_on f f' s c) : lipschitz_with c (λ x : s, «expr - »(f x, f' x)) :=
begin
  refine [expr lipschitz_with.of_dist_le_mul (λ x y, _)],
  rw ["[", expr dist_eq_norm, ",", expr subtype.dist_eq, ",", expr dist_eq_norm, "]"] [],
  convert [] [expr hf x x.2 y y.2] ["using", 2],
  rw ["[", expr f'.map_sub, "]"] [],
  abel [] [] []
end

protected theorem lipschitz (hf : ApproximatesLinearOn f f' s c) : LipschitzWith (nnnorm f'+c) (s.restrict f) :=
  by 
    simpa only [restrict_apply, add_sub_cancel'_right] using (f'.lipschitz.restrict s).add hf.lipschitz_sub

protected theorem Continuous (hf : ApproximatesLinearOn f f' s c) : Continuous (s.restrict f) :=
  hf.lipschitz.continuous

protected theorem ContinuousOn (hf : ApproximatesLinearOn f f' s c) : ContinuousOn f s :=
  continuous_on_iff_continuous_restrict.2 hf.continuous

end 

section LocallyOnto

/-!
We prove that a function which is linearly approximated by a continuous linear map with a nonlinear
right inverse is locally onto. This will apply to the case where the approximating map is a linear
equivalence, for the local inverse theorem, but also whenever the approximating map is onto,
by Banach's open mapping theorem. -/


include cs

variable{s : Set E}{c :  ℝ≥0 }{f' : E →L[𝕜] F}

-- error in Analysis.Calculus.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is linearly approximated by a continuous linear map with a (possibly nonlinear)
right inverse, then it is locally onto: a ball of an explicit radius is included in the image
of the map. -/
theorem surj_on_closed_ball_of_nonlinear_right_inverse
(hf : approximates_linear_on f f' s c)
(f'symm : f'.nonlinear_right_inverse)
{ε : exprℝ()}
{b : E}
(ε0 : «expr ≤ »(0, ε))
(hε : «expr ⊆ »(closed_ball b ε, s)) : surj_on f (closed_ball b ε) (closed_ball (f b) «expr * »(«expr - »(«expr ⁻¹»((f'symm.nnnorm : exprℝ())), c), ε)) :=
begin
  assume [binders (y hy)],
  cases [expr le_or_lt «expr ⁻¹»((f'symm.nnnorm : exprℝ())) c] ["with", ident hc, ident hc],
  { refine [expr ⟨b, by simp [] [] [] ["[", expr ε0, "]"] [] [], _⟩],
    have [] [":", expr «expr ≤ »(dist y (f b), 0)] [":=", expr (mem_closed_ball.1 hy).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith [] [] []) ε0)],
    simp [] [] ["only"] ["[", expr dist_le_zero, "]"] [] ["at", ident this],
    rw [expr this] [] },
  have [ident If'] [":", expr «expr < »((0 : exprℝ()), f'symm.nnnorm)] [],
  by { rw ["[", "<-", expr inv_pos, "]"] [],
    exact [expr (nnreal.coe_nonneg _).trans_lt hc] },
  have [ident Icf'] [":", expr «expr < »(«expr * »((c : exprℝ()), f'symm.nnnorm), 1)] [],
  by rwa ["[", expr inv_eq_one_div, ",", expr lt_div_iff If', "]"] ["at", ident hc],
  have [ident Jf'] [":", expr «expr ≠ »((f'symm.nnnorm : exprℝ()), 0)] [":=", expr ne_of_gt If'],
  have [ident Jcf'] [":", expr «expr ≠ »(«expr - »((1 : exprℝ()), «expr * »(c, f'symm.nnnorm)), 0)] [],
  by { apply [expr ne_of_gt],
    linarith [] [] [] },
  set [] [ident g] [] [":="] [expr λ x, «expr + »(x, f'symm «expr - »(y, f x))] ["with", ident hg],
  set [] [ident u] [] [":="] [expr λ n : exprℕ(), «expr ^[ ]»(g, n) b] ["with", ident hu],
  have [ident usucc] [":", expr ∀ n, «expr = »(u «expr + »(n, 1), g (u n))] [],
  by simp [] [] [] ["[", expr hu, ",", "<-", expr iterate_succ_apply' g _ b, "]"] [] [],
  have [ident A] [":", expr ∀ z, «expr ≤ »(dist (g z) z, «expr * »(f'symm.nnnorm, dist (f z) y))] [],
  { assume [binders (z)],
    rw ["[", expr dist_eq_norm, ",", expr hg, ",", expr add_sub_cancel', ",", expr dist_eq_norm', "]"] [],
    exact [expr f'symm.bound _] },
  have [ident B] [":", expr ∀
   z «expr ∈ » closed_ball b ε, «expr ∈ »(g z, closed_ball b ε) → «expr ≤ »(dist (f (g z)) y, «expr * »(«expr * »(c, f'symm.nnnorm), dist (f z) y))] [],
  { assume [binders (z hz hgz)],
    set [] [ident v] [] [":="] [expr f'symm «expr - »(y, f z)] ["with", ident hv],
    calc
      «expr = »(dist (f (g z)) y, «expr∥ ∥»(«expr - »(f «expr + »(z, v), y))) : by rw ["[", expr dist_eq_norm, "]"] []
      «expr = »(..., «expr∥ ∥»(«expr - »(«expr + »(«expr - »(«expr - »(f «expr + »(z, v), f z), f' v), f' v), «expr - »(y, f z)))) : by { congr' [1] [],
        abel [] [] [] }
      «expr = »(..., «expr∥ ∥»(«expr - »(«expr - »(f «expr + »(z, v), f z), f' «expr - »(«expr + »(z, v), z)))) : by simp [] [] ["only"] ["[", expr continuous_linear_map.nonlinear_right_inverse.right_inv, ",", expr add_sub_cancel', ",", expr sub_add_cancel, "]"] [] []
      «expr ≤ »(..., «expr * »(c, «expr∥ ∥»(«expr - »(«expr + »(z, v), z)))) : hf _ (hε hgz) _ (hε hz)
      «expr ≤ »(..., «expr * »(c, «expr * »(f'symm.nnnorm, dist (f z) y))) : begin
        apply [expr mul_le_mul_of_nonneg_left _ (nnreal.coe_nonneg c)],
        simpa [] [] [] ["[", expr hv, ",", expr dist_eq_norm', "]"] [] ["using", expr f'symm.bound «expr - »(y, f z)]
      end
      «expr = »(..., «expr * »(«expr * »(c, f'symm.nnnorm), dist (f z) y)) : by ring [] },
  have [ident C] [":", expr ∀
   (n : exprℕ())
   (w : E), «expr ≤ »(dist w b, «expr * »(«expr / »(«expr * »(f'symm.nnnorm, «expr - »(1, «expr ^ »(«expr * »(c, f'symm.nnnorm), n))), «expr - »(1, «expr * »(c, f'symm.nnnorm))), dist (f b) y)) → «expr ∈ »(w, closed_ball b ε)] [],
  { assume [binders (n w hw)],
    apply [expr hw.trans],
    rw ["[", expr div_mul_eq_mul_div, ",", expr div_le_iff, "]"] [],
    swap,
    { linarith [] [] [] },
    calc
      «expr = »(«expr * »(«expr * »((f'symm.nnnorm : exprℝ()), «expr - »(1, «expr ^ »(«expr * »(c, f'symm.nnnorm), n))), dist (f b) y), «expr * »(«expr * »(f'symm.nnnorm, dist (f b) y), «expr - »(1, «expr ^ »(«expr * »(c, f'symm.nnnorm), n)))) : by ring []
      «expr ≤ »(..., «expr * »(«expr * »(f'symm.nnnorm, dist (f b) y), 1)) : begin
        apply [expr mul_le_mul_of_nonneg_left _ (mul_nonneg (nnreal.coe_nonneg _) dist_nonneg)],
        rw ["[", expr sub_le_self_iff, "]"] [],
        exact [expr pow_nonneg (mul_nonneg (nnreal.coe_nonneg _) (nnreal.coe_nonneg _)) _]
      end
      «expr ≤ »(..., «expr * »(f'symm.nnnorm, «expr * »(«expr - »(«expr ⁻¹»((f'symm.nnnorm : exprℝ())), c), ε))) : by { rw ["[", expr mul_one, "]"] [],
        exact [expr mul_le_mul_of_nonneg_left (mem_closed_ball'.1 hy) (nnreal.coe_nonneg _)] }
      «expr = »(..., «expr * »(ε, «expr - »(1, «expr * »(c, f'symm.nnnorm)))) : by { field_simp [] [] [] [],
        ring [] } },
  have [ident D] [":", expr ∀
   n : exprℕ(), «expr ∧ »(«expr ≤ »(dist (f (u n)) y, «expr * »(«expr ^ »(«expr * »(c, f'symm.nnnorm), n), dist (f b) y)), «expr ≤ »(dist (u n) b, «expr * »(«expr / »(«expr * »(f'symm.nnnorm, «expr - »(1, «expr ^ »(«expr * »(c, f'symm.nnnorm), n))), «expr - »(1, «expr * »(c, f'symm.nnnorm))), dist (f b) y)))] [],
  { assume [binders (n)],
    induction [expr n] [] ["with", ident n, ident IH] [],
    { simp [] [] [] ["[", expr hu, ",", expr le_refl, "]"] [] [] },
    rw [expr usucc] [],
    have [ident Ign] [":", expr «expr ≤ »(dist (g (u n)) b, «expr * »(«expr / »(«expr * »(f'symm.nnnorm, «expr - »(1, «expr ^ »(«expr * »(c, f'symm.nnnorm), n.succ))), «expr - »(1, «expr * »(c, f'symm.nnnorm))), dist (f b) y))] [":=", expr calc
       «expr ≤ »(dist (g (u n)) b, «expr + »(dist (g (u n)) (u n), dist (u n) b)) : dist_triangle _ _ _
       «expr ≤ »(..., «expr + »(«expr * »(f'symm.nnnorm, dist (f (u n)) y), dist (u n) b)) : add_le_add (A _) (le_refl _)
       «expr ≤ »(..., «expr + »(«expr * »(f'symm.nnnorm, «expr * »(«expr ^ »(«expr * »(c, f'symm.nnnorm), n), dist (f b) y)), «expr * »(«expr / »(«expr * »(f'symm.nnnorm, «expr - »(1, «expr ^ »(«expr * »(c, f'symm.nnnorm), n))), «expr - »(1, «expr * »(c, f'symm.nnnorm))), dist (f b) y))) : add_le_add (mul_le_mul_of_nonneg_left IH.1 (nnreal.coe_nonneg _)) IH.2
       «expr = »(..., «expr * »(«expr / »(«expr * »(f'symm.nnnorm, «expr - »(1, «expr ^ »(«expr * »(c, f'symm.nnnorm), n.succ))), «expr - »(1, «expr * »(c, f'symm.nnnorm))), dist (f b) y)) : by { field_simp [] ["[", expr Jcf', "]"] [] [],
         ring_exp [] [] }],
    refine [expr ⟨_, Ign⟩],
    calc
      «expr ≤ »(dist (f (g (u n))) y, «expr * »(«expr * »(c, f'symm.nnnorm), dist (f (u n)) y)) : B _ (C n _ IH.2) (C n.succ _ Ign)
      «expr ≤ »(..., «expr * »(«expr * »(c, f'symm.nnnorm), «expr * »(«expr ^ »(«expr * »(c, f'symm.nnnorm), n), dist (f b) y))) : mul_le_mul_of_nonneg_left IH.1 (mul_nonneg (nnreal.coe_nonneg _) (nnreal.coe_nonneg _))
      «expr = »(..., «expr * »(«expr ^ »(«expr * »(c, f'symm.nnnorm), n.succ), dist (f b) y)) : by ring_exp [] [] },
  have [] [":", expr cauchy_seq u] [],
  { have [] [":", expr ∀
     n : exprℕ(), «expr ≤ »(dist (u n) (u «expr + »(n, 1)), «expr * »(«expr * »(f'symm.nnnorm, dist (f b) y), «expr ^ »(«expr * »(c, f'symm.nnnorm), n)))] [],
    { assume [binders (n)],
      calc
        «expr = »(dist (u n) (u «expr + »(n, 1)), dist (g (u n)) (u n)) : by rw ["[", expr usucc, ",", expr dist_comm, "]"] []
        «expr ≤ »(..., «expr * »(f'symm.nnnorm, dist (f (u n)) y)) : A _
        «expr ≤ »(..., «expr * »(f'symm.nnnorm, «expr * »(«expr ^ »(«expr * »(c, f'symm.nnnorm), n), dist (f b) y))) : mul_le_mul_of_nonneg_left (D n).1 (nnreal.coe_nonneg _)
        «expr = »(..., «expr * »(«expr * »(f'symm.nnnorm, dist (f b) y), «expr ^ »(«expr * »(c, f'symm.nnnorm), n))) : by ring [] },
    exact [expr cauchy_seq_of_le_geometric _ _ Icf' this] },
  obtain ["⟨", ident x, ",", ident hx, "⟩", ":", expr «expr∃ , »((x), tendsto u at_top (expr𝓝() x)), ":=", expr cauchy_seq_tendsto_of_complete this],
  have [ident xmem] [":", expr «expr ∈ »(x, closed_ball b ε)] [":=", expr is_closed_ball.mem_of_tendsto hx (eventually_of_forall (λ
     n, C n _ (D n).2))],
  refine [expr ⟨x, xmem, _⟩],
  have [ident hx'] [":", expr tendsto u at_top «expr𝓝[ ] »(closed_ball b ε, x)] [],
  { simp [] [] ["only"] ["[", expr nhds_within, ",", expr tendsto_inf, ",", expr hx, ",", expr true_and, ",", expr ge_iff_le, ",", expr tendsto_principal, "]"] [] [],
    exact [expr eventually_of_forall (λ n, C n _ (D n).2)] },
  have [ident T1] [":", expr tendsto (λ
    n, f (u n)) at_top (expr𝓝() (f x))] [":=", expr (hf.continuous_on.mono hε x xmem).tendsto.comp hx'],
  have [ident T2] [":", expr tendsto (λ n, f (u n)) at_top (expr𝓝() y)] [],
  { rw [expr tendsto_iff_dist_tendsto_zero] [],
    refine [expr squeeze_zero (λ n, dist_nonneg) (λ n, (D n).1) _],
    simpa [] [] [] [] [] ["using", expr (tendsto_pow_at_top_nhds_0_of_lt_1 (mul_nonneg (nnreal.coe_nonneg _) (nnreal.coe_nonneg _)) Icf').mul tendsto_const_nhds] },
  exact [expr tendsto_nhds_unique T1 T2]
end

theorem open_image (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.nonlinear_right_inverse) (hs : IsOpen s)
  (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : IsOpen (f '' s) :=
  by 
    cases' hc with hE hc
    ·
      skip 
      apply is_open_discrete 
    simp only [is_open_iff_mem_nhds, nhds_basis_closed_ball.mem_iff, ball_image_iff] at hs⊢
    intro x hx 
    rcases hs x hx with ⟨ε, ε0, hε⟩
    refine' ⟨(f'symm.nnnorm⁻¹ - c)*ε, mul_pos (sub_pos.2 hc) ε0, _⟩
    exact (hf.surj_on_closed_ball_of_nonlinear_right_inverse f'symm (le_of_ltₓ ε0) hε).mono hε (subset.refl _)

-- error in Analysis.Calculus.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem image_mem_nhds
(hf : approximates_linear_on f f' s c)
(f'symm : f'.nonlinear_right_inverse)
{x : E}
(hs : «expr ∈ »(s, expr𝓝() x))
(hc : «expr ∨ »(subsingleton F, «expr < »(c, «expr ⁻¹»(f'symm.nnnorm)))) : «expr ∈ »(«expr '' »(f, s), expr𝓝() (f x)) :=
begin
  obtain ["⟨", ident t, ",", ident hts, ",", ident ht, ",", ident xt, "⟩", ":", expr «expr∃ , »((t «expr ⊆ » s), «expr ∧ »(is_open t, «expr ∈ »(x, t))), ":=", expr _root_.mem_nhds_iff.1 hs],
  have [] [] [":=", expr is_open.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt)],
  exact [expr mem_of_superset this (image_subset _ hts)]
end

-- error in Analysis.Calculus.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_nhds_eq
(hf : approximates_linear_on f f' s c)
(f'symm : f'.nonlinear_right_inverse)
{x : E}
(hs : «expr ∈ »(s, expr𝓝() x))
(hc : «expr ∨ »(subsingleton F, «expr < »(c, «expr ⁻¹»(f'symm.nnnorm)))) : «expr = »(map f (expr𝓝() x), expr𝓝() (f x)) :=
begin
  refine [expr le_antisymm ((hf.continuous_on x (mem_of_mem_nhds hs)).continuous_at hs) (le_map (λ t ht, _))],
  have [] [":", expr «expr ∈ »(«expr '' »(f, «expr ∩ »(s, t)), expr𝓝() (f x))] [":=", expr (hf.mono_set (inter_subset_left s t)).image_mem_nhds f'symm (inter_mem hs ht) hc],
  exact [expr mem_of_superset this (image_subset _ (inter_subset_right _ _))]
end

end LocallyOnto

/-!
From now on we assume that `f` approximates an invertible continuous linear map `f : E ≃L[𝕜] F`.

We also assume that either `E = {0}`, or `c < ∥f'⁻¹∥⁻¹`. We use `N` as an abbreviation for `∥f'⁻¹∥`.
-/


variable{f' : E ≃L[𝕜] F}{s : Set E}{c :  ℝ≥0 }

local notation "N" => nnnorm (f'.symm : F →L[𝕜] E)

-- error in Analysis.Calculus.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem antilipschitz
(hf : approximates_linear_on f (f' : «expr →L[ ] »(E, 𝕜, F)) s c)
(hc : «expr ∨ »(subsingleton E, «expr < »(c, «expr ⁻¹»(exprN())))) : antilipschitz_with «expr ⁻¹»(«expr - »(«expr ⁻¹»(exprN()), c)) (s.restrict f) :=
begin
  cases [expr hc] ["with", ident hE, ident hc],
  { haveI [] [":", expr subsingleton s] [":=", expr ⟨λ x y, «expr $ »(subtype.eq, @subsingleton.elim _ hE _ _)⟩],
    exact [expr antilipschitz_with.of_subsingleton] },
  convert [] [expr (f'.antilipschitz.restrict s).add_lipschitz_with hf.lipschitz_sub hc] [],
  simp [] [] [] ["[", expr restrict, "]"] [] []
end

protected theorem injective (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
  injective (s.restrict f) :=
  (hf.antilipschitz hc).Injective

protected theorem inj_on (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
  inj_on f s :=
  inj_on_iff_injective.2$ hf.injective hc

/-- A map approximating a linear equivalence on a set defines a local equivalence on this set.
Should not be used outside of this file, because it is superseded by `to_local_homeomorph` below.

This is a first step towards the inverse function. -/
def to_local_equiv (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
  LocalEquiv E F :=
  (hf.inj_on hc).toLocalEquiv _ _

/-- The inverse function is continuous on `f '' s`. Use properties of `local_homeomorph` instead. -/
theorem inverse_continuous_on (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
  ContinuousOn (hf.to_local_equiv hc).symm (f '' s) :=
  by 
    apply continuous_on_iff_continuous_restrict.2
    refine' ((hf.antilipschitz hc).to_right_inv_on' _ (hf.to_local_equiv hc).right_inv').Continuous 
    exact fun x hx => (hf.to_local_equiv hc).map_target hx

include cs

section 

variable(f s)

/-- Given a function `f` that approximates a linear equivalence on an open set `s`,
returns a local homeomorph with `to_fun = f` and `source = s`. -/
def to_local_homeomorph (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
  (hs : IsOpen s) : LocalHomeomorph E F :=
  { toLocalEquiv := hf.to_local_equiv hc, open_source := hs,
    open_target :=
      hf.open_image f'.to_nonlinear_right_inverse hs
        (by 
          rwa [f'.to_linear_equiv.to_equiv.subsingleton_congr] at hc),
    continuous_to_fun := hf.continuous_on, continuous_inv_fun := hf.inverse_continuous_on hc }

end 

@[simp]
theorem to_local_homeomorph_coe (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
  (hs : IsOpen s) : (hf.to_local_homeomorph f s hc hs : E → F) = f :=
  rfl

@[simp]
theorem to_local_homeomorph_source (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
  (hs : IsOpen s) : (hf.to_local_homeomorph f s hc hs).Source = s :=
  rfl

@[simp]
theorem to_local_homeomorph_target (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
  (hs : IsOpen s) : (hf.to_local_homeomorph f s hc hs).Target = f '' s :=
  rfl

theorem closed_ball_subset_target (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
  (hs : IsOpen s) {b : E} (ε0 : 0 ≤ ε) (hε : closed_ball b ε ⊆ s) :
  closed_ball (f b) ((N⁻¹ - c)*ε) ⊆ (hf.to_local_homeomorph f s hc hs).Target :=
  (hf.surj_on_closed_ball_of_nonlinear_right_inverse f'.to_nonlinear_right_inverse ε0 hε).mono hε (subset.refl _)

end ApproximatesLinearOn

/-!
### Inverse function theorem

Now we prove the inverse function theorem. Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `approximates_linear_on` on an open neighborhood
of `a`, and we can apply `approximates_linear_on.to_local_homeomorph` to construct the inverse
function. -/


namespace HasStrictFderivAt

-- error in Analysis.Calculus.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` has derivative `f'` at `a` in the strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
theorem approximates_deriv_on_nhds
{f : E → F}
{f' : «expr →L[ ] »(E, 𝕜, F)}
{a : E}
(hf : has_strict_fderiv_at f f' a)
{c : «exprℝ≥0»()}
(hc : «expr ∨ »(subsingleton E, «expr < »(0, c))) : «expr∃ , »((s «expr ∈ » expr𝓝() a), approximates_linear_on f f' s c) :=
begin
  cases [expr hc] ["with", ident hE, ident hc],
  { refine [expr ⟨univ, is_open.mem_nhds is_open_univ trivial, λ x hx y hy, _⟩],
    simp [] [] [] ["[", expr @subsingleton.elim E hE x y, "]"] [] [] },
  have [] [] [":=", expr hf.def hc],
  rw ["[", expr nhds_prod_eq, ",", expr filter.eventually, ",", expr mem_prod_same_iff, "]"] ["at", ident this],
  rcases [expr this, "with", "⟨", ident s, ",", ident has, ",", ident hs, "⟩"],
  exact [expr ⟨s, has, λ x hx y hy, hs (mk_mem_prod hx hy)⟩]
end

-- error in Analysis.Calculus.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_nhds_eq_of_surj
[complete_space E]
[complete_space F]
{f : E → F}
{f' : «expr →L[ ] »(E, 𝕜, F)}
{a : E}
(hf : has_strict_fderiv_at f (f' : «expr →L[ ] »(E, 𝕜, F)) a)
(h : «expr = »(f'.range, «expr⊤»())) : «expr = »(map f (expr𝓝() a), expr𝓝() (f a)) :=
begin
  let [ident f'symm] [] [":=", expr f'.nonlinear_right_inverse_of_surjective h],
  set [] [ident c] [":", expr «exprℝ≥0»()] [":="] [expr «expr / »(«expr ⁻¹»(f'symm.nnnorm), 2)] ["with", ident hc],
  have [ident f'symm_pos] [":", expr «expr < »(0, f'symm.nnnorm)] [":=", expr f'.nonlinear_right_inverse_of_surjective_nnnorm_pos h],
  have [ident cpos] [":", expr «expr < »(0, c)] [],
  by simp [] [] [] ["[", expr hc, ",", expr nnreal.half_pos, ",", expr nnreal.inv_pos, ",", expr f'symm_pos, "]"] [] [],
  obtain ["⟨", ident s, ",", ident s_nhds, ",", ident hs, "⟩", ":", expr «expr∃ , »((s «expr ∈ » expr𝓝() a), approximates_linear_on f f' s c), ":=", expr hf.approximates_deriv_on_nhds (or.inr cpos)],
  apply [expr hs.map_nhds_eq f'symm s_nhds (or.inr (nnreal.half_lt_self _))],
  simp [] [] [] ["[", expr ne_of_gt f'symm_pos, "]"] [] []
end

variable[cs : CompleteSpace E]{f : E → F}{f' : E ≃L[𝕜] F}{a : E}

theorem approximates_deriv_on_open_nhds (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  ∃ (s : Set E)(hs : a ∈ s ∧ IsOpen s),
    ApproximatesLinearOn f (f' : E →L[𝕜] F) s (nnnorm (f'.symm : F →L[𝕜] E)⁻¹ / 2) :=
  by 
    refine' ((nhds_basis_opens a).exists_iff _).1 _ 
    exact fun s t => ApproximatesLinearOn.mono_set 
    exact
      hf.approximates_deriv_on_nhds$
        f'.subsingleton_or_nnnorm_symm_pos.imp id$ fun hf' => Nnreal.half_pos$ Nnreal.inv_pos.2$ hf'

include cs

variable(f)

/-- Given a function with an invertible strict derivative at `a`, returns a `local_homeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `has_strict_fderiv_at.to_local_inverse` states that the inverse function
of this `local_homeomorph` has derivative `f'.symm`. -/
def to_local_homeomorph (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : LocalHomeomorph E F :=
  ApproximatesLinearOn.toLocalHomeomorph f (Classical.some hf.approximates_deriv_on_open_nhds)
    (Classical.some_spec hf.approximates_deriv_on_open_nhds).snd
    (f'.subsingleton_or_nnnorm_symm_pos.imp id$ fun hf' => Nnreal.half_lt_self$ ne_of_gtₓ$ Nnreal.inv_pos.2$ hf')
    (Classical.some_spec hf.approximates_deriv_on_open_nhds).fst.2

variable{f}

@[simp]
theorem to_local_homeomorph_coe (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  (hf.to_local_homeomorph f : E → F) = f :=
  rfl

theorem mem_to_local_homeomorph_source (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  a ∈ (hf.to_local_homeomorph f).Source :=
  (Classical.some_spec hf.approximates_deriv_on_open_nhds).fst.1

theorem image_mem_to_local_homeomorph_target (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  f a ∈ (hf.to_local_homeomorph f).Target :=
  (hf.to_local_homeomorph f).map_source hf.mem_to_local_homeomorph_source

theorem map_nhds_eq_of_equiv (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.to_local_homeomorph f).map_nhds_eq hf.mem_to_local_homeomorph_source

variable(f f' a)

/-- Given a function `f` with an invertible derivative, returns a function that is locally inverse
to `f`. -/
def local_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : F → E :=
  (hf.to_local_homeomorph f).symm

variable{f f' a}

theorem local_inverse_def (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  hf.local_inverse f _ _ = (hf.to_local_homeomorph f).symm :=
  rfl

theorem eventually_left_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  ∀ᶠx in 𝓝 a, hf.local_inverse f f' a (f x) = x :=
  (hf.to_local_homeomorph f).eventually_left_inverse hf.mem_to_local_homeomorph_source

@[simp]
theorem local_inverse_apply_image (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : hf.local_inverse f f' a (f a) = a :=
  hf.eventually_left_inverse.self_of_nhds

theorem eventually_right_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  ∀ᶠy in 𝓝 (f a), f (hf.local_inverse f f' a y) = y :=
  (hf.to_local_homeomorph f).eventually_right_inverse' hf.mem_to_local_homeomorph_source

theorem local_inverse_continuous_at (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  ContinuousAt (hf.local_inverse f f' a) (f a) :=
  (hf.to_local_homeomorph f).continuous_at_symm hf.image_mem_to_local_homeomorph_target

theorem local_inverse_tendsto (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  tendsto (hf.local_inverse f f' a) (𝓝$ f a) (𝓝 a) :=
  (hf.to_local_homeomorph f).tendsto_symm hf.mem_to_local_homeomorph_source

theorem local_inverse_unique (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) {g : F → E} (hg : ∀ᶠx in 𝓝 a, g (f x) = x) :
  ∀ᶠy in 𝓝 (f a), g y = local_inverse f f' a hf y :=
  eventually_eq_of_left_inv_of_right_inv hg hf.eventually_right_inverse$
    (hf.to_local_homeomorph f).tendsto_symm hf.mem_to_local_homeomorph_source

/-- If `f` has an invertible derivative `f'` at `a` in the sense of strict differentiability `(hf)`,
then the inverse function `hf.local_inverse f` has derivative `f'.symm` at `f a`. -/
theorem to_local_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
  HasStrictFderivAt (hf.local_inverse f f' a) (f'.symm : F →L[𝕜] E) (f a) :=
  (hf.to_local_homeomorph f).has_strict_fderiv_at_symm hf.image_mem_to_local_homeomorph_target$
    by 
      simpa [←local_inverse_def] using hf

/-- If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict differentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at `f a`.

For a version assuming `f (g y) = y` and continuity of `g` at `f a` but not `[complete_space E]`
see `of_local_left_inverse`.  -/
theorem to_local_left_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) {g : F → E} (hg : ∀ᶠx in 𝓝 a, g (f x) = x) :
  HasStrictFderivAt g (f'.symm : F →L[𝕜] E) (f a) :=
  hf.to_local_inverse.congr_of_eventually_eq$ (hf.local_inverse_unique hg).mono$ fun _ => Eq.symm

end HasStrictFderivAt

/-- If a function has an invertible strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_fderiv_equiv [CompleteSpace E] {f : E → F} {f' : E → E ≃L[𝕜] F}
  (hf : ∀ x, HasStrictFderivAt f (f' x : E →L[𝕜] F) x) : IsOpenMap f :=
  is_open_map_iff_nhds_le.2$ fun x => (hf x).map_nhds_eq_of_equiv.Ge

/-!
### Inverse function theorem, 1D case

In this case we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `continuous_linear_equiv.units_equiv_aut` to translate `has_strict_deriv_at f f' a` and
`f' ≠ 0` into `has_strict_fderiv_at f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/


namespace HasStrictDerivAt

variable[cs : CompleteSpace 𝕜]{f : 𝕜 → 𝕜}{f' a : 𝕜}(hf : HasStrictDerivAt f f' a)(hf' : f' ≠ 0)

include cs

variable(f f' a)

/-- A function that is inverse to `f` near `a`. -/
@[reducible]
def local_inverse : 𝕜 → 𝕜 :=
  (hf.has_strict_fderiv_at_equiv hf').localInverse _ _ _

variable{f f' a}

theorem map_nhds_eq : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.has_strict_fderiv_at_equiv hf').map_nhds_eq_of_equiv

theorem to_local_inverse : HasStrictDerivAt (hf.local_inverse f f' a hf') (f'⁻¹) (f a) :=
  (hf.has_strict_fderiv_at_equiv hf').to_local_inverse

theorem to_local_left_inverse {g : 𝕜 → 𝕜} (hg : ∀ᶠx in 𝓝 a, g (f x) = x) : HasStrictDerivAt g (f'⁻¹) (f a) :=
  (hf.has_strict_fderiv_at_equiv hf').to_local_left_inverse hg

end HasStrictDerivAt

/-- If a function has a non-zero strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_deriv [CompleteSpace 𝕜] {f f' : 𝕜 → 𝕜} (hf : ∀ x, HasStrictDerivAt f (f' x) x)
  (h0 : ∀ x, f' x ≠ 0) : IsOpenMap f :=
  is_open_map_iff_nhds_le.2$ fun x => ((hf x).map_nhds_eq (h0 x)).Ge

/-!
### Inverse function theorem, smooth case

-/


namespace TimesContDiffAt

variable{𝕂 : Type _}[IsROrC 𝕂]

variable{E' : Type _}[NormedGroup E'][NormedSpace 𝕂 E']

variable{F' : Type _}[NormedGroup F'][NormedSpace 𝕂 F']

variable[CompleteSpace E'](f : E' → F'){f' : E' ≃L[𝕂] F'}{a : E'}

/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns a `local_homeomorph` with `to_fun = f` and `a ∈ source`. -/
def to_local_homeomorph {n : WithTop ℕ} (hf : TimesContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) : LocalHomeomorph E' F' :=
  (hf.has_strict_fderiv_at' hf' hn).toLocalHomeomorph f

variable{f}

@[simp]
theorem to_local_homeomorph_coe {n : WithTop ℕ} (hf : TimesContDiffAt 𝕂 n f a)
  (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) : (hf.to_local_homeomorph f hf' hn : E' → F') = f :=
  rfl

theorem mem_to_local_homeomorph_source {n : WithTop ℕ} (hf : TimesContDiffAt 𝕂 n f a)
  (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) : a ∈ (hf.to_local_homeomorph f hf' hn).Source :=
  (hf.has_strict_fderiv_at' hf' hn).mem_to_local_homeomorph_source

theorem image_mem_to_local_homeomorph_target {n : WithTop ℕ} (hf : TimesContDiffAt 𝕂 n f a)
  (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) : f a ∈ (hf.to_local_homeomorph f hf' hn).Target :=
  (hf.has_strict_fderiv_at' hf' hn).image_mem_to_local_homeomorph_target

/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
def local_inverse {n : WithTop ℕ} (hf : TimesContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) : F' → E' :=
  (hf.has_strict_fderiv_at' hf' hn).localInverse f f' a

theorem local_inverse_apply_image {n : WithTop ℕ} (hf : TimesContDiffAt 𝕂 n f a)
  (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) : hf.local_inverse hf' hn (f a) = a :=
  (hf.has_strict_fderiv_at' hf' hn).local_inverse_apply_image

-- error in Analysis.Calculus.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `times_cont_diff.to_local_homeomorph`) is
also `times_cont_diff`. -/
theorem to_local_inverse
{n : with_top exprℕ()}
(hf : times_cont_diff_at 𝕂 n f a)
(hf' : has_fderiv_at f (f' : «expr →L[ ] »(E', 𝕂, F')) a)
(hn : «expr ≤ »(1, n)) : times_cont_diff_at 𝕂 n (hf.local_inverse hf' hn) (f a) :=
begin
  have [] [] [":=", expr hf.local_inverse_apply_image hf' hn],
  apply [expr (hf.to_local_homeomorph f hf' hn).times_cont_diff_at_symm (image_mem_to_local_homeomorph_target hf hf' hn)],
  { convert [] [expr hf'] [] },
  { convert [] [expr hf] [] }
end

end TimesContDiffAt

