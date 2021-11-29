import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent 
import Mathbin.Analysis.Calculus.TangentCone 
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps 
import Mathbin.Analysis.NormedSpace.Units

/-!
# The Fréchet derivative

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `has_fderiv_within_at f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_within_at f f' x univ`

Finally,

  `has_strict_fderiv_at f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`is_bounded_bilinear_map.has_fderiv_at` twice: first for `has_fderiv_at`, then for
`has_strict_fderiv_at`.

## Main results

In addition to the definition and basic properties of the derivative, this file contains the
usual formulas (and existence assertions) for the derivative of
* constants
* the identity
* bounded linear maps
* bounded bilinear maps
* sum of two functions
* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
* multiplication of a function by a scalar function
* multiplication of two scalar functions
* composition of functions (the chain rule)
* inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : differentiable ℝ (λ x, sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : differentiable_at ℝ (λ x, exp x / (1 + sin x)) x :=
by simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `analysis.special_functions.trigonometric`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `deriv.lean`.

## Implementation details

The derivative is defined in terms of the `is_o` relation, but also
characterized in terms of the `tendsto` relation.

We also introduce predicates `differentiable_within_at 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `differentiable_at 𝕜 f x`,
`differentiable_on 𝕜 f s` and `differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderiv_within 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `unique_diff_within_at s x` and
`unique_diff_on s`, defined in `tangent_cone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(λ x, exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

Tests for this ability of the simplifier (with more examples) are provided in
`tests/differentiable.lean`.

## Tags

derivative, differentiable, Fréchet, calculus

-/


open Filter Asymptotics ContinuousLinearMap Set Metric

open_locale TopologicalSpace Classical Nnreal Filter Asymptotics Ennreal

noncomputable theory

section 

variable{𝕜 : Type _}[NondiscreteNormedField 𝕜]

variable{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]

variable{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]

variable{G : Type _}[NormedGroup G][NormedSpace 𝕜 G]

variable{G' : Type _}[NormedGroup G'][NormedSpace 𝕜 G']

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` converges along the filter `L`. This definition
is designed to be specialized for `L = 𝓝 x` (in `has_fderiv_at`), giving rise to the usual notion
of Fréchet derivative, and for `L = 𝓝[s] x` (in `has_fderiv_within_at`), giving rise to
the notion of Fréchet derivative along the set `s`. -/
def HasFderivAtFilter (f : E → F) (f' : E →L[𝕜] F) (x : E) (L : Filter E) :=
  is_o (fun x' => f x' - f x - f' (x' - x)) (fun x' => x' - x) L

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`. -/
def HasFderivWithinAt (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x : E) :=
  HasFderivAtFilter f f' x (𝓝[s] x)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`. -/
def HasFderivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  HasFderivAtFilter f f' x (𝓝 x)

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
def has_strict_fderiv_at (f : E → F) (f' : «expr →L[ ] »(E, 𝕜, F)) (x : E) :=
is_o (λ
 p : «expr × »(E, E), «expr - »(«expr - »(f p.1, f p.2), f' «expr - »(p.1, p.2))) (λ
 p : «expr × »(E, E), «expr - »(p.1, p.2)) (expr𝓝() (x, x))

variable(𝕜)

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
def DifferentiableWithinAt (f : E → F) (s : Set E) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFderivWithinAt f f' s x

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
def DifferentiableAt (f : E → F) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFderivAt f f' x

/-- If `f` has a derivative at `x` within `s`, then `fderiv_within 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. -/
def fderivWithin (f : E → F) (s : Set E) (x : E) : E →L[𝕜] F :=
  if h : ∃ f', HasFderivWithinAt f f' s x then Classical.some h else 0

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
  if h : ∃ f', HasFderivAt f f' x then Classical.some h else 0

/-- `differentiable_on 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
def DifferentiableOn (f : E → F) (s : Set E) :=
  ∀ x (_ : x ∈ s), DifferentiableWithinAt 𝕜 f s x

/-- `differentiable 𝕜 f` means that `f` is differentiable at any point. -/
def Differentiable (f : E → F) :=
  ∀ x, DifferentiableAt 𝕜 f x

variable{𝕜}

variable{f f₀ f₁ g : E → F}

variable{f' f₀' f₁' g' : E →L[𝕜] F}

variable(e : E →L[𝕜] F)

variable{x : E}

variable{s t : Set E}

variable{L L₁ L₂ : Filter E}

theorem fderiv_within_zero_of_not_differentiable_within_at (h : ¬DifferentiableWithinAt 𝕜 f s x) :
  fderivWithin 𝕜 f s x = 0 :=
  have  : ¬∃ f', HasFderivWithinAt f f' s x := h 
  by 
    simp [fderivWithin, this]

theorem fderiv_zero_of_not_differentiable_at (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0 :=
  have  : ¬∃ f', HasFderivAt f f' x := h 
  by 
    simp [fderiv, this]

section DerivativeUniqueness

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `c n` tends to infinity
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulation is useful for
tangent cone related discussions. -/
theorem has_fderiv_within_at.lim
(h : has_fderiv_within_at f f' s x)
{α : Type*}
(l : filter α)
{c : α → 𝕜}
{d : α → E}
{v : E}
(dtop : «expr∀ᶠ in , »((n), l, «expr ∈ »(«expr + »(x, d n), s)))
(clim : tendsto (λ n, «expr∥ ∥»(c n)) l at_top)
(cdlim : tendsto (λ
  n, «expr • »(c n, d n)) l (expr𝓝() v)) : tendsto (λ
 n, «expr • »(c n, «expr - »(f «expr + »(x, d n), f x))) l (expr𝓝() (f' v)) :=
begin
  have [ident tendsto_arg] [":", expr tendsto (λ n, «expr + »(x, d n)) l «expr𝓝[ ] »(s, x)] [],
  { conv [] ["in", expr «expr𝓝[ ] »(s, x)] { rw ["<-", expr add_zero x] },
    rw ["[", expr nhds_within, ",", expr tendsto_inf, "]"] [],
    split,
    { apply [expr tendsto_const_nhds.add (tangent_cone_at.lim_zero l clim cdlim)] },
    { rwa [expr tendsto_principal] [] } },
  have [] [":", expr is_o (λ
    y, «expr - »(«expr - »(f y, f x), f' «expr - »(y, x))) (λ y, «expr - »(y, x)) «expr𝓝[ ] »(s, x)] [":=", expr h],
  have [] [":", expr is_o (λ
    n, «expr - »(«expr - »(f «expr + »(x, d n), f x), f' «expr - »(«expr + »(x, d n), x))) (λ
    n, «expr - »(«expr + »(x, d n), x)) l] [":=", expr this.comp_tendsto tendsto_arg],
  have [] [":", expr is_o (λ
    n, «expr - »(«expr - »(f «expr + »(x, d n), f x), f' (d n))) d l] [":=", expr by simpa [] [] ["only"] ["[", expr add_sub_cancel', "]"] [] []],
  have [] [":", expr is_o (λ
    n, «expr • »(c n, «expr - »(«expr - »(f «expr + »(x, d n), f x), f' (d n)))) (λ
    n, «expr • »(c n, d n)) l] [":=", expr (is_O_refl c l).smul_is_o this],
  have [] [":", expr is_o (λ
    n, «expr • »(c n, «expr - »(«expr - »(f «expr + »(x, d n), f x), f' (d n)))) (λ
    n, (1 : exprℝ())) l] [":=", expr this.trans_is_O (is_O_one_of_tendsto exprℝ() cdlim)],
  have [ident L1] [":", expr tendsto (λ
    n, «expr • »(c n, «expr - »(«expr - »(f «expr + »(x, d n), f x), f' (d n)))) l (expr𝓝() 0)] [":=", expr (is_o_one_iff exprℝ()).1 this],
  have [ident L2] [":", expr tendsto (λ
    n, f' «expr • »(c n, d n)) l (expr𝓝() (f' v))] [":=", expr tendsto.comp f'.cont.continuous_at cdlim],
  have [ident L3] [":", expr tendsto (λ
    n, «expr + »(«expr • »(c n, «expr - »(«expr - »(f «expr + »(x, d n), f x), f' (d n))), f' «expr • »(c n, d n))) l (expr𝓝() «expr + »(0, f' v))] [":=", expr L1.add L2],
  have [] [":", expr «expr = »(λ
    n, «expr + »(«expr • »(c n, «expr - »(«expr - »(f «expr + »(x, d n), f x), f' (d n))), f' «expr • »(c n, d n)), λ
    n, «expr • »(c n, «expr - »(f «expr + »(x, d n), f x)))] [],
  by { ext [] [ident n] [],
    simp [] [] [] ["[", expr smul_add, ",", expr smul_sub, "]"] [] [] },
  rwa ["[", expr this, ",", expr zero_add, "]"] ["at", ident L3]
end

/-- If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are equal on the
tangent cone to `s` at `x` -/
theorem HasFderivWithinAt.unique_on (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt f f₁' s x) :
  eq_on f' f₁' (TangentConeAt 𝕜 s x) :=
  fun y ⟨c, d, dtop, clim, cdlim⟩ => tendsto_nhds_unique (hf.lim at_top dtop clim cdlim) (hg.lim at_top dtop clim cdlim)

/-- `unique_diff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFderivWithinAt f f' s x)
  (hg : HasFderivWithinAt f f₁' s x) : f' = f₁' :=
  ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)

theorem UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : HasFderivWithinAt f f' s x)
  (h₁ : HasFderivWithinAt f f₁' s x) : f' = f₁' :=
  (H x hx).Eq h h₁

end DerivativeUniqueness

section FderivProperties

/-! ### Basic properties of the derivative -/


theorem has_fderiv_at_filter_iff_tendsto :
  HasFderivAtFilter f f' x L ↔ tendsto (fun x' => ∥x' - x∥⁻¹*∥f x' - f x - f' (x' - x)∥) L (𝓝 0) :=
  have h : ∀ x', ∥x' - x∥ = 0 → ∥f x' - f x - f' (x' - x)∥ = 0 :=
    fun x' hx' =>
      by 
        rw [sub_eq_zero.1 (norm_eq_zero.1 hx')]
        simp 
  by 
    unfold HasFderivAtFilter 
    rw [←is_o_norm_left, ←is_o_norm_right, is_o_iff_tendsto h]
    exact tendsto_congr fun _ => div_eq_inv_mul

theorem has_fderiv_within_at_iff_tendsto :
  HasFderivWithinAt f f' s x ↔ tendsto (fun x' => ∥x' - x∥⁻¹*∥f x' - f x - f' (x' - x)∥) (𝓝[s] x) (𝓝 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_tendsto :
  HasFderivAt f f' x ↔ tendsto (fun x' => ∥x' - x∥⁻¹*∥f x' - f x - f' (x' - x)∥) (𝓝 x) (𝓝 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_is_o_nhds_zero :
  HasFderivAt f f' x ↔ is_o (fun h => f (x+h) - f x - f' h) (fun h => h) (𝓝 0) :=
  by 
    rw [HasFderivAt, HasFderivAtFilter, ←map_add_left_nhds_zero x, is_o_map]
    simp [· ∘ ·]

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `∥f x - f x₀∥ ≤ C * ∥x - x₀∥` in a neighborhood of `x`. -/
theorem HasFderivAt.le_of_lip' {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFderivAt f f' x₀) {C : ℝ} (hC₀ : 0 ≤ C)
  (hlip : ∀ᶠx in 𝓝 x₀, ∥f x - f x₀∥ ≤ C*∥x - x₀∥) : ∥f'∥ ≤ C :=
  by 
    refine' le_of_forall_pos_le_add fun ε ε0 => op_norm_le_of_nhds_zero _ _ 
    exact add_nonneg hC₀ ε0.le 
    rw [←map_add_left_nhds_zero x₀, eventually_map] at hlip 
    filterUpwards [is_o_iff.1 (has_fderiv_at_iff_is_o_nhds_zero.1 hf) ε0, hlip]
    intro y hy hyC 
    rw [add_sub_cancel'] at hyC 
    calc ∥f' y∥ ≤ ∥f (x₀+y) - f x₀∥+∥f (x₀+y) - f x₀ - f' y∥ := norm_le_insert _ _ _ ≤ (C*∥y∥)+ε*∥y∥ :=
      add_le_add hyC hy _ = (C+ε)*∥y∥ := (add_mulₓ _ _ _).symm

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. -/
theorem HasFderivAt.le_of_lip {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFderivAt f f' x₀) {s : Set E}
  (hs : s ∈ 𝓝 x₀) {C :  ℝ≥0 } (hlip : LipschitzOnWith C f s) : ∥f'∥ ≤ C :=
  by 
    refine' hf.le_of_lip' C.coe_nonneg _ 
    filterUpwards [hs]
    exact fun x hx => hlip.norm_sub_le hx (mem_of_mem_nhds hs)

theorem HasFderivAtFilter.mono (h : HasFderivAtFilter f f' x L₂) (hst : L₁ ≤ L₂) : HasFderivAtFilter f f' x L₁ :=
  h.mono hst

theorem HasFderivWithinAt.mono (h : HasFderivWithinAt f f' t x) (hst : s ⊆ t) : HasFderivWithinAt f f' s x :=
  h.mono (nhds_within_mono _ hst)

theorem HasFderivAt.has_fderiv_at_filter (h : HasFderivAt f f' x) (hL : L ≤ 𝓝 x) : HasFderivAtFilter f f' x L :=
  h.mono hL

theorem HasFderivAt.has_fderiv_within_at (h : HasFderivAt f f' x) : HasFderivWithinAt f f' s x :=
  h.has_fderiv_at_filter inf_le_left

theorem HasFderivWithinAt.differentiable_within_at (h : HasFderivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x :=
  ⟨f', h⟩

theorem HasFderivAt.differentiable_at (h : HasFderivAt f f' x) : DifferentiableAt 𝕜 f x :=
  ⟨f', h⟩

@[simp]
theorem has_fderiv_within_at_univ : HasFderivWithinAt f f' univ x ↔ HasFderivAt f f' x :=
  by 
    simp only [HasFderivWithinAt, nhds_within_univ]
    rfl

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_strict_fderiv_at.is_O_sub
(hf : has_strict_fderiv_at f f' x) : is_O (λ
 p : «expr × »(E, E), «expr - »(f p.1, f p.2)) (λ p : «expr × »(E, E), «expr - »(p.1, p.2)) (expr𝓝() (x, x)) :=
hf.is_O.congr_of_sub.2 (f'.is_O_comp _ _)

theorem HasFderivAtFilter.is_O_sub (h : HasFderivAtFilter f f' x L) :
  is_O (fun x' => f x' - f x) (fun x' => x' - x) L :=
  h.is_O.congr_of_sub.2 (f'.is_O_sub _ _)

protected theorem HasStrictFderivAt.has_fderiv_at (hf : HasStrictFderivAt f f' x) : HasFderivAt f f' x :=
  by 
    rw [HasFderivAt, HasFderivAtFilter, is_o_iff]
    exact fun c hc => tendsto_id.prod_mk_nhds tendsto_const_nhds (is_o_iff.1 hf hc)

protected theorem HasStrictFderivAt.differentiable_at (hf : HasStrictFderivAt f f' x) : DifferentiableAt 𝕜 f x :=
  hf.has_fderiv_at.differentiable_at

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is strictly differentiable at `x` with derivative `f'` and `K > ∥f'∥₊`, then `f` is
`K`-Lipschitz in a neighborhood of `x`. -/
theorem has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt
(hf : has_strict_fderiv_at f f' x)
(K : «exprℝ≥0»())
(hK : «expr < »(«expr∥ ∥₊»(f'), K)) : «expr∃ , »((s «expr ∈ » expr𝓝() x), lipschitz_on_with K f s) :=
begin
  have [] [] [":=", expr hf.add_is_O_with (f'.is_O_with_comp _ _) hK],
  simp [] [] ["only"] ["[", expr sub_add_cancel, ",", expr is_O_with, "]"] [] ["at", ident this],
  rcases [expr exists_nhds_square this, "with", "⟨", ident U, ",", ident Uo, ",", ident xU, ",", ident hU, "⟩"],
  exact [expr ⟨U, Uo.mem_nhds xU, «expr $ »(lipschitz_on_with_iff_norm_sub_le.2, λ x hx y hy, hU (mk_mem_prod hx hy))⟩]
end

/-- If `f` is strictly differentiable at `x` with derivative `f'`, then `f` is Lipschitz in a
neighborhood of `x`. See also `has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt` for a
more precise statement. -/
theorem HasStrictFderivAt.exists_lipschitz_on_with (hf : HasStrictFderivAt f f' x) :
  ∃ (K : _)(s : _)(_ : s ∈ 𝓝 x), LipschitzOnWith K f s :=
  (no_top _).imp hf.exists_lipschitz_on_with_of_nnnorm_lt

/-- Directional derivative agrees with `has_fderiv`. -/
theorem HasFderivAt.lim (hf : HasFderivAt f f' x) (v : E) {α : Type _} {c : α → 𝕜} {l : Filter α}
  (hc : tendsto (fun n => ∥c n∥) l at_top) : tendsto (fun n => c n • (f (x+c n⁻¹ • v) - f x)) l (𝓝 (f' v)) :=
  by 
    refine' (has_fderiv_within_at_univ.2 hf).lim _ (univ_mem' fun _ => trivialₓ) hc _ 
    intro U hU 
    refine' (eventually_ne_of_tendsto_norm_at_top hc (0 : 𝕜)).mono fun y hy => _ 
    convert mem_of_mem_nhds hU 
    dsimp only 
    rw [←mul_smul, mul_inv_cancel hy, one_smul]

theorem HasFderivAt.unique (h₀ : HasFderivAt f f₀' x) (h₁ : HasFderivAt f f₁' x) : f₀' = f₁' :=
  by 
    rw [←has_fderiv_within_at_univ] at h₀ h₁ 
    exact unique_diff_within_at_univ.eq h₀ h₁

theorem has_fderiv_within_at_inter' (h : t ∈ 𝓝[s] x) : HasFderivWithinAt f f' (s ∩ t) x ↔ HasFderivWithinAt f f' s x :=
  by 
    simp [HasFderivWithinAt, nhds_within_restrict'' s h]

theorem has_fderiv_within_at_inter (h : t ∈ 𝓝 x) : HasFderivWithinAt f f' (s ∩ t) x ↔ HasFderivWithinAt f f' s x :=
  by 
    simp [HasFderivWithinAt, nhds_within_restrict' s h]

theorem HasFderivWithinAt.union (hs : HasFderivWithinAt f f' s x) (ht : HasFderivWithinAt f f' t x) :
  HasFderivWithinAt f f' (s ∪ t) x :=
  by 
    simp only [HasFderivWithinAt, nhds_within_union]
    exact hs.join ht

theorem HasFderivWithinAt.nhds_within (h : HasFderivWithinAt f f' s x) (ht : s ∈ 𝓝[t] x) : HasFderivWithinAt f f' t x :=
  (has_fderiv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

theorem HasFderivWithinAt.has_fderiv_at (h : HasFderivWithinAt f f' s x) (hs : s ∈ 𝓝 x) : HasFderivAt f f' x :=
  by 
    rwa [←univ_inter s, has_fderiv_within_at_inter hs, has_fderiv_within_at_univ] at h

theorem DifferentiableWithinAt.differentiable_at (h : DifferentiableWithinAt 𝕜 f s x) (hs : s ∈ 𝓝 x) :
  DifferentiableAt 𝕜 f x :=
  h.imp fun f' hf' => hf'.has_fderiv_at hs

theorem DifferentiableWithinAt.has_fderiv_within_at (h : DifferentiableWithinAt 𝕜 f s x) :
  HasFderivWithinAt f (fderivWithin 𝕜 f s x) s x :=
  by 
    dunfold fderivWithin 
    dunfold DifferentiableWithinAt  at h 
    rw [dif_pos h]
    exact Classical.some_spec h

theorem DifferentiableAt.has_fderiv_at (h : DifferentiableAt 𝕜 f x) : HasFderivAt f (fderiv 𝕜 f x) x :=
  by 
    dunfold fderiv 
    dunfold DifferentiableAt  at h 
    rw [dif_pos h]
    exact Classical.some_spec h

theorem DifferentiableOn.has_fderiv_at (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) : HasFderivAt f (fderiv 𝕜 f x) x :=
  ((h x (mem_of_mem_nhds hs)).DifferentiableAt hs).HasFderivAt

theorem HasFderivAt.fderiv (h : HasFderivAt f f' x) : fderiv 𝕜 f x = f' :=
  by 
    ext 
    rw [h.unique h.differentiable_at.has_fderiv_at]

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
theorem FderivAt.le_of_lip {f : E → F} {x₀ : E} (hf : DifferentiableAt 𝕜 f x₀) {s : Set E} (hs : s ∈ 𝓝 x₀) {C :  ℝ≥0 }
  (hlip : LipschitzOnWith C f s) : ∥fderiv 𝕜 f x₀∥ ≤ C :=
  hf.has_fderiv_at.le_of_lip hs hlip

theorem HasFderivWithinAt.fderiv_within (h : HasFderivWithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
  fderivWithin 𝕜 f s x = f' :=
  (hxs.eq h h.differentiable_within_at.has_fderiv_within_at).symm

/-- If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
theorem has_fderiv_within_at_of_not_mem_closure (h : x ∉ Closure s) : HasFderivWithinAt f f' s x :=
  by 
    simp only [mem_closure_iff_nhds_within_ne_bot, ne_bot_iff, Ne.def, not_not] at h 
    simp [HasFderivWithinAt, HasFderivAtFilter, h, is_o, is_O_with]

theorem DifferentiableWithinAt.mono (h : DifferentiableWithinAt 𝕜 f t x) (st : s ⊆ t) :
  DifferentiableWithinAt 𝕜 f s x :=
  by 
    rcases h with ⟨f', hf'⟩
    exact ⟨f', hf'.mono st⟩

theorem differentiable_within_at_univ : DifferentiableWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x :=
  by 
    simp only [DifferentiableWithinAt, has_fderiv_within_at_univ, DifferentiableAt]

theorem differentiable_within_at_inter (ht : t ∈ 𝓝 x) :
  DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x :=
  by 
    simp only [DifferentiableWithinAt, HasFderivWithinAt, HasFderivAtFilter, nhds_within_restrict' s ht]

theorem differentiable_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x :=
  by 
    simp only [DifferentiableWithinAt, HasFderivWithinAt, HasFderivAtFilter, nhds_within_restrict'' s ht]

theorem DifferentiableAt.differentiable_within_at (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x :=
  (differentiable_within_at_univ.2 h).mono (subset_univ _)

theorem Differentiable.differentiable_at (h : Differentiable 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h x

theorem DifferentiableAt.fderiv_within (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
  fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  by 
    apply HasFderivWithinAt.fderiv_within _ hxs 
    exact h.has_fderiv_at.has_fderiv_within_at

theorem DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t) (st : s ⊆ t) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x (st hx)).mono st

theorem differentiable_on_univ : DifferentiableOn 𝕜 f univ ↔ Differentiable 𝕜 f :=
  by 
    simp [DifferentiableOn, differentiable_within_at_univ]
    rfl

theorem Differentiable.differentiable_on (h : Differentiable 𝕜 f) : DifferentiableOn 𝕜 f s :=
  (differentiable_on_univ.2 h).mono (subset_univ _)

theorem differentiable_on_of_locally_differentiable_on
  (h : ∀ x (_ : x ∈ s), ∃ u, IsOpen u ∧ x ∈ u ∧ DifferentiableOn 𝕜 f (s ∩ u)) : DifferentiableOn 𝕜 f s :=
  by 
    intro x xs 
    rcases h x xs with ⟨t, t_open, xt, ht⟩
    exact (differentiable_within_at_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)

theorem fderiv_within_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f t x) :
  fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  ((DifferentiableWithinAt.has_fderiv_within_at h).mono st).fderivWithin ht

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem fderiv_within_univ : «expr = »(fderiv_within 𝕜 f univ, fderiv 𝕜 f) :=
begin
  ext [] [ident x] [":", 1],
  by_cases [expr h, ":", expr differentiable_at 𝕜 f x],
  { apply [expr has_fderiv_within_at.fderiv_within _ unique_diff_within_at_univ],
    rw [expr has_fderiv_within_at_univ] [],
    apply [expr h.has_fderiv_at] },
  { have [] [":", expr «expr¬ »(differentiable_within_at 𝕜 f univ x)] [],
    by contrapose ["!"] [ident h]; rwa ["<-", expr differentiable_within_at_univ] [],
    rw ["[", expr fderiv_zero_of_not_differentiable_at h, ",", expr fderiv_within_zero_of_not_differentiable_within_at this, "]"] [] }
end

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fderiv_within_inter
(ht : «expr ∈ »(t, expr𝓝() x))
(hs : unique_diff_within_at 𝕜 s x) : «expr = »(fderiv_within 𝕜 f «expr ∩ »(s, t) x, fderiv_within 𝕜 f s x) :=
begin
  by_cases [expr h, ":", expr differentiable_within_at 𝕜 f «expr ∩ »(s, t) x],
  { apply [expr fderiv_within_subset (inter_subset_left _ _) _ ((differentiable_within_at_inter ht).1 h)],
    apply [expr hs.inter ht] },
  { have [] [":", expr «expr¬ »(differentiable_within_at 𝕜 f s x)] [],
    by contrapose ["!"] [ident h]; rw [expr differentiable_within_at_inter] []; assumption,
    rw ["[", expr fderiv_within_zero_of_not_differentiable_within_at h, ",", expr fderiv_within_zero_of_not_differentiable_within_at this, "]"] [] }
end

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fderiv_within_of_mem_nhds (h : «expr ∈ »(s, expr𝓝() x)) : «expr = »(fderiv_within 𝕜 f s x, fderiv 𝕜 f x) :=
begin
  have [] [":", expr «expr = »(s, «expr ∩ »(univ, s))] [],
  by simp [] [] ["only"] ["[", expr univ_inter, "]"] [] [],
  rw ["[", expr this, ",", "<-", expr fderiv_within_univ, "]"] [],
  exact [expr fderiv_within_inter h (unique_diff_on_univ _ (mem_univ _))]
end

theorem fderiv_within_of_open (hs : IsOpen s) (hx : x ∈ s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  fderiv_within_of_mem_nhds (IsOpen.mem_nhds hs hx)

theorem fderiv_within_eq_fderiv (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableAt 𝕜 f x) :
  fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  by 
    rw [←fderiv_within_univ]
    exact fderiv_within_subset (subset_univ _) hs h.differentiable_within_at

theorem fderiv_mem_iff {f : E → F} {s : Set (E →L[𝕜] F)} {x : E} :
  fderiv 𝕜 f x ∈ s ↔ DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ s ∨ (0 : E →L[𝕜] F) ∈ s ∧ ¬DifferentiableAt 𝕜 f x :=
  by 
    split 
    ·
      intro hfx 
      byCases' hx : DifferentiableAt 𝕜 f x
      ·
        exact Or.inl ⟨hx, hfx⟩
      ·
        rw [fderiv_zero_of_not_differentiable_at hx] at hfx 
        exact Or.inr ⟨hfx, hx⟩
    ·
      rintro (⟨hf, hf'⟩ | ⟨h₀, hx⟩)
      ·
        exact hf'
      ·
        rwa [fderiv_zero_of_not_differentiable_at hx]

end FderivProperties

section Continuous

/-! ### Deducing continuity from differentiability -/


-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_fderiv_at_filter.tendsto_nhds
(hL : «expr ≤ »(L, expr𝓝() x))
(h : has_fderiv_at_filter f f' x L) : tendsto f L (expr𝓝() (f x)) :=
begin
  have [] [":", expr tendsto (λ x', «expr - »(f x', f x)) L (expr𝓝() 0)] [],
  { refine [expr h.is_O_sub.trans_tendsto (tendsto.mono_left _ hL)],
    rw ["<-", expr sub_self x] [],
    exact [expr tendsto_id.sub tendsto_const_nhds] },
  have [] [] [":=", expr tendsto.add this tendsto_const_nhds],
  rw [expr zero_add (f x)] ["at", ident this],
  exact [expr this.congr (by simp [] [] [] [] [] [])]
end

theorem HasFderivWithinAt.continuous_within_at (h : HasFderivWithinAt f f' s x) : ContinuousWithinAt f s x :=
  HasFderivAtFilter.tendsto_nhds inf_le_left h

theorem HasFderivAt.continuous_at (h : HasFderivAt f f' x) : ContinuousAt f x :=
  HasFderivAtFilter.tendsto_nhds (le_reflₓ _) h

theorem DifferentiableWithinAt.continuous_within_at (h : DifferentiableWithinAt 𝕜 f s x) : ContinuousWithinAt f s x :=
  let ⟨f', hf'⟩ := h 
  hf'.continuous_within_at

theorem DifferentiableAt.continuous_at (h : DifferentiableAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨f', hf'⟩ := h 
  hf'.continuous_at

theorem DifferentiableOn.continuous_on (h : DifferentiableOn 𝕜 f s) : ContinuousOn f s :=
  fun x hx => (h x hx).ContinuousWithinAt

theorem Differentiable.continuous (h : Differentiable 𝕜 f) : Continuous f :=
  continuous_iff_continuous_at.2$ fun x => (h x).ContinuousAt

protected theorem HasStrictFderivAt.continuous_at (hf : HasStrictFderivAt f f' x) : ContinuousAt f x :=
  hf.has_fderiv_at.continuous_at

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_strict_fderiv_at.is_O_sub_rev
{f' : «expr ≃L[ ] »(E, 𝕜, F)}
(hf : has_strict_fderiv_at f (f' : «expr →L[ ] »(E, 𝕜, F)) x) : is_O (λ
 p : «expr × »(E, E), «expr - »(p.1, p.2)) (λ p : «expr × »(E, E), «expr - »(f p.1, f p.2)) (expr𝓝() (x, x)) :=
((f'.is_O_comp_rev _ _).trans (hf.trans_is_O (f'.is_O_comp_rev _ _)).right_is_O_add).congr (λ
 _, rfl) (λ _, sub_add_cancel _ _)

theorem HasFderivAtFilter.is_O_sub_rev {f' : E ≃L[𝕜] F} (hf : HasFderivAtFilter f (f' : E →L[𝕜] F) x L) :
  is_O (fun x' => x' - x) (fun x' => f x' - f x) L :=
  ((f'.is_O_sub_rev _ _).trans (hf.trans_is_O (f'.is_O_sub_rev _ _)).right_is_O_add).congr (fun _ => rfl)
    fun _ => sub_add_cancel _ _

end Continuous

section congr

/-! ### congr properties of the derivative -/


theorem Filter.EventuallyEq.has_strict_fderiv_at_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
  HasStrictFderivAt f₀ f₀' x ↔ HasStrictFderivAt f₁ f₁' x :=
  by 
    refine' is_o_congr ((h.prod_mk_nhds h).mono _) (eventually_of_forall$ fun _ => rfl)
    rintro p ⟨hp₁, hp₂⟩
    simp only 

theorem HasStrictFderivAt.congr_of_eventually_eq (h : HasStrictFderivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) :
  HasStrictFderivAt f₁ f' x :=
  (h₁.has_strict_fderiv_at_iff fun _ => rfl).1 h

theorem Filter.EventuallyEq.has_fderiv_at_filter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  HasFderivAtFilter f₀ f₀' x L ↔ HasFderivAtFilter f₁ f₁' x L :=
  is_o_congr
    (h₀.mono$
      fun y hy =>
        by 
          simp only [hy, h₁, hx])
    (eventually_of_forall$ fun _ => rfl)

theorem HasFderivAtFilter.congr_of_eventually_eq (h : HasFderivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) :
  HasFderivAtFilter f₁ f' x L :=
  (hL.has_fderiv_at_filter_iff hx$ fun _ => rfl).2 h

theorem HasFderivWithinAt.congr_mono (h : HasFderivWithinAt f f' s x) (ht : ∀ x (_ : x ∈ t), f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasFderivWithinAt f₁ f' t x :=
  HasFderivAtFilter.congr_of_eventually_eq (h.mono h₁) (Filter.mem_inf_of_right ht) hx

theorem HasFderivWithinAt.congr (h : HasFderivWithinAt f f' s x) (hs : ∀ x (_ : x ∈ s), f₁ x = f x) (hx : f₁ x = f x) :
  HasFderivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (subset.refl _)

theorem HasFderivWithinAt.congr' (h : HasFderivWithinAt f f' s x) (hs : ∀ x (_ : x ∈ s), f₁ x = f x) (hx : x ∈ s) :
  HasFderivWithinAt f₁ f' s x :=
  h.congr hs (hs x hx)

theorem HasFderivWithinAt.congr_of_eventually_eq (h : HasFderivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  (hx : f₁ x = f x) : HasFderivWithinAt f₁ f' s x :=
  HasFderivAtFilter.congr_of_eventually_eq h h₁ hx

theorem HasFderivAt.congr_of_eventually_eq (h : HasFderivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasFderivAt f₁ f' x :=
  HasFderivAtFilter.congr_of_eventually_eq h h₁ (mem_of_mem_nhds h₁ : _)

theorem DifferentiableWithinAt.congr_mono (h : DifferentiableWithinAt 𝕜 f s x) (ht : ∀ x (_ : x ∈ t), f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : DifferentiableWithinAt 𝕜 f₁ t x :=
  (HasFderivWithinAt.congr_mono h.has_fderiv_within_at ht hx h₁).DifferentiableWithinAt

theorem DifferentiableWithinAt.congr (h : DifferentiableWithinAt 𝕜 f s x) (ht : ∀ x (_ : x ∈ s), f₁ x = f x)
  (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  DifferentiableWithinAt.congr_mono h ht hx (subset.refl _)

theorem DifferentiableWithinAt.congr_of_eventually_eq (h : DifferentiableWithinAt 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.has_fderiv_within_at.congr_of_eventually_eq h₁ hx).DifferentiableWithinAt

theorem DifferentiableOn.congr_mono (h : DifferentiableOn 𝕜 f s) (h' : ∀ x (_ : x ∈ t), f₁ x = f x) (h₁ : t ⊆ s) :
  DifferentiableOn 𝕜 f₁ t :=
  fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

theorem DifferentiableOn.congr (h : DifferentiableOn 𝕜 f s) (h' : ∀ x (_ : x ∈ s), f₁ x = f x) :
  DifferentiableOn 𝕜 f₁ s :=
  fun x hx => (h x hx).congr h' (h' x hx)

theorem differentiable_on_congr (h' : ∀ x (_ : x ∈ s), f₁ x = f x) : DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => DifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h => DifferentiableOn.congr h h'⟩

theorem DifferentiableAt.congr_of_eventually_eq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
  DifferentiableAt 𝕜 f₁ x :=
  HasFderivAt.differentiable_at (HasFderivAtFilter.congr_of_eventually_eq h.has_fderiv_at hL (mem_of_mem_nhds hL : _))

theorem DifferentiableWithinAt.fderiv_within_congr_mono (h : DifferentiableWithinAt 𝕜 f s x)
  (hs : ∀ x (_ : x ∈ t), f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
  fderivWithin 𝕜 f₁ t x = fderivWithin 𝕜 f s x :=
  (HasFderivWithinAt.congr_mono h.has_fderiv_within_at hs hx h₁).fderivWithin hxt

theorem Filter.EventuallyEq.fderiv_within_eq (hs : UniqueDiffWithinAt 𝕜 s x) (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  if h : DifferentiableWithinAt 𝕜 f s x then
    HasFderivWithinAt.fderiv_within (h.has_fderiv_within_at.congr_of_eventually_eq hL hx) hs else
    have h' : ¬DifferentiableWithinAt 𝕜 f₁ s x :=
      mt (fun h => h.congr_of_eventually_eq (hL.mono$ fun x => Eq.symm) hx.symm) h 
    by 
      rw [fderiv_within_zero_of_not_differentiable_within_at h, fderiv_within_zero_of_not_differentiable_within_at h']

theorem fderiv_within_congr (hs : UniqueDiffWithinAt 𝕜 s x) (hL : ∀ y (_ : y ∈ s), f₁ y = f y) (hx : f₁ x = f x) :
  fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  by 
    apply Filter.EventuallyEq.fderiv_within_eq hs _ hx 
    apply mem_of_superset self_mem_nhds_within 
    exact hL

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem filter.eventually_eq.fderiv_eq
(hL : «expr =ᶠ[ ] »(f₁, expr𝓝() x, f)) : «expr = »(fderiv 𝕜 f₁ x, fderiv 𝕜 f x) :=
begin
  have [ident A] [":", expr «expr = »(f₁ x, f x)] [":=", expr hL.eq_of_nhds],
  rw ["[", "<-", expr fderiv_within_univ, ",", "<-", expr fderiv_within_univ, "]"] [],
  rw ["<-", expr nhds_within_univ] ["at", ident hL],
  exact [expr hL.fderiv_within_eq unique_diff_within_at_univ A]
end

protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
  h.eventually_eq_nhds.mono$ fun x h => h.fderiv_eq

end congr

section id

/-! ### Derivative of the identity -/


theorem has_strict_fderiv_at_id (x : E) : HasStrictFderivAt id (id 𝕜 E) x :=
  (is_o_zero _ _).congr_left$
    by 
      simp 

theorem has_fderiv_at_filter_id (x : E) (L : Filter E) : HasFderivAtFilter id (id 𝕜 E) x L :=
  (is_o_zero _ _).congr_left$
    by 
      simp 

theorem has_fderiv_within_at_id (x : E) (s : Set E) : HasFderivWithinAt id (id 𝕜 E) s x :=
  has_fderiv_at_filter_id _ _

theorem has_fderiv_at_id (x : E) : HasFderivAt id (id 𝕜 E) x :=
  has_fderiv_at_filter_id _ _

@[simp]
theorem differentiable_at_id : DifferentiableAt 𝕜 id x :=
  (has_fderiv_at_id x).DifferentiableAt

@[simp]
theorem differentiable_at_id' : DifferentiableAt 𝕜 (fun x => x) x :=
  (has_fderiv_at_id x).DifferentiableAt

theorem differentiable_within_at_id : DifferentiableWithinAt 𝕜 id s x :=
  differentiable_at_id.DifferentiableWithinAt

@[simp]
theorem differentiable_id : Differentiable 𝕜 (id : E → E) :=
  fun x => differentiable_at_id

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem differentiable_id' : differentiable 𝕜 (λ x : E, x) := λ x, differentiable_at_id

theorem differentiable_on_id : DifferentiableOn 𝕜 id s :=
  differentiable_id.DifferentiableOn

theorem fderiv_id : fderiv 𝕜 id x = id 𝕜 E :=
  HasFderivAt.fderiv (has_fderiv_at_id x)

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem fderiv_id' : «expr = »(fderiv 𝕜 (λ x : E, x) x, continuous_linear_map.id 𝕜 E) := fderiv_id

theorem fderiv_within_id (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = id 𝕜 E :=
  by 
    rw [DifferentiableAt.fderiv_within differentiable_at_id hxs]
    exact fderiv_id

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem fderiv_within_id'
(hxs : unique_diff_within_at 𝕜 s x) : «expr = »(fderiv_within 𝕜 (λ x : E, x) s x, continuous_linear_map.id 𝕜 E) :=
fderiv_within_id hxs

end id

section Const

/-! ### derivative of a constant function -/


theorem has_strict_fderiv_at_const (c : F) (x : E) : HasStrictFderivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  (is_o_zero _ _).congr_left$
    fun _ =>
      by 
        simp only [zero_apply, sub_self]

theorem has_fderiv_at_filter_const (c : F) (x : E) (L : Filter E) :
  HasFderivAtFilter (fun x => c) (0 : E →L[𝕜] F) x L :=
  (is_o_zero _ _).congr_left$
    fun _ =>
      by 
        simp only [zero_apply, sub_self]

theorem has_fderiv_within_at_const (c : F) (x : E) (s : Set E) : HasFderivWithinAt (fun x => c) (0 : E →L[𝕜] F) s x :=
  has_fderiv_at_filter_const _ _ _

theorem has_fderiv_at_const (c : F) (x : E) : HasFderivAt (fun x => c) (0 : E →L[𝕜] F) x :=
  has_fderiv_at_filter_const _ _ _

@[simp]
theorem differentiable_at_const (c : F) : DifferentiableAt 𝕜 (fun x => c) x :=
  ⟨0, has_fderiv_at_const c x⟩

theorem differentiable_within_at_const (c : F) : DifferentiableWithinAt 𝕜 (fun x => c) s x :=
  DifferentiableAt.differentiable_within_at (differentiable_at_const _)

theorem fderiv_const_apply (c : F) : fderiv 𝕜 (fun y => c) x = 0 :=
  HasFderivAt.fderiv (has_fderiv_at_const c x)

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem fderiv_const (c : F) : «expr = »(fderiv 𝕜 (λ y : E, c), 0) :=
by { ext [] [ident m] [],
  rw [expr fderiv_const_apply] [],
  refl }

theorem fderiv_within_const_apply (c : F) (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (fun y => c) s x = 0 :=
  by 
    rw [DifferentiableAt.fderiv_within (differentiable_at_const _) hxs]
    exact fderiv_const_apply _

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem differentiable_const (c : F) : differentiable 𝕜 (λ x : E, c) := λ x, differentiable_at_const _

theorem differentiable_on_const (c : F) : DifferentiableOn 𝕜 (fun x => c) s :=
  (differentiable_const _).DifferentiableOn

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_fderiv_at_of_subsingleton
{R X Y : Type*}
[nondiscrete_normed_field R]
[normed_group X]
[normed_group Y]
[normed_space R X]
[normed_space R Y]
[h : subsingleton X]
(f : X → Y)
(x : X) : has_fderiv_at f (0 : «expr →L[ ] »(X, R, Y)) x :=
begin
  rw [expr subsingleton_iff] ["at", ident h],
  have [ident key] [":", expr «expr = »(function.const X (f 0), f)] [":=", expr by ext [] [ident x'] []; rw [expr h x' 0] []],
  exact [expr «expr ▸ »(key, has_fderiv_at_const (f 0) _)]
end

end Const

section ContinuousLinearMap

/-!
### Continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `continuous_linear_map`, and denoted `E →L[𝕜] F`), and the unbundled version (with a
predicate `is_bounded_linear_map`). We give statements for both versions. -/


protected theorem ContinuousLinearMap.has_strict_fderiv_at {x : E} : HasStrictFderivAt e e x :=
  (is_o_zero _ _).congr_left$
    fun x =>
      by 
        simp only [e.map_sub, sub_self]

protected theorem ContinuousLinearMap.has_fderiv_at_filter : HasFderivAtFilter e e x L :=
  (is_o_zero _ _).congr_left$
    fun x =>
      by 
        simp only [e.map_sub, sub_self]

protected theorem ContinuousLinearMap.has_fderiv_within_at : HasFderivWithinAt e e s x :=
  e.has_fderiv_at_filter

protected theorem ContinuousLinearMap.has_fderiv_at : HasFderivAt e e x :=
  e.has_fderiv_at_filter

@[simp]
protected theorem ContinuousLinearMap.differentiable_at : DifferentiableAt 𝕜 e x :=
  e.has_fderiv_at.differentiable_at

protected theorem ContinuousLinearMap.differentiable_within_at : DifferentiableWithinAt 𝕜 e s x :=
  e.differentiable_at.differentiable_within_at

@[simp]
protected theorem ContinuousLinearMap.fderiv : fderiv 𝕜 e x = e :=
  e.has_fderiv_at.fderiv

protected theorem ContinuousLinearMap.fderiv_within (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 e s x = e :=
  by 
    rw [DifferentiableAt.fderiv_within e.differentiable_at hxs]
    exact e.fderiv

@[simp]
protected theorem ContinuousLinearMap.differentiable : Differentiable 𝕜 e :=
  fun x => e.differentiable_at

protected theorem ContinuousLinearMap.differentiable_on : DifferentiableOn 𝕜 e s :=
  e.differentiable.differentiable_on

theorem IsBoundedLinearMap.has_fderiv_at_filter (h : IsBoundedLinearMap 𝕜 f) :
  HasFderivAtFilter f h.to_continuous_linear_map x L :=
  h.to_continuous_linear_map.has_fderiv_at_filter

theorem IsBoundedLinearMap.has_fderiv_within_at (h : IsBoundedLinearMap 𝕜 f) :
  HasFderivWithinAt f h.to_continuous_linear_map s x :=
  h.has_fderiv_at_filter

theorem IsBoundedLinearMap.has_fderiv_at (h : IsBoundedLinearMap 𝕜 f) : HasFderivAt f h.to_continuous_linear_map x :=
  h.has_fderiv_at_filter

theorem IsBoundedLinearMap.differentiable_at (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.has_fderiv_at.differentiable_at

theorem IsBoundedLinearMap.differentiable_within_at (h : IsBoundedLinearMap 𝕜 f) : DifferentiableWithinAt 𝕜 f s x :=
  h.differentiable_at.differentiable_within_at

theorem IsBoundedLinearMap.fderiv (h : IsBoundedLinearMap 𝕜 f) : fderiv 𝕜 f x = h.to_continuous_linear_map :=
  HasFderivAt.fderiv h.has_fderiv_at

theorem IsBoundedLinearMap.fderiv_within (h : IsBoundedLinearMap 𝕜 f) (hxs : UniqueDiffWithinAt 𝕜 s x) :
  fderivWithin 𝕜 f s x = h.to_continuous_linear_map :=
  by 
    rw [DifferentiableAt.fderiv_within h.differentiable_at hxs]
    exact h.fderiv

theorem IsBoundedLinearMap.differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun x => h.differentiable_at

theorem IsBoundedLinearMap.differentiable_on (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.differentiable.differentiable_on

end ContinuousLinearMap

section Composition

/-!
### Derivative of the composition of two functions

For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/


variable(x)

theorem HasFderivAtFilter.comp {g : F → G} {g' : F →L[𝕜] G} (hg : HasFderivAtFilter g g' (f x) (L.map f))
  (hf : HasFderivAtFilter f f' x L) : HasFderivAtFilter (g ∘ f) (g'.comp f') x L :=
  let eq₁ := (g'.is_O_comp _ _).trans_is_o hf 
  let eq₂ := (hg.comp_tendsto tendsto_map).trans_is_O hf.is_O_sub 
  by 
    refine' eq₂.triangle (eq₁.congr_left fun x' => _)
    simp 

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
example
{g : F → G}
{g' : «expr →L[ ] »(F, 𝕜, G)}
(hg : has_fderiv_at_filter g g' (f x) (L.map f))
(hf : has_fderiv_at_filter f f' x L) : has_fderiv_at_filter «expr ∘ »(g, f) (g'.comp f') x L :=
begin
  unfold [ident has_fderiv_at_filter] ["at", ident hg],
  have [] [":", expr is_o (λ
    x', «expr - »(«expr - »(g (f x'), g (f x)), g' «expr - »(f x', f x))) (λ x', «expr - »(f x', f x)) L] [],
  from [expr hg.comp_tendsto (le_refl _)],
  have [ident eq₁] [":", expr is_o (λ
    x', «expr - »(«expr - »(g (f x'), g (f x)), g' «expr - »(f x', f x))) (λ x', «expr - »(x', x)) L] [],
  from [expr this.trans_is_O hf.is_O_sub],
  have [ident eq₂] [":", expr is_o (λ
    x', «expr - »(«expr - »(f x', f x), f' «expr - »(x', x))) (λ x', «expr - »(x', x)) L] [],
  from [expr hf],
  have [] [":", expr is_O (λ
    x', g' «expr - »(«expr - »(f x', f x), f' «expr - »(x', x))) (λ
    x', «expr - »(«expr - »(f x', f x), f' «expr - »(x', x))) L] [],
  from [expr g'.is_O_comp _ _],
  have [] [":", expr is_o (λ
    x', g' «expr - »(«expr - »(f x', f x), f' «expr - »(x', x))) (λ x', «expr - »(x', x)) L] [],
  from [expr this.trans_is_o eq₂],
  have [ident eq₃] [":", expr is_o (λ
    x', «expr - »(g' «expr - »(f x', f x), g' (f' «expr - »(x', x)))) (λ x', «expr - »(x', x)) L] [],
  by { refine [expr this.congr_left _],
    simp [] [] [] [] [] [] },
  exact [expr eq₁.triangle eq₃]
end

theorem HasFderivWithinAt.comp {g : F → G} {g' : F →L[𝕜] G} {t : Set F} (hg : HasFderivWithinAt g g' t (f x))
  (hf : HasFderivWithinAt f f' s x) (hst : s ⊆ f ⁻¹' t) : HasFderivWithinAt (g ∘ f) (g'.comp f') s x :=
  by 
    apply HasFderivAtFilter.comp _ (HasFderivAtFilter.mono hg _) hf 
    calc map f (𝓝[s] x) ≤ 𝓝[f '' s] f x := hf.continuous_within_at.tendsto_nhds_within_image _ ≤ 𝓝[t] f x :=
      nhds_within_mono _ (image_subset_iff.mpr hst)

/-- The chain rule. -/
theorem HasFderivAt.comp {g : F → G} {g' : F →L[𝕜] G} (hg : HasFderivAt g g' (f x)) (hf : HasFderivAt f f' x) :
  HasFderivAt (g ∘ f) (g'.comp f') x :=
  (hg.mono hf.continuous_at).comp x hf

theorem HasFderivAt.comp_has_fderiv_within_at {g : F → G} {g' : F →L[𝕜] G} (hg : HasFderivAt g g' (f x))
  (hf : HasFderivWithinAt f f' s x) : HasFderivWithinAt (g ∘ f) (g'.comp f') s x :=
  by 
    rw [←has_fderiv_within_at_univ] at hg 
    exact HasFderivWithinAt.comp x hg hf subset_preimage_univ

theorem DifferentiableWithinAt.comp {g : F → G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
  (hf : DifferentiableWithinAt 𝕜 f s x) (h : s ⊆ f ⁻¹' t) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  by 
    rcases hf with ⟨f', hf'⟩
    rcases hg with ⟨g', hg'⟩
    exact ⟨ContinuousLinearMap.comp g' f', hg'.comp x hf' h⟩

theorem DifferentiableWithinAt.comp' {g : F → G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
  (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

theorem DifferentiableAt.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
  DifferentiableAt 𝕜 (g ∘ f) x :=
  (hg.has_fderiv_at.comp x hf.has_fderiv_at).DifferentiableAt

theorem DifferentiableAt.comp_differentiable_within_at {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
  (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  (differentiable_within_at_univ.2 hg).comp x hf
    (by 
      simp )

theorem fderivWithin.comp {g : F → G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
  (hf : DifferentiableWithinAt 𝕜 f s x) (h : maps_to f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
  fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) :=
  by 
    apply HasFderivWithinAt.fderiv_within _ hxs 
    exact HasFderivWithinAt.comp x hg.has_fderiv_within_at hf.has_fderiv_within_at h

theorem fderiv.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
  fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  by 
    apply HasFderivAt.fderiv 
    exact HasFderivAt.comp x hg.has_fderiv_at hf.has_fderiv_at

theorem fderiv.comp_fderiv_within {g : F → G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableWithinAt 𝕜 f s x)
  (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderivWithin 𝕜 f s x) :=
  by 
    apply HasFderivWithinAt.fderiv_within _ hxs 
    exact HasFderivAt.comp_has_fderiv_within_at x hg.has_fderiv_at hf.has_fderiv_within_at

theorem DifferentiableOn.comp {g : F → G} {t : Set F} (hg : DifferentiableOn 𝕜 g t) (hf : DifferentiableOn 𝕜 f s)
  (st : s ⊆ f ⁻¹' t) : DifferentiableOn 𝕜 (g ∘ f) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

theorem Differentiable.comp {g : F → G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
  Differentiable 𝕜 (g ∘ f) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

theorem Differentiable.comp_differentiable_on {g : F → G} (hg : Differentiable 𝕜 g) (hf : DifferentiableOn 𝕜 f s) :
  DifferentiableOn 𝕜 (g ∘ f) s :=
  (differentiable_on_univ.2 hg).comp hf
    (by 
      simp )

/-- The chain rule for derivatives in the sense of strict differentiability. -/
protected theorem HasStrictFderivAt.comp {g : F → G} {g' : F →L[𝕜] G} (hg : HasStrictFderivAt g g' (f x))
  (hf : HasStrictFderivAt f f' x) : HasStrictFderivAt (fun x => g (f x)) (g'.comp f') x :=
  ((hg.comp_tendsto (hf.continuous_at.prod_map' hf.continuous_at)).trans_is_O hf.is_O_sub).triangle$
    by 
      simpa only [g'.map_sub, f'.coe_comp'] using (g'.is_O_comp _ _).trans_is_o hf

protected theorem Differentiable.iterate {f : E → E} (hf : Differentiable 𝕜 f) (n : ℕ) : Differentiable 𝕜 (f^[n]) :=
  Nat.recOn n differentiable_id fun n ihn => ihn.comp hf

protected theorem DifferentiableOn.iterate {f : E → E} (hf : DifferentiableOn 𝕜 f s) (hs : maps_to f s s) (n : ℕ) :
  DifferentiableOn 𝕜 (f^[n]) s :=
  Nat.recOn n differentiable_on_id fun n ihn => ihn.comp hf hs

variable{x}

protected theorem HasFderivAtFilter.iterate {f : E → E} {f' : E →L[𝕜] E} (hf : HasFderivAtFilter f f' x L)
  (hL : tendsto f L L) (hx : f x = x) (n : ℕ) : HasFderivAtFilter (f^[n]) (f' ^ n) x L :=
  by 
    induction' n with n ihn
    ·
      exact has_fderiv_at_filter_id x L
    ·
      change HasFderivAtFilter (f^[n] ∘ f) (f' ^ n+1) x L 
      rw [pow_succ'ₓ]
      refine' HasFderivAtFilter.comp x _ hf 
      rw [hx]
      exact ihn.mono hL

protected theorem HasFderivAt.iterate {f : E → E} {f' : E →L[𝕜] E} (hf : HasFderivAt f f' x) (hx : f x = x) (n : ℕ) :
  HasFderivAt (f^[n]) (f' ^ n) x :=
  by 
    refine' hf.iterate _ hx n 
    convert hf.continuous_at 
    exact hx.symm

protected theorem HasFderivWithinAt.iterate {f : E → E} {f' : E →L[𝕜] E} (hf : HasFderivWithinAt f f' s x)
  (hx : f x = x) (hs : maps_to f s s) (n : ℕ) : HasFderivWithinAt (f^[n]) (f' ^ n) s x :=
  by 
    refine' hf.iterate _ hx n 
    convert tendsto_inf.2 ⟨hf.continuous_within_at, _⟩
    exacts[hx.symm, (tendsto_principal_principal.2 hs).mono_left inf_le_right]

protected theorem HasStrictFderivAt.iterate {f : E → E} {f' : E →L[𝕜] E} (hf : HasStrictFderivAt f f' x) (hx : f x = x)
  (n : ℕ) : HasStrictFderivAt (f^[n]) (f' ^ n) x :=
  by 
    induction' n with n ihn
    ·
      exact has_strict_fderiv_at_id x
    ·
      change HasStrictFderivAt (f^[n] ∘ f) (f' ^ n+1) x 
      rw [pow_succ'ₓ]
      refine' HasStrictFderivAt.comp x _ hf 
      rwa [hx]

protected theorem DifferentiableAt.iterate {f : E → E} (hf : DifferentiableAt 𝕜 f x) (hx : f x = x) (n : ℕ) :
  DifferentiableAt 𝕜 (f^[n]) x :=
  Exists.elim hf$ fun f' hf => (hf.iterate hx n).DifferentiableAt

protected theorem DifferentiableWithinAt.iterate {f : E → E} (hf : DifferentiableWithinAt 𝕜 f s x) (hx : f x = x)
  (hs : maps_to f s s) (n : ℕ) : DifferentiableWithinAt 𝕜 (f^[n]) s x :=
  Exists.elim hf$ fun f' hf => (hf.iterate hx hs n).DifferentiableWithinAt

end Composition

section CartesianProduct

/-! ### Derivative of the cartesian product of two functions -/


section Prod

variable{f₂ : E → G}{f₂' : E →L[𝕜] G}

protected theorem HasStrictFderivAt.prod (hf₁ : HasStrictFderivAt f₁ f₁' x) (hf₂ : HasStrictFderivAt f₂ f₂' x) :
  HasStrictFderivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  hf₁.prod_left hf₂

theorem HasFderivAtFilter.prod (hf₁ : HasFderivAtFilter f₁ f₁' x L) (hf₂ : HasFderivAtFilter f₂ f₂' x L) :
  HasFderivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x L :=
  hf₁.prod_left hf₂

theorem HasFderivWithinAt.prod (hf₁ : HasFderivWithinAt f₁ f₁' s x) (hf₂ : HasFderivWithinAt f₂ f₂' s x) :
  HasFderivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
  hf₁.prod hf₂

theorem HasFderivAt.prod (hf₁ : HasFderivAt f₁ f₁' x) (hf₂ : HasFderivAt f₂ f₂' x) :
  HasFderivAt (fun x => (f₁ x, f₂ x)) (ContinuousLinearMap.prod f₁' f₂') x :=
  hf₁.prod hf₂

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem differentiable_within_at.prod
(hf₁ : differentiable_within_at 𝕜 f₁ s x)
(hf₂ : differentiable_within_at 𝕜 f₂ s x) : differentiable_within_at 𝕜 (λ x : E, (f₁ x, f₂ x)) s x :=
(hf₁.has_fderiv_within_at.prod hf₂.has_fderiv_within_at).differentiable_within_at

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem differentiable_at.prod
(hf₁ : differentiable_at 𝕜 f₁ x)
(hf₂ : differentiable_at 𝕜 f₂ x) : differentiable_at 𝕜 (λ x : E, (f₁ x, f₂ x)) x :=
(hf₁.has_fderiv_at.prod hf₂.has_fderiv_at).differentiable_at

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem differentiable_on.prod
(hf₁ : differentiable_on 𝕜 f₁ s)
(hf₂ : differentiable_on 𝕜 f₂ s) : differentiable_on 𝕜 (λ x : E, (f₁ x, f₂ x)) s :=
λ x hx, differentiable_within_at.prod (hf₁ x hx) (hf₂ x hx)

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem differentiable.prod
(hf₁ : differentiable 𝕜 f₁)
(hf₂ : differentiable 𝕜 f₂) : differentiable 𝕜 (λ x : E, (f₁ x, f₂ x)) :=
λ x, differentiable_at.prod (hf₁ x) (hf₂ x)

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem differentiable_at.fderiv_prod
(hf₁ : differentiable_at 𝕜 f₁ x)
(hf₂ : differentiable_at 𝕜 f₂ x) : «expr = »(fderiv 𝕜 (λ
  x : E, (f₁ x, f₂ x)) x, (fderiv 𝕜 f₁ x).prod (fderiv 𝕜 f₂ x)) :=
(hf₁.has_fderiv_at.prod hf₂.has_fderiv_at).fderiv

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem differentiable_at.fderiv_within_prod
(hf₁ : differentiable_within_at 𝕜 f₁ s x)
(hf₂ : differentiable_within_at 𝕜 f₂ s x)
(hxs : unique_diff_within_at 𝕜 s x) : «expr = »(fderiv_within 𝕜 (λ
  x : E, (f₁ x, f₂ x)) s x, (fderiv_within 𝕜 f₁ s x).prod (fderiv_within 𝕜 f₂ s x)) :=
begin
  apply [expr has_fderiv_within_at.fderiv_within _ hxs],
  exact [expr has_fderiv_within_at.prod hf₁.has_fderiv_within_at hf₂.has_fderiv_within_at]
end

end Prod

section Fst

variable{f₂ : E → F × G}{f₂' : E →L[𝕜] F × G}{p : E × F}

theorem has_strict_fderiv_at_fst : HasStrictFderivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  (fst 𝕜 E F).HasStrictFderivAt

protected theorem HasStrictFderivAt.fst (h : HasStrictFderivAt f₂ f₂' x) :
  HasStrictFderivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  has_strict_fderiv_at_fst.comp x h

theorem has_fderiv_at_filter_fst {L : Filter (E × F)} : HasFderivAtFilter (@Prod.fst E F) (fst 𝕜 E F) p L :=
  (fst 𝕜 E F).HasFderivAtFilter

protected theorem HasFderivAtFilter.fst (h : HasFderivAtFilter f₂ f₂' x L) :
  HasFderivAtFilter (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x L :=
  has_fderiv_at_filter_fst.comp x h

theorem has_fderiv_at_fst : HasFderivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  has_fderiv_at_filter_fst

protected theorem HasFderivAt.fst (h : HasFderivAt f₂ f₂' x) :
  HasFderivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst

theorem has_fderiv_within_at_fst {s : Set (E × F)} : HasFderivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p :=
  has_fderiv_at_filter_fst

protected theorem HasFderivWithinAt.fst (h : HasFderivWithinAt f₂ f₂' s x) :
  HasFderivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst

theorem differentiable_at_fst : DifferentiableAt 𝕜 Prod.fst p :=
  has_fderiv_at_fst.DifferentiableAt

@[simp]
protected theorem DifferentiableAt.fst (h : DifferentiableAt 𝕜 f₂ x) : DifferentiableAt 𝕜 (fun x => (f₂ x).1) x :=
  differentiable_at_fst.comp x h

theorem differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F → E) :=
  fun x => differentiable_at_fst

@[simp]
protected theorem Differentiable.fst (h : Differentiable 𝕜 f₂) : Differentiable 𝕜 fun x => (f₂ x).1 :=
  differentiable_fst.comp h

theorem differentiable_within_at_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.fst s p :=
  differentiable_at_fst.DifferentiableWithinAt

protected theorem DifferentiableWithinAt.fst (h : DifferentiableWithinAt 𝕜 f₂ s x) :
  DifferentiableWithinAt 𝕜 (fun x => (f₂ x).1) s x :=
  differentiable_at_fst.comp_differentiable_within_at x h

theorem differentiable_on_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s :=
  differentiable_fst.DifferentiableOn

protected theorem DifferentiableOn.fst (h : DifferentiableOn 𝕜 f₂ s) : DifferentiableOn 𝕜 (fun x => (f₂ x).1) s :=
  differentiable_fst.comp_differentiable_on h

theorem fderiv_fst : fderiv 𝕜 Prod.fst p = fst 𝕜 E F :=
  has_fderiv_at_fst.fderiv

theorem fderiv.fst (h : DifferentiableAt 𝕜 f₂ x) : fderiv 𝕜 (fun x => (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.has_fderiv_at.fst.fderiv

theorem fderiv_within_fst {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) : fderivWithin 𝕜 Prod.fst s p = fst 𝕜 E F :=
  has_fderiv_within_at_fst.fderivWithin hs

theorem fderivWithin.fst (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
  fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.has_fderiv_within_at.fst.fderiv_within hs

end Fst

section Snd

variable{f₂ : E → F × G}{f₂' : E →L[𝕜] F × G}{p : E × F}

theorem has_strict_fderiv_at_snd : HasStrictFderivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  (snd 𝕜 E F).HasStrictFderivAt

protected theorem HasStrictFderivAt.snd (h : HasStrictFderivAt f₂ f₂' x) :
  HasStrictFderivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  has_strict_fderiv_at_snd.comp x h

theorem has_fderiv_at_filter_snd {L : Filter (E × F)} : HasFderivAtFilter (@Prod.snd E F) (snd 𝕜 E F) p L :=
  (snd 𝕜 E F).HasFderivAtFilter

protected theorem HasFderivAtFilter.snd (h : HasFderivAtFilter f₂ f₂' x L) :
  HasFderivAtFilter (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x L :=
  has_fderiv_at_filter_snd.comp x h

theorem has_fderiv_at_snd : HasFderivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  has_fderiv_at_filter_snd

protected theorem HasFderivAt.snd (h : HasFderivAt f₂ f₂' x) :
  HasFderivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  h.snd

theorem has_fderiv_within_at_snd {s : Set (E × F)} : HasFderivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p :=
  has_fderiv_at_filter_snd

protected theorem HasFderivWithinAt.snd (h : HasFderivWithinAt f₂ f₂' s x) :
  HasFderivWithinAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
  h.snd

theorem differentiable_at_snd : DifferentiableAt 𝕜 Prod.snd p :=
  has_fderiv_at_snd.DifferentiableAt

@[simp]
protected theorem DifferentiableAt.snd (h : DifferentiableAt 𝕜 f₂ x) : DifferentiableAt 𝕜 (fun x => (f₂ x).2) x :=
  differentiable_at_snd.comp x h

theorem differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F → F) :=
  fun x => differentiable_at_snd

@[simp]
protected theorem Differentiable.snd (h : Differentiable 𝕜 f₂) : Differentiable 𝕜 fun x => (f₂ x).2 :=
  differentiable_snd.comp h

theorem differentiable_within_at_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.snd s p :=
  differentiable_at_snd.DifferentiableWithinAt

protected theorem DifferentiableWithinAt.snd (h : DifferentiableWithinAt 𝕜 f₂ s x) :
  DifferentiableWithinAt 𝕜 (fun x => (f₂ x).2) s x :=
  differentiable_at_snd.comp_differentiable_within_at x h

theorem differentiable_on_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s :=
  differentiable_snd.DifferentiableOn

protected theorem DifferentiableOn.snd (h : DifferentiableOn 𝕜 f₂ s) : DifferentiableOn 𝕜 (fun x => (f₂ x).2) s :=
  differentiable_snd.comp_differentiable_on h

theorem fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F :=
  has_fderiv_at_snd.fderiv

theorem fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) : fderiv 𝕜 (fun x => (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.has_fderiv_at.snd.fderiv

theorem fderiv_within_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) : fderivWithin 𝕜 Prod.snd s p = snd 𝕜 E F :=
  has_fderiv_within_at_snd.fderivWithin hs

theorem fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
  fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.has_fderiv_within_at.snd.fderiv_within hs

end Snd

section prod_mapₓ

variable{f₂ : G → G'}{f₂' : G →L[𝕜] G'}{y : G}(p : E × G)

protected theorem HasStrictFderivAt.prod_map (hf : HasStrictFderivAt f f' p.1) (hf₂ : HasStrictFderivAt f₂ f₂' p.2) :
  HasStrictFderivAt (Prod.mapₓ f f₂) (f'.prod_map f₂') p :=
  (hf.comp p has_strict_fderiv_at_fst).Prod (hf₂.comp p has_strict_fderiv_at_snd)

protected theorem HasFderivAt.prod_map (hf : HasFderivAt f f' p.1) (hf₂ : HasFderivAt f₂ f₂' p.2) :
  HasFderivAt (Prod.mapₓ f f₂) (f'.prod_map f₂') p :=
  (hf.comp p has_fderiv_at_fst).Prod (hf₂.comp p has_fderiv_at_snd)

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
protected
theorem differentiable_at.prod_map
(hf : differentiable_at 𝕜 f p.1)
(hf₂ : differentiable_at 𝕜 f₂ p.2) : differentiable_at 𝕜 (λ p : «expr × »(E, G), (f p.1, f₂ p.2)) p :=
(hf.comp p differentiable_at_fst).prod (hf₂.comp p differentiable_at_snd)

end prod_mapₓ

end CartesianProduct

section ConstSmul

variable{R : Type _}[Semiringₓ R][Module R F][TopologicalSpace R][SmulCommClass 𝕜 R F][HasContinuousSmul R F]

/-! ### Derivative of a function multiplied by a constant -/


theorem HasStrictFderivAt.const_smul (h : HasStrictFderivAt f f' x) (c : R) :
  HasStrictFderivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).HasStrictFderivAt.comp x h

theorem HasFderivAtFilter.const_smul (h : HasFderivAtFilter f f' x L) (c : R) :
  HasFderivAtFilter (fun x => c • f x) (c • f') x L :=
  (c • (1 : F →L[𝕜] F)).HasFderivAtFilter.comp x h

theorem HasFderivWithinAt.const_smul (h : HasFderivWithinAt f f' s x) (c : R) :
  HasFderivWithinAt (fun x => c • f x) (c • f') s x :=
  h.const_smul c

theorem HasFderivAt.const_smul (h : HasFderivAt f f' x) (c : R) : HasFderivAt (fun x => c • f x) (c • f') x :=
  h.const_smul c

theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
  DifferentiableWithinAt 𝕜 (fun y => c • f y) s x :=
  (h.has_fderiv_within_at.const_smul c).DifferentiableWithinAt

theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) : DifferentiableAt 𝕜 (fun y => c • f y) x :=
  (h.has_fderiv_at.const_smul c).DifferentiableAt

theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) : DifferentiableOn 𝕜 (fun y => c • f y) s :=
  fun x hx => (h x hx).const_smul c

theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) : Differentiable 𝕜 fun y => c • f y :=
  fun x => (h x).const_smul c

theorem fderiv_within_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
  fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.has_fderiv_within_at.const_smul c).fderivWithin hxs

theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) : fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.has_fderiv_at.const_smul c).fderiv

end ConstSmul

section Add

/-! ### Derivative of the sum of two functions -/


theorem HasStrictFderivAt.add (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
  HasStrictFderivAt (fun y => f y+g y) (f'+g') x :=
  (hf.add hg).congr_left$
    fun y =>
      by 
        simp  <;> abel

theorem HasFderivAtFilter.add (hf : HasFderivAtFilter f f' x L) (hg : HasFderivAtFilter g g' x L) :
  HasFderivAtFilter (fun y => f y+g y) (f'+g') x L :=
  (hf.add hg).congr_left$
    fun _ =>
      by 
        simp  <;> abel

theorem HasFderivWithinAt.add (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) :
  HasFderivWithinAt (fun y => f y+g y) (f'+g') s x :=
  hf.add hg

theorem HasFderivAt.add (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
  HasFderivAt (fun x => f x+g x) (f'+g') x :=
  hf.add hg

theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) :
  DifferentiableWithinAt 𝕜 (fun y => f y+g y) s x :=
  (hf.has_fderiv_within_at.add hg.has_fderiv_within_at).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
  DifferentiableAt 𝕜 (fun y => f y+g y) x :=
  (hf.has_fderiv_at.add hg.has_fderiv_at).DifferentiableAt

theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
  DifferentiableOn 𝕜 (fun y => f y+g y) s :=
  fun x hx => (hf x hx).add (hg x hx)

@[simp]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) : Differentiable 𝕜 fun y => f y+g y :=
  fun x => (hf x).add (hg x)

theorem fderiv_within_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  (hg : DifferentiableWithinAt 𝕜 g s x) :
  fderivWithin 𝕜 (fun y => f y+g y) s x = fderivWithin 𝕜 f s x+fderivWithin 𝕜 g s x :=
  (hf.has_fderiv_within_at.add hg.has_fderiv_within_at).fderivWithin hxs

theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
  fderiv 𝕜 (fun y => f y+g y) x = fderiv 𝕜 f x+fderiv 𝕜 g x :=
  (hf.has_fderiv_at.add hg.has_fderiv_at).fderiv

theorem HasStrictFderivAt.add_const (hf : HasStrictFderivAt f f' x) (c : F) : HasStrictFderivAt (fun y => f y+c) f' x :=
  add_zeroₓ f' ▸ hf.add (has_strict_fderiv_at_const _ _)

theorem HasFderivAtFilter.add_const (hf : HasFderivAtFilter f f' x L) (c : F) :
  HasFderivAtFilter (fun y => f y+c) f' x L :=
  add_zeroₓ f' ▸ hf.add (has_fderiv_at_filter_const _ _ _)

theorem HasFderivWithinAt.add_const (hf : HasFderivWithinAt f f' s x) (c : F) :
  HasFderivWithinAt (fun y => f y+c) f' s x :=
  hf.add_const c

theorem HasFderivAt.add_const (hf : HasFderivAt f f' x) (c : F) : HasFderivAt (fun x => f x+c) f' x :=
  hf.add_const c

theorem DifferentiableWithinAt.add_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
  DifferentiableWithinAt 𝕜 (fun y => f y+c) s x :=
  (hf.has_fderiv_within_at.add_const c).DifferentiableWithinAt

@[simp]
theorem differentiable_within_at_add_const_iff (c : F) :
  DifferentiableWithinAt 𝕜 (fun y => f y+c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h =>
      by 
        simpa using h.add_const (-c),
    fun h => h.add_const c⟩

theorem DifferentiableAt.add_const (hf : DifferentiableAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y+c) x :=
  (hf.has_fderiv_at.add_const c).DifferentiableAt

@[simp]
theorem differentiable_at_add_const_iff (c : F) : DifferentiableAt 𝕜 (fun y => f y+c) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h =>
      by 
        simpa using h.add_const (-c),
    fun h => h.add_const c⟩

theorem DifferentiableOn.add_const (hf : DifferentiableOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => f y+c) s :=
  fun x hx => (hf x hx).AddConst c

@[simp]
theorem differentiable_on_add_const_iff (c : F) : DifferentiableOn 𝕜 (fun y => f y+c) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h =>
      by 
        simpa using h.add_const (-c),
    fun h => h.add_const c⟩

theorem Differentiable.add_const (hf : Differentiable 𝕜 f) (c : F) : Differentiable 𝕜 fun y => f y+c :=
  fun x => (hf x).AddConst c

@[simp]
theorem differentiable_add_const_iff (c : F) : (Differentiable 𝕜 fun y => f y+c) ↔ Differentiable 𝕜 f :=
  ⟨fun h =>
      by 
        simpa using h.add_const (-c),
    fun h => h.add_const c⟩

theorem fderiv_within_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
  fderivWithin 𝕜 (fun y => f y+c) s x = fderivWithin 𝕜 f s x :=
  if hf : DifferentiableWithinAt 𝕜 f s x then (hf.has_fderiv_within_at.add_const c).fderivWithin hxs else
    by 
      rw [fderiv_within_zero_of_not_differentiable_within_at hf, fderiv_within_zero_of_not_differentiable_within_at]
      simpa

theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y+c) x = fderiv 𝕜 f x :=
  by 
    simp only [←fderiv_within_univ, fderiv_within_add_const unique_diff_within_at_univ]

theorem HasStrictFderivAt.const_add (hf : HasStrictFderivAt f f' x) (c : F) : HasStrictFderivAt (fun y => c+f y) f' x :=
  zero_addₓ f' ▸ (has_strict_fderiv_at_const _ _).add hf

theorem HasFderivAtFilter.const_add (hf : HasFderivAtFilter f f' x L) (c : F) :
  HasFderivAtFilter (fun y => c+f y) f' x L :=
  zero_addₓ f' ▸ (has_fderiv_at_filter_const _ _ _).add hf

theorem HasFderivWithinAt.const_add (hf : HasFderivWithinAt f f' s x) (c : F) :
  HasFderivWithinAt (fun y => c+f y) f' s x :=
  hf.const_add c

theorem HasFderivAt.const_add (hf : HasFderivAt f f' x) (c : F) : HasFderivAt (fun x => c+f x) f' x :=
  hf.const_add c

theorem DifferentiableWithinAt.const_add (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
  DifferentiableWithinAt 𝕜 (fun y => c+f y) s x :=
  (hf.has_fderiv_within_at.const_add c).DifferentiableWithinAt

@[simp]
theorem differentiable_within_at_const_add_iff (c : F) :
  DifferentiableWithinAt 𝕜 (fun y => c+f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h =>
      by 
        simpa using h.const_add (-c),
    fun h => h.const_add c⟩

theorem DifferentiableAt.const_add (hf : DifferentiableAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => c+f y) x :=
  (hf.has_fderiv_at.const_add c).DifferentiableAt

@[simp]
theorem differentiable_at_const_add_iff (c : F) : DifferentiableAt 𝕜 (fun y => c+f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h =>
      by 
        simpa using h.const_add (-c),
    fun h => h.const_add c⟩

theorem DifferentiableOn.const_add (hf : DifferentiableOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => c+f y) s :=
  fun x hx => (hf x hx).const_add c

@[simp]
theorem differentiable_on_const_add_iff (c : F) : DifferentiableOn 𝕜 (fun y => c+f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h =>
      by 
        simpa using h.const_add (-c),
    fun h => h.const_add c⟩

theorem Differentiable.const_add (hf : Differentiable 𝕜 f) (c : F) : Differentiable 𝕜 fun y => c+f y :=
  fun x => (hf x).const_add c

@[simp]
theorem differentiable_const_add_iff (c : F) : (Differentiable 𝕜 fun y => c+f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h =>
      by 
        simpa using h.const_add (-c),
    fun h => h.const_add c⟩

theorem fderiv_within_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
  fderivWithin 𝕜 (fun y => c+f y) s x = fderivWithin 𝕜 f s x :=
  by 
    simpa only [add_commₓ] using fderiv_within_add_const hxs c

theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c+f y) x = fderiv 𝕜 f x :=
  by 
    simp only [add_commₓ c, fderiv_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


open_locale BigOperators

variable{ι : Type _}{u : Finset ι}{A : ι → E → F}{A' : ι → E →L[𝕜] F}

theorem HasStrictFderivAt.sum (h : ∀ i (_ : i ∈ u), HasStrictFderivAt (A i) (A' i) x) :
  HasStrictFderivAt (fun y => ∑i in u, A i y) (∑i in u, A' i) x :=
  by 
    dsimp [HasStrictFderivAt]  at *
    convert is_o.sum h 
    simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]

theorem HasFderivAtFilter.sum (h : ∀ i (_ : i ∈ u), HasFderivAtFilter (A i) (A' i) x L) :
  HasFderivAtFilter (fun y => ∑i in u, A i y) (∑i in u, A' i) x L :=
  by 
    dsimp [HasFderivAtFilter]  at *
    convert is_o.sum h 
    simp [ContinuousLinearMap.sum_apply]

theorem HasFderivWithinAt.sum (h : ∀ i (_ : i ∈ u), HasFderivWithinAt (A i) (A' i) s x) :
  HasFderivWithinAt (fun y => ∑i in u, A i y) (∑i in u, A' i) s x :=
  HasFderivAtFilter.sum h

theorem HasFderivAt.sum (h : ∀ i (_ : i ∈ u), HasFderivAt (A i) (A' i) x) :
  HasFderivAt (fun y => ∑i in u, A i y) (∑i in u, A' i) x :=
  HasFderivAtFilter.sum h

theorem DifferentiableWithinAt.sum (h : ∀ i (_ : i ∈ u), DifferentiableWithinAt 𝕜 (A i) s x) :
  DifferentiableWithinAt 𝕜 (fun y => ∑i in u, A i y) s x :=
  HasFderivWithinAt.differentiable_within_at$ HasFderivWithinAt.sum$ fun i hi => (h i hi).HasFderivWithinAt

@[simp]
theorem DifferentiableAt.sum (h : ∀ i (_ : i ∈ u), DifferentiableAt 𝕜 (A i) x) :
  DifferentiableAt 𝕜 (fun y => ∑i in u, A i y) x :=
  HasFderivAt.differentiable_at$ HasFderivAt.sum$ fun i hi => (h i hi).HasFderivAt

theorem DifferentiableOn.sum (h : ∀ i (_ : i ∈ u), DifferentiableOn 𝕜 (A i) s) :
  DifferentiableOn 𝕜 (fun y => ∑i in u, A i y) s :=
  fun x hx => DifferentiableWithinAt.sum$ fun i hi => h i hi x hx

@[simp]
theorem Differentiable.sum (h : ∀ i (_ : i ∈ u), Differentiable 𝕜 (A i)) : Differentiable 𝕜 fun y => ∑i in u, A i y :=
  fun x => DifferentiableAt.sum$ fun i hi => h i hi x

theorem fderiv_within_sum (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i (_ : i ∈ u), DifferentiableWithinAt 𝕜 (A i) s x) :
  fderivWithin 𝕜 (fun y => ∑i in u, A i y) s x = ∑i in u, fderivWithin 𝕜 (A i) s x :=
  (HasFderivWithinAt.sum fun i hi => (h i hi).HasFderivWithinAt).fderivWithin hxs

theorem fderiv_sum (h : ∀ i (_ : i ∈ u), DifferentiableAt 𝕜 (A i) x) :
  fderiv 𝕜 (fun y => ∑i in u, A i y) x = ∑i in u, fderiv 𝕜 (A i) x :=
  (HasFderivAt.sum fun i hi => (h i hi).HasFderivAt).fderiv

end Sum

section Pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has_*fderiv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `λ x i, φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `λ x, Φ x i` from
  differentiability of `Φ`.
-/


variable{ι :
    Type
      _}[Fintype
      ι]{F' :
    ι →
      Type
        _}[∀ i,
      NormedGroup
        (F'
          i)][∀ i,
      NormedSpace 𝕜 (F' i)]{φ : ∀ i, E → F' i}{φ' : ∀ i, E →L[𝕜] F' i}{Φ : E → ∀ i, F' i}{Φ' : E →L[𝕜] ∀ i, F' i}

@[simp]
theorem has_strict_fderiv_at_pi' :
  HasStrictFderivAt Φ Φ' x ↔ ∀ i, HasStrictFderivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  by 
    simp only [HasStrictFderivAt, ContinuousLinearMap.coe_pi]
    exact is_o_pi

@[simp]
theorem has_strict_fderiv_at_pi :
  HasStrictFderivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔ ∀ i, HasStrictFderivAt (φ i) (φ' i) x :=
  has_strict_fderiv_at_pi'

@[simp]
theorem has_fderiv_at_filter_pi' :
  HasFderivAtFilter Φ Φ' x L ↔ ∀ i, HasFderivAtFilter (fun x => Φ x i) ((proj i).comp Φ') x L :=
  by 
    simp only [HasFderivAtFilter, ContinuousLinearMap.coe_pi]
    exact is_o_pi

theorem has_fderiv_at_filter_pi :
  HasFderivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') x L ↔ ∀ i, HasFderivAtFilter (φ i) (φ' i) x L :=
  has_fderiv_at_filter_pi'

@[simp]
theorem has_fderiv_at_pi' : HasFderivAt Φ Φ' x ↔ ∀ i, HasFderivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  has_fderiv_at_filter_pi'

theorem has_fderiv_at_pi :
  HasFderivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔ ∀ i, HasFderivAt (φ i) (φ' i) x :=
  has_fderiv_at_filter_pi

@[simp]
theorem has_fderiv_within_at_pi' :
  HasFderivWithinAt Φ Φ' s x ↔ ∀ i, HasFderivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x :=
  has_fderiv_at_filter_pi'

theorem has_fderiv_within_at_pi :
  HasFderivWithinAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') s x ↔ ∀ i, HasFderivWithinAt (φ i) (φ' i) s x :=
  has_fderiv_at_filter_pi

@[simp]
theorem differentiable_within_at_pi :
  DifferentiableWithinAt 𝕜 Φ s x ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x :=
  ⟨fun h i => (has_fderiv_within_at_pi'.1 h.has_fderiv_within_at i).DifferentiableWithinAt,
    fun h => (has_fderiv_within_at_pi.2 fun i => (h i).HasFderivWithinAt).DifferentiableWithinAt⟩

@[simp]
theorem differentiable_at_pi : DifferentiableAt 𝕜 Φ x ↔ ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x :=
  ⟨fun h i => (has_fderiv_at_pi'.1 h.has_fderiv_at i).DifferentiableAt,
    fun h => (has_fderiv_at_pi.2 fun i => (h i).HasFderivAt).DifferentiableAt⟩

theorem differentiable_on_pi : DifferentiableOn 𝕜 Φ s ↔ ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i x hx => differentiable_within_at_pi.1 (h x hx) i,
    fun h x hx => differentiable_within_at_pi.2 fun i => h i x hx⟩

theorem differentiable_pi : Differentiable 𝕜 Φ ↔ ∀ i, Differentiable 𝕜 fun x => Φ x i :=
  ⟨fun h i x => differentiable_at_pi.1 (h x) i, fun h x => differentiable_at_pi.2 fun i => h i x⟩

theorem fderiv_within_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (φ i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
  fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  (has_fderiv_within_at_pi.2 fun i => (h i).HasFderivWithinAt).fderivWithin hs

theorem fderiv_pi (h : ∀ i, DifferentiableAt 𝕜 (φ i) x) :
  fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  (has_fderiv_at_pi.2 fun i => (h i).HasFderivAt).fderiv

end Pi

section Neg

/-! ### Derivative of the negative of a function -/


theorem HasStrictFderivAt.neg (h : HasStrictFderivAt f f' x) : HasStrictFderivAt (fun x => -f x) (-f') x :=
  (-1 : F →L[𝕜] F).HasStrictFderivAt.comp x h

theorem HasFderivAtFilter.neg (h : HasFderivAtFilter f f' x L) : HasFderivAtFilter (fun x => -f x) (-f') x L :=
  (-1 : F →L[𝕜] F).HasFderivAtFilter.comp x h

theorem HasFderivWithinAt.neg (h : HasFderivWithinAt f f' s x) : HasFderivWithinAt (fun x => -f x) (-f') s x :=
  h.neg

theorem HasFderivAt.neg (h : HasFderivAt f f' x) : HasFderivAt (fun x => -f x) (-f') x :=
  h.neg

theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
  DifferentiableWithinAt 𝕜 (fun y => -f y) s x :=
  h.has_fderiv_within_at.neg.differentiable_within_at

@[simp]
theorem differentiable_within_at_neg_iff :
  DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h =>
      by 
        simpa only [neg_negₓ] using h.neg,
    fun h => h.neg⟩

theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y => -f y) x :=
  h.has_fderiv_at.neg.differentiable_at

@[simp]
theorem differentiable_at_neg_iff : DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h =>
      by 
        simpa only [neg_negₓ] using h.neg,
    fun h => h.neg⟩

theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (fun y => -f y) s :=
  fun x hx => (h x hx).neg

@[simp]
theorem differentiable_on_neg_iff : DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h =>
      by 
        simpa only [neg_negₓ] using h.neg,
    fun h => h.neg⟩

theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => -f y :=
  fun x => (h x).neg

@[simp]
theorem differentiable_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h =>
      by 
        simpa only [neg_negₓ] using h.neg,
    fun h => h.neg⟩

theorem fderiv_within_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
  fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x :=
  if h : DifferentiableWithinAt 𝕜 f s x then h.has_fderiv_within_at.neg.fderiv_within hxs else
    by 
      rw [fderiv_within_zero_of_not_differentiable_within_at h, fderiv_within_zero_of_not_differentiable_within_at,
        neg_zero]
      simpa

@[simp]
theorem fderiv_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x :=
  by 
    simp only [←fderiv_within_univ, fderiv_within_neg unique_diff_within_at_univ]

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


theorem HasStrictFderivAt.sub (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
  HasStrictFderivAt (fun x => f x - g x) (f' - g') x :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFderivAtFilter.sub (hf : HasFderivAtFilter f f' x L) (hg : HasFderivAtFilter g g' x L) :
  HasFderivAtFilter (fun x => f x - g x) (f' - g') x L :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFderivWithinAt.sub (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) :
  HasFderivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg

theorem HasFderivAt.sub (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
  HasFderivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg

theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) :
  DifferentiableWithinAt 𝕜 (fun y => f y - g y) s x :=
  (hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
  DifferentiableAt 𝕜 (fun y => f y - g y) x :=
  (hf.has_fderiv_at.sub hg.has_fderiv_at).DifferentiableAt

theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
  DifferentiableOn 𝕜 (fun y => f y - g y) s :=
  fun x hx => (hf x hx).sub (hg x hx)

@[simp]
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) : Differentiable 𝕜 fun y => f y - g y :=
  fun x => (hf x).sub (hg x)

theorem fderiv_within_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
  (hg : DifferentiableWithinAt 𝕜 g s x) :
  fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).fderivWithin hxs

theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
  fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.has_fderiv_at.sub hg.has_fderiv_at).fderiv

theorem HasStrictFderivAt.sub_const (hf : HasStrictFderivAt f f' x) (c : F) :
  HasStrictFderivAt (fun x => f x - c) f' x :=
  by 
    simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem HasFderivAtFilter.sub_const (hf : HasFderivAtFilter f f' x L) (c : F) :
  HasFderivAtFilter (fun x => f x - c) f' x L :=
  by 
    simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem HasFderivWithinAt.sub_const (hf : HasFderivWithinAt f f' s x) (c : F) :
  HasFderivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c

theorem HasFderivAt.sub_const (hf : HasFderivAt f f' x) (c : F) : HasFderivAt (fun x => f x - c) f' x :=
  hf.sub_const c

theorem DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
  DifferentiableWithinAt 𝕜 (fun y => f y - c) s x :=
  (hf.has_fderiv_within_at.sub_const c).DifferentiableWithinAt

@[simp]
theorem differentiable_within_at_sub_const_iff (c : F) :
  DifferentiableWithinAt 𝕜 (fun y => f y - c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  by 
    simp only [sub_eq_add_neg, differentiable_within_at_add_const_iff]

theorem DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x :=
  (hf.has_fderiv_at.sub_const c).DifferentiableAt

@[simp]
theorem differentiable_at_sub_const_iff (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x ↔ DifferentiableAt 𝕜 f x :=
  by 
    simp only [sub_eq_add_neg, differentiable_at_add_const_iff]

theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => f y - c) s :=
  fun x hx => (hf x hx).sub_const c

@[simp]
theorem differentiable_on_sub_const_iff (c : F) : DifferentiableOn 𝕜 (fun y => f y - c) s ↔ DifferentiableOn 𝕜 f s :=
  by 
    simp only [sub_eq_add_neg, differentiable_on_add_const_iff]

theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) : Differentiable 𝕜 fun y => f y - c :=
  fun x => (hf x).sub_const c

@[simp]
theorem differentiable_sub_const_iff (c : F) : (Differentiable 𝕜 fun y => f y - c) ↔ Differentiable 𝕜 f :=
  by 
    simp only [sub_eq_add_neg, differentiable_add_const_iff]

theorem fderiv_within_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
  fderivWithin 𝕜 (fun y => f y - c) s x = fderivWithin 𝕜 f s x :=
  by 
    simp only [sub_eq_add_neg, fderiv_within_add_const hxs]

theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x :=
  by 
    simp only [sub_eq_add_neg, fderiv_add_const]

theorem HasStrictFderivAt.const_sub (hf : HasStrictFderivAt f f' x) (c : F) :
  HasStrictFderivAt (fun x => c - f x) (-f') x :=
  by 
    simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem HasFderivAtFilter.const_sub (hf : HasFderivAtFilter f f' x L) (c : F) :
  HasFderivAtFilter (fun x => c - f x) (-f') x L :=
  by 
    simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem HasFderivWithinAt.const_sub (hf : HasFderivWithinAt f f' s x) (c : F) :
  HasFderivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c

theorem HasFderivAt.const_sub (hf : HasFderivAt f f' x) (c : F) : HasFderivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c

theorem DifferentiableWithinAt.const_sub (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
  DifferentiableWithinAt 𝕜 (fun y => c - f y) s x :=
  (hf.has_fderiv_within_at.const_sub c).DifferentiableWithinAt

@[simp]
theorem differentiable_within_at_const_sub_iff (c : F) :
  DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  by 
    simp [sub_eq_add_neg]

theorem DifferentiableAt.const_sub (hf : DifferentiableAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => c - f y) x :=
  (hf.has_fderiv_at.const_sub c).DifferentiableAt

@[simp]
theorem differentiable_at_const_sub_iff (c : F) : DifferentiableAt 𝕜 (fun y => c - f y) x ↔ DifferentiableAt 𝕜 f x :=
  by 
    simp [sub_eq_add_neg]

theorem DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => c - f y) s :=
  fun x hx => (hf x hx).const_sub c

@[simp]
theorem differentiable_on_const_sub_iff (c : F) : DifferentiableOn 𝕜 (fun y => c - f y) s ↔ DifferentiableOn 𝕜 f s :=
  by 
    simp [sub_eq_add_neg]

theorem Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) : Differentiable 𝕜 fun y => c - f y :=
  fun x => (hf x).const_sub c

@[simp]
theorem differentiable_const_sub_iff (c : F) : (Differentiable 𝕜 fun y => c - f y) ↔ Differentiable 𝕜 f :=
  by 
    simp [sub_eq_add_neg]

theorem fderiv_within_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
  fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x :=
  by 
    simp only [sub_eq_add_neg, fderiv_within_const_add, fderiv_within_neg, hxs]

theorem fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x :=
  by 
    simp only [←fderiv_within_univ, fderiv_within_const_sub unique_diff_within_at_univ]

end Sub

section BilinearMap

/-! ### Derivative of a bounded bilinear map -/


variable{b : E × F → G}{u : Set (E × F)}

open NormedField

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_bounded_bilinear_map.has_strict_fderiv_at
(h : is_bounded_bilinear_map 𝕜 b)
(p : «expr × »(E, F)) : has_strict_fderiv_at b (h.deriv p) p :=
begin
  rw [expr has_strict_fderiv_at] [],
  set [] [ident T] [] [":="] [expr «expr × »(«expr × »(E, F), «expr × »(E, F))] [],
  have [] [":", expr is_o (λ
    q : T, b «expr - »(q.1, q.2)) (λ q : T, «expr * »(«expr∥ ∥»(«expr - »(q.1, q.2)), 1)) (expr𝓝() (p, p))] [],
  { refine [expr (h.is_O'.comp_tendsto le_top).trans_is_o _],
    simp [] [] ["only"] ["[", expr («expr ∘ »), "]"] [] [],
    refine [expr (is_O_refl (λ
       q : T, «expr∥ ∥»(«expr - »(q.1, q.2))) _).mul_is_o «expr $ »(is_o.norm_left, (is_o_one_iff _).2 _)],
    rw ["[", "<-", expr sub_self p, "]"] [],
    exact [expr continuous_at_fst.sub continuous_at_snd] },
  simp [] [] ["only"] ["[", expr mul_one, ",", expr is_o_norm_right, "]"] [] ["at", ident this],
  refine [expr (is_o.congr_of_sub _).1 this],
  clear [ident this],
  convert_to [expr is_o (λ
    q : T, h.deriv «expr - »(p, q.2) «expr - »(q.1, q.2)) (λ q : T, «expr - »(q.1, q.2)) (expr𝓝() (p, p))] [],
  { ext [] ["⟨", "⟨", ident x₁, ",", ident y₁, "⟩", ",", "⟨", ident x₂, ",", ident y₂, "⟩", "⟩"] [],
    rcases [expr p, "with", "⟨", ident x, ",", ident y, "⟩"],
    simp [] [] ["only"] ["[", expr is_bounded_bilinear_map_deriv_coe, ",", expr prod.mk_sub_mk, ",", expr h.map_sub_left, ",", expr h.map_sub_right, "]"] [] [],
    abel [] [] [] },
  have [] [":", expr is_o (λ q : T, «expr - »(p, q.2)) (λ q, (1 : exprℝ())) (expr𝓝() (p, p))] [],
  from [expr (is_o_one_iff _).2 «expr ▸ »(sub_self p, tendsto_const_nhds.sub continuous_at_snd)],
  apply [expr is_bounded_bilinear_map_apply.is_O_comp.trans_is_o],
  refine [expr is_o.trans_is_O _ (is_O_const_mul_self 1 _ _).of_norm_right],
  refine [expr is_o.mul_is_O _ (is_O_refl _ _)],
  exact [expr (((h.is_bounded_linear_map_deriv.is_O_id «expr⊤»()).comp_tendsto le_top : _).trans_is_o this).norm_left]
end

theorem IsBoundedBilinearMap.has_fderiv_at (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFderivAt b (h.deriv p) p :=
  (h.has_strict_fderiv_at p).HasFderivAt

theorem IsBoundedBilinearMap.has_fderiv_within_at (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
  HasFderivWithinAt b (h.deriv p) u p :=
  (h.has_fderiv_at p).HasFderivWithinAt

theorem IsBoundedBilinearMap.differentiable_at (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : DifferentiableAt 𝕜 b p :=
  (h.has_fderiv_at p).DifferentiableAt

theorem IsBoundedBilinearMap.differentiable_within_at (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
  DifferentiableWithinAt 𝕜 b u p :=
  (h.differentiable_at p).DifferentiableWithinAt

theorem IsBoundedBilinearMap.fderiv (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : fderiv 𝕜 b p = h.deriv p :=
  HasFderivAt.fderiv (h.has_fderiv_at p)

theorem IsBoundedBilinearMap.fderiv_within (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) (hxs : UniqueDiffWithinAt 𝕜 u p) :
  fderivWithin 𝕜 b u p = h.deriv p :=
  by 
    rw [DifferentiableAt.fderiv_within (h.differentiable_at p) hxs]
    exact h.fderiv p

theorem IsBoundedBilinearMap.differentiable (h : IsBoundedBilinearMap 𝕜 b) : Differentiable 𝕜 b :=
  fun x => h.differentiable_at x

theorem IsBoundedBilinearMap.differentiable_on (h : IsBoundedBilinearMap 𝕜 b) : DifferentiableOn 𝕜 b u :=
  h.differentiable.differentiable_on

end BilinearMap

section ClmCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


variable{H :
    Type
      _}[NormedGroup
      H][NormedSpace 𝕜
      H]{c :
    E → G →L[𝕜] H}{c' : E →L[𝕜] G →L[𝕜] H}{d : E → F →L[𝕜] G}{d' : E →L[𝕜] F →L[𝕜] G}{u : E → G}{u' : E →L[𝕜] G}

theorem HasStrictFderivAt.clm_comp (hc : HasStrictFderivAt c c' x) (hd : HasStrictFderivAt d d' x) :
  HasStrictFderivAt (fun y => (c y).comp (d y)) ((compL 𝕜 F G H (c x)).comp d'+((compL 𝕜 F G H).flip (d x)).comp c')
    x :=
  by 
    rw [add_commₓ]
    exact (is_bounded_bilinear_map_comp.has_strict_fderiv_at (d x, c x)).comp x (hd.prod hc)

theorem HasFderivWithinAt.clm_comp (hc : HasFderivWithinAt c c' s x) (hd : HasFderivWithinAt d d' s x) :
  HasFderivWithinAt (fun y => (c y).comp (d y)) ((compL 𝕜 F G H (c x)).comp d'+((compL 𝕜 F G H).flip (d x)).comp c') s
    x :=
  by 
    rw [add_commₓ]
    exact (is_bounded_bilinear_map_comp.has_fderiv_at (d x, c x)).comp_has_fderiv_within_at x (hd.prod hc)

theorem HasFderivAt.clm_comp (hc : HasFderivAt c c' x) (hd : HasFderivAt d d' x) :
  HasFderivAt (fun y => (c y).comp (d y)) ((compL 𝕜 F G H (c x)).comp d'+((compL 𝕜 F G H).flip (d x)).comp c') x :=
  by 
    rw [add_commₓ]
    exact (is_bounded_bilinear_map_comp.has_fderiv_at (d x, c x)).comp x (hd.prod hc)

theorem DifferentiableWithinAt.clm_comp (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) :
  DifferentiableWithinAt 𝕜 (fun y => (c y).comp (d y)) s x :=
  (hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).DifferentiableWithinAt

theorem DifferentiableAt.clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
  DifferentiableAt 𝕜 (fun y => (c y).comp (d y)) x :=
  (hc.has_fderiv_at.clm_comp hd.has_fderiv_at).DifferentiableAt

theorem DifferentiableOn.clm_comp (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s) :
  DifferentiableOn 𝕜 (fun y => (c y).comp (d y)) s :=
  fun x hx => (hc x hx).clm_comp (hd x hx)

theorem Differentiable.clm_comp (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) :
  Differentiable 𝕜 fun y => (c y).comp (d y) :=
  fun x => (hc x).clm_comp (hd x)

theorem fderiv_within_clm_comp (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  (hd : DifferentiableWithinAt 𝕜 d s x) :
  fderivWithin 𝕜 (fun y => (c y).comp (d y)) s x =
    (compL 𝕜 F G H (c x)).comp (fderivWithin 𝕜 d s x)+((compL 𝕜 F G H).flip (d x)).comp (fderivWithin 𝕜 c s x) :=
  (hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).fderivWithin hxs

theorem fderiv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
  fderiv 𝕜 (fun y => (c y).comp (d y)) x =
    (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x)+((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
  (hc.has_fderiv_at.clm_comp hd.has_fderiv_at).fderiv

theorem HasStrictFderivAt.clm_apply (hc : HasStrictFderivAt c c' x) (hu : HasStrictFderivAt u u' x) :
  HasStrictFderivAt (fun y => (c y) (u y)) ((c x).comp u'+c'.flip (u x)) x :=
  (is_bounded_bilinear_map_apply.HasStrictFderivAt (c x, u x)).comp x (hc.prod hu)

theorem HasFderivWithinAt.clm_apply (hc : HasFderivWithinAt c c' s x) (hu : HasFderivWithinAt u u' s x) :
  HasFderivWithinAt (fun y => (c y) (u y)) ((c x).comp u'+c'.flip (u x)) s x :=
  (is_bounded_bilinear_map_apply.HasFderivAt (c x, u x)).comp_has_fderiv_within_at x (hc.prod hu)

theorem HasFderivAt.clm_apply (hc : HasFderivAt c c' x) (hu : HasFderivAt u u' x) :
  HasFderivAt (fun y => (c y) (u y)) ((c x).comp u'+c'.flip (u x)) x :=
  (is_bounded_bilinear_map_apply.HasFderivAt (c x, u x)).comp x (hc.prod hu)

theorem DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) :
  DifferentiableWithinAt 𝕜 (fun y => (c y) (u y)) s x :=
  (hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).DifferentiableWithinAt

theorem DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
  DifferentiableAt 𝕜 (fun y => (c y) (u y)) x :=
  (hc.has_fderiv_at.clm_apply hu.has_fderiv_at).DifferentiableAt

theorem DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s) :
  DifferentiableOn 𝕜 (fun y => (c y) (u y)) s :=
  fun x hx => (hc x hx).clm_apply (hu x hx)

theorem Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u) :
  Differentiable 𝕜 fun y => (c y) (u y) :=
  fun x => (hc x).clm_apply (hu x)

theorem fderiv_within_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  (hu : DifferentiableWithinAt 𝕜 u s x) :
  fderivWithin 𝕜 (fun y => (c y) (u y)) s x = (c x).comp (fderivWithin 𝕜 u s x)+(fderivWithin 𝕜 c s x).flip (u x) :=
  (hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).fderivWithin hxs

theorem fderiv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
  fderiv 𝕜 (fun y => (c y) (u y)) x = (c x).comp (fderiv 𝕜 u x)+(fderiv 𝕜 c x).flip (u x) :=
  (hc.has_fderiv_at.clm_apply hu.has_fderiv_at).fderiv

end ClmCompApply

section Smul

/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `λ x, c x • f x` is differentiable as well. Lemmas in this section works for
function `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/


variable{𝕜' : Type _}[NondiscreteNormedField 𝕜'][NormedAlgebra 𝕜 𝕜'][NormedSpace 𝕜' F][IsScalarTower 𝕜 𝕜' F]

variable{c : E → 𝕜'}{c' : E →L[𝕜] 𝕜'}

theorem HasStrictFderivAt.smul (hc : HasStrictFderivAt c c' x) (hf : HasStrictFderivAt f f' x) :
  HasStrictFderivAt (fun y => c y • f y) ((c x • f')+c'.smul_right (f x)) x :=
  (is_bounded_bilinear_map_smul.HasStrictFderivAt (c x, f x)).comp x$ hc.prod hf

theorem HasFderivWithinAt.smul (hc : HasFderivWithinAt c c' s x) (hf : HasFderivWithinAt f f' s x) :
  HasFderivWithinAt (fun y => c y • f y) ((c x • f')+c'.smul_right (f x)) s x :=
  (is_bounded_bilinear_map_smul.HasFderivAt (c x, f x)).comp_has_fderiv_within_at x$ hc.prod hf

theorem HasFderivAt.smul (hc : HasFderivAt c c' x) (hf : HasFderivAt f f' x) :
  HasFderivAt (fun y => c y • f y) ((c x • f')+c'.smul_right (f x)) x :=
  (is_bounded_bilinear_map_smul.HasFderivAt (c x, f x)).comp x$ hc.prod hf

theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x) (hf : DifferentiableWithinAt 𝕜 f s x) :
  DifferentiableWithinAt 𝕜 (fun y => c y • f y) s x :=
  (hc.has_fderiv_within_at.smul hf.has_fderiv_within_at).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
  DifferentiableAt 𝕜 (fun y => c y • f y) x :=
  (hc.has_fderiv_at.smul hf.has_fderiv_at).DifferentiableAt

theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
  DifferentiableOn 𝕜 (fun y => c y • f y) s :=
  fun x hx => (hc x hx).smul (hf x hx)

@[simp]
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => c y • f y :=
  fun x => (hc x).smul (hf x)

theorem fderiv_within_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  (hf : DifferentiableWithinAt 𝕜 f s x) :
  fderivWithin 𝕜 (fun y => c y • f y) s x = (c x • fderivWithin 𝕜 f s x)+(fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.has_fderiv_within_at.smul hf.has_fderiv_within_at).fderivWithin hxs

theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
  fderiv 𝕜 (fun y => c y • f y) x = (c x • fderiv 𝕜 f x)+(fderiv 𝕜 c x).smulRight (f x) :=
  (hc.has_fderiv_at.smul hf.has_fderiv_at).fderiv

theorem HasStrictFderivAt.smul_const (hc : HasStrictFderivAt c c' x) (f : F) :
  HasStrictFderivAt (fun y => c y • f) (c'.smul_right f) x :=
  by 
    simpa only [smul_zero, zero_addₓ] using hc.smul (has_strict_fderiv_at_const f x)

theorem HasFderivWithinAt.smul_const (hc : HasFderivWithinAt c c' s x) (f : F) :
  HasFderivWithinAt (fun y => c y • f) (c'.smul_right f) s x :=
  by 
    simpa only [smul_zero, zero_addₓ] using hc.smul (has_fderiv_within_at_const f x s)

theorem HasFderivAt.smul_const (hc : HasFderivAt c c' x) (f : F) : HasFderivAt (fun y => c y • f) (c'.smul_right f) x :=
  by 
    simpa only [smul_zero, zero_addₓ] using hc.smul (has_fderiv_at_const f x)

theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
  DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.has_fderiv_within_at.smul_const f).DifferentiableWithinAt

theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) : DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.has_fderiv_at.smul_const f).DifferentiableAt

theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) : DifferentiableOn 𝕜 (fun y => c y • f) s :=
  fun x hx => (hc x hx).smul_const f

theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) : Differentiable 𝕜 fun y => c y • f :=
  fun x => (hc x).smul_const f

theorem fderiv_within_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
  fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smulRight f :=
  (hc.has_fderiv_within_at.smul_const f).fderivWithin hxs

theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
  fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smulRight f :=
  (hc.has_fderiv_at.smul_const f).fderiv

end Smul

section Mul

/-! ### Derivative of the product of two functions -/


variable{𝔸 𝔸' :
    Type
      _}[NormedRing
      𝔸][NormedCommRing
      𝔸'][NormedAlgebra 𝕜 𝔸][NormedAlgebra 𝕜 𝔸']{a b : E → 𝔸}{a' b' : E →L[𝕜] 𝔸}{c d : E → 𝔸'}{c' d' : E →L[𝕜] 𝔸'}

theorem HasStrictFderivAt.mul' {x : E} (ha : HasStrictFderivAt a a' x) (hb : HasStrictFderivAt b b' x) :
  HasStrictFderivAt (fun y => a y*b y) ((a x • b')+a'.smul_right (b x)) x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸).IsBoundedBilinearMap.HasStrictFderivAt (a x, b x)).comp x (ha.prod hb)

theorem HasStrictFderivAt.mul (hc : HasStrictFderivAt c c' x) (hd : HasStrictFderivAt d d' x) :
  HasStrictFderivAt (fun y => c y*d y) ((c x • d')+d x • c') x :=
  by 
    convert hc.mul' hd 
    ext z 
    apply mul_commₓ

theorem HasFderivWithinAt.mul' (ha : HasFderivWithinAt a a' s x) (hb : HasFderivWithinAt b b' s x) :
  HasFderivWithinAt (fun y => a y*b y) ((a x • b')+a'.smul_right (b x)) s x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸).IsBoundedBilinearMap.HasFderivAt (a x, b x)).comp_has_fderiv_within_at x (ha.prod hb)

theorem HasFderivWithinAt.mul (hc : HasFderivWithinAt c c' s x) (hd : HasFderivWithinAt d d' s x) :
  HasFderivWithinAt (fun y => c y*d y) ((c x • d')+d x • c') s x :=
  by 
    convert hc.mul' hd 
    ext z 
    apply mul_commₓ

theorem HasFderivAt.mul' (ha : HasFderivAt a a' x) (hb : HasFderivAt b b' x) :
  HasFderivAt (fun y => a y*b y) ((a x • b')+a'.smul_right (b x)) x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸).IsBoundedBilinearMap.HasFderivAt (a x, b x)).comp x (ha.prod hb)

theorem HasFderivAt.mul (hc : HasFderivAt c c' x) (hd : HasFderivAt d d' x) :
  HasFderivAt (fun y => c y*d y) ((c x • d')+d x • c') x :=
  by 
    convert hc.mul' hd 
    ext z 
    apply mul_commₓ

theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x) (hb : DifferentiableWithinAt 𝕜 b s x) :
  DifferentiableWithinAt 𝕜 (fun y => a y*b y) s x :=
  (ha.has_fderiv_within_at.mul' hb.has_fderiv_within_at).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
  DifferentiableAt 𝕜 (fun y => a y*b y) x :=
  (ha.has_fderiv_at.mul' hb.has_fderiv_at).DifferentiableAt

theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
  DifferentiableOn 𝕜 (fun y => a y*b y) s :=
  fun x hx => (ha x hx).mul (hb x hx)

@[simp]
theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) : Differentiable 𝕜 fun y => a y*b y :=
  fun x => (ha x).mul (hb x)

theorem fderiv_within_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
  (hb : DifferentiableWithinAt 𝕜 b s x) :
  fderivWithin 𝕜 (fun y => a y*b y) s x = (a x • fderivWithin 𝕜 b s x)+(fderivWithin 𝕜 a s x).smulRight (b x) :=
  (ha.has_fderiv_within_at.mul' hb.has_fderiv_within_at).fderivWithin hxs

theorem fderiv_within_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  (hd : DifferentiableWithinAt 𝕜 d s x) :
  fderivWithin 𝕜 (fun y => c y*d y) s x = (c x • fderivWithin 𝕜 d s x)+d x • fderivWithin 𝕜 c s x :=
  (hc.has_fderiv_within_at.mul hd.has_fderiv_within_at).fderivWithin hxs

theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
  fderiv 𝕜 (fun y => a y*b y) x = (a x • fderiv 𝕜 b x)+(fderiv 𝕜 a x).smulRight (b x) :=
  (ha.has_fderiv_at.mul' hb.has_fderiv_at).fderiv

theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
  fderiv 𝕜 (fun y => c y*d y) x = (c x • fderiv 𝕜 d x)+d x • fderiv 𝕜 c x :=
  (hc.has_fderiv_at.mul hd.has_fderiv_at).fderiv

theorem HasStrictFderivAt.mul_const' (ha : HasStrictFderivAt a a' x) (b : 𝔸) :
  HasStrictFderivAt (fun y => a y*b) (a'.smul_right b) x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸).flip b).HasStrictFderivAt.comp x ha

theorem HasStrictFderivAt.mul_const (hc : HasStrictFderivAt c c' x) (d : 𝔸') :
  HasStrictFderivAt (fun y => c y*d) (d • c') x :=
  by 
    convert hc.mul_const' d 
    ext z 
    apply mul_commₓ

theorem HasFderivWithinAt.mul_const' (ha : HasFderivWithinAt a a' s x) (b : 𝔸) :
  HasFderivWithinAt (fun y => a y*b) (a'.smul_right b) s x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸).flip b).HasFderivAt.comp_has_fderiv_within_at x ha

theorem HasFderivWithinAt.mul_const (hc : HasFderivWithinAt c c' s x) (d : 𝔸') :
  HasFderivWithinAt (fun y => c y*d) (d • c') s x :=
  by 
    convert hc.mul_const' d 
    ext z 
    apply mul_commₓ

theorem HasFderivAt.mul_const' (ha : HasFderivAt a a' x) (b : 𝔸) : HasFderivAt (fun y => a y*b) (a'.smul_right b) x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸).flip b).HasFderivAt.comp x ha

theorem HasFderivAt.mul_const (hc : HasFderivAt c c' x) (d : 𝔸') : HasFderivAt (fun y => c y*d) (d • c') x :=
  by 
    convert hc.mul_const' d 
    ext z 
    apply mul_commₓ

theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
  DifferentiableWithinAt 𝕜 (fun y => a y*b) s x :=
  (ha.has_fderiv_within_at.mul_const' b).DifferentiableWithinAt

theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => a y*b) x :=
  (ha.has_fderiv_at.mul_const' b).DifferentiableAt

theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) : DifferentiableOn 𝕜 (fun y => a y*b) s :=
  fun x hx => (ha x hx).mul_const b

theorem Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => a y*b :=
  fun x => (ha x).mul_const b

theorem fderiv_within_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
  fderivWithin 𝕜 (fun y => a y*b) s x = (fderivWithin 𝕜 a s x).smulRight b :=
  (ha.has_fderiv_within_at.mul_const' b).fderivWithin hxs

theorem fderiv_within_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸') :
  fderivWithin 𝕜 (fun y => c y*d) s x = d • fderivWithin 𝕜 c s x :=
  (hc.has_fderiv_within_at.mul_const d).fderivWithin hxs

theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
  fderiv 𝕜 (fun y => a y*b) x = (fderiv 𝕜 a x).smulRight b :=
  (ha.has_fderiv_at.mul_const' b).fderiv

theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') : fderiv 𝕜 (fun y => c y*d) x = d • fderiv 𝕜 c x :=
  (hc.has_fderiv_at.mul_const d).fderiv

theorem HasStrictFderivAt.const_mul (ha : HasStrictFderivAt a a' x) (b : 𝔸) :
  HasStrictFderivAt (fun y => b*a y) (b • a') x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸) b).HasStrictFderivAt.comp x ha

theorem HasFderivWithinAt.const_mul (ha : HasFderivWithinAt a a' s x) (b : 𝔸) :
  HasFderivWithinAt (fun y => b*a y) (b • a') s x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸) b).HasFderivAt.comp_has_fderiv_within_at x ha

theorem HasFderivAt.const_mul (ha : HasFderivAt a a' x) (b : 𝔸) : HasFderivAt (fun y => b*a y) (b • a') x :=
  ((ContinuousLinearMap.lmul 𝕜 𝔸) b).HasFderivAt.comp x ha

theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
  DifferentiableWithinAt 𝕜 (fun y => b*a y) s x :=
  (ha.has_fderiv_within_at.const_mul b).DifferentiableWithinAt

theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b*a y) x :=
  (ha.has_fderiv_at.const_mul b).DifferentiableAt

theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) : DifferentiableOn 𝕜 (fun y => b*a y) s :=
  fun x hx => (ha x hx).const_mul b

theorem Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => b*a y :=
  fun x => (ha x).const_mul b

theorem fderiv_within_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
  fderivWithin 𝕜 (fun y => b*a y) s x = b • fderivWithin 𝕜 a s x :=
  (ha.has_fderiv_within_at.const_mul b).fderivWithin hxs

theorem fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) : fderiv 𝕜 (fun y => b*a y) x = b • fderiv 𝕜 a x :=
  (ha.has_fderiv_at.const_mul b).fderiv

end Mul

section AlgebraInverse

variable{R : Type _}[NormedRing R][NormedAlgebra 𝕜 R][CompleteSpace R]

open NormedRing ContinuousLinearMap Ringₓ

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `λ t, - x⁻¹ * t * x⁻¹`. -/
theorem has_fderiv_at_ring_inverse
(x : units R) : has_fderiv_at ring.inverse «expr- »(lmul_left_right 𝕜 R «expr↑ »(«expr ⁻¹»(x)) «expr↑ »(«expr ⁻¹»(x))) x :=
begin
  have [ident h_is_o] [":", expr is_o (λ
    t : R, «expr + »(«expr - »(inverse «expr + »(«expr↑ »(x), t), «expr↑ »(«expr ⁻¹»(x))), «expr * »(«expr * »(«expr↑ »(«expr ⁻¹»(x)), t), «expr↑ »(«expr ⁻¹»(x))))) (λ
    t : R, t) (expr𝓝() 0)] [],
  { refine [expr (inverse_add_norm_diff_second_order x).trans_is_o (is_o_norm_norm.mp _)],
    simp [] [] ["only"] ["[", expr normed_field.norm_pow, ",", expr norm_norm, "]"] [] [],
    have [ident h12] [":", expr «expr < »(1, 2)] [":=", expr by norm_num [] []],
    convert [] [expr (asymptotics.is_o_pow_pow h12).comp_tendsto tendsto_norm_zero] [],
    ext [] [] [],
    simp [] [] [] [] [] [] },
  have [ident h_lim] [":", expr tendsto (λ y : R, «expr - »(y, x)) (expr𝓝() x) (expr𝓝() 0)] [],
  { refine [expr tendsto_zero_iff_norm_tendsto_zero.mpr _],
    exact [expr tendsto_iff_norm_tendsto_zero.mp tendsto_id] },
  simp [] [] ["only"] ["[", expr has_fderiv_at, ",", expr has_fderiv_at_filter, "]"] [] [],
  convert [] [expr h_is_o.comp_tendsto h_lim] [],
  ext [] [ident y] [],
  simp [] [] ["only"] ["[", expr coe_comp', ",", expr function.comp_app, ",", expr lmul_left_right_apply, ",", expr neg_apply, ",", expr inverse_unit x, ",", expr units.inv_mul, ",", expr add_sub_cancel'_right, ",", expr mul_sub, ",", expr sub_mul, ",", expr one_mul, ",", expr sub_neg_eq_add, "]"] [] []
end

theorem differentiable_at_inverse (x : Units R) : DifferentiableAt 𝕜 (@Ring.inverse R _) x :=
  (has_fderiv_at_ring_inverse x).DifferentiableAt

theorem fderiv_inverse (x : Units R) :
  fderiv 𝕜 (@Ring.inverse R _) x = -lmul_left_right 𝕜 R («expr↑ » (x⁻¹)) («expr↑ » (x⁻¹)) :=
  (has_fderiv_at_ring_inverse x).fderiv

end AlgebraInverse

namespace ContinuousLinearEquiv

/-! ### Differentiability of linear equivs, and invariance of differentiability -/


variable(iso : E ≃L[𝕜] F)

protected theorem HasStrictFderivAt : HasStrictFderivAt iso (iso : E →L[𝕜] F) x :=
  iso.to_continuous_linear_map.has_strict_fderiv_at

protected theorem HasFderivWithinAt : HasFderivWithinAt iso (iso : E →L[𝕜] F) s x :=
  iso.to_continuous_linear_map.has_fderiv_within_at

protected theorem HasFderivAt : HasFderivAt iso (iso : E →L[𝕜] F) x :=
  iso.to_continuous_linear_map.has_fderiv_at_filter

protected theorem DifferentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.has_fderiv_at.differentiable_at

protected theorem DifferentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.differentiable_at.differentiable_within_at

protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.has_fderiv_at.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  iso.to_continuous_linear_map.fderiv_within hxs

protected theorem Differentiable : Differentiable 𝕜 iso :=
  fun x => iso.differentiable_at

protected theorem DifferentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.differentiable.differentiable_on

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_differentiable_within_at_iff
{f : G → E}
{s : set G}
{x : G} : «expr ↔ »(differentiable_within_at 𝕜 «expr ∘ »(iso, f) s x, differentiable_within_at 𝕜 f s x) :=
begin
  refine [expr ⟨λ H, _, λ H, iso.differentiable.differentiable_at.comp_differentiable_within_at x H⟩],
  have [] [":", expr differentiable_within_at 𝕜 «expr ∘ »(iso.symm, «expr ∘ »(iso, f)) s x] [":=", expr iso.symm.differentiable.differentiable_at.comp_differentiable_within_at x H],
  rwa ["[", "<-", expr function.comp.assoc iso.symm iso f, ",", expr iso.symm_comp_self, "]"] ["at", ident this]
end

theorem comp_differentiable_at_iff {f : G → E} {x : G} : DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x :=
  by 
    rw [←differentiable_within_at_univ, ←differentiable_within_at_univ, iso.comp_differentiable_within_at_iff]

theorem comp_differentiable_on_iff {f : G → E} {s : Set G} : DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  by 
    rw [DifferentiableOn, DifferentiableOn]
    simp only [iso.comp_differentiable_within_at_iff]

theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  by 
    rw [←differentiable_on_univ, ←differentiable_on_univ]
    exact iso.comp_differentiable_on_iff

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_has_fderiv_within_at_iff
{f : G → E}
{s : set G}
{x : G}
{f' : «expr →L[ ] »(G, 𝕜, E)} : «expr ↔ »(has_fderiv_within_at «expr ∘ »(iso, f) ((iso : «expr →L[ ] »(E, 𝕜, F)).comp f') s x, has_fderiv_within_at f f' s x) :=
begin
  refine [expr ⟨λ H, _, λ H, iso.has_fderiv_at.comp_has_fderiv_within_at x H⟩],
  have [ident A] [":", expr «expr = »(f, «expr ∘ »(iso.symm, «expr ∘ »(iso, f)))] [],
  by { rw ["[", "<-", expr function.comp.assoc, ",", expr iso.symm_comp_self, "]"] [],
    refl },
  have [ident B] [":", expr «expr = »(f', (iso.symm : «expr →L[ ] »(F, 𝕜, E)).comp ((iso : «expr →L[ ] »(E, 𝕜, F)).comp f'))] [],
  by rw ["[", "<-", expr continuous_linear_map.comp_assoc, ",", expr iso.coe_symm_comp_coe, ",", expr continuous_linear_map.id_comp, "]"] [],
  rw ["[", expr A, ",", expr B, "]"] [],
  exact [expr iso.symm.has_fderiv_at.comp_has_fderiv_within_at x H]
end

theorem comp_has_strict_fderiv_at_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
  HasStrictFderivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFderivAt f f' x :=
  by 
    refine' ⟨fun H => _, fun H => iso.has_strict_fderiv_at.comp x H⟩
    convert iso.symm.has_strict_fderiv_at.comp x H <;> ext z <;> apply (iso.symm_apply_apply _).symm

theorem comp_has_fderiv_at_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
  HasFderivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFderivAt f f' x :=
  by 
    rw [←has_fderiv_within_at_univ, ←has_fderiv_within_at_univ, iso.comp_has_fderiv_within_at_iff]

theorem comp_has_fderiv_within_at_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
  HasFderivWithinAt (iso ∘ f) f' s x ↔ HasFderivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x :=
  by 
    rw [←iso.comp_has_fderiv_within_at_iff, ←ContinuousLinearMap.comp_assoc, iso.coe_comp_coe_symm,
      ContinuousLinearMap.id_comp]

theorem comp_has_fderiv_at_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
  HasFderivAt (iso ∘ f) f' x ↔ HasFderivAt f ((iso.symm : F →L[𝕜] E).comp f') x :=
  by 
    rw [←has_fderiv_within_at_univ, ←has_fderiv_within_at_univ, iso.comp_has_fderiv_within_at_iff']

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_fderiv_within
{f : G → E}
{s : set G}
{x : G}
(hxs : unique_diff_within_at 𝕜 s x) : «expr = »(fderiv_within 𝕜 «expr ∘ »(iso, f) s x, (iso : «expr →L[ ] »(E, 𝕜, F)).comp (fderiv_within 𝕜 f s x)) :=
begin
  by_cases [expr h, ":", expr differentiable_within_at 𝕜 f s x],
  { rw ["[", expr fderiv.comp_fderiv_within x iso.differentiable_at h hxs, ",", expr iso.fderiv, "]"] [] },
  { have [] [":", expr «expr¬ »(differentiable_within_at 𝕜 «expr ∘ »(iso, f) s x)] [],
    from [expr mt iso.comp_differentiable_within_at_iff.1 h],
    rw ["[", expr fderiv_within_zero_of_not_differentiable_within_at h, ",", expr fderiv_within_zero_of_not_differentiable_within_at this, ",", expr continuous_linear_map.comp_zero, "]"] [] }
end

theorem comp_fderiv {f : G → E} {x : G} : fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
  by 
    rw [←fderiv_within_univ, ←fderiv_within_univ]
    exact iso.comp_fderiv_within unique_diff_within_at_univ

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

/-! ### Differentiability of linear isometry equivs, and invariance of differentiability -/


variable(iso : E ≃ₗᵢ[𝕜] F)

protected theorem HasStrictFderivAt : HasStrictFderivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).HasStrictFderivAt

protected theorem HasFderivWithinAt : HasFderivWithinAt iso (iso : E →L[𝕜] F) s x :=
  (iso : E ≃L[𝕜] F).HasFderivWithinAt

protected theorem HasFderivAt : HasFderivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).HasFderivAt

protected theorem DifferentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.has_fderiv_at.differentiable_at

protected theorem DifferentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.differentiable_at.differentiable_within_at

protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.has_fderiv_at.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  (iso : E ≃L[𝕜] F).fderivWithin hxs

protected theorem Differentiable : Differentiable 𝕜 iso :=
  fun x => iso.differentiable_at

protected theorem DifferentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.differentiable.differentiable_on

theorem comp_differentiable_within_at_iff {f : G → E} {s : Set G} {x : G} :
  DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (iso : E ≃L[𝕜] F).comp_differentiable_within_at_iff

theorem comp_differentiable_at_iff {f : G → E} {x : G} : DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x :=
  (iso : E ≃L[𝕜] F).comp_differentiable_at_iff

theorem comp_differentiable_on_iff {f : G → E} {s : Set G} : DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  (iso : E ≃L[𝕜] F).comp_differentiable_on_iff

theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  (iso : E ≃L[𝕜] F).comp_differentiable_iff

theorem comp_has_fderiv_within_at_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
  HasFderivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFderivWithinAt f f' s x :=
  (iso : E ≃L[𝕜] F).comp_has_fderiv_within_at_iff

theorem comp_has_strict_fderiv_at_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
  HasStrictFderivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFderivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_has_strict_fderiv_at_iff

theorem comp_has_fderiv_at_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
  HasFderivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFderivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_has_fderiv_at_iff

theorem comp_has_fderiv_within_at_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
  HasFderivWithinAt (iso ∘ f) f' s x ↔ HasFderivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x :=
  (iso : E ≃L[𝕜] F).comp_has_fderiv_within_at_iff'

theorem comp_has_fderiv_at_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
  HasFderivAt (iso ∘ f) f' x ↔ HasFderivAt f ((iso.symm : F →L[𝕜] E).comp f') x :=
  (iso : E ≃L[𝕜] F).comp_has_fderiv_at_iff'

theorem comp_fderiv_within {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
  fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) :=
  (iso : E ≃L[𝕜] F).comp_fderiv_within hxs

theorem comp_fderiv {f : G → E} {x : G} : fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
  (iso : E ≃L[𝕜] F).comp_fderiv

end LinearIsometryEquiv

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem has_strict_fderiv_at.of_local_left_inverse
{f : E → F}
{f' : «expr ≃L[ ] »(E, 𝕜, F)}
{g : F → E}
{a : F}
(hg : continuous_at g a)
(hf : has_strict_fderiv_at f (f' : «expr →L[ ] »(E, 𝕜, F)) (g a))
(hfg : «expr∀ᶠ in , »((y), expr𝓝() a, «expr = »(f (g y), y))) : has_strict_fderiv_at g (f'.symm : «expr →L[ ] »(F, 𝕜, E)) a :=
begin
  replace [ident hg] [] [":=", expr hg.prod_map' hg],
  replace [ident hfg] [] [":=", expr hfg.prod_mk_nhds hfg],
  have [] [":", expr is_O (λ
    p : «expr × »(F, F), «expr - »(«expr - »(g p.1, g p.2), f'.symm «expr - »(p.1, p.2))) (λ
    p : «expr × »(F, F), «expr - »(f' «expr - »(g p.1, g p.2), «expr - »(p.1, p.2))) (expr𝓝() (a, a))] [],
  { refine [expr ((f'.symm : «expr →L[ ] »(F, 𝕜, E)).is_O_comp _ _).congr (λ x, _) (λ _, rfl)],
    simp [] [] [] [] [] [] },
  refine [expr this.trans_is_o _],
  clear [ident this],
  refine [expr ((hf.comp_tendsto hg).symm.congr' (hfg.mono _) «expr $ »(eventually_of_forall, λ _, rfl)).trans_is_O _],
  { rintros [ident p, "⟨", ident hp1, ",", ident hp2, "⟩"],
    simp [] [] [] ["[", expr hp1, ",", expr hp2, "]"] [] [] },
  { refine [expr (hf.is_O_sub_rev.comp_tendsto hg).congr' «expr $ »(eventually_of_forall, λ _, rfl) (hfg.mono _)],
    rintros [ident p, "⟨", ident hp1, ",", ident hp2, "⟩"],
    simp [] [] ["only"] ["[", expr («expr ∘ »), ",", expr hp1, ",", expr hp2, "]"] [] [] }
end

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem has_fderiv_at.of_local_left_inverse
{f : E → F}
{f' : «expr ≃L[ ] »(E, 𝕜, F)}
{g : F → E}
{a : F}
(hg : continuous_at g a)
(hf : has_fderiv_at f (f' : «expr →L[ ] »(E, 𝕜, F)) (g a))
(hfg : «expr∀ᶠ in , »((y), expr𝓝() a, «expr = »(f (g y), y))) : has_fderiv_at g (f'.symm : «expr →L[ ] »(F, 𝕜, E)) a :=
begin
  have [] [":", expr is_O (λ
    x : F, «expr - »(«expr - »(g x, g a), f'.symm «expr - »(x, a))) (λ
    x : F, «expr - »(f' «expr - »(g x, g a), «expr - »(x, a))) (expr𝓝() a)] [],
  { refine [expr ((f'.symm : «expr →L[ ] »(F, 𝕜, E)).is_O_comp _ _).congr (λ x, _) (λ _, rfl)],
    simp [] [] [] [] [] [] },
  refine [expr this.trans_is_o _],
  clear [ident this],
  refine [expr ((hf.comp_tendsto hg).symm.congr' (hfg.mono _) «expr $ »(eventually_of_forall, λ _, rfl)).trans_is_O _],
  { rintros [ident p, ident hp],
    simp [] [] [] ["[", expr hp, ",", expr hfg.self_of_nhds, "]"] [] [] },
  { refine [expr (hf.is_O_sub_rev.comp_tendsto hg).congr' «expr $ »(eventually_of_forall, λ _, rfl) (hfg.mono _)],
    rintros [ident p, ident hp],
    simp [] [] ["only"] ["[", expr («expr ∘ »), ",", expr hp, ",", expr hfg.self_of_nhds, "]"] [] [] }
end

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.has_strict_fderiv_at_symm (f : LocalHomeomorph E F) {f' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
  (htff' : HasStrictFderivAt f (f' : E →L[𝕜] F) (f.symm a)) : HasStrictFderivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuous_at ha) (f.eventually_right_inverse ha)

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.has_fderiv_at_symm (f : LocalHomeomorph E F) {f' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
  (htff' : HasFderivAt f (f' : E →L[𝕜] F) (f.symm a)) : HasFderivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.continuous_at ha) (f.eventually_right_inverse ha)

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_fderiv_within_at.eventually_ne
(h : has_fderiv_within_at f f' s x)
(hf' : «expr∃ , »((C), ∀
  z, «expr ≤ »(«expr∥ ∥»(z), «expr * »(C, «expr∥ ∥»(f' z))))) : «expr∀ᶠ in , »((z), «expr𝓝[ ] »(«expr \ »(s, {x}), x), «expr ≠ »(f z, f x)) :=
begin
  rw ["[", expr nhds_within, ",", expr diff_eq, ",", "<-", expr inf_principal, ",", "<-", expr inf_assoc, ",", expr eventually_inf_principal, "]"] [],
  have [ident A] [":", expr is_O (λ
    z, «expr - »(z, x)) (λ
    z, f' «expr - »(z, x)) «expr𝓝[ ] »(s, x)] [":=", expr «expr $ »(is_O_iff.2, «expr $ »(hf'.imp, λ
     C hC, «expr $ »(eventually_of_forall, λ z, hC _)))],
  have [] [":", expr «expr ~[ ] »(λ
    z, «expr - »(f z, f x), «expr𝓝[ ] »(s, x), λ z, f' «expr - »(z, x))] [":=", expr h.trans_is_O A],
  simpa [] [] [] ["[", expr not_imp_not, ",", expr sub_eq_zero, "]"] [] ["using", expr (A.trans this.is_O_symm).eq_zero_imp]
end

theorem HasFderivAt.eventually_ne (h : HasFderivAt f f' x) (hf' : ∃ C, ∀ z, ∥z∥ ≤ C*∥f' z∥) :
  ∀ᶠz in 𝓝[«expr ᶜ» {x}] x, f z ≠ f x :=
  by 
    simpa only [compl_eq_univ_diff] using (has_fderiv_within_at_univ.2 h).eventually_ne hf'

end 

section 

variable{E : Type _}[NormedGroup E][NormedSpace ℝ E]

variable{F : Type _}[NormedGroup F][NormedSpace ℝ F]

variable{f : E → F}{f' : E →L[ℝ] F}{x : E}

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_fderiv_at_filter_real_equiv
{L : filter E} : «expr ↔ »(tendsto (λ
  x' : E, «expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x', x))), «expr∥ ∥»(«expr - »(«expr - »(f x', f x), f' «expr - »(x', x))))) L (expr𝓝() 0), tendsto (λ
  x' : E, «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x', x))), «expr - »(«expr - »(f x', f x), f' «expr - »(x', x)))) L (expr𝓝() 0)) :=
begin
  symmetry,
  rw ["[", expr tendsto_iff_norm_tendsto_zero, "]"] [],
  refine [expr tendsto_congr (λ x', _)],
  have [] [":", expr «expr ≥ »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x', x))), 0)] [],
  from [expr inv_nonneg.mpr (norm_nonneg _)],
  simp [] [] [] ["[", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg this, "]"] [] []
end

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_fderiv_at.lim_real
(hf : has_fderiv_at f f' x)
(v : E) : tendsto (λ
 c : exprℝ(), «expr • »(c, «expr - »(f «expr + »(x, «expr • »(«expr ⁻¹»(c), v)), f x))) at_top (expr𝓝() (f' v)) :=
begin
  apply [expr hf.lim v],
  rw [expr tendsto_at_top_at_top] [],
  exact [expr λ b, ⟨b, λ a ha, le_trans ha (le_abs_self _)⟩]
end

end 

section TangentCone

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜 E]{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]{f : E → F}{s : Set E}{f' : E →L[𝕜] F}

-- error in Analysis.Calculus.Fderiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The image of a tangent cone under the differential of a map is included in the tangent cone to
the image. -/
theorem has_fderiv_within_at.maps_to_tangent_cone
{x : E}
(h : has_fderiv_within_at f f' s x) : maps_to f' (tangent_cone_at 𝕜 s x) (tangent_cone_at 𝕜 «expr '' »(f, s) (f x)) :=
begin
  rintros [ident v, "⟨", ident c, ",", ident d, ",", ident dtop, ",", ident clim, ",", ident cdlim, "⟩"],
  refine [expr ⟨c, λ
    n, «expr - »(f «expr + »(x, d n), f x), mem_of_superset dtop _, clim, h.lim at_top dtop clim cdlim⟩],
  simp [] [] [] ["[", "-", ident mem_image, ",", expr mem_image_of_mem, "]"] [] [] { contextual := tt }
end

/-- If a set has the unique differentiability property at a point x, then the image of this set
under a map with onto derivative has also the unique differentiability property at the image point.
-/
theorem HasFderivWithinAt.unique_diff_within_at {x : E} (h : HasFderivWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x)
  (h' : DenseRange f') : UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  by 
    refine' ⟨h'.dense_of_maps_to f'.continuous hs.1 _, h.continuous_within_at.mem_closure_image hs.2⟩
    show
      Submodule.span 𝕜 (TangentConeAt 𝕜 s x) ≤ (Submodule.span 𝕜 (TangentConeAt 𝕜 (f '' s) (f x))).comap («expr↑ » f')
    rw [Submodule.span_le]
    exact h.maps_to_tangent_cone.mono (subset.refl _) Submodule.subset_span

theorem UniqueDiffOn.image {f' : E → E →L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
  (hf' : ∀ x (_ : x ∈ s), HasFderivWithinAt f (f' x) s x) (hd : ∀ x (_ : x ∈ s), DenseRange (f' x)) :
  UniqueDiffOn 𝕜 (f '' s) :=
  ball_image_iff.2$ fun x hx => (hf' x hx).UniqueDiffWithinAt (hs x hx) (hd x hx)

theorem HasFderivWithinAt.unique_diff_within_at_of_continuous_linear_equiv {x : E} (e' : E ≃L[𝕜] F)
  (h : HasFderivWithinAt f (e' : E →L[𝕜] F) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
  UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  h.unique_diff_within_at hs e'.surjective.dense_range

theorem ContinuousLinearEquiv.unique_diff_on_image (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s) : UniqueDiffOn 𝕜 (e '' s) :=
  h.image (fun x _ => e.has_fderiv_within_at) fun x hx => e.surjective.dense_range

@[simp]
theorem ContinuousLinearEquiv.unique_diff_on_image_iff (e : E ≃L[𝕜] F) : UniqueDiffOn 𝕜 (e '' s) ↔ UniqueDiffOn 𝕜 s :=
  ⟨fun h => e.symm_image_image s ▸ e.symm.unique_diff_on_image h, e.unique_diff_on_image⟩

@[simp]
theorem ContinuousLinearEquiv.unique_diff_on_preimage_iff (e : F ≃L[𝕜] E) :
  UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiffOn 𝕜 s :=
  by 
    rw [←e.image_symm_eq_preimage, e.symm.unique_diff_on_image_iff]

end TangentCone

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/


variable(𝕜 : Type _)[NondiscreteNormedField 𝕜]

variable{𝕜' : Type _}[NondiscreteNormedField 𝕜'][NormedAlgebra 𝕜 𝕜']

variable{E : Type _}[NormedGroup E][NormedSpace 𝕜 E][NormedSpace 𝕜' E]

variable[IsScalarTower 𝕜 𝕜' E]

variable{F : Type _}[NormedGroup F][NormedSpace 𝕜 F][NormedSpace 𝕜' F]

variable[IsScalarTower 𝕜 𝕜' F]

variable{f : E → F}{f' : E →L[𝕜'] F}{s : Set E}{x : E}

theorem HasStrictFderivAt.restrict_scalars (h : HasStrictFderivAt f f' x) :
  HasStrictFderivAt f (f'.restrict_scalars 𝕜) x :=
  h

theorem HasFderivAt.restrict_scalars (h : HasFderivAt f f' x) : HasFderivAt f (f'.restrict_scalars 𝕜) x :=
  h

theorem HasFderivWithinAt.restrict_scalars (h : HasFderivWithinAt f f' s x) :
  HasFderivWithinAt f (f'.restrict_scalars 𝕜) s x :=
  h

theorem DifferentiableAt.restrict_scalars (h : DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x :=
  (h.has_fderiv_at.restrict_scalars 𝕜).DifferentiableAt

theorem DifferentiableWithinAt.restrict_scalars (h : DifferentiableWithinAt 𝕜' f s x) :
  DifferentiableWithinAt 𝕜 f s x :=
  (h.has_fderiv_within_at.restrict_scalars 𝕜).DifferentiableWithinAt

theorem DifferentiableOn.restrict_scalars (h : DifferentiableOn 𝕜' f s) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x hx).restrictScalars 𝕜

theorem Differentiable.restrict_scalars (h : Differentiable 𝕜' f) : Differentiable 𝕜 f :=
  fun x => (h x).restrictScalars 𝕜

theorem has_fderiv_within_at_of_restrict_scalars {g' : E →L[𝕜] F} (h : HasFderivWithinAt f g' s x)
  (H : f'.restrict_scalars 𝕜 = g') : HasFderivWithinAt f f' s x :=
  by 
    rw [←H] at h 
    exact h

theorem has_fderiv_at_of_restrict_scalars {g' : E →L[𝕜] F} (h : HasFderivAt f g' x) (H : f'.restrict_scalars 𝕜 = g') :
  HasFderivAt f f' x :=
  by 
    rw [←H] at h 
    exact h

theorem DifferentiableAt.fderiv_restrict_scalars (h : DifferentiableAt 𝕜' f x) :
  fderiv 𝕜 f x = (fderiv 𝕜' f x).restrictScalars 𝕜 :=
  (h.has_fderiv_at.restrict_scalars 𝕜).fderiv

theorem differentiable_within_at_iff_restrict_scalars (hf : DifferentiableWithinAt 𝕜 f s x)
  (hs : UniqueDiffWithinAt 𝕜 s x) :
  DifferentiableWithinAt 𝕜' f s x ↔ ∃ g' : E →L[𝕜'] F, g'.restrict_scalars 𝕜 = fderivWithin 𝕜 f s x :=
  by 
    split 
    ·
      rintro ⟨g', hg'⟩
      exact ⟨g', hs.eq (hg'.restrict_scalars 𝕜) hf.has_fderiv_within_at⟩
    ·
      rintro ⟨f', hf'⟩
      exact ⟨f', has_fderiv_within_at_of_restrict_scalars 𝕜 hf.has_fderiv_within_at hf'⟩

theorem differentiable_at_iff_restrict_scalars (hf : DifferentiableAt 𝕜 f x) :
  DifferentiableAt 𝕜' f x ↔ ∃ g' : E →L[𝕜'] F, g'.restrict_scalars 𝕜 = fderiv 𝕜 f x :=
  by 
    rw [←differentiable_within_at_univ, ←fderiv_within_univ]
    exact differentiable_within_at_iff_restrict_scalars 𝕜 hf.differentiable_within_at unique_diff_within_at_univ

end RestrictScalars

