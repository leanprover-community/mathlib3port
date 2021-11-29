import Mathbin.Analysis.Calculus.Deriv 
import Mathbin.Analysis.Calculus.TimesContDiff

/-!
# One-dimensional iterated derivatives

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iterated_deriv n f : 𝕜 → F`, as well as a version on domains `iterated_deriv_within n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nondiscrete normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iterated_deriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iterated_deriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iterated_deriv_within n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iterated_deriv_within_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iterated_deriv n f` as the composition of
`iterated_fderiv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iterated_deriv_within_succ`,
by translating the corresponding result `iterated_fderiv_within_succ_apply_left` for the
iterated Fréchet derivative.
-/


noncomputable theory

open_locale Classical TopologicalSpace BigOperators

open Filter Asymptotics Set

variable{𝕜 : Type _}[NondiscreteNormedField 𝕜]

variable{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]

variable{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]

-- error in Analysis.Calculus.IteratedDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The `n`-th iterated derivative of a function from `𝕜` to `F`, as a function from `𝕜` to `F`. -/
def iterated_deriv (n : exprℕ()) (f : 𝕜 → F) (x : 𝕜) : F :=
(iterated_fderiv 𝕜 n f x : (fin n → 𝕜) → F) (λ i : fin n, 1)

-- error in Analysis.Calculus.IteratedDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The `n`-th iterated derivative of a function from `𝕜` to `F` within a set `s`, as a function
from `𝕜` to `F`. -/ def iterated_deriv_within (n : exprℕ()) (f : 𝕜 → F) (s : set 𝕜) (x : 𝕜) : F :=
(iterated_fderiv_within 𝕜 n f s x : (fin n → 𝕜) → F) (λ i : fin n, 1)

variable{n : ℕ}{f : 𝕜 → F}{s : Set 𝕜}{x : 𝕜}

theorem iterated_deriv_within_univ : iteratedDerivWithin n f univ = iteratedDeriv n f :=
  by 
    ext x 
    rw [iteratedDerivWithin, iteratedDeriv, iterated_fderiv_within_univ]

/-! ### Properties of the iterated derivative within a set -/


-- error in Analysis.Calculus.IteratedDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem iterated_deriv_within_eq_iterated_fderiv_within : «expr = »(iterated_deriv_within n f s x, (iterated_fderiv_within 𝕜 n f s x : (fin n → 𝕜) → F) (λ
  i : fin n, 1)) :=
rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
theorem iterated_deriv_within_eq_equiv_comp :
  iteratedDerivWithin n f s =
    ((ContinuousMultilinearMap.piFieldEquiv 𝕜 (Finₓ n) F).symm ∘ iteratedFderivWithin 𝕜 n f s) :=
  by 
    ext x 
    rfl

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
theorem iterated_fderiv_within_eq_equiv_comp :
  iteratedFderivWithin 𝕜 n f s = (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Finₓ n) F ∘ iteratedDerivWithin n f s) :=
  by 
    rw [iterated_deriv_within_eq_equiv_comp, ←Function.comp.assoc, LinearIsometryEquiv.self_comp_symm, Function.left_id]

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
theorem iterated_fderiv_within_apply_eq_iterated_deriv_within_mul_prod {m : Finₓ n → 𝕜} :
  (iteratedFderivWithin 𝕜 n f s x : (Finₓ n → 𝕜) → F) m = (∏i, m i) • iteratedDerivWithin n f s x :=
  by 
    rw [iterated_deriv_within_eq_iterated_fderiv_within, ←ContinuousMultilinearMap.map_smul_univ]
    simp 

@[simp]
theorem iterated_deriv_within_zero : iteratedDerivWithin 0 f s = f :=
  by 
    ext x 
    simp [iteratedDerivWithin]

@[simp]
theorem iterated_deriv_within_one (hs : UniqueDiffOn 𝕜 s) {x : 𝕜} (hx : x ∈ s) :
  iteratedDerivWithin 1 f s x = derivWithin f s x :=
  by 
    simp [iteratedDerivWithin, iterated_fderiv_within_one_apply hs hx]
    rfl

/-- If the first `n` derivatives within a set of a function are continuous, and its first `n-1`
derivatives are differentiable, then the function is `C^n`. This is not an equivalence in general,
but this is an equivalence when the set has unique derivatives, see
`times_cont_diff_on_iff_continuous_on_differentiable_on_deriv`. -/
theorem times_cont_diff_on_of_continuous_on_differentiable_on_deriv {n : WithTop ℕ}
  (Hcont : ∀ (m : ℕ), (m : WithTop ℕ) ≤ n → ContinuousOn (fun x => iteratedDerivWithin m f s x) s)
  (Hdiff : ∀ (m : ℕ), (m : WithTop ℕ) < n → DifferentiableOn 𝕜 (fun x => iteratedDerivWithin m f s x) s) :
  TimesContDiffOn 𝕜 n f s :=
  by 
    apply times_cont_diff_on_of_continuous_on_differentiable_on
    ·
      simpa [iterated_fderiv_within_eq_equiv_comp, LinearIsometryEquiv.comp_continuous_on_iff]
    ·
      simpa [iterated_fderiv_within_eq_equiv_comp, LinearIsometryEquiv.comp_differentiable_on_iff]

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
theorem times_cont_diff_on_of_differentiable_on_deriv {n : WithTop ℕ}
  (h : ∀ (m : ℕ), (m : WithTop ℕ) ≤ n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s) : TimesContDiffOn 𝕜 n f s :=
  by 
    apply times_cont_diff_on_of_differentiable_on 
    simpa only [iterated_fderiv_within_eq_equiv_comp, LinearIsometryEquiv.comp_differentiable_on_iff]

/-- On a set with unique derivatives, a `C^n` function has derivatives up to `n` which are
continuous. -/
theorem TimesContDiffOn.continuous_on_iterated_deriv_within {n : WithTop ℕ} {m : ℕ} (h : TimesContDiffOn 𝕜 n f s)
  (hmn : (m : WithTop ℕ) ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedDerivWithin m f s) s :=
  by 
    simpa only [iterated_deriv_within_eq_equiv_comp, LinearIsometryEquiv.comp_continuous_on_iff] using
      h.continuous_on_iterated_fderiv_within hmn hs

/-- On a set with unique derivatives, a `C^n` function has derivatives less than `n` which are
differentiable. -/
theorem TimesContDiffOn.differentiable_on_iterated_deriv_within {n : WithTop ℕ} {m : ℕ} (h : TimesContDiffOn 𝕜 n f s)
  (hmn : (m : WithTop ℕ) < n) (hs : UniqueDiffOn 𝕜 s) : DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s :=
  by 
    simpa only [iterated_deriv_within_eq_equiv_comp, LinearIsometryEquiv.comp_differentiable_on_iff] using
      h.differentiable_on_iterated_fderiv_within hmn hs

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative on sets with unique derivatives. -/
theorem times_cont_diff_on_iff_continuous_on_differentiable_on_deriv {n : WithTop ℕ} (hs : UniqueDiffOn 𝕜 s) :
  TimesContDiffOn 𝕜 n f s ↔
    (∀ (m : ℕ), (m : WithTop ℕ) ≤ n → ContinuousOn (iteratedDerivWithin m f s) s) ∧
      ∀ (m : ℕ), (m : WithTop ℕ) < n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s :=
  by 
    simp only [times_cont_diff_on_iff_continuous_on_differentiable_on hs, iterated_fderiv_within_eq_equiv_comp,
      LinearIsometryEquiv.comp_continuous_on_iff, LinearIsometryEquiv.comp_differentiable_on_iff]

-- error in Analysis.Calculus.IteratedDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
differentiating the `n`-th iterated derivative. -/
theorem iterated_deriv_within_succ
{x : 𝕜}
(hxs : unique_diff_within_at 𝕜 s x) : «expr = »(iterated_deriv_within «expr + »(n, 1) f s x, deriv_within (iterated_deriv_within n f s) s x) :=
begin
  rw ["[", expr iterated_deriv_within_eq_iterated_fderiv_within, ",", expr iterated_fderiv_within_succ_apply_left, ",", expr iterated_fderiv_within_eq_equiv_comp, ",", expr linear_isometry_equiv.comp_fderiv_within _ hxs, ",", expr deriv_within, "]"] [],
  change [expr «expr = »((continuous_multilinear_map.mk_pi_field 𝕜 (fin n) ((fderiv_within 𝕜 (iterated_deriv_within n f s) s x : 𝕜 → F) 1) : (fin n → 𝕜) → F) (λ
     i : fin n, 1), (fderiv_within 𝕜 (iterated_deriv_within n f s) s x : 𝕜 → F) 1)] [] [],
  simp [] [] [] [] [] []
end

-- error in Analysis.Calculus.IteratedDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The `n`-th iterated derivative within a set with unique derivatives can be obtained by
iterating `n` times the differentiation operation. -/
theorem iterated_deriv_within_eq_iterate
{x : 𝕜}
(hs : unique_diff_on 𝕜 s)
(hx : «expr ∈ »(x, s)) : «expr = »(iterated_deriv_within n f s x, «expr ^[ ]»(λ g : 𝕜 → F, deriv_within g s, n) f x) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] ["generalizing", ident x],
  { simp [] [] [] [] [] [] },
  { rw ["[", expr iterated_deriv_within_succ (hs x hx), ",", expr function.iterate_succ', "]"] [],
    exact [expr deriv_within_congr (hs x hx) (λ y hy, IH hy) (IH hx)] }
end

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
taking the `n`-th derivative of the derivative. -/
theorem iterated_deriv_within_succ' {x : 𝕜} (hxs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
  iteratedDerivWithin (n+1) f s x = (iteratedDerivWithin n (derivWithin f s) s) x :=
  by 
    rw [iterated_deriv_within_eq_iterate hxs hx, iterated_deriv_within_eq_iterate hxs hx]
    rfl

/-! ### Properties of the iterated derivative on the whole space -/


-- error in Analysis.Calculus.IteratedDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem iterated_deriv_eq_iterated_fderiv : «expr = »(iterated_deriv n f x, (iterated_fderiv 𝕜 n f x : (fin n → 𝕜) → F) (λ
  i : fin n, 1)) :=
rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
theorem iterated_deriv_eq_equiv_comp :
  iteratedDeriv n f = ((ContinuousMultilinearMap.piFieldEquiv 𝕜 (Finₓ n) F).symm ∘ iteratedFderiv 𝕜 n f) :=
  by 
    ext x 
    rfl

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
theorem iterated_fderiv_eq_equiv_comp :
  iteratedFderiv 𝕜 n f = (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Finₓ n) F ∘ iteratedDeriv n f) :=
  by 
    rw [iterated_deriv_eq_equiv_comp, ←Function.comp.assoc, LinearIsometryEquiv.self_comp_symm, Function.left_id]

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
theorem iterated_fderiv_apply_eq_iterated_deriv_mul_prod {m : Finₓ n → 𝕜} :
  (iteratedFderiv 𝕜 n f x : (Finₓ n → 𝕜) → F) m = (∏i, m i) • iteratedDeriv n f x :=
  by 
    rw [iterated_deriv_eq_iterated_fderiv, ←ContinuousMultilinearMap.map_smul_univ]
    simp 

@[simp]
theorem iterated_deriv_zero : iteratedDeriv 0 f = f :=
  by 
    ext x 
    simp [iteratedDeriv]

@[simp]
theorem iterated_deriv_one : iteratedDeriv 1 f = deriv f :=
  by 
    ext x 
    simp [iteratedDeriv]
    rfl

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative. -/
theorem times_cont_diff_iff_iterated_deriv {n : WithTop ℕ} :
  TimesContDiff 𝕜 n f ↔
    (∀ (m : ℕ), (m : WithTop ℕ) ≤ n → Continuous (iteratedDeriv m f)) ∧
      ∀ (m : ℕ), (m : WithTop ℕ) < n → Differentiable 𝕜 (iteratedDeriv m f) :=
  by 
    simp only [times_cont_diff_iff_continuous_differentiable, iterated_fderiv_eq_equiv_comp,
      LinearIsometryEquiv.comp_continuous_iff, LinearIsometryEquiv.comp_differentiable_iff]

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
theorem times_cont_diff_of_differentiable_iterated_deriv {n : WithTop ℕ}
  (h : ∀ (m : ℕ), (m : WithTop ℕ) ≤ n → Differentiable 𝕜 (iteratedDeriv m f)) : TimesContDiff 𝕜 n f :=
  times_cont_diff_iff_iterated_deriv.2 ⟨fun m hm => (h m hm).Continuous, fun m hm => h m (le_of_ltₓ hm)⟩

theorem TimesContDiff.continuous_iterated_deriv {n : WithTop ℕ} (m : ℕ) (h : TimesContDiff 𝕜 n f)
  (hmn : (m : WithTop ℕ) ≤ n) : Continuous (iteratedDeriv m f) :=
  (times_cont_diff_iff_iterated_deriv.1 h).1 m hmn

theorem TimesContDiff.differentiable_iterated_deriv {n : WithTop ℕ} (m : ℕ) (h : TimesContDiff 𝕜 n f)
  (hmn : (m : WithTop ℕ) < n) : Differentiable 𝕜 (iteratedDeriv m f) :=
  (times_cont_diff_iff_iterated_deriv.1 h).2 m hmn

/-- The `n+1`-th iterated derivative can be obtained by differentiating the `n`-th
iterated derivative. -/
theorem iterated_deriv_succ : iteratedDeriv (n+1) f = deriv (iteratedDeriv n f) :=
  by 
    ext x 
    rw [←iterated_deriv_within_univ, ←iterated_deriv_within_univ, ←deriv_within_univ]
    exact iterated_deriv_within_succ unique_diff_within_at_univ

/-- The `n`-th iterated derivative can be obtained by iterating `n` times the
differentiation operation. -/
theorem iterated_deriv_eq_iterate : iteratedDeriv n f = (deriv^[n]) f :=
  by 
    ext x 
    rw [←iterated_deriv_within_univ]
    convert iterated_deriv_within_eq_iterate unique_diff_on_univ (mem_univ x)
    simp [deriv_within_univ]

/-- The `n+1`-th iterated derivative can be obtained by taking the `n`-th derivative of the
derivative. -/
theorem iterated_deriv_succ' : iteratedDeriv (n+1) f = iteratedDeriv n (deriv f) :=
  by 
    rw [iterated_deriv_eq_iterate, iterated_deriv_eq_iterate]
    rfl

