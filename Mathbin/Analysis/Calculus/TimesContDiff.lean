import Mathbin.Analysis.Calculus.MeanValue 
import Mathbin.Analysis.NormedSpace.Multilinear 
import Mathbin.Analysis.Calculus.FormalMultilinearSeries

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
Finally, it is `C^∞` if it is `C^n` for all n.

We formalize these notions by defining iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iterated_fderiv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iterated_fderiv_within` relative to a domain,
as well as predicates `times_cont_diff_within_at`, `times_cont_diff_at`, `times_cont_diff_on` and
`times_cont_diff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `times_cont_diff_on` is not defined directly in terms of the
regularity of the specific choice `iterated_fderiv_within 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`has_ftaylor_series_up_to_on`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nondiscrete normed field `𝕜`.

* `has_ftaylor_series_up_to n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `has_ftaylor_series_up_to_on n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.
* `times_cont_diff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `times_cont_diff_on 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `times_cont_diff_at 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `times_cont_diff_within_at 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.
* `iterated_fderiv_within 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iterated_fderiv_within 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iterated_fderiv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iterated_fderiv 𝕜 (n-1) f` if one exists, and `0` otherwise.

In sets of unique differentiability, `times_cont_diff_on 𝕜 n f s` can be expressed in terms of the
properties of `iterated_fderiv_within 𝕜 m f s` for `m ≤ n`. In the whole space,
`times_cont_diff 𝕜 n f` can be expressed in terms of the properties of `iterated_fderiv 𝕜 m f`
for `m ≤ n`.

We also prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iterated_fderiv_within`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
can not happen over reals, thanks to partition of unity, but the behavior over a general field is
not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be  glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `times_cont_diff_within_at` and `times_cont_diff_on`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `times_cont_diff_within_at 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iterated_fderiv 𝕜 (n + 1) f x = iterated_fderiv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where we depart from this explicit approach is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated and barely usable, while the inductive proof is very simple. Thus, we
give the inductive proof. As explained above, it works by generalizing over the target space, hence
it only works well if all spaces belong to the same universe. To get the general version, we lift
things to a common universe using a trick.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : with_top ℕ` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/


noncomputable theory

open_locale Classical BigOperators Nnreal

local notation "∞" => (⊤ : WithTop ℕ)

universe u v w

attribute [local instance] NormedGroup.toAddCommGroup NormedSpace.toModule AddCommGroupₓ.toAddCommMonoid

open Set Finₓ Filter

open_locale TopologicalSpace

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜
      E]{F :
    Type
      _}[NormedGroup
      F][NormedSpace 𝕜
      F]{G :
    Type _}[NormedGroup G][NormedSpace 𝕜 G]{s s₁ t u : Set E}{f f₁ : E → F}{g : F → G}{x : E}{c : F}{b : E × F → G}

/-! ### Functions with a Taylor series on a domain -/


variable{p : E → FormalMultilinearSeries 𝕜 E F}

/-- `has_ftaylor_series_up_to_on n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_within_at` but for higher order derivatives. -/
structure HasFtaylorSeriesUpToOn(n : WithTop ℕ)(f : E → F)(p : E → FormalMultilinearSeries 𝕜 E F)(s : Set E) :
  Prop where 
  zero_eq : ∀ x (_ : x ∈ s), (p x 0).uncurry0 = f x 
  fderivWithin :
  ∀ (m : ℕ) (hm : (m : WithTop ℕ) < n), ∀ x (_ : x ∈ s), HasFderivWithinAt (fun y => p y m) (p x m.succ).curryLeft s x 
  cont : ∀ (m : ℕ) (hm : (m : WithTop ℕ) ≤ n), ContinuousOn (fun x => p x m) s

theorem HasFtaylorSeriesUpToOn.zero_eq' {n : WithTop ℕ} (h : HasFtaylorSeriesUpToOn n f p s) {x : E} (hx : x ∈ s) :
  p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) :=
  by 
    rw [←h.zero_eq x hx]
    symm 
    exact ContinuousMultilinearMap.uncurry0_curry0 _

/-- If two functions coincide on a set `s`, then a Taylor series for the first one is as well a
Taylor series for the second one. -/
theorem HasFtaylorSeriesUpToOn.congr {n : WithTop ℕ} (h : HasFtaylorSeriesUpToOn n f p s)
  (h₁ : ∀ x (_ : x ∈ s), f₁ x = f x) : HasFtaylorSeriesUpToOn n f₁ p s :=
  by 
    refine' ⟨fun x hx => _, h.fderiv_within, h.cont⟩
    rw [h₁ x hx]
    exact h.zero_eq x hx

theorem HasFtaylorSeriesUpToOn.mono {n : WithTop ℕ} (h : HasFtaylorSeriesUpToOn n f p s) {t : Set E} (hst : t ⊆ s) :
  HasFtaylorSeriesUpToOn n f p t :=
  ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderiv_within m hm x (hst hx)).mono hst,
    fun m hm => (h.cont m hm).mono hst⟩

theorem HasFtaylorSeriesUpToOn.of_le {m n : WithTop ℕ} (h : HasFtaylorSeriesUpToOn n f p s) (hmn : m ≤ n) :
  HasFtaylorSeriesUpToOn m f p s :=
  ⟨h.zero_eq, fun k hk x hx => h.fderiv_within k (lt_of_lt_of_leₓ hk hmn) x hx, fun k hk => h.cont k (le_transₓ hk hmn)⟩

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_ftaylor_series_up_to_on.continuous_on
{n : with_top exprℕ()}
(h : has_ftaylor_series_up_to_on n f p s) : continuous_on f s :=
begin
  have [] [] [":=", expr (h.cont 0 bot_le).congr (λ x hx, (h.zero_eq' hx).symm)],
  rwa [expr linear_isometry_equiv.comp_continuous_on_iff] ["at", ident this]
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_ftaylor_series_up_to_on_zero_iff : «expr ↔ »(has_ftaylor_series_up_to_on 0 f p s, «expr ∧ »(continuous_on f s, ∀
  x «expr ∈ » s, «expr = »((p x 0).uncurry0, f x))) :=
begin
  refine [expr ⟨λ H, ⟨H.continuous_on, H.zero_eq⟩, λ H, ⟨H.2, λ m hm, false.elim (not_le.2 hm bot_le), _⟩⟩],
  assume [binders (m hm)],
  obtain [ident rfl, ":", expr «expr = »(m, 0)],
  by exact_mod_cast [expr hm.antisymm (zero_le _)],
  have [] [":", expr ∀ x «expr ∈ » s, «expr = »(p x 0, (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x))] [],
  by { assume [binders (x hx)],
    rw ["<-", expr H.2 x hx] [],
    symmetry,
    exact [expr continuous_multilinear_map.uncurry0_curry0 _] },
  rw ["[", expr continuous_on_congr this, ",", expr linear_isometry_equiv.comp_continuous_on_iff, "]"] [],
  exact [expr H.1]
end

theorem has_ftaylor_series_up_to_on_top_iff :
  HasFtaylorSeriesUpToOn ∞ f p s ↔ ∀ (n : ℕ), HasFtaylorSeriesUpToOn n f p s :=
  by 
    split 
    ·
      intro H n 
      exact H.of_le le_top
    ·
      intro H 
      split 
      ·
        exact (H 0).zero_eq
      ·
        intro m hm 
        apply (H m.succ).fderivWithin m (WithTop.coe_lt_coe.2 (lt_add_one m))
      ·
        intro m hm 
        apply (H m).cont m (le_reflₓ _)

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_on.has_fderiv_within_at
{n : with_top exprℕ()}
(h : has_ftaylor_series_up_to_on n f p s)
(hn : «expr ≤ »(1, n))
(hx : «expr ∈ »(x, s)) : has_fderiv_within_at f (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) s x :=
begin
  have [ident A] [":", expr ∀ y «expr ∈ » s, «expr = »(f y, continuous_multilinear_curry_fin0 𝕜 E F (p y 0))] [],
  { assume [binders (y hy)],
    rw ["<-", expr h.zero_eq y hy] [],
    refl },
  suffices [ident H] [":", expr has_fderiv_within_at (λ
    y, continuous_multilinear_curry_fin0 𝕜 E F (p y 0)) (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) s x],
  by exact [expr H.congr A (A x hx)],
  rw [expr linear_isometry_equiv.comp_has_fderiv_within_at_iff'] [],
  have [] [":", expr «expr < »(((0 : exprℕ()) : with_top exprℕ()), n)] [":=", expr lt_of_lt_of_le (with_top.coe_lt_coe.2 nat.zero_lt_one) hn],
  convert [] [expr h.fderiv_within _ this x hx] [],
  ext [] [ident y, ident v] [],
  change [expr «expr = »(p x 1 (snoc 0 y), p x 1 (cons y v))] [] [],
  unfold_coes [],
  congr' [] ["with", ident i],
  rw [expr unique.eq_default i] [],
  refl
end

theorem HasFtaylorSeriesUpToOn.differentiable_on {n : WithTop ℕ} (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) :
  DifferentiableOn 𝕜 f s :=
  fun x hx => (h.has_fderiv_within_at hn hx).DifferentiableWithinAt

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then the term
of order `1` of this series is a derivative of `f` at `x`. -/
theorem HasFtaylorSeriesUpToOn.has_fderiv_at {n : WithTop ℕ} (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
  (hx : s ∈ 𝓝 x) : HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x :=
  (h.has_fderiv_within_at hn (mem_of_mem_nhds hx)).HasFderivAt hx

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
in a neighborhood of `x`, the term of order `1` of this series is a derivative of `f`. -/
theorem HasFtaylorSeriesUpToOn.eventually_has_fderiv_at {n : WithTop ℕ} (h : HasFtaylorSeriesUpToOn n f p s)
  (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) : ∀ᶠy in 𝓝 x, HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p y 1)) y :=
  (eventually_eventually_nhds.2 hx).mono$ fun y hy => h.has_fderiv_at hn hy

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
it is differentiable at `x`. -/
theorem HasFtaylorSeriesUpToOn.differentiable_at {n : WithTop ℕ} (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
  (hx : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  (h.has_fderiv_at hn hx).DifferentiableAt

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p` is a Taylor series up to `n`, and
`p (n + 1)` is a derivative of `p n`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_left
{n : exprℕ()} : «expr ↔ »(has_ftaylor_series_up_to_on «expr + »(n, 1) f p s, «expr ∧ »(has_ftaylor_series_up_to_on n f p s, «expr ∧ »(∀
   x «expr ∈ » s, has_fderiv_within_at (λ
    y, p y n) (p x n.succ).curry_left s x, continuous_on (λ x, p x «expr + »(n, 1)) s))) :=
begin
  split,
  { assume [binders (h)],
    exact [expr ⟨h.of_le (with_top.coe_le_coe.2 (nat.le_succ n)), h.fderiv_within _ (with_top.coe_lt_coe.2 (lt_add_one n)), h.cont «expr + »(n, 1) (le_refl _)⟩] },
  { assume [binders (h)],
    split,
    { exact [expr h.1.zero_eq] },
    { assume [binders (m hm)],
      by_cases [expr h', ":", expr «expr < »(m, n)],
      { exact [expr h.1.fderiv_within m (with_top.coe_lt_coe.2 h')] },
      { have [] [":", expr «expr = »(m, n)] [":=", expr nat.eq_of_lt_succ_of_not_lt (with_top.coe_lt_coe.1 hm) h'],
        rw [expr this] [],
        exact [expr h.2.1] } },
    { assume [binders (m hm)],
      by_cases [expr h', ":", expr «expr ≤ »(m, n)],
      { apply [expr h.1.cont m (with_top.coe_le_coe.2 h')] },
      { have [] [":", expr «expr = »(m, «expr + »(n, 1))] [":=", expr le_antisymm (with_top.coe_le_coe.1 hm) (not_le.1 h')],
        rw [expr this] [],
        exact [expr h.2.2] } } }
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_right
{n : exprℕ()} : «expr ↔ »(has_ftaylor_series_up_to_on («expr + »(n, 1) : exprℕ()) f p s, «expr ∧ »(∀
  x «expr ∈ » s, «expr = »((p x 0).uncurry0, f x), «expr ∧ »(∀
   x «expr ∈ » s, has_fderiv_within_at (λ
    y, p y 0) (p x 1).curry_left s x, has_ftaylor_series_up_to_on n (λ
    x, continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) (λ x, (p x).shift) s))) :=
begin
  split,
  { assume [binders (H)],
    refine [expr ⟨H.zero_eq, H.fderiv_within 0 (with_top.coe_lt_coe.2 (nat.succ_pos n)), _⟩],
    split,
    { assume [binders (x hx)],
      refl },
    { assume [binders (m) (hm : «expr < »((m : with_top exprℕ()), n)) (x) (hx : «expr ∈ »(x, s))],
      have [ident A] [":", expr «expr < »((m.succ : with_top exprℕ()), n.succ)] [],
      by { rw [expr with_top.coe_lt_coe] ["at", "⊢", ident hm],
        exact [expr nat.lt_succ_iff.mpr hm] },
      change [expr has_fderiv_within_at «expr ∘ »((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm, λ
        y : E, p y m.succ) (p x m.succ.succ).curry_right.curry_left s x] [] [],
      rw [expr linear_isometry_equiv.comp_has_fderiv_within_at_iff'] [],
      convert [] [expr H.fderiv_within _ A x hx] [],
      ext [] [ident y, ident v] [],
      change [expr «expr = »(p x m.succ.succ (snoc (cons y (init v)) (v (last _))), p x (nat.succ (nat.succ m)) (cons y v))] [] [],
      rw ["[", "<-", expr cons_snoc_eq_snoc_cons, ",", expr snoc_init_self, "]"] [] },
    { assume [binders (m) (hm : «expr ≤ »((m : with_top exprℕ()), n))],
      have [ident A] [":", expr «expr ≤ »((m.succ : with_top exprℕ()), n.succ)] [],
      by { rw [expr with_top.coe_le_coe] ["at", "⊢", ident hm],
        exact [expr nat.pred_le_iff.mp hm] },
      change [expr continuous_on «expr ∘ »((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm, λ
        y : E, p y m.succ) s] [] [],
      rw [expr linear_isometry_equiv.comp_continuous_on_iff] [],
      exact [expr H.cont _ A] } },
  { rintros ["⟨", ident Hzero_eq, ",", ident Hfderiv_zero, ",", ident Htaylor, "⟩"],
    split,
    { exact [expr Hzero_eq] },
    { assume [binders (m) (hm : «expr < »((m : with_top exprℕ()), n.succ)) (x) (hx : «expr ∈ »(x, s))],
      cases [expr m] [],
      { exact [expr Hfderiv_zero x hx] },
      { have [ident A] [":", expr «expr < »((m : with_top exprℕ()), n)] [],
        by { rw [expr with_top.coe_lt_coe] ["at", ident hm, "⊢"],
          exact [expr nat.lt_of_succ_lt_succ hm] },
        have [] [":", expr has_fderiv_within_at «expr ∘ »((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm, λ
          y : E, p y m.succ) ((p x).shift m.succ).curry_left s x] [":=", expr Htaylor.fderiv_within _ A x hx],
        rw [expr linear_isometry_equiv.comp_has_fderiv_within_at_iff'] ["at", ident this],
        convert [] [expr this] [],
        ext [] [ident y, ident v] [],
        change [expr «expr = »(p x (nat.succ (nat.succ m)) (cons y v), p x m.succ.succ (snoc (cons y (init v)) (v (last _))))] [] [],
        rw ["[", "<-", expr cons_snoc_eq_snoc_cons, ",", expr snoc_init_self, "]"] [] } },
    { assume [binders (m) (hm : «expr ≤ »((m : with_top exprℕ()), n.succ))],
      cases [expr m] [],
      { have [] [":", expr differentiable_on 𝕜 (λ
          x, p x 0) s] [":=", expr λ x hx, (Hfderiv_zero x hx).differentiable_within_at],
        exact [expr this.continuous_on] },
      { have [ident A] [":", expr «expr ≤ »((m : with_top exprℕ()), n)] [],
        by { rw [expr with_top.coe_le_coe] ["at", ident hm, "⊢"],
          exact [expr nat.lt_succ_iff.mp hm] },
        have [] [":", expr continuous_on «expr ∘ »((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm, λ
          y : E, p y m.succ) s] [":=", expr Htaylor.cont _ A],
        rwa [expr linear_isometry_equiv.comp_continuous_on_iff] ["at", ident this] } } }
end

/-! ### Smooth functions within a set around a point -/


variable(𝕜)

/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
def TimesContDiffWithinAt (n : WithTop ℕ) (f : E → F) (s : Set E) (x : E) :=
  ∀ (m : ℕ),
    (m : WithTop ℕ) ≤ n →
      ∃ (u : _)(_ : u ∈ 𝓝[insert x s] x), ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpToOn m f p u

variable{𝕜}

theorem times_cont_diff_within_at_nat {n : ℕ} :
  TimesContDiffWithinAt 𝕜 n f s x ↔
    ∃ (u : _)(_ : u ∈ 𝓝[insert x s] x), ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpToOn n f p u :=
  ⟨fun H => H n (le_reflₓ _), fun ⟨u, hu, p, hp⟩ m hm => ⟨u, hu, p, hp.of_le hm⟩⟩

theorem TimesContDiffWithinAt.of_le {m n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x) (hmn : m ≤ n) :
  TimesContDiffWithinAt 𝕜 m f s x :=
  fun k hk => h k (le_transₓ hk hmn)

theorem times_cont_diff_within_at_iff_forall_nat_le {n : WithTop ℕ} :
  TimesContDiffWithinAt 𝕜 n f s x ↔ ∀ (m : ℕ), «expr↑ » m ≤ n → TimesContDiffWithinAt 𝕜 m f s x :=
  ⟨fun H m hm => H.of_le hm, fun H m hm => H m hm _ le_rfl⟩

theorem times_cont_diff_within_at_top : TimesContDiffWithinAt 𝕜 ∞ f s x ↔ ∀ (n : ℕ), TimesContDiffWithinAt 𝕜 n f s x :=
  times_cont_diff_within_at_iff_forall_nat_le.trans$
    by 
      simp only [forall_prop_of_true, le_top]

theorem TimesContDiffWithinAt.continuous_within_at {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x) :
  ContinuousWithinAt f s x :=
  by 
    rcases h 0 bot_le with ⟨u, hu, p, H⟩
    rw [mem_nhds_within_insert] at hu 
    exact (H.continuous_on.continuous_within_at hu.1).mono_of_mem hu.2

theorem TimesContDiffWithinAt.congr_of_eventually_eq {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : TimesContDiffWithinAt 𝕜 n f₁ s x :=
  fun m hm =>
    let ⟨u, hu, p, H⟩ := h m hm
    ⟨{ x∈u | f₁ x = f x }, Filter.inter_mem hu (mem_nhds_within_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ => And.right⟩

theorem TimesContDiffWithinAt.congr_of_eventually_eq' {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : TimesContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventually_eq h₁$ h₁.self_of_nhds_within hx

theorem Filter.EventuallyEq.times_cont_diff_within_at_iff {n : WithTop ℕ} (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  TimesContDiffWithinAt 𝕜 n f₁ s x ↔ TimesContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => TimesContDiffWithinAt.congr_of_eventually_eq H h₁.symm hx.symm, fun H => H.congr_of_eventually_eq h₁ hx⟩

theorem TimesContDiffWithinAt.congr {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x)
  (h₁ : ∀ y (_ : y ∈ s), f₁ y = f y) (hx : f₁ x = f x) : TimesContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventually_eq (Filter.eventually_eq_of_mem self_mem_nhds_within h₁) hx

theorem TimesContDiffWithinAt.congr' {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x)
  (h₁ : ∀ y (_ : y ∈ s), f₁ y = f y) (hx : x ∈ s) : TimesContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr h₁ (h₁ _ hx)

theorem TimesContDiffWithinAt.mono_of_mem {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x) {t : Set E}
  (hst : s ∈ 𝓝[t] x) : TimesContDiffWithinAt 𝕜 n f t x :=
  by 
    intro m hm 
    rcases h m hm with ⟨u, hu, p, H⟩
    exact ⟨u, nhds_within_le_of_mem (insert_mem_nhds_within_insert hst) hu, p, H⟩

theorem TimesContDiffWithinAt.mono {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t ⊆ s) :
  TimesContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem$ Filter.mem_of_superset self_mem_nhds_within hst

theorem TimesContDiffWithinAt.congr_nhds {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x) {t : Set E}
  (hst : 𝓝[s] x = 𝓝[t] x) : TimesContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem$ hst ▸ self_mem_nhds_within

theorem times_cont_diff_within_at_congr_nhds {n : WithTop ℕ} {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) :
  TimesContDiffWithinAt 𝕜 n f s x ↔ TimesContDiffWithinAt 𝕜 n f t x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

theorem times_cont_diff_within_at_inter' {n : WithTop ℕ} (h : t ∈ 𝓝[s] x) :
  TimesContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ TimesContDiffWithinAt 𝕜 n f s x :=
  times_cont_diff_within_at_congr_nhds$ Eq.symm$ nhds_within_restrict'' _ h

theorem times_cont_diff_within_at_inter {n : WithTop ℕ} (h : t ∈ 𝓝 x) :
  TimesContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ TimesContDiffWithinAt 𝕜 n f s x :=
  times_cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds h)

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
theorem times_cont_diff_within_at.differentiable_within_at'
{n : with_top exprℕ()}
(h : times_cont_diff_within_at 𝕜 n f s x)
(hn : «expr ≤ »(1, n)) : differentiable_within_at 𝕜 f (insert x s) x :=
begin
  rcases [expr h 1 hn, "with", "⟨", ident u, ",", ident hu, ",", ident p, ",", ident H, "⟩"],
  rcases [expr mem_nhds_within.1 hu, "with", "⟨", ident t, ",", ident t_open, ",", ident xt, ",", ident tu, "⟩"],
  rw [expr inter_comm] ["at", ident tu],
  have [] [] [":=", expr (H.mono tu).differentiable_on (le_refl _) x ⟨mem_insert x s, xt⟩],
  exact [expr (differentiable_within_at_inter (is_open.mem_nhds t_open xt)).1 this]
end

theorem TimesContDiffWithinAt.differentiable_within_at {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x)
  (hn : 1 ≤ n) : DifferentiableWithinAt 𝕜 f s x :=
  (h.differentiable_within_at' hn).mono (subset_insert x s)

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_within_at_succ_iff_has_fderiv_within_at
{n : exprℕ()} : «expr ↔ »(times_cont_diff_within_at 𝕜 («expr + »(n, 1) : exprℕ()) f s x, «expr∃ , »((u «expr ∈ » «expr𝓝[ ] »(insert x s, x)), «expr∃ , »((f' : E → «expr →L[ ] »(E, 𝕜, F)), «expr ∧ »(∀
    x «expr ∈ » u, has_fderiv_within_at f (f' x) u x, times_cont_diff_within_at 𝕜 n f' u x)))) :=
begin
  split,
  { assume [binders (h)],
    rcases [expr h n.succ (le_refl _), "with", "⟨", ident u, ",", ident hu, ",", ident p, ",", ident Hp, "⟩"],
    refine [expr ⟨u, hu, λ
      y, continuous_multilinear_curry_fin1 𝕜 E F (p y 1), λ
      y hy, Hp.has_fderiv_within_at (with_top.coe_le_coe.2 (nat.le_add_left 1 n)) hy, _⟩],
    assume [binders (m hm)],
    refine [expr ⟨u, _, λ y : E, (p y).shift, _⟩],
    { convert [] [expr self_mem_nhds_within] [],
      have [] [":", expr «expr ∈ »(x, insert x s)] [],
      by simp [] [] [] [] [] [],
      exact [expr insert_eq_of_mem (mem_of_mem_nhds_within this hu)] },
    { rw [expr has_ftaylor_series_up_to_on_succ_iff_right] ["at", ident Hp],
      exact [expr Hp.2.2.of_le hm] } },
  { rintros ["⟨", ident u, ",", ident hu, ",", ident f', ",", ident f'_eq_deriv, ",", ident Hf', "⟩"],
    rw [expr times_cont_diff_within_at_nat] [],
    rcases [expr Hf' n (le_refl _), "with", "⟨", ident v, ",", ident hv, ",", ident p', ",", ident Hp', "⟩"],
    refine [expr ⟨«expr ∩ »(v, u), _, λ x, (p' x).unshift (f x), _⟩],
    { apply [expr filter.inter_mem _ hu],
      apply [expr nhds_within_le_of_mem hu],
      exact [expr nhds_within_mono _ (subset_insert x u) hv] },
    { rw [expr has_ftaylor_series_up_to_on_succ_iff_right] [],
      refine [expr ⟨λ y hy, rfl, λ y hy, _, _⟩],
      { change [expr has_fderiv_within_at (λ
          z, (continuous_multilinear_curry_fin0 𝕜 E F).symm (f z)) (formal_multilinear_series.unshift (p' y) (f y) 1).curry_left «expr ∩ »(v, u) y] [] [],
        rw [expr linear_isometry_equiv.comp_has_fderiv_within_at_iff'] [],
        convert [] [expr (f'_eq_deriv y hy.2).mono (inter_subset_right v u)] [],
        rw ["<-", expr Hp'.zero_eq y hy.1] [],
        ext [] [ident z] [],
        change [expr «expr = »(p' y 0 (init (@cons 0 (λ i, E) z 0)) (@cons 0 (λ i, E) z 0 (last 0)), p' y 0 0 z)] [] [],
        unfold_coes [],
        congr },
      { convert [] [expr (Hp'.mono (inter_subset_left v u)).congr (λ x hx, Hp'.zero_eq x hx.1)] [],
        { ext [] [ident x, ident y] [],
          change [expr «expr = »(p' x 0 (init (@snoc 0 (λ i : fin 1, E) 0 y)) y, p' x 0 0 y)] [] [],
          rw [expr init_snoc] [] },
        { ext [] [ident x, ident k, ident v, ident y] [],
          change [expr «expr = »(p' x k (init (@snoc k (λ
               i : fin k.succ, E) v y)) (@snoc k (λ i : fin k.succ, E) v y (last k)), p' x k v y)] [] [],
          rw ["[", expr snoc_last, ",", expr init_snoc, "]"] [] } } } }
end

/-! ### Smooth functions within a set -/


variable(𝕜)

/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
-/
def TimesContDiffOn (n : WithTop ℕ) (f : E → F) (s : Set E) :=
  ∀ x (_ : x ∈ s), TimesContDiffWithinAt 𝕜 n f s x

variable{𝕜}

theorem TimesContDiffOn.times_cont_diff_within_at {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f s) (hx : x ∈ s) :
  TimesContDiffWithinAt 𝕜 n f s x :=
  h x hx

theorem TimesContDiffWithinAt.times_cont_diff_on {n : WithTop ℕ} {m : ℕ} (hm : (m : WithTop ℕ) ≤ n)
  (h : TimesContDiffWithinAt 𝕜 n f s x) :
  ∃ (u : _)(_ : u ∈ 𝓝[insert x s] x), u ⊆ insert x s ∧ TimesContDiffOn 𝕜 m f u :=
  by 
    rcases h m hm with ⟨u, u_nhd, p, hp⟩
    refine' ⟨u ∩ insert x s, Filter.inter_mem u_nhd self_mem_nhds_within, inter_subset_right _ _, _⟩
    intro y hy m' hm' 
    refine' ⟨u ∩ insert x s, _, p, (hp.mono (inter_subset_left _ _)).ofLe hm'⟩
    convert self_mem_nhds_within 
    exact insert_eq_of_mem hy

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem times_cont_diff_within_at.eventually
{n : exprℕ()}
(h : times_cont_diff_within_at 𝕜 n f s x) : «expr∀ᶠ in , »((y), «expr𝓝[ ] »(insert x s, x), times_cont_diff_within_at 𝕜 n f s y) :=
begin
  rcases [expr h.times_cont_diff_on le_rfl, "with", "⟨", ident u, ",", ident hu, ",", ident hu_sub, ",", ident hd, "⟩"],
  have [] [":", expr «expr∀ᶠ in , »((y : E), «expr𝓝[ ] »(insert x s, x), «expr ∧ »(«expr ∈ »(u, «expr𝓝[ ] »(insert x s, y)), «expr ∈ »(y, u)))] [],
  from [expr (eventually_nhds_within_nhds_within.2 hu).and hu],
  refine [expr this.mono (λ y hy, (hd y hy.2).mono_of_mem _)],
  exact [expr nhds_within_mono y (subset_insert _ _) hy.1]
end

theorem TimesContDiffOn.of_le {m n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f s) (hmn : m ≤ n) : TimesContDiffOn 𝕜 m f s :=
  fun x hx => (h x hx).ofLe hmn

theorem times_cont_diff_on_iff_forall_nat_le {n : WithTop ℕ} :
  TimesContDiffOn 𝕜 n f s ↔ ∀ (m : ℕ), «expr↑ » m ≤ n → TimesContDiffOn 𝕜 m f s :=
  ⟨fun H m hm => H.of_le hm, fun H x hx m hm => H m hm x hx m le_rfl⟩

theorem times_cont_diff_on_top : TimesContDiffOn 𝕜 ∞ f s ↔ ∀ (n : ℕ), TimesContDiffOn 𝕜 n f s :=
  times_cont_diff_on_iff_forall_nat_le.trans$
    by 
      simp only [le_top, forall_prop_of_true]

theorem times_cont_diff_on_all_iff_nat : (∀ n, TimesContDiffOn 𝕜 n f s) ↔ ∀ (n : ℕ), TimesContDiffOn 𝕜 n f s :=
  by 
    refine' ⟨fun H n => H n, _⟩
    rintro H (_ | n)
    exacts[times_cont_diff_on_top.2 H, H n]

theorem TimesContDiffOn.continuous_on {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f s) : ContinuousOn f s :=
  fun x hx => (h x hx).ContinuousWithinAt

theorem TimesContDiffOn.congr {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f s) (h₁ : ∀ x (_ : x ∈ s), f₁ x = f x) :
  TimesContDiffOn 𝕜 n f₁ s :=
  fun x hx => (h x hx).congr h₁ (h₁ x hx)

theorem times_cont_diff_on_congr {n : WithTop ℕ} (h₁ : ∀ x (_ : x ∈ s), f₁ x = f x) :
  TimesContDiffOn 𝕜 n f₁ s ↔ TimesContDiffOn 𝕜 n f s :=
  ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩

theorem TimesContDiffOn.mono {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f s) {t : Set E} (hst : t ⊆ s) :
  TimesContDiffOn 𝕜 n f t :=
  fun x hx => (h x (hst hx)).mono hst

theorem TimesContDiffOn.congr_mono {n : WithTop ℕ} (hf : TimesContDiffOn 𝕜 n f s) (h₁ : ∀ x (_ : x ∈ s₁), f₁ x = f x)
  (hs : s₁ ⊆ s) : TimesContDiffOn 𝕜 n f₁ s₁ :=
  (hf.mono hs).congr h₁

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
theorem TimesContDiffOn.differentiable_on {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f s) (hn : 1 ≤ n) :
  DifferentiableOn 𝕜 f s :=
  fun x hx => (h x hx).DifferentiableWithinAt hn

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
theorem times_cont_diff_on_of_locally_times_cont_diff_on {n : WithTop ℕ}
  (h : ∀ x (_ : x ∈ s), ∃ u, IsOpen u ∧ x ∈ u ∧ TimesContDiffOn 𝕜 n f (s ∩ u)) : TimesContDiffOn 𝕜 n f s :=
  by 
    intro x xs 
    rcases h x xs with ⟨u, u_open, xu, hu⟩
    apply (times_cont_diff_within_at_inter _).1 (hu x ⟨xs, xu⟩)
    exact IsOpen.mem_nhds u_open xu

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_on_succ_iff_has_fderiv_within_at
{n : exprℕ()} : «expr ↔ »(times_cont_diff_on 𝕜 («expr + »(n, 1) : exprℕ()) f s, ∀
 x «expr ∈ » s, «expr∃ , »((u «expr ∈ » «expr𝓝[ ] »(insert x s, x)), «expr∃ , »((f' : E → «expr →L[ ] »(E, 𝕜, F)), «expr ∧ »(∀
    x «expr ∈ » u, has_fderiv_within_at f (f' x) u x, times_cont_diff_on 𝕜 n f' u)))) :=
begin
  split,
  { assume [binders (h x hx)],
    rcases [expr h x hx n.succ (le_refl _), "with", "⟨", ident u, ",", ident hu, ",", ident p, ",", ident Hp, "⟩"],
    refine [expr ⟨u, hu, λ
      y, continuous_multilinear_curry_fin1 𝕜 E F (p y 1), λ
      y hy, Hp.has_fderiv_within_at (with_top.coe_le_coe.2 (nat.le_add_left 1 n)) hy, _⟩],
    rw [expr has_ftaylor_series_up_to_on_succ_iff_right] ["at", ident Hp],
    assume [binders (z hz m hm)],
    refine [expr ⟨u, _, λ x : E, (p x).shift, Hp.2.2.of_le hm⟩],
    convert [] [expr self_mem_nhds_within] [],
    exact [expr insert_eq_of_mem hz] },
  { assume [binders (h x hx)],
    rw [expr times_cont_diff_within_at_succ_iff_has_fderiv_within_at] [],
    rcases [expr h x hx, "with", "⟨", ident u, ",", ident u_nhbd, ",", ident f', ",", ident hu, ",", ident hf', "⟩"],
    have [] [":", expr «expr ∈ »(x, u)] [":=", expr mem_of_mem_nhds_within (mem_insert _ _) u_nhbd],
    exact [expr ⟨u, u_nhbd, f', hu, hf' x this⟩] }
end

/-! ### Iterated derivative within a set -/


variable(𝕜)

/--
The `n`-th derivative of a function along a set, defined inductively by saying that the `n+1`-th
derivative of `f` is the derivative of the `n`-th derivative of `f` along this set, together with
an uncurrying step to see it as a multilinear map in `n+1` variables..
-/
noncomputable def iteratedFderivWithin (n : ℕ) (f : E → F) (s : Set E) : E → «expr [× ]→L[ ] » E n 𝕜 F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.curry0 𝕜 E (f x))
    fun n rec x => ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)

/-- Formal Taylor series associated to a function within a set. -/
def ftaylorSeriesWithin (f : E → F) (s : Set E) (x : E) : FormalMultilinearSeries 𝕜 E F :=
  fun n => iteratedFderivWithin 𝕜 n f s x

variable{𝕜}

@[simp]
theorem iterated_fderiv_within_zero_apply (m : Finₓ 0 → E) :
  (iteratedFderivWithin 𝕜 0 f s x : (Finₓ 0 → E) → F) m = f x :=
  rfl

theorem iterated_fderiv_within_zero_eq_comp :
  iteratedFderivWithin 𝕜 0 f s = ((continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f) :=
  rfl

theorem iterated_fderiv_within_succ_apply_left {n : ℕ} (m : Finₓ (n+1) → E) :
  (iteratedFderivWithin 𝕜 (n+1) f s x : (Finₓ (n+1) → E) → F) m =
    (fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n f s) s x : E → «expr [× ]→L[ ] » E n 𝕜 F) (m 0) (tail m) :=
  rfl

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iterated_fderiv_within_succ_eq_comp_left
{n : exprℕ()} : «expr = »(iterated_fderiv_within 𝕜 «expr + »(n, 1) f s, «expr ∘ »(continuous_multilinear_curry_left_equiv 𝕜 (λ
   i : fin «expr + »(n, 1), E) F, fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s)) :=
rfl

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem iterated_fderiv_within_succ_apply_right
{n : exprℕ()}
(hs : unique_diff_on 𝕜 s)
(hx : «expr ∈ »(x, s))
(m : fin «expr + »(n, 1) → E) : «expr = »((iterated_fderiv_within 𝕜 «expr + »(n, 1) f s x : (fin «expr + »(n, 1) → E) → F) m, iterated_fderiv_within 𝕜 n (λ
  y, fderiv_within 𝕜 f s y) s x (init m) (m (last n))) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] ["generalizing", ident x],
  { rw ["[", expr iterated_fderiv_within_succ_eq_comp_left, ",", expr iterated_fderiv_within_zero_eq_comp, ",", expr iterated_fderiv_within_zero_apply, ",", expr function.comp_apply, ",", expr linear_isometry_equiv.comp_fderiv_within _ (hs x hx), "]"] [],
    refl },
  { let [ident I] [] [":=", expr continuous_multilinear_curry_right_equiv' 𝕜 n E F],
    have [ident A] [":", expr ∀
     y «expr ∈ » s, «expr = »(iterated_fderiv_within 𝕜 n.succ f s y, «expr ∘ »(I, iterated_fderiv_within 𝕜 n (λ
        y, fderiv_within 𝕜 f s y) s) y)] [],
    by { assume [binders (y hy)],
      ext [] [ident m] [],
      rw [expr @IH m y hy] [],
      refl },
    calc
      «expr = »((iterated_fderiv_within 𝕜 «expr + »(n, 2) f s x : (fin «expr + »(n, 2) → E) → F) m, (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n.succ f s) s x : E → «expr [× ]→L[ ] »(E, «expr + »(n, 1), 𝕜, F)) (m 0) (tail m)) : rfl
      «expr = »(..., (fderiv_within 𝕜 «expr ∘ »(I, iterated_fderiv_within 𝕜 n (fderiv_within 𝕜 f s) s) s x : E → «expr [× ]→L[ ] »(E, «expr + »(n, 1), 𝕜, F)) (m 0) (tail m)) : by rw [expr fderiv_within_congr (hs x hx) A (A x hx)] []
      «expr = »(..., («expr ∘ »(I, fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n (fderiv_within 𝕜 f s) s) s x) : E → «expr [× ]→L[ ] »(E, «expr + »(n, 1), 𝕜, F)) (m 0) (tail m)) : by { rw [expr linear_isometry_equiv.comp_fderiv_within _ (hs x hx)] [],
        refl }
      «expr = »(..., (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n (λ
         y, fderiv_within 𝕜 f s y) s) s x : E → «expr [× ]→L[ ] »(E, n, 𝕜, «expr →L[ ] »(E, 𝕜, F))) (m 0) (init (tail m)) (tail m (last n))) : rfl
      «expr = »(..., iterated_fderiv_within 𝕜 (nat.succ n) (λ
        y, fderiv_within 𝕜 f s y) s x (init m) (m (last «expr + »(n, 1)))) : by { rw ["[", expr iterated_fderiv_within_succ_apply_left, ",", expr tail_init_eq_init_tail, "]"] [],
        refl } }
end

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iterated_fderiv_within_succ_eq_comp_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
  iteratedFderivWithin 𝕜 (n+1) f s x =
    (continuousMultilinearCurryRightEquiv' 𝕜 n E F ∘ iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) x :=
  by 
    ext m 
    rw [iterated_fderiv_within_succ_apply_right hs hx]
    rfl

@[simp]
theorem iterated_fderiv_within_one_apply (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (m : Finₓ 1 → E) :
  (iteratedFderivWithin 𝕜 1 f s x : (Finₓ 1 → E) → F) m = (fderivWithin 𝕜 f s x : E → F) (m 0) :=
  by 
    rw [iterated_fderiv_within_succ_apply_right hs hx, iterated_fderiv_within_zero_apply]
    rfl

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two functions coincide on a set `s` of unique differentiability, then their iterated
differentials within this set coincide. -/
theorem iterated_fderiv_within_congr
{n : exprℕ()}
(hs : unique_diff_on 𝕜 s)
(hL : ∀ y «expr ∈ » s, «expr = »(f₁ y, f y))
(hx : «expr ∈ »(x, s)) : «expr = »(iterated_fderiv_within 𝕜 n f₁ s x, iterated_fderiv_within 𝕜 n f s x) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] ["generalizing", ident x],
  { ext [] [ident m] [],
    simp [] [] [] ["[", expr hL x hx, "]"] [] [] },
  { have [] [":", expr «expr = »(fderiv_within 𝕜 (λ
       y, iterated_fderiv_within 𝕜 n f₁ s y) s x, fderiv_within 𝕜 (λ
       y, iterated_fderiv_within 𝕜 n f s y) s x)] [":=", expr fderiv_within_congr (hs x hx) (λ y hy, IH hy) (IH hx)],
    ext [] [ident m] [],
    rw ["[", expr iterated_fderiv_within_succ_apply_left, ",", expr iterated_fderiv_within_succ_apply_left, ",", expr this, "]"] [] }
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with an open set containing `x`. -/
theorem iterated_fderiv_within_inter_open
{n : exprℕ()}
(hu : is_open u)
(hs : unique_diff_on 𝕜 «expr ∩ »(s, u))
(hx : «expr ∈ »(x, «expr ∩ »(s, u))) : «expr = »(iterated_fderiv_within 𝕜 n f «expr ∩ »(s, u) x, iterated_fderiv_within 𝕜 n f s x) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] ["generalizing", ident x],
  { ext [] [ident m] [],
    simp [] [] [] [] [] [] },
  { have [ident A] [":", expr «expr = »(fderiv_within 𝕜 (λ
       y, iterated_fderiv_within 𝕜 n f «expr ∩ »(s, u) y) «expr ∩ »(s, u) x, fderiv_within 𝕜 (λ
       y, iterated_fderiv_within 𝕜 n f s y) «expr ∩ »(s, u) x)] [":=", expr fderiv_within_congr (hs x hx) (λ
      y hy, IH hy) (IH hx)],
    have [ident B] [":", expr «expr = »(fderiv_within 𝕜 (λ
       y, iterated_fderiv_within 𝕜 n f s y) «expr ∩ »(s, u) x, fderiv_within 𝕜 (λ
       y, iterated_fderiv_within 𝕜 n f s y) s x)] [":=", expr fderiv_within_inter (is_open.mem_nhds hu hx.2) ((unique_diff_within_at_inter (is_open.mem_nhds hu hx.2)).1 (hs x hx))],
    ext [] [ident m] [],
    rw ["[", expr iterated_fderiv_within_succ_apply_left, ",", expr iterated_fderiv_within_succ_apply_left, ",", expr A, ",", expr B, "]"] [] }
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x` within `s`. -/
theorem iterated_fderiv_within_inter'
{n : exprℕ()}
(hu : «expr ∈ »(u, «expr𝓝[ ] »(s, x)))
(hs : unique_diff_on 𝕜 s)
(xs : «expr ∈ »(x, s)) : «expr = »(iterated_fderiv_within 𝕜 n f «expr ∩ »(s, u) x, iterated_fderiv_within 𝕜 n f s x) :=
begin
  obtain ["⟨", ident v, ",", ident v_open, ",", ident xv, ",", ident vu, "⟩", ":", expr «expr∃ , »((v), «expr ∧ »(is_open v, «expr ∧ »(«expr ∈ »(x, v), «expr ⊆ »(«expr ∩ »(v, s), u)))), ":=", expr mem_nhds_within.1 hu],
  have [ident A] [":", expr «expr = »(«expr ∩ »(«expr ∩ »(s, u), v), «expr ∩ »(s, v))] [],
  { apply [expr subset.antisymm (inter_subset_inter (inter_subset_left _ _) (subset.refl _))],
    exact [expr λ (y) ⟨ys, yv⟩, ⟨⟨ys, vu ⟨yv, ys⟩⟩, yv⟩] },
  have [] [":", expr «expr = »(iterated_fderiv_within 𝕜 n f «expr ∩ »(s, v) x, iterated_fderiv_within 𝕜 n f s x)] [":=", expr iterated_fderiv_within_inter_open v_open (hs.inter v_open) ⟨xs, xv⟩],
  rw ["<-", expr this] [],
  have [] [":", expr «expr = »(iterated_fderiv_within 𝕜 n f «expr ∩ »(«expr ∩ »(s, u), v) x, iterated_fderiv_within 𝕜 n f «expr ∩ »(s, u) x)] [],
  { refine [expr iterated_fderiv_within_inter_open v_open _ ⟨⟨xs, vu ⟨xv, xs⟩⟩, xv⟩],
    rw [expr A] [],
    exact [expr hs.inter v_open] },
  rw [expr A] ["at", ident this],
  rw ["<-", expr this] []
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`. -/
theorem iterated_fderiv_within_inter {n : ℕ} (hu : u ∈ 𝓝 x) (hs : UniqueDiffOn 𝕜 s) (xs : x ∈ s) :
  iteratedFderivWithin 𝕜 n f (s ∩ u) x = iteratedFderivWithin 𝕜 n f s x :=
  iterated_fderiv_within_inter' (mem_nhds_within_of_mem_nhds hu) hs xs

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem times_cont_diff_on_zero : «expr ↔ »(times_cont_diff_on 𝕜 0 f s, continuous_on f s) :=
begin
  refine [expr ⟨λ H, H.continuous_on, λ H, _⟩],
  assume [binders (x hx m hm)],
  have [] [":", expr «expr = »((m : with_top exprℕ()), 0)] [":=", expr le_antisymm hm bot_le],
  rw [expr this] [],
  refine [expr ⟨insert x s, self_mem_nhds_within, ftaylor_series_within 𝕜 f s, _⟩],
  rw [expr has_ftaylor_series_up_to_on_zero_iff] [],
  exact [expr ⟨by rwa [expr insert_eq_of_mem hx] [], λ
    x hx, by simp [] [] [] ["[", expr ftaylor_series_within, "]"] [] []⟩]
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem times_cont_diff_within_at_zero
(hx : «expr ∈ »(x, s)) : «expr ↔ »(times_cont_diff_within_at 𝕜 0 f s x, «expr∃ , »((u «expr ∈ » «expr𝓝[ ] »(s, x)), continuous_on f «expr ∩ »(s, u))) :=
begin
  split,
  { intros [ident h],
    obtain ["⟨", ident u, ",", ident H, ",", ident p, ",", ident hp, "⟩", ":=", expr h 0 (by norm_num [] [])],
    refine [expr ⟨u, _, _⟩],
    { simpa [] [] [] ["[", expr hx, "]"] [] ["using", expr H] },
    { simp [] [] ["only"] ["[", expr with_top.coe_zero, ",", expr has_ftaylor_series_up_to_on_zero_iff, "]"] [] ["at", ident hp],
      exact [expr hp.1.mono (inter_subset_right s u)] } },
  { rintros ["⟨", ident u, ",", ident H, ",", ident hu, "⟩"],
    rw ["<-", expr times_cont_diff_within_at_inter' H] [],
    have [ident h'] [":", expr «expr ∈ »(x, «expr ∩ »(s, u))] [":=", expr ⟨hx, mem_of_mem_nhds_within hx H⟩],
    exact [expr (times_cont_diff_on_zero.mpr hu).times_cont_diff_within_at h'] }
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- On a set with unique differentiability, any choice of iterated differential has to coincide
with the one we have chosen in `iterated_fderiv_within 𝕜 m f s`. -/
theorem has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on
{n : with_top exprℕ()}
(h : has_ftaylor_series_up_to_on n f p s)
{m : exprℕ()}
(hmn : «expr ≤ »((m : with_top exprℕ()), n))
(hs : unique_diff_on 𝕜 s)
(hx : «expr ∈ »(x, s)) : «expr = »(p x m, iterated_fderiv_within 𝕜 m f s x) :=
begin
  induction [expr m] [] ["with", ident m, ident IH] ["generalizing", ident x],
  { rw ["[", expr h.zero_eq' hx, ",", expr iterated_fderiv_within_zero_eq_comp, "]"] [] },
  { have [ident A] [":", expr «expr < »((m : with_top exprℕ()), n)] [":=", expr lt_of_lt_of_le (with_top.coe_lt_coe.2 (lt_add_one m)) hmn],
    have [] [":", expr has_fderiv_within_at (λ
      y : E, iterated_fderiv_within 𝕜 m f s y) (continuous_multilinear_map.curry_left (p x (nat.succ m))) s x] [":=", expr (h.fderiv_within m A x hx).congr (λ
      y hy, (IH (le_of_lt A) hy).symm) (IH (le_of_lt A) hx).symm],
    rw ["[", expr iterated_fderiv_within_succ_eq_comp_left, ",", expr function.comp_apply, ",", expr this.fderiv_within (hs x hx), "]"] [],
    exact [expr (continuous_multilinear_map.uncurry_curry_left _).symm] }
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem times_cont_diff_on.ftaylor_series_within
{n : with_top exprℕ()}
(h : times_cont_diff_on 𝕜 n f s)
(hs : unique_diff_on 𝕜 s) : has_ftaylor_series_up_to_on n f (ftaylor_series_within 𝕜 f s) s :=
begin
  split,
  { assume [binders (x hx)],
    simp [] [] ["only"] ["[", expr ftaylor_series_within, ",", expr continuous_multilinear_map.uncurry0_apply, ",", expr iterated_fderiv_within_zero_apply, "]"] [] [] },
  { assume [binders (m hm x hx)],
    rcases [expr h x hx m.succ (with_top.add_one_le_of_lt hm), "with", "⟨", ident u, ",", ident hu, ",", ident p, ",", ident Hp, "⟩"],
    rw [expr insert_eq_of_mem hx] ["at", ident hu],
    rcases [expr mem_nhds_within.1 hu, "with", "⟨", ident o, ",", ident o_open, ",", ident xo, ",", ident ho, "⟩"],
    rw [expr inter_comm] ["at", ident ho],
    have [] [":", expr «expr = »(p x m.succ, ftaylor_series_within 𝕜 f s x m.succ)] [],
    { change [expr «expr = »(p x m.succ, iterated_fderiv_within 𝕜 m.succ f s x)] [] [],
      rw ["<-", expr iterated_fderiv_within_inter (is_open.mem_nhds o_open xo) hs hx] [],
      exact [expr (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (le_refl _) (hs.inter o_open) ⟨hx, xo⟩] },
    rw ["[", "<-", expr this, ",", "<-", expr has_fderiv_within_at_inter (is_open.mem_nhds o_open xo), "]"] [],
    have [ident A] [":", expr ∀ y «expr ∈ » «expr ∩ »(s, o), «expr = »(p y m, ftaylor_series_within 𝕜 f s y m)] [],
    { rintros [ident y, "⟨", ident hy, ",", ident yo, "⟩"],
      change [expr «expr = »(p y m, iterated_fderiv_within 𝕜 m f s y)] [] [],
      rw ["<-", expr iterated_fderiv_within_inter (is_open.mem_nhds o_open yo) hs hy] [],
      exact [expr (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (with_top.coe_le_coe.2 (nat.le_succ m)) (hs.inter o_open) ⟨hy, yo⟩] },
    exact [expr ((Hp.mono ho).fderiv_within m (with_top.coe_lt_coe.2 (lt_add_one m)) x ⟨hx, xo⟩).congr (λ
      y hy, (A y hy).symm) (A x ⟨hx, xo⟩).symm] },
  { assume [binders (m hm)],
    apply [expr continuous_on_of_locally_continuous_on],
    assume [binders (x hx)],
    rcases [expr h x hx m hm, "with", "⟨", ident u, ",", ident hu, ",", ident p, ",", ident Hp, "⟩"],
    rcases [expr mem_nhds_within.1 hu, "with", "⟨", ident o, ",", ident o_open, ",", ident xo, ",", ident ho, "⟩"],
    rw [expr insert_eq_of_mem hx] ["at", ident ho],
    rw [expr inter_comm] ["at", ident ho],
    refine [expr ⟨o, o_open, xo, _⟩],
    have [ident A] [":", expr ∀ y «expr ∈ » «expr ∩ »(s, o), «expr = »(p y m, ftaylor_series_within 𝕜 f s y m)] [],
    { rintros [ident y, "⟨", ident hy, ",", ident yo, "⟩"],
      change [expr «expr = »(p y m, iterated_fderiv_within 𝕜 m f s y)] [] [],
      rw ["<-", expr iterated_fderiv_within_inter (is_open.mem_nhds o_open yo) hs hy] [],
      exact [expr (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (le_refl _) (hs.inter o_open) ⟨hy, yo⟩] },
    exact [expr ((Hp.mono ho).cont m (le_refl _)).congr (λ y hy, (A y hy).symm)] }
end

theorem times_cont_diff_on_of_continuous_on_differentiable_on {n : WithTop ℕ}
  (Hcont : ∀ (m : ℕ), (m : WithTop ℕ) ≤ n → ContinuousOn (fun x => iteratedFderivWithin 𝕜 m f s x) s)
  (Hdiff : ∀ (m : ℕ), (m : WithTop ℕ) < n → DifferentiableOn 𝕜 (fun x => iteratedFderivWithin 𝕜 m f s x) s) :
  TimesContDiffOn 𝕜 n f s :=
  by 
    intro x hx m hm 
    rw [insert_eq_of_mem hx]
    refine' ⟨s, self_mem_nhds_within, ftaylorSeriesWithin 𝕜 f s, _⟩
    split 
    ·
      intro y hy 
      simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.uncurry0_apply, iterated_fderiv_within_zero_apply]
    ·
      intro k hk y hy 
      convert (Hdiff k (lt_of_lt_of_leₓ hk hm) y hy).HasFderivWithinAt 
      simp only [ftaylorSeriesWithin, iterated_fderiv_within_succ_eq_comp_left, ContinuousLinearEquiv.coe_apply,
        Function.comp_app, coe_fn_coe_base]
      exact ContinuousLinearMap.curry_uncurry_left _
    ·
      intro k hk 
      exact Hcont k (le_transₓ hk hm)

theorem times_cont_diff_on_of_differentiable_on {n : WithTop ℕ}
  (h : ∀ (m : ℕ), (m : WithTop ℕ) ≤ n → DifferentiableOn 𝕜 (iteratedFderivWithin 𝕜 m f s) s) :
  TimesContDiffOn 𝕜 n f s :=
  times_cont_diff_on_of_continuous_on_differentiable_on (fun m hm => (h m hm).ContinuousOn)
    fun m hm => h m (le_of_ltₓ hm)

theorem TimesContDiffOn.continuous_on_iterated_fderiv_within {n : WithTop ℕ} {m : ℕ} (h : TimesContDiffOn 𝕜 n f s)
  (hmn : (m : WithTop ℕ) ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedFderivWithin 𝕜 m f s) s :=
  (h.ftaylor_series_within hs).cont m hmn

theorem TimesContDiffOn.differentiable_on_iterated_fderiv_within {n : WithTop ℕ} {m : ℕ} (h : TimesContDiffOn 𝕜 n f s)
  (hmn : (m : WithTop ℕ) < n) (hs : UniqueDiffOn 𝕜 s) : DifferentiableOn 𝕜 (iteratedFderivWithin 𝕜 m f s) s :=
  fun x hx => ((h.ftaylor_series_within hs).fderivWithin m hmn x hx).DifferentiableWithinAt

theorem times_cont_diff_on_iff_continuous_on_differentiable_on {n : WithTop ℕ} (hs : UniqueDiffOn 𝕜 s) :
  TimesContDiffOn 𝕜 n f s ↔
    (∀ (m : ℕ), (m : WithTop ℕ) ≤ n → ContinuousOn (fun x => iteratedFderivWithin 𝕜 m f s x) s) ∧
      ∀ (m : ℕ), (m : WithTop ℕ) < n → DifferentiableOn 𝕜 (fun x => iteratedFderivWithin 𝕜 m f s x) s :=
  by 
    split 
    ·
      intro h 
      split 
      ·
        intro m hm 
        exact h.continuous_on_iterated_fderiv_within hm hs
      ·
        intro m hm 
        exact h.differentiable_on_iterated_fderiv_within hm hs
    ·
      intro h 
      exact times_cont_diff_on_of_continuous_on_differentiable_on h.1 h.2

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderiv_within`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_fderiv_within
{n : exprℕ()}
(hs : unique_diff_on 𝕜 s) : «expr ↔ »(times_cont_diff_on 𝕜 («expr + »(n, 1) : exprℕ()) f s, «expr ∧ »(differentiable_on 𝕜 f s, times_cont_diff_on 𝕜 n (λ
   y, fderiv_within 𝕜 f s y) s)) :=
begin
  split,
  { assume [binders (H)],
    refine [expr ⟨H.differentiable_on (with_top.coe_le_coe.2 (nat.le_add_left 1 n)), λ x hx, _⟩],
    rcases [expr times_cont_diff_within_at_succ_iff_has_fderiv_within_at.1 (H x hx), "with", "⟨", ident u, ",", ident hu, ",", ident f', ",", ident hff', ",", ident hf', "⟩"],
    rcases [expr mem_nhds_within.1 hu, "with", "⟨", ident o, ",", ident o_open, ",", ident xo, ",", ident ho, "⟩"],
    rw ["[", expr inter_comm, ",", expr insert_eq_of_mem hx, "]"] ["at", ident ho],
    have [] [] [":=", expr hf'.mono ho],
    rw [expr times_cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds (is_open.mem_nhds o_open xo))] ["at", ident this],
    apply [expr this.congr_of_eventually_eq' _ hx],
    have [] [":", expr «expr ∈ »(«expr ∩ »(o, s), «expr𝓝[ ] »(s, x))] [":=", expr mem_nhds_within.2 ⟨o, o_open, xo, subset.refl _⟩],
    rw [expr inter_comm] ["at", ident this],
    apply [expr filter.eventually_eq_of_mem this (λ y hy, _)],
    have [ident A] [":", expr «expr = »(fderiv_within 𝕜 f «expr ∩ »(s, o) y, f' y)] [":=", expr ((hff' y (ho hy)).mono ho).fderiv_within (hs.inter o_open y hy)],
    rwa [expr fderiv_within_inter (is_open.mem_nhds o_open hy.2) (hs y hy.1)] ["at", ident A] },
  { rintros ["⟨", ident hdiff, ",", ident h, "⟩", ident x, ident hx],
    rw ["[", expr times_cont_diff_within_at_succ_iff_has_fderiv_within_at, ",", expr insert_eq_of_mem hx, "]"] [],
    exact [expr ⟨s, self_mem_nhds_within, fderiv_within 𝕜 f s, λ y hy, (hdiff y hy).has_fderiv_within_at, h x hx⟩] }
end

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_fderiv_of_open {n : ℕ} (hs : IsOpen s) :
  TimesContDiffOn 𝕜 (n+1 : ℕ) f s ↔ DifferentiableOn 𝕜 f s ∧ TimesContDiffOn 𝕜 n (fun y => fderiv 𝕜 f y) s :=
  by 
    rw [times_cont_diff_on_succ_iff_fderiv_within hs.unique_diff_on]
    congr 2
    rw [←iff_iff_eq]
    apply times_cont_diff_on_congr 
    intro x hx 
    exact fderiv_within_of_open hs hx

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (expressed with `fderiv_within`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_fderiv_within
(hs : unique_diff_on 𝕜 s) : «expr ↔ »(times_cont_diff_on 𝕜 «expr∞»() f s, «expr ∧ »(differentiable_on 𝕜 f s, times_cont_diff_on 𝕜 «expr∞»() (λ
   y, fderiv_within 𝕜 f s y) s)) :=
begin
  split,
  { assume [binders (h)],
    refine [expr ⟨h.differentiable_on le_top, _⟩],
    apply [expr times_cont_diff_on_top.2 (λ n, ((times_cont_diff_on_succ_iff_fderiv_within hs).1 _).2)],
    exact [expr h.of_le le_top] },
  { assume [binders (h)],
    refine [expr times_cont_diff_on_top.2 (λ n, _)],
    have [ident A] [":", expr «expr ≤ »((n : with_top exprℕ()), «expr∞»())] [":=", expr le_top],
    apply [expr ((times_cont_diff_on_succ_iff_fderiv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le],
    exact [expr with_top.coe_le_coe.2 (nat.le_succ n)] }
end

/-- A function is `C^∞` on an open domain if and only if it is differentiable there, and its
derivative (expressed with `fderiv`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_fderiv_of_open (hs : IsOpen s) :
  TimesContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ TimesContDiffOn 𝕜 ∞ (fun y => fderiv 𝕜 f y) s :=
  by 
    rw [times_cont_diff_on_top_iff_fderiv_within hs.unique_diff_on]
    congr 2
    rw [←iff_iff_eq]
    apply times_cont_diff_on_congr 
    intro x hx 
    exact fderiv_within_of_open hs hx

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem times_cont_diff_on.fderiv_within
{m n : with_top exprℕ()}
(hf : times_cont_diff_on 𝕜 n f s)
(hs : unique_diff_on 𝕜 s)
(hmn : «expr ≤ »(«expr + »(m, 1), n)) : times_cont_diff_on 𝕜 m (λ y, fderiv_within 𝕜 f s y) s :=
begin
  cases [expr m] [],
  { change [expr «expr ≤ »(«expr + »(«expr∞»(), 1), n)] [] ["at", ident hmn],
    have [] [":", expr «expr = »(n, «expr∞»())] [],
    by simpa [] [] [] [] [] ["using", expr hmn],
    rw [expr this] ["at", ident hf],
    exact [expr ((times_cont_diff_on_top_iff_fderiv_within hs).1 hf).2] },
  { change [expr «expr ≤ »((m.succ : with_top exprℕ()), n)] [] ["at", ident hmn],
    exact [expr ((times_cont_diff_on_succ_iff_fderiv_within hs).1 (hf.of_le hmn)).2] }
end

theorem TimesContDiffOn.fderiv_of_open {m n : WithTop ℕ} (hf : TimesContDiffOn 𝕜 n f s) (hs : IsOpen s)
  (hmn : (m+1) ≤ n) : TimesContDiffOn 𝕜 m (fun y => fderiv 𝕜 f y) s :=
  (hf.fderiv_within hs.unique_diff_on hmn).congr fun x hx => (fderiv_within_of_open hs hx).symm

theorem TimesContDiffOn.continuous_on_fderiv_within {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f s)
  (hs : UniqueDiffOn 𝕜 s) (hn : 1 ≤ n) : ContinuousOn (fun x => fderivWithin 𝕜 f s x) s :=
  ((times_cont_diff_on_succ_iff_fderiv_within hs).1 (h.of_le hn)).2.ContinuousOn

theorem TimesContDiffOn.continuous_on_fderiv_of_open {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f s) (hs : IsOpen s)
  (hn : 1 ≤ n) : ContinuousOn (fun x => fderiv 𝕜 f x) s :=
  ((times_cont_diff_on_succ_iff_fderiv_of_open hs).1 (h.of_le hn)).2.ContinuousOn

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem times_cont_diff_on.continuous_on_fderiv_within_apply
{n : with_top exprℕ()}
(h : times_cont_diff_on 𝕜 n f s)
(hs : unique_diff_on 𝕜 s)
(hn : «expr ≤ »(1, n)) : continuous_on (λ
 p : «expr × »(E, E), (fderiv_within 𝕜 f s p.1 : E → F) p.2) (set.prod s univ) :=
begin
  have [ident A] [":", expr continuous (λ
    q : «expr × »(«expr →L[ ] »(E, 𝕜, F), E), q.1 q.2)] [":=", expr is_bounded_bilinear_map_apply.continuous],
  have [ident B] [":", expr continuous_on (λ p : «expr × »(E, E), (fderiv_within 𝕜 f s p.1, p.2)) (set.prod s univ)] [],
  { apply [expr continuous_on.prod _ continuous_snd.continuous_on],
    exact [expr continuous_on.comp (h.continuous_on_fderiv_within hs hn) continuous_fst.continuous_on (prod_subset_preimage_fst _ _)] },
  exact [expr A.comp_continuous_on B]
end

/-! ### Functions with a Taylor series on the whole space -/


/-- `has_ftaylor_series_up_to n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_at` but for higher order derivatives. -/
structure HasFtaylorSeriesUpTo(n : WithTop ℕ)(f : E → F)(p : E → FormalMultilinearSeries 𝕜 E F) : Prop where 
  zero_eq : ∀ x, (p x 0).uncurry0 = f x 
  fderiv : ∀ (m : ℕ) (hm : (m : WithTop ℕ) < n), ∀ x, HasFderivAt (fun y => p y m) (p x m.succ).curryLeft x 
  cont : ∀ (m : ℕ) (hm : (m : WithTop ℕ) ≤ n), Continuous fun x => p x m

theorem HasFtaylorSeriesUpTo.zero_eq' {n : WithTop ℕ} (h : HasFtaylorSeriesUpTo n f p) (x : E) :
  p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) :=
  by 
    rw [←h.zero_eq x]
    symm 
    exact ContinuousMultilinearMap.uncurry0_curry0 _

theorem has_ftaylor_series_up_to_on_univ_iff {n : WithTop ℕ} :
  HasFtaylorSeriesUpToOn n f p univ ↔ HasFtaylorSeriesUpTo n f p :=
  by 
    split 
    ·
      intro H 
      split 
      ·
        exact fun x => H.zero_eq x (mem_univ x)
      ·
        intro m hm x 
        rw [←has_fderiv_within_at_univ]
        exact H.fderiv_within m hm x (mem_univ x)
      ·
        intro m hm 
        rw [continuous_iff_continuous_on_univ]
        exact H.cont m hm
    ·
      intro H 
      split 
      ·
        exact fun x hx => H.zero_eq x
      ·
        intro m hm x hx 
        rw [has_fderiv_within_at_univ]
        exact H.fderiv m hm x
      ·
        intro m hm 
        rw [←continuous_iff_continuous_on_univ]
        exact H.cont m hm

theorem HasFtaylorSeriesUpTo.has_ftaylor_series_up_to_on {n : WithTop ℕ} (h : HasFtaylorSeriesUpTo n f p) (s : Set E) :
  HasFtaylorSeriesUpToOn n f p s :=
  (has_ftaylor_series_up_to_on_univ_iff.2 h).mono (subset_univ _)

theorem HasFtaylorSeriesUpTo.of_le {m n : WithTop ℕ} (h : HasFtaylorSeriesUpTo n f p) (hmn : m ≤ n) :
  HasFtaylorSeriesUpTo m f p :=
  by 
    rw [←has_ftaylor_series_up_to_on_univ_iff] at h⊢
    exact h.of_le hmn

theorem HasFtaylorSeriesUpTo.continuous {n : WithTop ℕ} (h : HasFtaylorSeriesUpTo n f p) : Continuous f :=
  by 
    rw [←has_ftaylor_series_up_to_on_univ_iff] at h 
    rw [continuous_iff_continuous_on_univ]
    exact h.continuous_on

theorem has_ftaylor_series_up_to_zero_iff : HasFtaylorSeriesUpTo 0 f p ↔ Continuous f ∧ ∀ x, (p x 0).uncurry0 = f x :=
  by 
    simp [has_ftaylor_series_up_to_on_univ_iff.symm, continuous_iff_continuous_on_univ,
      has_ftaylor_series_up_to_on_zero_iff]

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem HasFtaylorSeriesUpTo.has_fderiv_at {n : WithTop ℕ} (h : HasFtaylorSeriesUpTo n f p) (hn : 1 ≤ n) (x : E) :
  HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x :=
  by 
    rw [←has_fderiv_within_at_univ]
    exact (has_ftaylor_series_up_to_on_univ_iff.2 h).HasFderivWithinAt hn (mem_univ _)

theorem HasFtaylorSeriesUpTo.differentiable {n : WithTop ℕ} (h : HasFtaylorSeriesUpTo n f p) (hn : 1 ≤ n) :
  Differentiable 𝕜 f :=
  fun x => (h.has_fderiv_at hn x).DifferentiableAt

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_succ_iff_right {n : ℕ} :
  HasFtaylorSeriesUpTo (n+1 : ℕ) f p ↔
    (∀ x, (p x 0).uncurry0 = f x) ∧
      (∀ x, HasFderivAt (fun y => p y 0) (p x 1).curryLeft x) ∧
        HasFtaylorSeriesUpTo n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1)) fun x => (p x).shift :=
  by 
    simp [has_ftaylor_series_up_to_on_succ_iff_right, has_ftaylor_series_up_to_on_univ_iff.symm, -add_commₓ,
      -WithZero.coe_add]

/-! ### Smooth functions at a point -/


variable(𝕜)

/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
-/
def TimesContDiffAt (n : WithTop ℕ) (f : E → F) (x : E) :=
  TimesContDiffWithinAt 𝕜 n f univ x

variable{𝕜}

theorem times_cont_diff_within_at_univ {n : WithTop ℕ} : TimesContDiffWithinAt 𝕜 n f univ x ↔ TimesContDiffAt 𝕜 n f x :=
  Iff.rfl

theorem times_cont_diff_at_top : TimesContDiffAt 𝕜 ∞ f x ↔ ∀ (n : ℕ), TimesContDiffAt 𝕜 n f x :=
  by 
    simp [←times_cont_diff_within_at_univ, times_cont_diff_within_at_top]

theorem TimesContDiffAt.times_cont_diff_within_at {n : WithTop ℕ} (h : TimesContDiffAt 𝕜 n f x) :
  TimesContDiffWithinAt 𝕜 n f s x :=
  h.mono (subset_univ _)

theorem TimesContDiffWithinAt.times_cont_diff_at {n : WithTop ℕ} (h : TimesContDiffWithinAt 𝕜 n f s x) (hx : s ∈ 𝓝 x) :
  TimesContDiffAt 𝕜 n f x :=
  by 
    rwa [TimesContDiffAt, ←times_cont_diff_within_at_inter hx, univ_inter]

theorem TimesContDiffAt.congr_of_eventually_eq {n : WithTop ℕ} (h : TimesContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
  TimesContDiffAt 𝕜 n f₁ x :=
  h.congr_of_eventually_eq'
    (by 
      rwa [nhds_within_univ])
    (mem_univ x)

theorem TimesContDiffAt.of_le {m n : WithTop ℕ} (h : TimesContDiffAt 𝕜 n f x) (hmn : m ≤ n) : TimesContDiffAt 𝕜 m f x :=
  h.of_le hmn

theorem TimesContDiffAt.continuous_at {n : WithTop ℕ} (h : TimesContDiffAt 𝕜 n f x) : ContinuousAt f x :=
  by 
    simpa [continuous_within_at_univ] using h.continuous_within_at

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
theorem TimesContDiffAt.differentiable_at {n : WithTop ℕ} (h : TimesContDiffAt 𝕜 n f x) (hn : 1 ≤ n) :
  DifferentiableAt 𝕜 f x :=
  by 
    simpa [hn, differentiable_within_at_univ] using h.differentiable_within_at

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_at_succ_iff_has_fderiv_at {n : ℕ} :
  TimesContDiffAt 𝕜 (n+1 : ℕ) f x ↔
    ∃ f' : E → E →L[𝕜] F,
      (∃ (u : _)(_ : u ∈ 𝓝 x), ∀ x (_ : x ∈ u), HasFderivAt f (f' x) x) ∧ TimesContDiffAt 𝕜 n f' x :=
  by 
    rw [←times_cont_diff_within_at_univ, times_cont_diff_within_at_succ_iff_has_fderiv_within_at]
    simp only [nhds_within_univ, exists_prop, mem_univ, insert_eq_of_mem]
    split 
    ·
      rintro ⟨u, H, f', h_fderiv, h_times_cont_diff⟩
      rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
      refine' ⟨f', ⟨t, _⟩, h_times_cont_diff.times_cont_diff_at H⟩
      refine' ⟨mem_nhds_iff.mpr ⟨t, subset.rfl, ht, hxt⟩, _⟩
      intro y hyt 
      refine' (h_fderiv y (htu hyt)).HasFderivAt _ 
      exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
    ·
      rintro ⟨f', ⟨u, H, h_fderiv⟩, h_times_cont_diff⟩
      refine' ⟨u, H, f', _, h_times_cont_diff.times_cont_diff_within_at⟩
      intro x hxu 
      exact (h_fderiv x hxu).HasFderivWithinAt

protected theorem TimesContDiffAt.eventually {n : ℕ} (h : TimesContDiffAt 𝕜 n f x) :
  ∀ᶠy in 𝓝 x, TimesContDiffAt 𝕜 n f y :=
  by 
    simpa [nhds_within_univ] using h.eventually

/-! ### Smooth functions -/


variable(𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
def TimesContDiff (n : WithTop ℕ) (f : E → F) :=
  ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpTo n f p

variable{𝕜}

theorem times_cont_diff_on_univ {n : WithTop ℕ} : TimesContDiffOn 𝕜 n f univ ↔ TimesContDiff 𝕜 n f :=
  by 
    split 
    ·
      intro H 
      use ftaylorSeriesWithin 𝕜 f univ 
      rw [←has_ftaylor_series_up_to_on_univ_iff]
      exact H.ftaylor_series_within unique_diff_on_univ
    ·
      rintro ⟨p, hp⟩ x hx m hm 
      exact ⟨univ, Filter.univ_sets _, p, (hp.has_ftaylor_series_up_to_on univ).ofLe hm⟩

theorem times_cont_diff_iff_times_cont_diff_at {n : WithTop ℕ} : TimesContDiff 𝕜 n f ↔ ∀ x, TimesContDiffAt 𝕜 n f x :=
  by 
    simp [←times_cont_diff_on_univ, TimesContDiffOn, TimesContDiffAt]

theorem TimesContDiff.times_cont_diff_at {n : WithTop ℕ} (h : TimesContDiff 𝕜 n f) : TimesContDiffAt 𝕜 n f x :=
  times_cont_diff_iff_times_cont_diff_at.1 h x

theorem TimesContDiff.times_cont_diff_within_at {n : WithTop ℕ} (h : TimesContDiff 𝕜 n f) :
  TimesContDiffWithinAt 𝕜 n f s x :=
  h.times_cont_diff_at.times_cont_diff_within_at

theorem times_cont_diff_top : TimesContDiff 𝕜 ∞ f ↔ ∀ (n : ℕ), TimesContDiff 𝕜 n f :=
  by 
    simp [times_cont_diff_on_univ.symm, times_cont_diff_on_top]

theorem times_cont_diff_all_iff_nat : (∀ n, TimesContDiff 𝕜 n f) ↔ ∀ (n : ℕ), TimesContDiff 𝕜 n f :=
  by 
    simp only [←times_cont_diff_on_univ, times_cont_diff_on_all_iff_nat]

theorem TimesContDiff.times_cont_diff_on {n : WithTop ℕ} (h : TimesContDiff 𝕜 n f) : TimesContDiffOn 𝕜 n f s :=
  (times_cont_diff_on_univ.2 h).mono (subset_univ _)

@[simp]
theorem times_cont_diff_zero : TimesContDiff 𝕜 0 f ↔ Continuous f :=
  by 
    rw [←times_cont_diff_on_univ, continuous_iff_continuous_on_univ]
    exact times_cont_diff_on_zero

theorem times_cont_diff_at_zero : TimesContDiffAt 𝕜 0 f x ↔ ∃ (u : _)(_ : u ∈ 𝓝 x), ContinuousOn f u :=
  by 
    rw [←times_cont_diff_within_at_univ]
    simp [times_cont_diff_within_at_zero, nhds_within_univ]

theorem TimesContDiff.of_le {m n : WithTop ℕ} (h : TimesContDiff 𝕜 n f) (hmn : m ≤ n) : TimesContDiff 𝕜 m f :=
  times_cont_diff_on_univ.1$ (times_cont_diff_on_univ.2 h).ofLe hmn

theorem TimesContDiff.continuous {n : WithTop ℕ} (h : TimesContDiff 𝕜 n f) : Continuous f :=
  times_cont_diff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
theorem TimesContDiff.differentiable {n : WithTop ℕ} (h : TimesContDiff 𝕜 n f) (hn : 1 ≤ n) : Differentiable 𝕜 f :=
  differentiable_on_univ.1$ (times_cont_diff_on_univ.2 h).DifferentiableOn hn

/-! ### Iterated derivative -/


variable(𝕜)

/-- The `n`-th derivative of a function, as a multilinear map, defined inductively. -/
noncomputable def iteratedFderiv (n : ℕ) (f : E → F) : E → «expr [× ]→L[ ] » E n 𝕜 F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.curry0 𝕜 E (f x))
    fun n rec x => ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)

/-- Formal Taylor series associated to a function within a set. -/
def ftaylorSeries (f : E → F) (x : E) : FormalMultilinearSeries 𝕜 E F :=
  fun n => iteratedFderiv 𝕜 n f x

variable{𝕜}

@[simp]
theorem iterated_fderiv_zero_apply (m : Finₓ 0 → E) : (iteratedFderiv 𝕜 0 f x : (Finₓ 0 → E) → F) m = f x :=
  rfl

theorem iterated_fderiv_zero_eq_comp : iteratedFderiv 𝕜 0 f = ((continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f) :=
  rfl

theorem iterated_fderiv_succ_apply_left {n : ℕ} (m : Finₓ (n+1) → E) :
  (iteratedFderiv 𝕜 (n+1) f x : (Finₓ (n+1) → E) → F) m =
    (fderiv 𝕜 (iteratedFderiv 𝕜 n f) x : E → «expr [× ]→L[ ] » E n 𝕜 F) (m 0) (tail m) :=
  rfl

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iterated_fderiv_succ_eq_comp_left
{n : exprℕ()} : «expr = »(iterated_fderiv 𝕜 «expr + »(n, 1) f, «expr ∘ »(continuous_multilinear_curry_left_equiv 𝕜 (λ
   i : fin «expr + »(n, 1), E) F, fderiv 𝕜 (iterated_fderiv 𝕜 n f))) :=
rfl

theorem iterated_fderiv_within_univ {n : ℕ} : iteratedFderivWithin 𝕜 n f univ = iteratedFderiv 𝕜 n f :=
  by 
    induction' n with n IH
    ·
      ext x 
      simp 
    ·
      ext x m 
      rw [iterated_fderiv_succ_apply_left, iterated_fderiv_within_succ_apply_left, IH, fderiv_within_univ]

theorem ftaylor_series_within_univ : ftaylorSeriesWithin 𝕜 f univ = ftaylorSeries 𝕜 f :=
  by 
    ext1 x 
    ext1 n 
    change iteratedFderivWithin 𝕜 n f univ x = iteratedFderiv 𝕜 n f x 
    rw [iterated_fderiv_within_univ]

theorem iterated_fderiv_succ_apply_right {n : ℕ} (m : Finₓ (n+1) → E) :
  (iteratedFderiv 𝕜 (n+1) f x : (Finₓ (n+1) → E) → F) m =
    iteratedFderiv 𝕜 n (fun y => fderiv 𝕜 f y) x (init m) (m (last n)) :=
  by 
    rw [←iterated_fderiv_within_univ, ←iterated_fderiv_within_univ, ←fderiv_within_univ]
    exact iterated_fderiv_within_succ_apply_right unique_diff_on_univ (mem_univ _) _

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iterated_fderiv_succ_eq_comp_right {n : ℕ} :
  iteratedFderiv 𝕜 (n+1) f x =
    (continuousMultilinearCurryRightEquiv' 𝕜 n E F ∘ iteratedFderiv 𝕜 n fun y => fderiv 𝕜 f y) x :=
  by 
    ext m 
    rw [iterated_fderiv_succ_apply_right]
    rfl

@[simp]
theorem iterated_fderiv_one_apply (m : Finₓ 1 → E) :
  (iteratedFderiv 𝕜 1 f x : (Finₓ 1 → E) → F) m = (fderiv 𝕜 f x : E → F) (m 0) :=
  by 
    rw [iterated_fderiv_succ_apply_right, iterated_fderiv_zero_apply]
    rfl

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem times_cont_diff_on_iff_ftaylor_series {n : WithTop ℕ} :
  TimesContDiff 𝕜 n f ↔ HasFtaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) :=
  by 
    split 
    ·
      rw [←times_cont_diff_on_univ, ←has_ftaylor_series_up_to_on_univ_iff, ←ftaylor_series_within_univ]
      exact fun h => TimesContDiffOn.ftaylor_series_within h unique_diff_on_univ
    ·
      intro h 
      exact ⟨ftaylorSeries 𝕜 f, h⟩

theorem times_cont_diff_iff_continuous_differentiable {n : WithTop ℕ} :
  TimesContDiff 𝕜 n f ↔
    (∀ (m : ℕ), (m : WithTop ℕ) ≤ n → Continuous fun x => iteratedFderiv 𝕜 m f x) ∧
      ∀ (m : ℕ), (m : WithTop ℕ) < n → Differentiable 𝕜 fun x => iteratedFderiv 𝕜 m f x :=
  by 
    simp [times_cont_diff_on_univ.symm, continuous_iff_continuous_on_univ, differentiable_on_univ.symm,
      iterated_fderiv_within_univ, times_cont_diff_on_iff_continuous_on_differentiable_on unique_diff_on_univ]

theorem times_cont_diff_of_differentiable_iterated_fderiv {n : WithTop ℕ}
  (h : ∀ (m : ℕ), (m : WithTop ℕ) ≤ n → Differentiable 𝕜 (iteratedFderiv 𝕜 m f)) : TimesContDiff 𝕜 n f :=
  times_cont_diff_iff_continuous_differentiable.2 ⟨fun m hm => (h m hm).Continuous, fun m hm => h m (le_of_ltₓ hm)⟩

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if
it is differentiable there, and its derivative is `C^n`. -/
theorem times_cont_diff_succ_iff_fderiv {n : ℕ} :
  TimesContDiff 𝕜 (n+1 : ℕ) f ↔ Differentiable 𝕜 f ∧ TimesContDiff 𝕜 n fun y => fderiv 𝕜 f y :=
  by 
    simp [times_cont_diff_on_univ.symm, differentiable_on_univ.symm, fderiv_within_univ.symm, -fderiv_within_univ,
      times_cont_diff_on_succ_iff_fderiv_within unique_diff_on_univ, -WithZero.coe_add, -add_commₓ]

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^∞`. -/
theorem times_cont_diff_top_iff_fderiv :
  TimesContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ TimesContDiff 𝕜 ∞ fun y => fderiv 𝕜 f y :=
  by 
    simp [times_cont_diff_on_univ.symm, differentiable_on_univ.symm, fderiv_within_univ.symm, -fderiv_within_univ]
    rw [times_cont_diff_on_top_iff_fderiv_within unique_diff_on_univ]

theorem TimesContDiff.continuous_fderiv {n : WithTop ℕ} (h : TimesContDiff 𝕜 n f) (hn : 1 ≤ n) :
  Continuous fun x => fderiv 𝕜 f x :=
  (times_cont_diff_succ_iff_fderiv.1 (h.of_le hn)).2.Continuous

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem times_cont_diff.continuous_fderiv_apply
{n : with_top exprℕ()}
(h : times_cont_diff 𝕜 n f)
(hn : «expr ≤ »(1, n)) : continuous (λ p : «expr × »(E, E), (fderiv 𝕜 f p.1 : E → F) p.2) :=
begin
  have [ident A] [":", expr continuous (λ
    q : «expr × »(«expr →L[ ] »(E, 𝕜, F), E), q.1 q.2)] [":=", expr is_bounded_bilinear_map_apply.continuous],
  have [ident B] [":", expr continuous (λ p : «expr × »(E, E), (fderiv 𝕜 f p.1, p.2))] [],
  { apply [expr continuous.prod_mk _ continuous_snd],
    exact [expr continuous.comp (h.continuous_fderiv hn) continuous_fst] },
  exact [expr A.comp B]
end

/-! ### Constants -/


-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem iterated_fderiv_within_zero_fun {n : exprℕ()} : «expr = »(iterated_fderiv 𝕜 n (λ x : E, (0 : F)), 0) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] [],
  { ext [] [ident m] [],
    simp [] [] [] [] [] [] },
  { ext [] [ident x, ident m] [],
    rw ["[", expr iterated_fderiv_succ_apply_left, ",", expr IH, "]"] [],
    change [expr «expr = »((fderiv 𝕜 (λ
       x : E, (0 : «expr [× ]→L[ ] »(E, n, 𝕜, F))) x : E → «expr [× ]→L[ ] »(E, n, 𝕜, F)) (m 0) (tail m), _)] [] [],
    rw [expr fderiv_const] [],
    refl }
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff_zero_fun {n : with_top exprℕ()} : times_cont_diff 𝕜 n (λ x : E, (0 : F)) :=
begin
  apply [expr times_cont_diff_of_differentiable_iterated_fderiv (λ m hm, _)],
  rw [expr iterated_fderiv_within_zero_fun] [],
  apply [expr differentiable_const (0 : «expr [× ]→L[ ] »(E, m, 𝕜, F))]
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
Constants are `C^∞`.
-/ theorem times_cont_diff_const {n : with_top exprℕ()} {c : F} : times_cont_diff 𝕜 n (λ x : E, c) :=
begin
  suffices [ident h] [":", expr times_cont_diff 𝕜 «expr∞»() (λ x : E, c)],
  by exact [expr h.of_le le_top],
  rw [expr times_cont_diff_top_iff_fderiv] [],
  refine [expr ⟨differentiable_const c, _⟩],
  rw [expr fderiv_const] [],
  exact [expr times_cont_diff_zero_fun]
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff_on_const {n : with_top exprℕ()} {c : F} {s : set E} : times_cont_diff_on 𝕜 n (λ x : E, c) s :=
times_cont_diff_const.times_cont_diff_on

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff_at_const {n : with_top exprℕ()} {c : F} : times_cont_diff_at 𝕜 n (λ x : E, c) x :=
times_cont_diff_const.times_cont_diff_at

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff_within_at_const
{n : with_top exprℕ()}
{c : F} : times_cont_diff_within_at 𝕜 n (λ x : E, c) s x :=
times_cont_diff_at_const.times_cont_diff_within_at

@[nontriviality]
theorem times_cont_diff_of_subsingleton [Subsingleton F] {n : WithTop ℕ} : TimesContDiff 𝕜 n f :=
  by 
    rw [Subsingleton.elimₓ f fun _ => 0]
    exact times_cont_diff_const

@[nontriviality]
theorem times_cont_diff_at_of_subsingleton [Subsingleton F] {n : WithTop ℕ} : TimesContDiffAt 𝕜 n f x :=
  by 
    rw [Subsingleton.elimₓ f fun _ => 0]
    exact times_cont_diff_at_const

@[nontriviality]
theorem times_cont_diff_within_at_of_subsingleton [Subsingleton F] {n : WithTop ℕ} : TimesContDiffWithinAt 𝕜 n f s x :=
  by 
    rw [Subsingleton.elimₓ f fun _ => 0]
    exact times_cont_diff_within_at_const

@[nontriviality]
theorem times_cont_diff_on_of_subsingleton [Subsingleton F] {n : WithTop ℕ} : TimesContDiffOn 𝕜 n f s :=
  by 
    rw [Subsingleton.elimₓ f fun _ => 0]
    exact times_cont_diff_on_const

/-! ### Linear functions -/


/--
Unbundled bounded linear functions are `C^∞`.
-/
theorem IsBoundedLinearMap.times_cont_diff {n : WithTop ℕ} (hf : IsBoundedLinearMap 𝕜 f) : TimesContDiff 𝕜 n f :=
  by 
    suffices h : TimesContDiff 𝕜 ∞ f
    ·
      exact h.of_le le_top 
    rw [times_cont_diff_top_iff_fderiv]
    refine' ⟨hf.differentiable, _⟩
    simp [hf.fderiv]
    exact times_cont_diff_const

theorem ContinuousLinearMap.times_cont_diff {n : WithTop ℕ} (f : E →L[𝕜] F) : TimesContDiff 𝕜 n f :=
  f.is_bounded_linear_map.times_cont_diff

theorem ContinuousLinearEquiv.times_cont_diff {n : WithTop ℕ} (f : E ≃L[𝕜] F) : TimesContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).TimesContDiff

theorem LinearIsometry.times_cont_diff {n : WithTop ℕ} (f : E →ₗᵢ[𝕜] F) : TimesContDiff 𝕜 n f :=
  f.to_continuous_linear_map.times_cont_diff

theorem LinearIsometryEquiv.times_cont_diff {n : WithTop ℕ} (f : E ≃ₗᵢ[𝕜] F) : TimesContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).TimesContDiff

/--
The first projection in a product is `C^∞`.
-/
theorem times_cont_diff_fst {n : WithTop ℕ} : TimesContDiff 𝕜 n (Prod.fst : E × F → E) :=
  IsBoundedLinearMap.times_cont_diff IsBoundedLinearMap.fst

/--
The first projection on a domain in a product is `C^∞`.
-/
theorem times_cont_diff_on_fst {s : Set (E × F)} {n : WithTop ℕ} : TimesContDiffOn 𝕜 n (Prod.fst : E × F → E) s :=
  TimesContDiff.times_cont_diff_on times_cont_diff_fst

/--
The first projection at a point in a product is `C^∞`.
-/
theorem times_cont_diff_at_fst {p : E × F} {n : WithTop ℕ} : TimesContDiffAt 𝕜 n (Prod.fst : E × F → E) p :=
  times_cont_diff_fst.TimesContDiffAt

/--
The first projection within a domain at a point in a product is `C^∞`.
-/
theorem times_cont_diff_within_at_fst {s : Set (E × F)} {p : E × F} {n : WithTop ℕ} :
  TimesContDiffWithinAt 𝕜 n (Prod.fst : E × F → E) s p :=
  times_cont_diff_fst.TimesContDiffWithinAt

/--
The second projection in a product is `C^∞`.
-/
theorem times_cont_diff_snd {n : WithTop ℕ} : TimesContDiff 𝕜 n (Prod.snd : E × F → F) :=
  IsBoundedLinearMap.times_cont_diff IsBoundedLinearMap.snd

/--
The second projection on a domain in a product is `C^∞`.
-/
theorem times_cont_diff_on_snd {s : Set (E × F)} {n : WithTop ℕ} : TimesContDiffOn 𝕜 n (Prod.snd : E × F → F) s :=
  TimesContDiff.times_cont_diff_on times_cont_diff_snd

/--
The second projection at a point in a product is `C^∞`.
-/
theorem times_cont_diff_at_snd {p : E × F} {n : WithTop ℕ} : TimesContDiffAt 𝕜 n (Prod.snd : E × F → F) p :=
  times_cont_diff_snd.TimesContDiffAt

/--
The second projection within a domain at a point in a product is `C^∞`.
-/
theorem times_cont_diff_within_at_snd {s : Set (E × F)} {p : E × F} {n : WithTop ℕ} :
  TimesContDiffWithinAt 𝕜 n (Prod.snd : E × F → F) s p :=
  times_cont_diff_snd.TimesContDiffWithinAt

/--
The natural equivalence `(E × F) × G ≃ E × (F × G)` is smooth.

Warning: if you think you need this lemma, it is likely that you can simplify your proof by
reformulating the lemma that you're applying next using the tips in
Note [continuity lemma statement]
-/
theorem times_cont_diff_prod_assoc : TimesContDiff 𝕜 ⊤$ Equiv.prodAssoc E F G :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).TimesContDiff

/--
The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `times_cont_diff_prod_assoc`
-/
theorem times_cont_diff_prod_assoc_symm : TimesContDiff 𝕜 ⊤$ (Equiv.prodAssoc E F G).symm :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.TimesContDiff

/--
The identity is `C^∞`.
-/
theorem times_cont_diff_id {n : WithTop ℕ} : TimesContDiff 𝕜 n (id : E → E) :=
  IsBoundedLinearMap.id.TimesContDiff

theorem times_cont_diff_within_at_id {n : WithTop ℕ} {s x} : TimesContDiffWithinAt 𝕜 n (id : E → E) s x :=
  times_cont_diff_id.TimesContDiffWithinAt

theorem times_cont_diff_at_id {n : WithTop ℕ} {x} : TimesContDiffAt 𝕜 n (id : E → E) x :=
  times_cont_diff_id.TimesContDiffAt

theorem times_cont_diff_on_id {n : WithTop ℕ} {s} : TimesContDiffOn 𝕜 n (id : E → E) s :=
  times_cont_diff_id.TimesContDiffOn

/--
Bilinear functions are `C^∞`.
-/
theorem IsBoundedBilinearMap.times_cont_diff {n : WithTop ℕ} (hb : IsBoundedBilinearMap 𝕜 b) : TimesContDiff 𝕜 n b :=
  by 
    suffices h : TimesContDiff 𝕜 ∞ b
    ·
      exact h.of_le le_top 
    rw [times_cont_diff_top_iff_fderiv]
    refine' ⟨hb.differentiable, _⟩
    simp [hb.fderiv]
    exact hb.is_bounded_linear_map_deriv.times_cont_diff

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
theorem HasFtaylorSeriesUpToOn.continuous_linear_map_comp {n : WithTop ℕ} (g : F →L[𝕜] G)
  (hf : HasFtaylorSeriesUpToOn n f p s) :
  HasFtaylorSeriesUpToOn n (g ∘ f) (fun x k => g.comp_continuous_multilinear_map (p x k)) s :=
  by 
    set L : ∀ (m : ℕ), «expr [× ]→L[ ] » E m 𝕜 F →L[𝕜] «expr [× ]→L[ ] » E m 𝕜 G :=
      fun m => ContinuousLinearMap.compContinuousMultilinearMapL g 
    split 
    ·
      exact fun x hx => congr_argₓ g (hf.zero_eq x hx)
    ·
      intro m hm x hx 
      convert (L m).HasFderivAt.comp_has_fderiv_within_at x (hf.fderiv_within m hm x hx)
    ·
      intro m hm 
      convert (L m).Continuous.comp_continuous_on (hf.cont m hm)

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem TimesContDiffWithinAt.continuous_linear_map_comp {n : WithTop ℕ} (g : F →L[𝕜] G)
  (hf : TimesContDiffWithinAt 𝕜 n f s x) : TimesContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  by 
    intro m hm 
    rcases hf m hm with ⟨u, hu, p, hp⟩
    exact ⟨u, hu, _, hp.continuous_linear_map_comp g⟩

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem TimesContDiffAt.continuous_linear_map_comp {n : WithTop ℕ} (g : F →L[𝕜] G) (hf : TimesContDiffAt 𝕜 n f x) :
  TimesContDiffAt 𝕜 n (g ∘ f) x :=
  TimesContDiffWithinAt.continuous_linear_map_comp g hf

/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
theorem TimesContDiffOn.continuous_linear_map_comp {n : WithTop ℕ} (g : F →L[𝕜] G) (hf : TimesContDiffOn 𝕜 n f s) :
  TimesContDiffOn 𝕜 n (g ∘ f) s :=
  fun x hx => (hf x hx).continuous_linear_map_comp g

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
theorem TimesContDiff.continuous_linear_map_comp {n : WithTop ℕ} {f : E → F} (g : F →L[𝕜] G)
  (hf : TimesContDiff 𝕜 n f) : TimesContDiff 𝕜 n fun x => g (f x) :=
  times_cont_diff_on_univ.1$ TimesContDiffOn.continuous_linear_map_comp _ (times_cont_diff_on_univ.2 hf)

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.comp_times_cont_diff_within_at_iff {n : WithTop ℕ} (e : F ≃L[𝕜] G) :
  TimesContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ TimesContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H =>
      by 
        simpa only [· ∘ ·, e.symm.coe_coe, e.symm_apply_apply] using H.continuous_linear_map_comp (e.symm : G →L[𝕜] F),
    fun H => H.continuous_linear_map_comp (e : F →L[𝕜] G)⟩

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.comp_times_cont_diff_on_iff {n : WithTop ℕ} (e : F ≃L[𝕜] G) :
  TimesContDiffOn 𝕜 n (e ∘ f) s ↔ TimesContDiffOn 𝕜 n f s :=
  by 
    simp [TimesContDiffOn, e.comp_times_cont_diff_within_at_iff]

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term is given by `p k (g v₁, ..., g vₖ)` . -/
theorem has_ftaylor_series_up_to_on.comp_continuous_linear_map
{n : with_top exprℕ()}
(hf : has_ftaylor_series_up_to_on n f p s)
(g : «expr →L[ ] »(G, 𝕜, E)) : has_ftaylor_series_up_to_on n «expr ∘ »(f, g) (λ
 x k, (p (g x) k).comp_continuous_linear_map (λ _, g)) «expr ⁻¹' »(g, s) :=
begin
  let [ident A] [":", expr ∀
   m : exprℕ(), «expr [× ]→L[ ] »(E, m, 𝕜, F) → «expr [× ]→L[ ] »(G, m, 𝕜, F)] [":=", expr λ
   m h, h.comp_continuous_linear_map (λ _, g)],
  have [ident hA] [":", expr ∀
   m, is_bounded_linear_map 𝕜 (A m)] [":=", expr λ m, is_bounded_linear_map_continuous_multilinear_map_comp_linear g],
  split,
  { assume [binders (x hx)],
    simp [] [] ["only"] ["[", expr (hf.zero_eq (g x) hx).symm, ",", expr function.comp_app, "]"] [] [],
    change [expr «expr = »(p (g x) 0 (λ i : fin 0, g 0), p (g x) 0 0)] [] [],
    rw [expr continuous_linear_map.map_zero] [],
    refl },
  { assume [binders (m hm x hx)],
    convert [] [expr (hA m).has_fderiv_at.comp_has_fderiv_within_at x ((hf.fderiv_within m hm (g x) hx).comp x g.has_fderiv_within_at (subset.refl _))] [],
    ext [] [ident y, ident v] [],
    change [expr «expr = »(p (g x) (nat.succ m) «expr ∘ »(g, cons y v), p (g x) m.succ (cons (g y) «expr ∘ »(g, v)))] [] [],
    rw [expr comp_cons] [] },
  { assume [binders (m hm)],
    exact [expr (hA m).continuous.comp_continuous_on ((hf.cont m hm).comp g.continuous.continuous_on (subset.refl _))] }
end

/-- Composition by continuous linear maps on the right preserves `C^n` functions at a point on
a domain. -/
theorem TimesContDiffWithinAt.comp_continuous_linear_map {n : WithTop ℕ} {x : G} (g : G →L[𝕜] E)
  (hf : TimesContDiffWithinAt 𝕜 n f s (g x)) : TimesContDiffWithinAt 𝕜 n (f ∘ g) (g ⁻¹' s) x :=
  by 
    intro m hm 
    rcases hf m hm with ⟨u, hu, p, hp⟩
    refine' ⟨g ⁻¹' u, _, _, hp.comp_continuous_linear_map g⟩
    apply ContinuousWithinAt.preimage_mem_nhds_within'
    ·
      exact g.continuous.continuous_within_at
    ·
      apply nhds_within_mono (g x) _ hu 
      rw [image_insert_eq]
      exact insert_subset_insert (image_preimage_subset g s)

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
theorem TimesContDiffOn.comp_continuous_linear_map {n : WithTop ℕ} (hf : TimesContDiffOn 𝕜 n f s) (g : G →L[𝕜] E) :
  TimesContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s) :=
  fun x hx => (hf (g x) hx).compContinuousLinearMap g

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
theorem TimesContDiff.comp_continuous_linear_map {n : WithTop ℕ} {f : E → F} {g : G →L[𝕜] E}
  (hf : TimesContDiff 𝕜 n f) : TimesContDiff 𝕜 n (f ∘ g) :=
  times_cont_diff_on_univ.1$ TimesContDiffOn.comp_continuous_linear_map (times_cont_diff_on_univ.2 hf) _

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point in a domain. -/
theorem ContinuousLinearEquiv.times_cont_diff_within_at_comp_iff {n : WithTop ℕ} (e : G ≃L[𝕜] E) :
  TimesContDiffWithinAt 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔ TimesContDiffWithinAt 𝕜 n f s x :=
  by 
    split 
    ·
      intro H 
      simpa [←preimage_comp, · ∘ ·] using H.comp_continuous_linear_map (e.symm : E →L[𝕜] G)
    ·
      intro H 
      rw [←e.apply_symm_apply x, ←e.coe_coe] at H 
      exact H.comp_continuous_linear_map _

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
theorem continuous_linear_equiv.times_cont_diff_on_comp_iff
{n : with_top exprℕ()}
(e : «expr ≃L[ ] »(G, 𝕜, E)) : «expr ↔ »(times_cont_diff_on 𝕜 n «expr ∘ »(f, e) «expr ⁻¹' »(e, s), times_cont_diff_on 𝕜 n f s) :=
begin
  refine [expr ⟨λ H, _, λ H, H.comp_continuous_linear_map (e : «expr →L[ ] »(G, 𝕜, E))⟩],
  have [ident A] [":", expr «expr = »(f, «expr ∘ »(«expr ∘ »(f, e), e.symm))] [],
  by { ext [] [ident y] [],
    simp [] [] ["only"] ["[", expr function.comp_app, "]"] [] [],
    rw [expr e.apply_symm_apply y] [] },
  have [ident B] [":", expr «expr = »(«expr ⁻¹' »(e.symm, «expr ⁻¹' »(e, s)), s)] [],
  by { rw ["[", "<-", expr preimage_comp, ",", expr e.self_comp_symm, "]"] [],
    refl },
  rw ["[", expr A, ",", "<-", expr B, "]"] [],
  exact [expr H.comp_continuous_linear_map (e.symm : «expr →L[ ] »(E, 𝕜, G))]
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the cartesian
product of `f` and `g` admits the cartesian product of `p` and `q` as a Taylor series. -/
theorem has_ftaylor_series_up_to_on.prod
{n : with_top exprℕ()}
(hf : has_ftaylor_series_up_to_on n f p s)
{g : E → G}
{q : E → formal_multilinear_series 𝕜 E G}
(hg : has_ftaylor_series_up_to_on n g q s) : has_ftaylor_series_up_to_on n (λ
 y, (f y, g y)) (λ y k, (p y k).prod (q y k)) s :=
begin
  set [] [ident L] [] [":="] [expr λ m, continuous_multilinear_map.prodL 𝕜 (λ i : fin m, E) F G] [],
  split,
  { assume [binders (x hx)],
    rw ["[", "<-", expr hf.zero_eq x hx, ",", "<-", expr hg.zero_eq x hx, "]"] [],
    refl },
  { assume [binders (m hm x hx)],
    convert [] [expr (L m).has_fderiv_at.comp_has_fderiv_within_at x ((hf.fderiv_within m hm x hx).prod (hg.fderiv_within m hm x hx))] [] },
  { assume [binders (m hm)],
    exact [expr (L m).continuous.comp_continuous_on ((hf.cont m hm).prod (hg.cont m hm))] }
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
theorem times_cont_diff_within_at.prod
{n : with_top exprℕ()}
{s : set E}
{f : E → F}
{g : E → G}
(hf : times_cont_diff_within_at 𝕜 n f s x)
(hg : times_cont_diff_within_at 𝕜 n g s x) : times_cont_diff_within_at 𝕜 n (λ x : E, (f x, g x)) s x :=
begin
  assume [binders (m hm)],
  rcases [expr hf m hm, "with", "⟨", ident u, ",", ident hu, ",", ident p, ",", ident hp, "⟩"],
  rcases [expr hg m hm, "with", "⟨", ident v, ",", ident hv, ",", ident q, ",", ident hq, "⟩"],
  exact [expr ⟨«expr ∩ »(u, v), filter.inter_mem hu hv, _, (hp.mono (inter_subset_left u v)).prod (hq.mono (inter_subset_right u v))⟩]
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The cartesian product of `C^n` functions on domains is `C^n`. -/
theorem times_cont_diff_on.prod
{n : with_top exprℕ()}
{s : set E}
{f : E → F}
{g : E → G}
(hf : times_cont_diff_on 𝕜 n f s)
(hg : times_cont_diff_on 𝕜 n g s) : times_cont_diff_on 𝕜 n (λ x : E, (f x, g x)) s :=
λ x hx, (hf x hx).prod (hg x hx)

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The cartesian product of `C^n` functions at a point is `C^n`. -/
theorem times_cont_diff_at.prod
{n : with_top exprℕ()}
{f : E → F}
{g : E → G}
(hf : times_cont_diff_at 𝕜 n f x)
(hg : times_cont_diff_at 𝕜 n g x) : times_cont_diff_at 𝕜 n (λ x : E, (f x, g x)) x :=
«expr $ »(times_cont_diff_within_at_univ.1, times_cont_diff_within_at.prod (times_cont_diff_within_at_univ.2 hf) (times_cont_diff_within_at_univ.2 hg))

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
The cartesian product of `C^n` functions is `C^n`.
-/
theorem times_cont_diff.prod
{n : with_top exprℕ()}
{f : E → F}
{g : E → G}
(hf : times_cont_diff 𝕜 n f)
(hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n (λ x : E, (f x, g x)) :=
«expr $ »(times_cont_diff_on_univ.1, times_cont_diff_on.prod (times_cont_diff_on_univ.2 hf) (times_cont_diff_on_univ.2 hg))

/-!
### Smoothness of functions `f : E → Π i, F' i`
-/


section Pi

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
      NormedSpace 𝕜
        (F'
          i)]{φ :
    ∀ i,
      E →
        F'
          i}{p' :
    ∀ i,
      E →
        FormalMultilinearSeries 𝕜 E
          (F' i)}{Φ : E → ∀ i, F' i}{P' : E → FormalMultilinearSeries 𝕜 E (∀ i, F' i)}{n : WithTop ℕ}

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_ftaylor_series_up_to_on_pi : «expr ↔ »(has_ftaylor_series_up_to_on n (λ
  x
  i, φ i x) (λ
  x m, continuous_multilinear_map.pi (λ i, p' i x m)) s, ∀ i, has_ftaylor_series_up_to_on n (φ i) (p' i) s) :=
begin
  set [] [ident pr] [] [":="] [expr @continuous_linear_map.proj 𝕜 _ ι F' _ _ _] [],
  letI [] [":", expr ∀
   (m : exprℕ())
   (i : ι), normed_space 𝕜 «expr [× ]→L[ ] »(E, m, 𝕜, F' i)] [":=", expr λ m i, infer_instance],
  set [] [ident L] [":", expr ∀
   m : exprℕ(), «expr ≃ₗᵢ[ ] »(∀
    i, «expr [× ]→L[ ] »(E, m, 𝕜, F' i), 𝕜, «expr [× ]→L[ ] »(E, m, 𝕜, ∀
     i, F' i))] [":="] [expr λ m, continuous_multilinear_map.piₗᵢ _ _] [],
  refine [expr ⟨λ h i, _, λ h, ⟨λ x hx, _, _, _⟩⟩],
  { convert [] [expr h.continuous_linear_map_comp (pr i)] [],
    ext [] [] [],
    refl },
  { ext1 [] [ident i],
    exact [expr (h i).zero_eq x hx] },
  { intros [ident m, ident hm, ident x, ident hx],
    have [] [] [":=", expr has_fderiv_within_at_pi.2 (λ i, (h i).fderiv_within m hm x hx)],
    convert [] [expr (L m).has_fderiv_at.comp_has_fderiv_within_at x this] [] },
  { intros [ident m, ident hm],
    have [] [] [":=", expr continuous_on_pi.2 (λ i, (h i).cont m hm)],
    convert [] [expr (L m).continuous.comp_continuous_on this] [] }
end

@[simp]
theorem has_ftaylor_series_up_to_on_pi' :
  HasFtaylorSeriesUpToOn n Φ P' s ↔
    ∀ i,
      HasFtaylorSeriesUpToOn n (fun x => Φ x i)
        (fun x m => (@ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap (P' x m)) s :=
  by 
    convert has_ftaylor_series_up_to_on_pi 
    ext 
    rfl

theorem times_cont_diff_within_at_pi :
  TimesContDiffWithinAt 𝕜 n Φ s x ↔ ∀ i, TimesContDiffWithinAt 𝕜 n (fun x => Φ x i) s x :=
  by 
    set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ 
    refine' ⟨fun h i => h.continuous_linear_map_comp (pr i), fun h m hm => _⟩
    choose u hux p hp using fun i => h i m hm 
    exact ⟨⋂i, u i, Filter.Inter_mem.2 hux, _, has_ftaylor_series_up_to_on_pi.2 fun i => (hp i).mono$ Inter_subset _ _⟩

theorem times_cont_diff_on_pi : TimesContDiffOn 𝕜 n Φ s ↔ ∀ i, TimesContDiffOn 𝕜 n (fun x => Φ x i) s :=
  ⟨fun h i x hx => times_cont_diff_within_at_pi.1 (h x hx) _,
    fun h x hx => times_cont_diff_within_at_pi.2 fun i => h i x hx⟩

theorem times_cont_diff_at_pi : TimesContDiffAt 𝕜 n Φ x ↔ ∀ i, TimesContDiffAt 𝕜 n (fun x => Φ x i) x :=
  times_cont_diff_within_at_pi

theorem times_cont_diff_pi : TimesContDiff 𝕜 n Φ ↔ ∀ i, TimesContDiff 𝕜 n fun x => Φ x i :=
  by 
    simp only [←times_cont_diff_on_univ, times_cont_diff_on_pi]

end Pi

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to prove it would be to write
the `n`-th derivative of the composition (this is Faà di Bruno's formula) and check its continuity,
but this is very painful. Instead, we go for a simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There is a subtlety in this argument: we apply the inductive assumption to functions on other Banach
spaces. In maths, one would say: prove by induction over `n` that, for all `C^n` maps between all
pairs of Banach spaces, their composition is `C^n`. In Lean, this is fine as long as the spaces
stay in the same universe. This is not the case in the above argument: if `E` lives in universe `u`
and `F` lives in universe `v`, then linear maps from `E` to `F` (to which the derivative of `f`
belongs) is in universe `max u v`. If one could quantify over finitely many universes, the above
proof would work fine, but this is not the case. One could still write the proof considering spaces
in any universe in `u, v, w, max u v, max v w, max u v w`, but it would be extremely tedious and
lead to a lot of duplication. Instead, we formulate the above proof when all spaces live in the same
universe (where everything is fine), and then we deduce the general result by lifting all our spaces
to a common universe. We use the trick that any space `H` is isomorphic through a continuous linear
equiv to `continuous_multilinear_map (λ (i : fin 0), E × F × G) H` to change the universe level,
and then argue that composing with such a linear equiv does not change the fact of being `C^n`,
which we have already proved previously.
-/


-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Auxiliary lemma proving that the composition of `C^n` functions on domains is `C^n` when all
spaces live in the same universe. Use instead `times_cont_diff_on.comp` which removes the universe
assumption (but is deduced from this one). -/
private
theorem times_cont_diff_on.comp_same_univ
{Eu : Type u}
[normed_group Eu]
[normed_space 𝕜 Eu]
{Fu : Type u}
[normed_group Fu]
[normed_space 𝕜 Fu]
{Gu : Type u}
[normed_group Gu]
[normed_space 𝕜 Gu]
{n : with_top exprℕ()}
{s : set Eu}
{t : set Fu}
{g : Fu → Gu}
{f : Eu → Fu}
(hg : times_cont_diff_on 𝕜 n g t)
(hf : times_cont_diff_on 𝕜 n f s)
(st : «expr ⊆ »(s, «expr ⁻¹' »(f, t))) : times_cont_diff_on 𝕜 n «expr ∘ »(g, f) s :=
begin
  unfreezingI { induction [expr n] ["using", ident with_top.nat_induction] ["with", ident n, ident IH, ident Itop] ["generalizing", ident Eu, ident Fu, ident Gu] },
  { rw [expr times_cont_diff_on_zero] ["at", ident hf, ident hg, "⊢"],
    exact [expr continuous_on.comp hg hf st] },
  { rw [expr times_cont_diff_on_succ_iff_has_fderiv_within_at] ["at", ident hg, "⊢"],
    assume [binders (x hx)],
    rcases [expr times_cont_diff_on_succ_iff_has_fderiv_within_at.1 hf x hx, "with", "⟨", ident u, ",", ident hu, ",", ident f', ",", ident hf', ",", ident f'_diff, "⟩"],
    rcases [expr hg (f x) (st hx), "with", "⟨", ident v, ",", ident hv, ",", ident g', ",", ident hg', ",", ident g'_diff, "⟩"],
    rw [expr insert_eq_of_mem hx] ["at", ident hu, "⊢"],
    have [ident xu] [":", expr «expr ∈ »(x, u)] [":=", expr mem_of_mem_nhds_within hx hu],
    let [ident w] [] [":=", expr «expr ∩ »(s, «expr ∩ »(u, «expr ⁻¹' »(f, v)))],
    have [ident wv] [":", expr «expr ⊆ »(w, «expr ⁻¹' »(f, v))] [":=", expr λ y hy, hy.2.2],
    have [ident wu] [":", expr «expr ⊆ »(w, u)] [":=", expr λ y hy, hy.2.1],
    have [ident ws] [":", expr «expr ⊆ »(w, s)] [":=", expr λ y hy, hy.1],
    refine [expr ⟨w, _, λ y, (g' (f y)).comp (f' y), _, _⟩],
    show [expr «expr ∈ »(w, «expr𝓝[ ] »(s, x))],
    { apply [expr filter.inter_mem self_mem_nhds_within],
      apply [expr filter.inter_mem hu],
      apply [expr continuous_within_at.preimage_mem_nhds_within'],
      { rw ["<-", expr continuous_within_at_inter' hu] [],
        exact [expr (hf' x xu).differentiable_within_at.continuous_within_at.mono (inter_subset_right _ _)] },
      { apply [expr nhds_within_mono _ _ hv],
        exact [expr subset.trans (image_subset_iff.mpr st) (subset_insert (f x) t)] } },
    show [expr ∀ y «expr ∈ » w, has_fderiv_within_at «expr ∘ »(g, f) ((g' (f y)).comp (f' y)) w y],
    { rintros [ident y, "⟨", ident ys, ",", ident yu, ",", ident yv, "⟩"],
      exact [expr (hg' (f y) yv).comp y ((hf' y yu).mono wu) wv] },
    show [expr times_cont_diff_on 𝕜 n (λ y, (g' (f y)).comp (f' y)) w],
    { have [ident A] [":", expr times_cont_diff_on 𝕜 n (λ
        y, g' (f y)) w] [":=", expr IH g'_diff ((hf.of_le (with_top.coe_le_coe.2 (nat.le_succ n))).mono ws) wv],
      have [ident B] [":", expr times_cont_diff_on 𝕜 n f' w] [":=", expr f'_diff.mono wu],
      have [ident C] [":", expr times_cont_diff_on 𝕜 n (λ
        y, (f' y, g' (f y))) w] [":=", expr times_cont_diff_on.prod B A],
      have [ident D] [":", expr times_cont_diff_on 𝕜 n (λ
        p : «expr × »(«expr →L[ ] »(Eu, 𝕜, Fu), «expr →L[ ] »(Fu, 𝕜, Gu)), p.2.comp p.1) univ] [":=", expr is_bounded_bilinear_map_comp.times_cont_diff.times_cont_diff_on],
      exact [expr IH D C (subset_univ _)] } },
  { rw [expr times_cont_diff_on_top] ["at", ident hf, ident hg, "⊢"],
    assume [binders (n)],
    apply [expr Itop n (hg n) (hf n) st] }
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem times_cont_diff_on.comp
{n : with_top exprℕ()}
{s : set E}
{t : set F}
{g : F → G}
{f : E → F}
(hg : times_cont_diff_on 𝕜 n g t)
(hf : times_cont_diff_on 𝕜 n f s)
(st : «expr ⊆ »(s, «expr ⁻¹' »(f, t))) : times_cont_diff_on 𝕜 n «expr ∘ »(g, f) s :=
begin
  let [ident Eu] [] [":=", expr continuous_multilinear_map 𝕜 (λ i : fin 0, «expr × »(E, «expr × »(F, G))) E],
  letI [] [":", expr normed_group Eu] [":=", expr by apply_instance],
  letI [] [":", expr normed_space 𝕜 Eu] [":=", expr by apply_instance],
  let [ident Fu] [] [":=", expr continuous_multilinear_map 𝕜 (λ i : fin 0, «expr × »(E, «expr × »(F, G))) F],
  letI [] [":", expr normed_group Fu] [":=", expr by apply_instance],
  letI [] [":", expr normed_space 𝕜 Fu] [":=", expr by apply_instance],
  let [ident Gu] [] [":=", expr continuous_multilinear_map 𝕜 (λ i : fin 0, «expr × »(E, «expr × »(F, G))) G],
  letI [] [":", expr normed_group Gu] [":=", expr by apply_instance],
  letI [] [":", expr normed_space 𝕜 Gu] [":=", expr by apply_instance],
  let [ident isoE] [":", expr «expr ≃L[ ] »(Eu, 𝕜, E)] [":=", expr continuous_multilinear_curry_fin0 𝕜 «expr × »(E, «expr × »(F, G)) E],
  let [ident isoF] [":", expr «expr ≃L[ ] »(Fu, 𝕜, F)] [":=", expr continuous_multilinear_curry_fin0 𝕜 «expr × »(E, «expr × »(F, G)) F],
  let [ident isoG] [":", expr «expr ≃L[ ] »(Gu, 𝕜, G)] [":=", expr continuous_multilinear_curry_fin0 𝕜 «expr × »(E, «expr × »(F, G)) G],
  let [ident fu] [":", expr Eu → Fu] [":=", expr «expr ∘ »(«expr ∘ »(isoF.symm, f), isoE)],
  have [ident fu_diff] [":", expr times_cont_diff_on 𝕜 n fu «expr ⁻¹' »(isoE, s)] [],
  by rwa ["[", expr isoE.times_cont_diff_on_comp_iff, ",", expr isoF.symm.comp_times_cont_diff_on_iff, "]"] [],
  let [ident gu] [":", expr Fu → Gu] [":=", expr «expr ∘ »(«expr ∘ »(isoG.symm, g), isoF)],
  have [ident gu_diff] [":", expr times_cont_diff_on 𝕜 n gu «expr ⁻¹' »(isoF, t)] [],
  by rwa ["[", expr isoF.times_cont_diff_on_comp_iff, ",", expr isoG.symm.comp_times_cont_diff_on_iff, "]"] [],
  have [ident main] [":", expr times_cont_diff_on 𝕜 n «expr ∘ »(gu, fu) «expr ⁻¹' »(isoE, s)] [],
  { apply [expr times_cont_diff_on.comp_same_univ gu_diff fu_diff],
    assume [binders (y hy)],
    simp [] [] ["only"] ["[", expr fu, ",", expr continuous_linear_equiv.coe_apply, ",", expr function.comp_app, ",", expr mem_preimage, "]"] [] [],
    rw [expr isoF.apply_symm_apply (f (isoE y))] [],
    exact [expr st hy] },
  have [] [":", expr «expr = »(«expr ∘ »(gu, fu), «expr ∘ »(«expr ∘ »(isoG.symm, «expr ∘ »(g, f)), isoE))] [],
  { ext [] [ident y] [],
    simp [] [] ["only"] ["[", expr function.comp_apply, ",", expr gu, ",", expr fu, "]"] [] [],
    rw [expr isoF.apply_symm_apply (f (isoE y))] [] },
  rwa ["[", expr this, ",", expr isoE.times_cont_diff_on_comp_iff, ",", expr isoG.symm.comp_times_cont_diff_on_iff, "]"] ["at", ident main]
end

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem TimesContDiffOn.comp' {n : WithTop ℕ} {s : Set E} {t : Set F} {g : F → G} {f : E → F}
  (hg : TimesContDiffOn 𝕜 n g t) (hf : TimesContDiffOn 𝕜 n f s) : TimesContDiffOn 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
theorem TimesContDiff.comp_times_cont_diff_on {n : WithTop ℕ} {s : Set E} {g : F → G} {f : E → F}
  (hg : TimesContDiff 𝕜 n g) (hf : TimesContDiffOn 𝕜 n f s) : TimesContDiffOn 𝕜 n (g ∘ f) s :=
  (times_cont_diff_on_univ.2 hg).comp hf subset_preimage_univ

/-- The composition of `C^n` functions is `C^n`. -/
theorem TimesContDiff.comp {n : WithTop ℕ} {g : F → G} {f : E → F} (hg : TimesContDiff 𝕜 n g)
  (hf : TimesContDiff 𝕜 n f) : TimesContDiff 𝕜 n (g ∘ f) :=
  times_cont_diff_on_univ.1$
    TimesContDiffOn.comp (times_cont_diff_on_univ.2 hg) (times_cont_diff_on_univ.2 hf) (subset_univ _)

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem times_cont_diff_within_at.comp
{n : with_top exprℕ()}
{s : set E}
{t : set F}
{g : F → G}
{f : E → F}
(x : E)
(hg : times_cont_diff_within_at 𝕜 n g t (f x))
(hf : times_cont_diff_within_at 𝕜 n f s x)
(st : «expr ⊆ »(s, «expr ⁻¹' »(f, t))) : times_cont_diff_within_at 𝕜 n «expr ∘ »(g, f) s x :=
begin
  assume [binders (m hm)],
  rcases [expr hg.times_cont_diff_on hm, "with", "⟨", ident u, ",", ident u_nhd, ",", ident ut, ",", ident hu, "⟩"],
  rcases [expr hf.times_cont_diff_on hm, "with", "⟨", ident v, ",", ident v_nhd, ",", ident vs, ",", ident hv, "⟩"],
  have [ident xmem] [":", expr «expr ∈ »(x, «expr ∩ »(«expr ⁻¹' »(f, u), v))] [":=", expr ⟨(mem_of_mem_nhds_within (mem_insert (f x) _) u_nhd : _), mem_of_mem_nhds_within (mem_insert x s) v_nhd⟩],
  have [] [":", expr «expr ∈ »(«expr ⁻¹' »(f, u), «expr𝓝[ ] »(insert x s, x))] [],
  { apply [expr hf.continuous_within_at.insert_self.preimage_mem_nhds_within'],
    apply [expr nhds_within_mono _ _ u_nhd],
    rw [expr image_insert_eq] [],
    exact [expr insert_subset_insert (image_subset_iff.mpr st)] },
  have [ident Z] [] [":=", expr (hu.comp (hv.mono (inter_subset_right «expr ⁻¹' »(f, u) v)) (inter_subset_left _ _)).times_cont_diff_within_at xmem m (le_refl _)],
  have [] [":", expr «expr = »(«expr𝓝[ ] »(«expr ∩ »(«expr ⁻¹' »(f, u), v), x), «expr𝓝[ ] »(insert x s, x))] [],
  { have [ident A] [":", expr «expr = »(«expr ∩ »(«expr ⁻¹' »(f, u), v), «expr ∩ »(insert x s, «expr ∩ »(«expr ⁻¹' »(f, u), v)))] [],
    { apply [expr subset.antisymm _ (inter_subset_right _ _)],
      rintros [ident y, "⟨", ident hy1, ",", ident hy2, "⟩"],
      simp [] [] [] ["[", expr hy1, ",", expr hy2, ",", expr vs hy2, "]"] [] [] },
    rw ["[", expr A, ",", "<-", expr nhds_within_restrict'', "]"] [],
    exact [expr filter.inter_mem this v_nhd] },
  rwa ["[", expr insert_eq_of_mem xmem, ",", expr this, "]"] ["at", ident Z]
end

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem TimesContDiffWithinAt.comp' {n : WithTop ℕ} {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
  (hg : TimesContDiffWithinAt 𝕜 n g t (f x)) (hf : TimesContDiffWithinAt 𝕜 n f s x) :
  TimesContDiffWithinAt 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

theorem TimesContDiffAt.comp_times_cont_diff_within_at {n} (x : E) (hg : TimesContDiffAt 𝕜 n g (f x))
  (hf : TimesContDiffWithinAt 𝕜 n f s x) : TimesContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  hg.comp x hf (maps_to_univ _ _)

/-- The composition of `C^n` functions at points is `C^n`. -/
theorem TimesContDiffAt.comp {n : WithTop ℕ} (x : E) (hg : TimesContDiffAt 𝕜 n g (f x)) (hf : TimesContDiffAt 𝕜 n f x) :
  TimesContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp x hf subset_preimage_univ

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem times_cont_diff.comp_times_cont_diff_within_at
{n : with_top exprℕ()}
{g : F → G}
{f : E → F}
(h : times_cont_diff 𝕜 n g)
(hf : times_cont_diff_within_at 𝕜 n f t x) : times_cont_diff_within_at 𝕜 n «expr ∘ »(g, f) t x :=
begin
  have [] [":", expr times_cont_diff_within_at 𝕜 n g univ (f x)] [":=", expr h.times_cont_diff_at.times_cont_diff_within_at],
  exact [expr this.comp x hf (subset_univ _)]
end

theorem TimesContDiff.comp_times_cont_diff_at {n : WithTop ℕ} {g : F → G} {f : E → F} (x : E) (hg : TimesContDiff 𝕜 n g)
  (hf : TimesContDiffAt 𝕜 n f x) : TimesContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp_times_cont_diff_within_at hf

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem times_cont_diff_on_fderiv_within_apply
{m n : with_top exprℕ()}
{s : set E}
{f : E → F}
(hf : times_cont_diff_on 𝕜 n f s)
(hs : unique_diff_on 𝕜 s)
(hmn : «expr ≤ »(«expr + »(m, 1), n)) : times_cont_diff_on 𝕜 m (λ
 p : «expr × »(E, E), (fderiv_within 𝕜 f s p.1 : «expr →L[ ] »(E, 𝕜, F)) p.2) (set.prod s (univ : set E)) :=
begin
  have [ident A] [":", expr times_cont_diff 𝕜 m (λ p : «expr × »(«expr →L[ ] »(E, 𝕜, F), E), p.1 p.2)] [],
  { apply [expr is_bounded_bilinear_map.times_cont_diff],
    exact [expr is_bounded_bilinear_map_apply] },
  have [ident B] [":", expr times_cont_diff_on 𝕜 m (λ
    p : «expr × »(E, E), (fderiv_within 𝕜 f s p.fst, p.snd)) (set.prod s univ)] [],
  { apply [expr times_cont_diff_on.prod _ _],
    { have [ident I] [":", expr times_cont_diff_on 𝕜 m (λ
        x : E, fderiv_within 𝕜 f s x) s] [":=", expr hf.fderiv_within hs hmn],
      have [ident J] [":", expr times_cont_diff_on 𝕜 m (λ
        x : «expr × »(E, E), x.1) (set.prod s univ)] [":=", expr times_cont_diff_fst.times_cont_diff_on],
      exact [expr times_cont_diff_on.comp I J (prod_subset_preimage_fst _ _)] },
    { apply [expr times_cont_diff.times_cont_diff_on _],
      apply [expr is_bounded_linear_map.snd.times_cont_diff] } },
  exact [expr A.comp_times_cont_diff_on B]
end

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem times_cont_diff.times_cont_diff_fderiv_apply
{n m : with_top exprℕ()}
{f : E → F}
(hf : times_cont_diff 𝕜 n f)
(hmn : «expr ≤ »(«expr + »(m, 1), n)) : times_cont_diff 𝕜 m (λ
 p : «expr × »(E, E), (fderiv 𝕜 f p.1 : «expr →L[ ] »(E, 𝕜, F)) p.2) :=
begin
  rw ["<-", expr times_cont_diff_on_univ] ["at", "⊢", ident hf],
  rw ["[", "<-", expr fderiv_within_univ, ",", "<-", expr univ_prod_univ, "]"] [],
  exact [expr times_cont_diff_on_fderiv_within_apply hf unique_diff_on_univ hmn]
end

/-! ### Sum of two functions -/


-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff_add {n : with_top exprℕ()} : times_cont_diff 𝕜 n (λ p : «expr × »(F, F), «expr + »(p.1, p.2)) :=
(is_bounded_linear_map.fst.add is_bounded_linear_map.snd).times_cont_diff

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem TimesContDiffWithinAt.add {n : WithTop ℕ} {s : Set E} {f g : E → F} (hf : TimesContDiffWithinAt 𝕜 n f s x)
  (hg : TimesContDiffWithinAt 𝕜 n g s x) : TimesContDiffWithinAt 𝕜 n (fun x => f x+g x) s x :=
  times_cont_diff_add.TimesContDiffWithinAt.comp x (hf.prod hg) subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
theorem TimesContDiffAt.add {n : WithTop ℕ} {f g : E → F} (hf : TimesContDiffAt 𝕜 n f x)
  (hg : TimesContDiffAt 𝕜 n g x) : TimesContDiffAt 𝕜 n (fun x => f x+g x) x :=
  by 
    rw [←times_cont_diff_within_at_univ] at * <;> exact hf.add hg

/-- The sum of two `C^n`functions is `C^n`. -/
theorem TimesContDiff.add {n : WithTop ℕ} {f g : E → F} (hf : TimesContDiff 𝕜 n f) (hg : TimesContDiff 𝕜 n g) :
  TimesContDiff 𝕜 n fun x => f x+g x :=
  times_cont_diff_add.comp (hf.prod hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
theorem TimesContDiffOn.add {n : WithTop ℕ} {s : Set E} {f g : E → F} (hf : TimesContDiffOn 𝕜 n f s)
  (hg : TimesContDiffOn 𝕜 n g s) : TimesContDiffOn 𝕜 n (fun x => f x+g x) s :=
  fun x hx => (hf x hx).add (hg x hx)

/-! ### Negative -/


-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff_neg {n : with_top exprℕ()} : times_cont_diff 𝕜 n (λ p : F, «expr- »(p)) :=
is_bounded_linear_map.id.neg.times_cont_diff

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
theorem TimesContDiffWithinAt.neg {n : WithTop ℕ} {s : Set E} {f : E → F} (hf : TimesContDiffWithinAt 𝕜 n f s x) :
  TimesContDiffWithinAt 𝕜 n (fun x => -f x) s x :=
  times_cont_diff_neg.TimesContDiffWithinAt.comp x hf subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
theorem TimesContDiffAt.neg {n : WithTop ℕ} {f : E → F} (hf : TimesContDiffAt 𝕜 n f x) :
  TimesContDiffAt 𝕜 n (fun x => -f x) x :=
  by 
    rw [←times_cont_diff_within_at_univ] at * <;> exact hf.neg

/-- The negative of a `C^n`function is `C^n`. -/
theorem TimesContDiff.neg {n : WithTop ℕ} {f : E → F} (hf : TimesContDiff 𝕜 n f) : TimesContDiff 𝕜 n fun x => -f x :=
  times_cont_diff_neg.comp hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
theorem TimesContDiffOn.neg {n : WithTop ℕ} {s : Set E} {f : E → F} (hf : TimesContDiffOn 𝕜 n f s) :
  TimesContDiffOn 𝕜 n (fun x => -f x) s :=
  fun x hx => (hf x hx).neg

/-! ### Subtraction -/


/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem TimesContDiffWithinAt.sub {n : WithTop ℕ} {s : Set E} {f g : E → F} (hf : TimesContDiffWithinAt 𝕜 n f s x)
  (hg : TimesContDiffWithinAt 𝕜 n g s x) : TimesContDiffWithinAt 𝕜 n (fun x => f x - g x) s x :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
theorem TimesContDiffAt.sub {n : WithTop ℕ} {f g : E → F} (hf : TimesContDiffAt 𝕜 n f x)
  (hg : TimesContDiffAt 𝕜 n g x) : TimesContDiffAt 𝕜 n (fun x => f x - g x) x :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
theorem TimesContDiffOn.sub {n : WithTop ℕ} {s : Set E} {f g : E → F} (hf : TimesContDiffOn 𝕜 n f s)
  (hg : TimesContDiffOn 𝕜 n g s) : TimesContDiffOn 𝕜 n (fun x => f x - g x) s :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions is `C^n`. -/
theorem TimesContDiff.sub {n : WithTop ℕ} {f g : E → F} (hf : TimesContDiff 𝕜 n f) (hg : TimesContDiff 𝕜 n g) :
  TimesContDiff 𝕜 n fun x => f x - g x :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

/-! ### Sum of finitely many functions -/


theorem TimesContDiffWithinAt.sum {ι : Type _} {f : ι → E → F} {s : Finset ι} {n : WithTop ℕ} {t : Set E} {x : E}
  (h : ∀ i (_ : i ∈ s), TimesContDiffWithinAt 𝕜 n (fun x => f i x) t x) :
  TimesContDiffWithinAt 𝕜 n (fun x => ∑i in s, f i x) t x :=
  by 
    classical 
    induction' s using Finset.induction_on with i s is IH
    ·
      simp [times_cont_diff_within_at_const]
    ·
      simp only [is, Finset.sum_insert, not_false_iff]
      exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))

theorem TimesContDiffAt.sum {ι : Type _} {f : ι → E → F} {s : Finset ι} {n : WithTop ℕ} {x : E}
  (h : ∀ i (_ : i ∈ s), TimesContDiffAt 𝕜 n (fun x => f i x) x) : TimesContDiffAt 𝕜 n (fun x => ∑i in s, f i x) x :=
  by 
    rw [←times_cont_diff_within_at_univ] at * <;> exact TimesContDiffWithinAt.sum h

theorem TimesContDiffOn.sum {ι : Type _} {f : ι → E → F} {s : Finset ι} {n : WithTop ℕ} {t : Set E}
  (h : ∀ i (_ : i ∈ s), TimesContDiffOn 𝕜 n (fun x => f i x) t) : TimesContDiffOn 𝕜 n (fun x => ∑i in s, f i x) t :=
  fun x hx => TimesContDiffWithinAt.sum fun i hi => h i hi x hx

theorem TimesContDiff.sum {ι : Type _} {f : ι → E → F} {s : Finset ι} {n : WithTop ℕ}
  (h : ∀ i (_ : i ∈ s), TimesContDiff 𝕜 n fun x => f i x) : TimesContDiff 𝕜 n fun x => ∑i in s, f i x :=
  by 
    simp [←times_cont_diff_on_univ] at * <;> exact TimesContDiffOn.sum h

/-! ### Product of two functions -/


-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff_mul {n : with_top exprℕ()} : times_cont_diff 𝕜 n (λ p : «expr × »(𝕜, 𝕜), «expr * »(p.1, p.2)) :=
is_bounded_bilinear_map_mul.times_cont_diff

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem TimesContDiffWithinAt.mul {n : WithTop ℕ} {s : Set E} {f g : E → 𝕜} (hf : TimesContDiffWithinAt 𝕜 n f s x)
  (hg : TimesContDiffWithinAt 𝕜 n g s x) : TimesContDiffWithinAt 𝕜 n (fun x => f x*g x) s x :=
  times_cont_diff_mul.TimesContDiffWithinAt.comp x (hf.prod hg) subset_preimage_univ

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
theorem TimesContDiffAt.mul {n : WithTop ℕ} {f g : E → 𝕜} (hf : TimesContDiffAt 𝕜 n f x)
  (hg : TimesContDiffAt 𝕜 n g x) : TimesContDiffAt 𝕜 n (fun x => f x*g x) x :=
  by 
    rw [←times_cont_diff_within_at_univ] at * <;> exact hf.mul hg

/-- The product of two `C^n` functions on a domain is `C^n`. -/
theorem TimesContDiffOn.mul {n : WithTop ℕ} {s : Set E} {f g : E → 𝕜} (hf : TimesContDiffOn 𝕜 n f s)
  (hg : TimesContDiffOn 𝕜 n g s) : TimesContDiffOn 𝕜 n (fun x => f x*g x) s :=
  fun x hx => (hf x hx).mul (hg x hx)

/-- The product of two `C^n`functions is `C^n`. -/
theorem TimesContDiff.mul {n : WithTop ℕ} {f g : E → 𝕜} (hf : TimesContDiff 𝕜 n f) (hg : TimesContDiff 𝕜 n g) :
  TimesContDiff 𝕜 n fun x => f x*g x :=
  times_cont_diff_mul.comp (hf.prod hg)

theorem TimesContDiffWithinAt.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : TimesContDiffWithinAt 𝕜 n f s x) :
  TimesContDiffWithinAt 𝕜 n (fun x => f x / c) s x :=
  by 
    simpa only [div_eq_mul_inv] using hf.mul times_cont_diff_within_at_const

theorem TimesContDiffAt.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : TimesContDiffAt 𝕜 n f x) :
  TimesContDiffAt 𝕜 n (fun x => f x / c) x :=
  by 
    simpa only [div_eq_mul_inv] using hf.mul times_cont_diff_at_const

theorem TimesContDiffOn.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : TimesContDiffOn 𝕜 n f s) :
  TimesContDiffOn 𝕜 n (fun x => f x / c) s :=
  by 
    simpa only [div_eq_mul_inv] using hf.mul times_cont_diff_on_const

theorem TimesContDiff.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : TimesContDiff 𝕜 n f) :
  TimesContDiff 𝕜 n fun x => f x / c :=
  by 
    simpa only [div_eq_mul_inv] using hf.mul times_cont_diff_const

theorem TimesContDiff.pow {n : WithTop ℕ} {f : E → 𝕜} (hf : TimesContDiff 𝕜 n f) :
  ∀ (m : ℕ), TimesContDiff 𝕜 n fun x => f x^m
| 0 =>
  by 
    simpa using times_cont_diff_const
| m+1 =>
  by 
    simpa [pow_succₓ] using hf.mul (TimesContDiff.pow m)

theorem TimesContDiffAt.pow {n : WithTop ℕ} {f : E → 𝕜} (hf : TimesContDiffAt 𝕜 n f x) (m : ℕ) :
  TimesContDiffAt 𝕜 n (fun y => f y^m) x :=
  (times_cont_diff_id.pow m).TimesContDiffAt.comp x hf

theorem TimesContDiffWithinAt.pow {n : WithTop ℕ} {f : E → 𝕜} (hf : TimesContDiffWithinAt 𝕜 n f s x) (m : ℕ) :
  TimesContDiffWithinAt 𝕜 n (fun y => f y^m) s x :=
  (times_cont_diff_id.pow m).TimesContDiffAt.comp_times_cont_diff_within_at x hf

theorem TimesContDiffOn.pow {n : WithTop ℕ} {f : E → 𝕜} (hf : TimesContDiffOn 𝕜 n f s) (m : ℕ) :
  TimesContDiffOn 𝕜 n (fun y => f y^m) s :=
  fun y hy => (hf y hy).pow m

/-! ### Scalar multiplication -/


-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff_smul
{n : with_top exprℕ()} : times_cont_diff 𝕜 n (λ p : «expr × »(𝕜, F), «expr • »(p.1, p.2)) :=
is_bounded_bilinear_map_smul.times_cont_diff

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
theorem TimesContDiffWithinAt.smul {n : WithTop ℕ} {s : Set E} {f : E → 𝕜} {g : E → F}
  (hf : TimesContDiffWithinAt 𝕜 n f s x) (hg : TimesContDiffWithinAt 𝕜 n g s x) :
  TimesContDiffWithinAt 𝕜 n (fun x => f x • g x) s x :=
  times_cont_diff_smul.TimesContDiffWithinAt.comp x (hf.prod hg) subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
theorem TimesContDiffAt.smul {n : WithTop ℕ} {f : E → 𝕜} {g : E → F} (hf : TimesContDiffAt 𝕜 n f x)
  (hg : TimesContDiffAt 𝕜 n g x) : TimesContDiffAt 𝕜 n (fun x => f x • g x) x :=
  by 
    rw [←times_cont_diff_within_at_univ] at * <;> exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
theorem TimesContDiff.smul {n : WithTop ℕ} {f : E → 𝕜} {g : E → F} (hf : TimesContDiff 𝕜 n f)
  (hg : TimesContDiff 𝕜 n g) : TimesContDiff 𝕜 n fun x => f x • g x :=
  times_cont_diff_smul.comp (hf.prod hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
theorem TimesContDiffOn.smul {n : WithTop ℕ} {s : Set E} {f : E → 𝕜} {g : E → F} (hf : TimesContDiffOn 𝕜 n f s)
  (hg : TimesContDiffOn 𝕜 n g s) : TimesContDiffOn 𝕜 n (fun x => f x • g x) s :=
  fun x hx => (hf x hx).smul (hg x hx)

/-! ### Cartesian product of two functions-/


section prod_mapₓ

variable{E' : Type _}[NormedGroup E'][NormedSpace 𝕜 E']{F' : Type _}[NormedGroup F'][NormedSpace 𝕜 F']{n : WithTop ℕ}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem TimesContDiffWithinAt.prod_map' {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {p : E × E'}
  (hf : TimesContDiffWithinAt 𝕜 n f s p.1) (hg : TimesContDiffWithinAt 𝕜 n g t p.2) :
  TimesContDiffWithinAt 𝕜 n (Prod.mapₓ f g) (Set.Prod s t) p :=
  (hf.comp p times_cont_diff_within_at_fst (prod_subset_preimage_fst _ _)).Prod
    (hg.comp p times_cont_diff_within_at_snd (prod_subset_preimage_snd _ _))

theorem TimesContDiffWithinAt.prod_map {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {x : E} {y : E'}
  (hf : TimesContDiffWithinAt 𝕜 n f s x) (hg : TimesContDiffWithinAt 𝕜 n g t y) :
  TimesContDiffWithinAt 𝕜 n (Prod.mapₓ f g) (Set.Prod s t) (x, y) :=
  TimesContDiffWithinAt.prod_map' hf hg

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
theorem TimesContDiffOn.prod_map {E' : Type _} [NormedGroup E'] [NormedSpace 𝕜 E'] {F' : Type _} [NormedGroup F']
  [NormedSpace 𝕜 F'] {s : Set E} {t : Set E'} {n : WithTop ℕ} {f : E → F} {g : E' → F'} (hf : TimesContDiffOn 𝕜 n f s)
  (hg : TimesContDiffOn 𝕜 n g t) : TimesContDiffOn 𝕜 n (Prod.mapₓ f g) (Set.Prod s t) :=
  (hf.comp times_cont_diff_on_fst (prod_subset_preimage_fst _ _)).Prod
    (hg.comp times_cont_diff_on_snd (prod_subset_preimage_snd _ _))

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem TimesContDiffAt.prod_map {f : E → F} {g : E' → F'} {x : E} {y : E'} (hf : TimesContDiffAt 𝕜 n f x)
  (hg : TimesContDiffAt 𝕜 n g y) : TimesContDiffAt 𝕜 n (Prod.mapₓ f g) (x, y) :=
  by 
    rw [TimesContDiffAt] at *
    convert hf.prod_map hg 
    simp only [univ_prod_univ]

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem TimesContDiffAt.prod_map' {f : E → F} {g : E' → F'} {p : E × E'} (hf : TimesContDiffAt 𝕜 n f p.1)
  (hg : TimesContDiffAt 𝕜 n g p.2) : TimesContDiffAt 𝕜 n (Prod.mapₓ f g) p :=
  by 
    rcases p with ⟨⟩
    exact TimesContDiffAt.prod_map hf hg

/-- The product map of two `C^n` functions is `C^n`. -/
theorem TimesContDiff.prod_map {f : E → F} {g : E' → F'} (hf : TimesContDiff 𝕜 n f) (hg : TimesContDiff 𝕜 n g) :
  TimesContDiff 𝕜 n (Prod.mapₓ f g) :=
  by 
    rw [times_cont_diff_iff_times_cont_diff_at] at *
    exact fun ⟨x, y⟩ => (hf x).prod_map (hg y)

end prod_mapₓ

/-! ### Inversion in a complete normed algebra -/


section AlgebraInverse

variable(𝕜){R : Type _}[NormedRing R][NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ringₓ

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element.  The proof is by induction, bootstrapping using an identity expressing the
derivative of inversion as a bilinear map of inversion itself. -/
theorem times_cont_diff_at_ring_inverse
[complete_space R]
{n : with_top exprℕ()}
(x : units R) : times_cont_diff_at 𝕜 n ring.inverse (x : R) :=
begin
  induction [expr n] ["using", ident with_top.nat_induction] ["with", ident n, ident IH, ident Itop] [],
  { intros [ident m, ident hm],
    refine [expr ⟨{y : R | is_unit y}, _, _⟩],
    { simp [] [] [] ["[", expr nhds_within_univ, "]"] [] [],
      exact [expr x.nhds] },
    { use [expr ftaylor_series_within 𝕜 inverse univ],
      rw ["[", expr le_antisymm hm bot_le, ",", expr has_ftaylor_series_up_to_on_zero_iff, "]"] [],
      split,
      { rintros ["_", "⟨", ident x', ",", ident rfl, "⟩"],
        exact [expr (inverse_continuous_at x').continuous_within_at] },
      { simp [] [] [] ["[", expr ftaylor_series_within, "]"] [] [] } } },
  { apply [expr times_cont_diff_at_succ_iff_has_fderiv_at.mpr],
    refine [expr ⟨λ x : R, «expr- »(lmul_left_right 𝕜 R (inverse x) (inverse x)), _, _⟩],
    { refine [expr ⟨{y : R | is_unit y}, x.nhds, _⟩],
      rintros ["_", "⟨", ident y, ",", ident rfl, "⟩"],
      rw ["[", expr inverse_unit, "]"] [],
      exact [expr has_fderiv_at_ring_inverse y] },
    { convert [] [expr (lmul_left_right_is_bounded_bilinear 𝕜 R).times_cont_diff.neg.comp_times_cont_diff_at (x : R) (IH.prod IH)] [] } },
  { exact [expr times_cont_diff_at_top.mpr Itop] }
end

variable(𝕜){𝕜' : Type _}[NormedField 𝕜'][NormedAlgebra 𝕜 𝕜'][CompleteSpace 𝕜']

theorem times_cont_diff_at_inv {x : 𝕜'} (hx : x ≠ 0) {n} : TimesContDiffAt 𝕜 n HasInv.inv x :=
  by 
    simpa only [Ring.inverse_eq_inv'] using times_cont_diff_at_ring_inverse 𝕜 (Units.mk0 x hx)

theorem times_cont_diff_on_inv {n} : TimesContDiffOn 𝕜 n (HasInv.inv : 𝕜' → 𝕜') («expr ᶜ» {0}) :=
  fun x hx => (times_cont_diff_at_inv 𝕜 hx).TimesContDiffWithinAt

variable{𝕜}

theorem TimesContDiffWithinAt.inv {f : E → 𝕜'} {n} (hf : TimesContDiffWithinAt 𝕜 n f s x) (hx : f x ≠ 0) :
  TimesContDiffWithinAt 𝕜 n (fun x => f x⁻¹) s x :=
  (times_cont_diff_at_inv 𝕜 hx).comp_times_cont_diff_within_at x hf

theorem TimesContDiffOn.inv {f : E → 𝕜'} {n} (hf : TimesContDiffOn 𝕜 n f s) (h : ∀ x (_ : x ∈ s), f x ≠ 0) :
  TimesContDiffOn 𝕜 n (fun x => f x⁻¹) s :=
  fun x hx => (hf.times_cont_diff_within_at hx).inv (h x hx)

theorem TimesContDiffAt.inv {f : E → 𝕜'} {n} (hf : TimesContDiffAt 𝕜 n f x) (hx : f x ≠ 0) :
  TimesContDiffAt 𝕜 n (fun x => f x⁻¹) x :=
  hf.inv hx

theorem TimesContDiff.inv {f : E → 𝕜'} {n} (hf : TimesContDiff 𝕜 n f) (h : ∀ x, f x ≠ 0) :
  TimesContDiff 𝕜 n fun x => f x⁻¹ :=
  by 
    rw [times_cont_diff_iff_times_cont_diff_at]
    exact fun x => hf.times_cont_diff_at.inv (h x)

theorem TimesContDiffWithinAt.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : TimesContDiffWithinAt 𝕜 n f s x)
  (hg : TimesContDiffWithinAt 𝕜 n g s x) (hx : g x ≠ 0) : TimesContDiffWithinAt 𝕜 n (fun x => f x / g x) s x :=
  by 
    simpa only [div_eq_mul_inv] using hf.mul (hg.inv hx)

theorem TimesContDiffOn.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : TimesContDiffOn 𝕜 n f s)
  (hg : TimesContDiffOn 𝕜 n g s) (h₀ : ∀ x (_ : x ∈ s), g x ≠ 0) : TimesContDiffOn 𝕜 n (f / g) s :=
  fun x hx => (hf x hx).div (hg x hx) (h₀ x hx)

theorem TimesContDiffAt.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : TimesContDiffAt 𝕜 n f x)
  (hg : TimesContDiffAt 𝕜 n g x) (hx : g x ≠ 0) : TimesContDiffAt 𝕜 n (fun x => f x / g x) x :=
  hf.div hg hx

theorem TimesContDiff.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : TimesContDiff 𝕜 n f) (hg : TimesContDiff 𝕜 n g)
  (h0 : ∀ x, g x ≠ 0) : TimesContDiff 𝕜 n fun x => f x / g x :=
  by 
    simp only [times_cont_diff_iff_times_cont_diff_at] at *
    exact fun x => (hf x).div (hg x) (h0 x)

end AlgebraInverse

/-! ### Inversion of continuous linear maps between Banach spaces -/


section MapInverse

open ContinuousLinearMap

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
theorem times_cont_diff_at_map_inverse
[complete_space E]
{n : with_top exprℕ()}
(e : «expr ≃L[ ] »(E, 𝕜, F)) : times_cont_diff_at 𝕜 n inverse (e : «expr →L[ ] »(E, 𝕜, F)) :=
begin
  nontriviality [expr E] [],
  let [ident O₁] [":", expr «expr →L[ ] »(E, 𝕜, E) → «expr →L[ ] »(F, 𝕜, E)] [":=", expr λ
   f, f.comp (e.symm : «expr →L[ ] »(F, 𝕜, E))],
  let [ident O₂] [":", expr «expr →L[ ] »(E, 𝕜, F) → «expr →L[ ] »(E, 𝕜, E)] [":=", expr λ
   f, (e.symm : «expr →L[ ] »(F, 𝕜, E)).comp f],
  have [] [":", expr «expr = »(continuous_linear_map.inverse, «expr ∘ »(O₁, «expr ∘ »(ring.inverse, O₂)))] [":=", expr funext (to_ring_inverse e)],
  rw [expr this] [],
  have [ident h₁] [":", expr times_cont_diff 𝕜 n O₁] [],
  from [expr is_bounded_bilinear_map_comp.times_cont_diff.comp (times_cont_diff_const.prod times_cont_diff_id)],
  have [ident h₂] [":", expr times_cont_diff 𝕜 n O₂] [],
  from [expr is_bounded_bilinear_map_comp.times_cont_diff.comp (times_cont_diff_id.prod times_cont_diff_const)],
  refine [expr h₁.times_cont_diff_at.comp _ (times_cont_diff_at.comp _ _ h₂.times_cont_diff_at)],
  convert [] [expr times_cont_diff_at_ring_inverse 𝕜 (1 : units «expr →L[ ] »(E, 𝕜, E))] [],
  simp [] [] [] ["[", expr O₂, ",", expr one_def, "]"] [] []
end

end MapInverse

section FunctionInverse

open ContinuousLinearMap

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a local homeomorphism and the point `a` is in its target,
and if `f` is `n` times continuously differentiable at `f.symm a`,
and if the derivative at `f.symm a` is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.times_cont_diff_at_symm
[complete_space E]
{n : with_top exprℕ()}
(f : local_homeomorph E F)
{f₀' : «expr ≃L[ ] »(E, 𝕜, F)}
{a : F}
(ha : «expr ∈ »(a, f.target))
(hf₀' : has_fderiv_at f (f₀' : «expr →L[ ] »(E, 𝕜, F)) (f.symm a))
(hf : times_cont_diff_at 𝕜 n f (f.symm a)) : times_cont_diff_at 𝕜 n f.symm a :=
begin
  induction [expr n] ["using", ident with_top.nat_induction] ["with", ident n, ident IH, ident Itop] [],
  { rw [expr times_cont_diff_at_zero] [],
    exact [expr ⟨f.target, is_open.mem_nhds f.open_target ha, f.continuous_inv_fun⟩] },
  { obtain ["⟨", ident f', ",", "⟨", ident u, ",", ident hu, ",", ident hff', "⟩", ",", ident hf', "⟩", ":=", expr times_cont_diff_at_succ_iff_has_fderiv_at.mp hf],
    apply [expr times_cont_diff_at_succ_iff_has_fderiv_at.mpr],
    have [ident eq_f₀'] [":", expr «expr = »(f' (f.symm a), f₀')] [],
    { exact [expr (hff' (f.symm a) (mem_of_mem_nhds hu)).unique hf₀'] },
    refine [expr ⟨«expr ∘ »(inverse, «expr ∘ »(f', f.symm)), _, _⟩],
    { have [ident h_nhds] [":", expr «expr ∈ »({y : E | «expr∃ , »((e : «expr ≃L[ ] »(E, 𝕜, F)), «expr = »(«expr↑ »(e), f' y))}, expr𝓝() (f.symm a))] [],
      { have [ident hf₀'] [] [":=", expr f₀'.nhds],
        rw ["<-", expr eq_f₀'] ["at", ident hf₀'],
        exact [expr hf'.continuous_at.preimage_mem_nhds hf₀'] },
      obtain ["⟨", ident t, ",", ident htu, ",", ident ht, ",", ident htf, "⟩", ":=", expr mem_nhds_iff.mp (filter.inter_mem hu h_nhds)],
      use [expr «expr ∩ »(f.target, «expr ⁻¹' »(f.symm, t))],
      refine [expr ⟨is_open.mem_nhds _ _, _⟩],
      { exact [expr f.preimage_open_of_open_symm ht] },
      { exact [expr mem_inter ha (mem_preimage.mpr htf)] },
      intros [ident x, ident hx],
      obtain ["⟨", ident hxu, ",", ident e, ",", ident he, "⟩", ":=", expr htu hx.2],
      have [ident h_deriv] [":", expr has_fderiv_at f «expr↑ »(e) (f.symm x)] [],
      { rw [expr he] [],
        exact [expr hff' (f.symm x) hxu] },
      convert [] [expr f.has_fderiv_at_symm hx.1 h_deriv] [],
      simp [] [] [] ["[", "<-", expr he, "]"] [] [] },
    { have [ident h_deriv₁] [":", expr times_cont_diff_at 𝕜 n inverse (f' (f.symm a))] [],
      { rw [expr eq_f₀'] [],
        exact [expr times_cont_diff_at_map_inverse _] },
      have [ident h_deriv₂] [":", expr times_cont_diff_at 𝕜 n f.symm a] [],
      { refine [expr IH (hf.of_le _)],
        norm_cast [],
        exact [expr nat.le_succ n] },
      exact [expr (h_deriv₁.comp _ hf').comp _ h_deriv₂] } },
  { refine [expr times_cont_diff_at_top.mpr _],
    intros [ident n],
    exact [expr Itop n (times_cont_diff_at_top.mp hf n)] }
end

/-- Let `f` be a local homeomorphism of a nondiscrete normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.times_cont_diff_at_symm_deriv [CompleteSpace 𝕜] {n : WithTop ℕ} (f : LocalHomeomorph 𝕜 𝕜)
  {f₀' a : 𝕜} (h₀ : f₀' ≠ 0) (ha : a ∈ f.target) (hf₀' : HasDerivAt f f₀' (f.symm a))
  (hf : TimesContDiffAt 𝕜 n f (f.symm a)) : TimesContDiffAt 𝕜 n f.symm a :=
  f.times_cont_diff_at_symm ha (hf₀'.has_fderiv_at_equiv h₀) hf

end FunctionInverse

section Real

/-!
### Results over `ℝ` or `ℂ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/


variable{𝕂 :
    Type _}[IsROrC 𝕂]{E' : Type _}[NormedGroup E'][NormedSpace 𝕂 E']{F' : Type _}[NormedGroup F'][NormedSpace 𝕂 F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
    domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
theorem HasFtaylorSeriesUpToOn.has_strict_fderiv_at {s : Set E'} {f : E' → F'} {x : E'}
  {p : E' → FormalMultilinearSeries 𝕂 E' F'} {n : WithTop ℕ} (hf : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
  (hs : s ∈ 𝓝 x) : HasStrictFderivAt f ((continuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x :=
  has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at (hf.eventually_has_fderiv_at hn hs)$
    (continuousMultilinearCurryFin1 𝕂 E' F').ContinuousAt.comp$ (hf.cont 1 hn).ContinuousAt hs

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem times_cont_diff_at.has_strict_fderiv_at'
{f : E' → F'}
{f' : «expr →L[ ] »(E', 𝕂, F')}
{x : E'}
{n : with_top exprℕ()}
(hf : times_cont_diff_at 𝕂 n f x)
(hf' : has_fderiv_at f f' x)
(hn : «expr ≤ »(1, n)) : has_strict_fderiv_at f f' x :=
begin
  rcases [expr hf 1 hn, "with", "⟨", ident u, ",", ident H, ",", ident p, ",", ident hp, "⟩"],
  simp [] [] ["only"] ["[", expr nhds_within_univ, ",", expr mem_univ, ",", expr insert_eq_of_mem, "]"] [] ["at", ident H],
  have [] [] [":=", expr hp.has_strict_fderiv_at le_rfl H],
  rwa [expr hf'.unique this.has_fderiv_at] []
end

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem TimesContDiffAt.has_strict_deriv_at' {f : 𝕂 → F'} {f' : F'} {x : 𝕂} {n : WithTop ℕ}
  (hf : TimesContDiffAt 𝕂 n f x) (hf' : HasDerivAt f f' x) (hn : 1 ≤ n) : HasStrictDerivAt f f' x :=
  hf.has_strict_fderiv_at' hf' hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem TimesContDiffAt.has_strict_fderiv_at {f : E' → F'} {x : E'} {n : WithTop ℕ} (hf : TimesContDiffAt 𝕂 n f x)
  (hn : 1 ≤ n) : HasStrictFderivAt f (fderiv 𝕂 f x) x :=
  hf.has_strict_fderiv_at' (hf.differentiable_at hn).HasFderivAt hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem TimesContDiffAt.has_strict_deriv_at {f : 𝕂 → F'} {x : 𝕂} {n : WithTop ℕ} (hf : TimesContDiffAt 𝕂 n f x)
  (hn : 1 ≤ n) : HasStrictDerivAt f (deriv f x) x :=
  (hf.has_strict_fderiv_at hn).HasStrictDerivAt

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem TimesContDiff.has_strict_fderiv_at {f : E' → F'} {x : E'} {n : WithTop ℕ} (hf : TimesContDiff 𝕂 n f)
  (hn : 1 ≤ n) : HasStrictFderivAt f (fderiv 𝕂 f x) x :=
  hf.times_cont_diff_at.has_strict_fderiv_at hn

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem TimesContDiff.has_strict_deriv_at {f : 𝕂 → F'} {x : 𝕂} {n : WithTop ℕ} (hf : TimesContDiff 𝕂 n f) (hn : 1 ≤ n) :
  HasStrictDerivAt f (deriv f x) x :=
  hf.times_cont_diff_at.has_strict_deriv_at hn

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
and `∥p x 1∥₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s`. -/
theorem has_ftaylor_series_up_to_on.exists_lipschitz_on_with_of_nnnorm_lt
{E F : Type*}
[normed_group E]
[normed_space exprℝ() E]
[normed_group F]
[normed_space exprℝ() F]
{f : E → F}
{p : E → formal_multilinear_series exprℝ() E F}
{s : set E}
{x : E}
(hf : has_ftaylor_series_up_to_on 1 f p (insert x s))
(hs : convex exprℝ() s)
(K : «exprℝ≥0»())
(hK : «expr < »(«expr∥ ∥₊»(p x 1), K)) : «expr∃ , »((t «expr ∈ » «expr𝓝[ ] »(s, x)), lipschitz_on_with K f t) :=
begin
  set [] [ident f'] [] [":="] [expr λ y, continuous_multilinear_curry_fin1 exprℝ() E F (p y 1)] [],
  have [ident hder] [":", expr ∀ y «expr ∈ » s, has_fderiv_within_at f (f' y) s y] [],
  from [expr λ y hy, (hf.has_fderiv_within_at le_rfl (subset_insert x s hy)).mono (subset_insert x s)],
  have [ident hcont] [":", expr continuous_within_at f' s x] [],
  from [expr (continuous_multilinear_curry_fin1 exprℝ() E F).continuous_at.comp_continuous_within_at ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s))],
  replace [ident hK] [":", expr «expr < »(«expr∥ ∥₊»(f' x), K)] [],
  by simpa [] [] ["only"] ["[", expr linear_isometry_equiv.nnnorm_map, "]"] [] [],
  exact [expr hs.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt «expr $ »(eventually_nhds_within_iff.2, eventually_of_forall hder) hcont K hK]
end

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
then `f` is Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFtaylorSeriesUpToOn.exists_lipschitz_on_with {E F : Type _} [NormedGroup E] [NormedSpace ℝ E] [NormedGroup F]
  [NormedSpace ℝ F] {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}
  (hf : HasFtaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) :
  ∃ (K : _)(t : _)(_ : t ∈ 𝓝[s] x), LipschitzOnWith K f t :=
  (no_top _).imp$ hf.exists_lipschitz_on_with_of_nnnorm_lt hs

/-- If `f` is `C^1` within a conves set `s` at `x`, then it is Lipschitz on a neighborhood of `x`
within `s`. -/
theorem TimesContDiffWithinAt.exists_lipschitz_on_with {E F : Type _} [NormedGroup E] [NormedSpace ℝ E] [NormedGroup F]
  [NormedSpace ℝ F] {f : E → F} {s : Set E} {x : E} (hf : TimesContDiffWithinAt ℝ 1 f s x) (hs : Convex ℝ s) :
  ∃ (K :  ℝ≥0 )(t : _)(_ : t ∈ 𝓝[s] x), LipschitzOnWith K f t :=
  by 
    rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩
    rcases metric.mem_nhds_within_iff.mp hst with ⟨ε, ε0, hε⟩
    replace hp : HasFtaylorSeriesUpToOn 1 f p (Metric.Ball x ε ∩ insert x s) := hp.mono hε 
    clear hst hε t 
    rw [←insert_eq_of_mem (Metric.mem_ball_self ε0), ←insert_inter] at hp 
    rcases hp.exists_lipschitz_on_with ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩
    rw [inter_comm, ←nhds_within_restrict' _ (Metric.ball_mem_nhds _ ε0)] at hst 
    exact ⟨K, t, hst, hft⟩

/-- If `f` is `C^1` at `x` and `K > ∥fderiv 𝕂 f x∥`, then `f` is `K`-Lipschitz in a neighborhood of
`x`. -/
theorem TimesContDiffAt.exists_lipschitz_on_with_of_nnnorm_lt {f : E' → F'} {x : E'} (hf : TimesContDiffAt 𝕂 1 f x)
  (K :  ℝ≥0 ) (hK : ∥fderiv 𝕂 f x∥₊ < K) : ∃ (t : _)(_ : t ∈ 𝓝 x), LipschitzOnWith K f t :=
  (hf.has_strict_fderiv_at le_rfl).exists_lipschitz_on_with_of_nnnorm_lt K hK

/-- If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`. -/
theorem TimesContDiffAt.exists_lipschitz_on_with {f : E' → F'} {x : E'} (hf : TimesContDiffAt 𝕂 1 f x) :
  ∃ (K : _)(t : _)(_ : t ∈ 𝓝 x), LipschitzOnWith K f t :=
  (hf.has_strict_fderiv_at le_rfl).exists_lipschitz_on_with

end Real

section deriv

/-!
### One dimension

All results up to now have been expressed in terms of the general Fréchet derivative `fderiv`. For
maps defined on the field, the one-dimensional derivative `deriv` is often easier to use. In this
paragraph, we reformulate some higher smoothness results in terms of `deriv`.
-/


variable{f₂ : 𝕜 → F}{s₂ : Set 𝕜}

open continuous_linear_map(smulRight)

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `deriv_within`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_deriv_within
{n : exprℕ()}
(hs : unique_diff_on 𝕜 s₂) : «expr ↔ »(times_cont_diff_on 𝕜 («expr + »(n, 1) : exprℕ()) f₂ s₂, «expr ∧ »(differentiable_on 𝕜 f₂ s₂, times_cont_diff_on 𝕜 n (deriv_within f₂ s₂) s₂)) :=
begin
  rw [expr times_cont_diff_on_succ_iff_fderiv_within hs] [],
  congr' [2] [],
  apply [expr le_antisymm],
  { assume [binders (h)],
    have [] [":", expr «expr = »(deriv_within f₂ s₂, «expr ∘ »(λ
       u : «expr →L[ ] »(𝕜, 𝕜, F), u 1, fderiv_within 𝕜 f₂ s₂))] [],
    by { ext [] [ident x] [],
      refl },
    simp [] [] ["only"] ["[", expr this, "]"] [] [],
    apply [expr times_cont_diff.comp_times_cont_diff_on _ h],
    exact [expr (is_bounded_bilinear_map_apply.is_bounded_linear_map_left _).times_cont_diff] },
  { assume [binders (h)],
    have [] [":", expr «expr = »(fderiv_within 𝕜 f₂ s₂, «expr ∘ »(smul_right (1 : «expr →L[ ] »(𝕜, 𝕜, 𝕜)), deriv_within f₂ s₂))] [],
    by { ext [] [ident x] [],
      simp [] [] [] ["[", expr deriv_within, "]"] [] [] },
    simp [] [] ["only"] ["[", expr this, "]"] [] [],
    apply [expr times_cont_diff.comp_times_cont_diff_on _ h],
    exact [expr (is_bounded_bilinear_map_smul_right.is_bounded_linear_map_right _).times_cont_diff] }
end

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_deriv_of_open {n : ℕ} (hs : IsOpen s₂) :
  TimesContDiffOn 𝕜 (n+1 : ℕ) f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ TimesContDiffOn 𝕜 n (deriv f₂) s₂ :=
  by 
    rw [times_cont_diff_on_succ_iff_deriv_within hs.unique_diff_on]
    congr 2
    rw [←iff_iff_eq]
    apply times_cont_diff_on_congr 
    intro x hx 
    exact deriv_within_of_open hs hx

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (formulated with `deriv_within`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_deriv_within
(hs : unique_diff_on 𝕜 s₂) : «expr ↔ »(times_cont_diff_on 𝕜 «expr∞»() f₂ s₂, «expr ∧ »(differentiable_on 𝕜 f₂ s₂, times_cont_diff_on 𝕜 «expr∞»() (deriv_within f₂ s₂) s₂)) :=
begin
  split,
  { assume [binders (h)],
    refine [expr ⟨h.differentiable_on le_top, _⟩],
    apply [expr times_cont_diff_on_top.2 (λ n, ((times_cont_diff_on_succ_iff_deriv_within hs).1 _).2)],
    exact [expr h.of_le le_top] },
  { assume [binders (h)],
    refine [expr times_cont_diff_on_top.2 (λ n, _)],
    have [ident A] [":", expr «expr ≤ »((n : with_top exprℕ()), «expr∞»())] [":=", expr le_top],
    apply [expr ((times_cont_diff_on_succ_iff_deriv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le],
    exact [expr with_top.coe_le_coe.2 (nat.le_succ n)] }
end

/-- A function is `C^∞` on an open domain if and only if it is differentiable
there, and its derivative (formulated with `deriv`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_deriv_of_open (hs : IsOpen s₂) :
  TimesContDiffOn 𝕜 ∞ f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ TimesContDiffOn 𝕜 ∞ (deriv f₂) s₂ :=
  by 
    rw [times_cont_diff_on_top_iff_deriv_within hs.unique_diff_on]
    congr 2
    rw [←iff_iff_eq]
    apply times_cont_diff_on_congr 
    intro x hx 
    exact deriv_within_of_open hs hx

-- error in Analysis.Calculus.TimesContDiff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem times_cont_diff_on.deriv_within
{m n : with_top exprℕ()}
(hf : times_cont_diff_on 𝕜 n f₂ s₂)
(hs : unique_diff_on 𝕜 s₂)
(hmn : «expr ≤ »(«expr + »(m, 1), n)) : times_cont_diff_on 𝕜 m (deriv_within f₂ s₂) s₂ :=
begin
  cases [expr m] [],
  { change [expr «expr ≤ »(«expr + »(«expr∞»(), 1), n)] [] ["at", ident hmn],
    have [] [":", expr «expr = »(n, «expr∞»())] [],
    by simpa [] [] [] [] [] ["using", expr hmn],
    rw [expr this] ["at", ident hf],
    exact [expr ((times_cont_diff_on_top_iff_deriv_within hs).1 hf).2] },
  { change [expr «expr ≤ »((m.succ : with_top exprℕ()), n)] [] ["at", ident hmn],
    exact [expr ((times_cont_diff_on_succ_iff_deriv_within hs).1 (hf.of_le hmn)).2] }
end

theorem TimesContDiffOn.deriv_of_open {m n : WithTop ℕ} (hf : TimesContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂)
  (hmn : (m+1) ≤ n) : TimesContDiffOn 𝕜 m (deriv f₂) s₂ :=
  (hf.deriv_within hs.unique_diff_on hmn).congr fun x hx => (deriv_within_of_open hs hx).symm

theorem TimesContDiffOn.continuous_on_deriv_within {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f₂ s₂)
  (hs : UniqueDiffOn 𝕜 s₂) (hn : 1 ≤ n) : ContinuousOn (derivWithin f₂ s₂) s₂ :=
  ((times_cont_diff_on_succ_iff_deriv_within hs).1 (h.of_le hn)).2.ContinuousOn

theorem TimesContDiffOn.continuous_on_deriv_of_open {n : WithTop ℕ} (h : TimesContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂)
  (hn : 1 ≤ n) : ContinuousOn (deriv f₂) s₂ :=
  ((times_cont_diff_on_succ_iff_deriv_of_open hs).1 (h.of_le hn)).2.ContinuousOn

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative is `C^n`. -/
theorem times_cont_diff_succ_iff_deriv {n : ℕ} :
  TimesContDiff 𝕜 (n+1 : ℕ) f₂ ↔ Differentiable 𝕜 f₂ ∧ TimesContDiff 𝕜 n (deriv f₂) :=
  by 
    simp only [←times_cont_diff_on_univ, times_cont_diff_on_succ_iff_deriv_of_open, is_open_univ,
      differentiable_on_univ]

end deriv

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/


variable(𝕜){𝕜' : Type _}[NondiscreteNormedField 𝕜'][NormedAlgebra 𝕜 𝕜']

variable[NormedSpace 𝕜' E][IsScalarTower 𝕜 𝕜' E]

variable[NormedSpace 𝕜' F][IsScalarTower 𝕜 𝕜' F]

variable{p' : E → FormalMultilinearSeries 𝕜' E F}{n : WithTop ℕ}

theorem HasFtaylorSeriesUpToOn.restrict_scalars (h : HasFtaylorSeriesUpToOn n f p' s) :
  HasFtaylorSeriesUpToOn n f (fun x => (p' x).restrictScalars 𝕜) s :=
  { zero_eq := fun x hx => h.zero_eq x hx,
    fderivWithin :=
      by 
        intro m hm x hx 
        convert
          (ContinuousMultilinearMap.restrictScalarsLinear 𝕜).HasFderivAt.comp_has_fderiv_within_at _
            ((h.fderiv_within m hm x hx).restrictScalars 𝕜),
    cont := fun m hm => ContinuousMultilinearMap.continuous_restrict_scalars.comp_continuous_on (h.cont m hm) }

theorem TimesContDiffWithinAt.restrict_scalars (h : TimesContDiffWithinAt 𝕜' n f s x) :
  TimesContDiffWithinAt 𝕜 n f s x :=
  by 
    intro m hm 
    rcases h m hm with ⟨u, u_mem, p', hp'⟩
    exact ⟨u, u_mem, _, hp'.restrict_scalars _⟩

theorem TimesContDiffOn.restrict_scalars (h : TimesContDiffOn 𝕜' n f s) : TimesContDiffOn 𝕜 n f s :=
  fun x hx => (h x hx).restrictScalars _

theorem TimesContDiffAt.restrict_scalars (h : TimesContDiffAt 𝕜' n f x) : TimesContDiffAt 𝕜 n f x :=
  times_cont_diff_within_at_univ.1$ h.times_cont_diff_within_at.restrict_scalars _

theorem TimesContDiff.restrict_scalars (h : TimesContDiff 𝕜' n f) : TimesContDiff 𝕜 n f :=
  times_cont_diff_iff_times_cont_diff_at.2$ fun x => h.times_cont_diff_at.restrict_scalars _

end RestrictScalars

