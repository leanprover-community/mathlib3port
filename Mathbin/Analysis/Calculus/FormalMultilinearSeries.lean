import Mathbin.Analysis.NormedSpace.Multilinear

/-!
# Formal multilinear series

In this file we define `formal_multilinear_series 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `times_cont_diff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/


noncomputable theory

open Set Finₓ

open_locale TopologicalSpace

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

-- error in Analysis.Calculus.FormalMultilinearSeries: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler add_comm_group
/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[derive #[expr add_comm_group]]
def formal_multilinear_series
(𝕜 : Type*)
[nondiscrete_normed_field 𝕜]
(E : Type*)
[normed_group E]
[normed_space 𝕜 E]
(F : Type*)
[normed_group F]
[normed_space 𝕜 F] :=
∀ n : exprℕ(), «expr [× ]→L[ ] »(E, n, 𝕜, F)

instance : Inhabited (FormalMultilinearSeries 𝕜 E F) :=
  ⟨0⟩

section Module

attribute [local reducible] FormalMultilinearSeries

-- error in Analysis.Calculus.FormalMultilinearSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : module 𝕜 (formal_multilinear_series 𝕜 E F) :=
begin
  letI [] [":", expr ∀
   n, module 𝕜 (continuous_multilinear_map 𝕜 (λ i : fin n, E) F)] [":=", expr λ n, by apply_instance],
  apply_instance
end

end Module

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E →L[𝕜] F`. If `p` corresponds to the Taylor series of a function, then
`p.shift` is the Taylor series of the derivative of the function. -/
def shift : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) :=
  fun n => (p n.succ).curryRight

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series for the derivative of a function, and building a Taylor
series for the function itself. -/
def unshift (q : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) : FormalMultilinearSeries 𝕜 E F
| 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm z
| n+1 => continuousMultilinearCurryRightEquiv' 𝕜 n E F (q n)

/-- Killing the zeroth coefficient in a formal multilinear series -/
def remove_zero (p : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E F
| 0 => 0
| n+1 => p (n+1)

@[simp]
theorem remove_zero_coeff_zero : p.remove_zero 0 = 0 :=
  rfl

@[simp]
theorem remove_zero_coeff_succ (n : ℕ) : p.remove_zero (n+1) = p (n+1) :=
  rfl

theorem remove_zero_of_pos {n : ℕ} (h : 0 < n) : p.remove_zero n = p n :=
  by 
    rw [←Nat.succ_pred_eq_of_posₓ h]
    rfl

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
theorem congr (p : FormalMultilinearSeries 𝕜 E F) {m n : ℕ} {v : Finₓ m → E} {w : Finₓ n → E} (h1 : m = n)
  (h2 : ∀ i : ℕ him : i < m hin : i < n, v ⟨i, him⟩ = w ⟨i, hin⟩) : p m v = p n w :=
  by 
    cases h1 
    congr with ⟨i, hi⟩
    exact h2 i hi hi

/-- Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.comp_continuous_linear_map u`. -/
def comp_continuous_linear_map (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) : FormalMultilinearSeries 𝕜 E G :=
  fun n => (p n).compContinuousLinearMap fun i : Finₓ n => u

@[simp]
theorem comp_continuous_linear_map_apply (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ) (v : Finₓ n → E) :
  (p.comp_continuous_linear_map u) n v = p n (u ∘ v) :=
  rfl

variable (𝕜) {𝕜' : Type _} [NondiscreteNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series, where `𝕜'` is a
normed algebra over `𝕜`. -/
@[simp]
protected def RestrictScalars (p : FormalMultilinearSeries 𝕜' E F) : FormalMultilinearSeries 𝕜 E F :=
  fun n => (p n).restrictScalars 𝕜

end FormalMultilinearSeries

