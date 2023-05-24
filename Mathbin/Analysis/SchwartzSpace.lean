/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll

! This file was ported from Lean 3 source module analysis.schwartz_space
! leanprover-community/mathlib commit 0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.Analysis.Calculus.IteratedDeriv
import Mathbin.Analysis.LocallyConvex.WithSeminorms
import Mathbin.Topology.Algebra.UniformFilterBasis
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Tactic.Positivity
import Mathbin.Analysis.SpecialFunctions.Pow.Real

/-!
# Schwartz space

This file defines the Schwartz space. Usually, the Schwartz space is defined as the set of smooth
functions $f : ℝ^n → ℂ$ such that there exists $C_{αβ} > 0$ with $$|x^α ∂^β f(x)| < C_{αβ}$$ for
all $x ∈ ℝ^n$ and for all multiindices $α, β$.
In mathlib, we use a slightly different approach and define define the Schwartz space as all
smooth functions `f : E → F`, where `E` and `F` are real normed vector spaces such that for all
natural numbers `k` and `n` we have uniform bounds `‖x‖^k * ‖iterated_fderiv ℝ n f x‖ < C`.
This approach completely avoids using partial derivatives as well as polynomials.
We construct the topology on the Schwartz space by a family of seminorms, which are the best
constants in the above estimates. The abstract theory of topological vector spaces developed in
`seminorm_family.module_filter_basis` and `with_seminorms.to_locally_convex_space` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `schwartz_map`: The Schwartz space is the space of smooth functions such that all derivatives
decay faster than any power of `‖x‖`.
* `schwartz_map.seminorm`: The family of seminorms as described above
* `schwartz_map.fderiv_clm`: The differential as a continuous linear map
`𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`
* `schwartz_map.deriv_clm`: The one-dimensional derivative as a continuous linear map
`𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F)`

## Main statements

* `schwartz_map.uniform_add_group` and `schwartz_map.locally_convex`: The Schwartz space is a
locally convex topological vector space.
* `schwartz_map.one_add_le_sup_seminorm_apply`: For a Schwartz function `f` there is a uniform bound
on `(1 + ‖x‖) ^ k * ‖iterated_fderiv ℝ n f x‖`.

## Implementation details

The implementation of the seminorms is taken almost literally from `continuous_linear_map.op_norm`.

## Notation

* `𝓢(E, F)`: The Schwartz space `schwartz_map E F` localized in `schwartz_space`

## Tags

Schwartz space, tempered distributions
-/


noncomputable section

variable {𝕜 𝕜' D E F G : Type _}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E F)

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of `‖x‖`. -/
structure SchwartzMap where
  toFun : E → F
  smooth' : ContDiff ℝ ⊤ to_fun
  decay' : ∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n to_fun x‖ ≤ C
#align schwartz_map SchwartzMap

-- mathport name: «expr𝓢( , )»
scoped[SchwartzSpace] notation "𝓢(" E ", " F ")" => SchwartzMap E F

variable {E F}

namespace SchwartzMap

instance : Coe 𝓢(E, F) (E → F) :=
  ⟨toFun⟩

instance funLike : FunLike 𝓢(E, F) E fun _ => F
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
#align schwartz_map.fun_like SchwartzMap.funLike

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun 𝓢(E, F) fun _ => E → F :=
  ⟨fun p => p.toFun⟩

/-- All derivatives of a Schwartz function are rapidly decaying. -/
theorem decay (f : 𝓢(E, F)) (k n : ℕ) :
    ∃ (C : ℝ)(hC : 0 < C), ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ C :=
  by
  rcases f.decay' k n with ⟨C, hC⟩
  exact ⟨max C 1, by positivity, fun x => (hC x).trans (le_max_left _ _)⟩
#align schwartz_map.decay SchwartzMap.decay

/-- Every Schwartz function is smooth. -/
theorem smooth (f : 𝓢(E, F)) (n : ℕ∞) : ContDiff ℝ n f :=
  f.smooth'.of_le le_top
#align schwartz_map.smooth SchwartzMap.smooth

/-- Every Schwartz function is continuous. -/
@[continuity, protected]
theorem continuous (f : 𝓢(E, F)) : Continuous f :=
  (f.smooth 0).Continuous
#align schwartz_map.continuous SchwartzMap.continuous

/-- Every Schwartz function is differentiable. -/
@[protected]
theorem differentiable (f : 𝓢(E, F)) : Differentiable ℝ f :=
  (f.smooth 1).Differentiable rfl.le
#align schwartz_map.differentiable SchwartzMap.differentiable

/-- Every Schwartz function is differentiable at any point. -/
@[protected]
theorem differentiableAt (f : 𝓢(E, F)) {x : E} : DifferentiableAt ℝ f x :=
  f.Differentiable.DifferentiableAt
#align schwartz_map.differentiable_at SchwartzMap.differentiableAt

@[ext]
theorem ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g :=
  FunLike.ext f g h
#align schwartz_map.ext SchwartzMap.ext

section IsO

variable (f : 𝓢(E, F))

/-- Auxiliary lemma, used in proving the more general result `is_O_cocompact_zpow`. -/
theorem isBigO_cocompact_zpow_neg_nat (k : ℕ) :
    Asymptotics.IsBigO (Filter.cocompact E) f fun x => ‖x‖ ^ (-k : ℤ) :=
  by
  obtain ⟨d, hd, hd'⟩ := f.decay k 0
  simp_rw [norm_iteratedFderiv_zero] at hd'
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine' ⟨d, Filter.Eventually.filter_mono Filter.cocompact_le_cofinite _⟩
  refine' (Filter.eventually_cofinite_ne 0).mp (Filter.eventually_of_forall fun x hx => _)
  rwa [Real.norm_of_nonneg (zpow_nonneg (norm_nonneg _) _), zpow_neg, ← div_eq_mul_inv, le_div_iff']
  exacts[hd' x, zpow_pos_of_pos (norm_pos_iff.mpr hx) _]
#align schwartz_map.is_O_cocompact_zpow_neg_nat SchwartzMap.isBigO_cocompact_zpow_neg_nat

theorem isBigO_cocompact_rpow [ProperSpace E] (s : ℝ) :
    Asymptotics.IsBigO (Filter.cocompact E) f fun x => ‖x‖ ^ s :=
  by
  let k := ⌈-s⌉₊
  have hk : -(k : ℝ) ≤ s := neg_le.mp (Nat.le_ceil (-s))
  refine' (is_O_cocompact_zpow_neg_nat f k).trans _
  refine'
    (_ :
          Asymptotics.IsBigO Filter.atTop (fun x : ℝ => x ^ (-k : ℤ)) fun x : ℝ =>
            x ^ s).comp_tendsto
      tendsto_norm_cocompact_atTop
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine' ⟨1, Filter.eventually_of_mem (Filter.eventually_ge_atTop 1) fun x hx => _⟩
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg_of_nonneg (zero_le_one.trans hx) _),
    Real.norm_of_nonneg (zpow_nonneg (zero_le_one.trans hx) _), ← Real.rpow_int_cast, Int.cast_neg,
    Int.cast_ofNat]
  exact Real.rpow_le_rpow_of_exponent_le hx hk
#align schwartz_map.is_O_cocompact_rpow SchwartzMap.isBigO_cocompact_rpow

theorem isBigO_cocompact_zpow [ProperSpace E] (k : ℤ) :
    Asymptotics.IsBigO (Filter.cocompact E) f fun x => ‖x‖ ^ k := by
  simpa only [Real.rpow_int_cast] using is_O_cocompact_rpow f k
#align schwartz_map.is_O_cocompact_zpow SchwartzMap.isBigO_cocompact_zpow

end IsO

section Aux

theorem bounds_nonempty (k n : ℕ) (f : 𝓢(E, F)) :
    ∃ c : ℝ, c ∈ { c : ℝ | 0 ≤ c ∧ ∀ x : E, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ c } :=
  let ⟨M, hMp, hMb⟩ := f.decay k n
  ⟨M, le_of_lt hMp, hMb⟩
#align schwartz_map.bounds_nonempty SchwartzMap.bounds_nonempty

theorem bounds_bddBelow (k n : ℕ) (f : 𝓢(E, F)) :
    BddBelow { c | 0 ≤ c ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ c } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
#align schwartz_map.bounds_bdd_below SchwartzMap.bounds_bddBelow

theorem decay_add_le_aux (k n : ℕ) (f g : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFderiv ℝ n (f + g) x‖ ≤
      ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ + ‖x‖ ^ k * ‖iteratedFderiv ℝ n g x‖ :=
  by
  rw [← mul_add]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  convert norm_add_le _ _
  exact iteratedFderiv_add_apply (f.smooth _) (g.smooth _)
#align schwartz_map.decay_add_le_aux SchwartzMap.decay_add_le_aux

theorem decay_neg_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFderiv ℝ n (-f) x‖ = ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ :=
  by
  nth_rw 4 [← norm_neg]
  congr
  exact iteratedFderiv_neg_apply
#align schwartz_map.decay_neg_aux SchwartzMap.decay_neg_aux

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

theorem decay_smul_aux (k n : ℕ) (f : 𝓢(E, F)) (c : 𝕜) (x : E) :
    ‖x‖ ^ k * ‖iteratedFderiv ℝ n (c • f) x‖ = ‖c‖ * ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ := by
  rw [mul_comm ‖c‖, mul_assoc, iteratedFderiv_const_smul_apply (f.smooth _), norm_smul]
#align schwartz_map.decay_smul_aux SchwartzMap.decay_smul_aux

end Aux

section SeminormAux

/-- Helper definition for the seminorms of the Schwartz space. -/
@[protected]
def seminormAux (k n : ℕ) (f : 𝓢(E, F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ c }
#align schwartz_map.seminorm_aux SchwartzMap.seminormAux

theorem seminormAux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminormAux k n :=
  le_csInf (bounds_nonempty k n f) fun _ ⟨hx, _⟩ => hx
#align schwartz_map.seminorm_aux_nonneg SchwartzMap.seminormAux_nonneg

theorem le_seminormAux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFderiv ℝ n (⇑f) x‖ ≤ f.seminormAux k n :=
  le_csInf (bounds_nonempty k n f) fun y ⟨_, h⟩ => h x
#align schwartz_map.le_seminorm_aux SchwartzMap.le_seminormAux

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem seminormAux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ M) : f.seminormAux k n ≤ M :=
  csInf_le (bounds_bddBelow k n f) ⟨hMp, hM⟩
#align schwartz_map.seminorm_aux_le_bound SchwartzMap.seminormAux_le_bound

end SeminormAux

/-! ### Algebraic properties -/


section Smul

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [NormedField 𝕜'] [NormedSpace 𝕜' F]
  [SMulCommClass ℝ 𝕜' F]

instance : SMul 𝕜 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • f
      smooth' := (f.smooth _).const_smul c
      decay' := fun k n =>
        by
        refine' ⟨f.seminorm_aux k n * (‖c‖ + 1), fun x => _⟩
        have hc : 0 ≤ ‖c‖ := by positivity
        refine' le_trans _ ((mul_le_mul_of_nonneg_right (f.le_seminorm_aux k n x) hc).trans _)
        · apply Eq.le
          rw [mul_comm _ ‖c‖, ← mul_assoc]
          exact decay_smul_aux k n f c x
        · apply mul_le_mul_of_nonneg_left _ (f.seminorm_aux_nonneg k n)
          linarith }⟩

@[simp]
theorem smul_apply {f : 𝓢(E, F)} {c : 𝕜} {x : E} : (c • f) x = c • f x :=
  rfl
#align schwartz_map.smul_apply SchwartzMap.smul_apply

instance [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' F] : IsScalarTower 𝕜 𝕜' 𝓢(E, F) :=
  ⟨fun a b f => ext fun x => smul_assoc a b (f x)⟩

instance [SMulCommClass 𝕜 𝕜' F] : SMulCommClass 𝕜 𝕜' 𝓢(E, F) :=
  ⟨fun a b f => ext fun x => smul_comm a b (f x)⟩

theorem seminormAux_smul_le (k n : ℕ) (c : 𝕜) (f : 𝓢(E, F)) :
    (c • f).seminormAux k n ≤ ‖c‖ * f.seminormAux k n :=
  by
  refine'
    (c • f).seminormAux_le_bound k n (mul_nonneg (norm_nonneg _) (seminorm_aux_nonneg _ _ _))
      fun x => (decay_smul_aux k n f c x).le.trans _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (f.le_seminorm_aux k n x) (norm_nonneg _)
#align schwartz_map.seminorm_aux_smul_le SchwartzMap.seminormAux_smul_le

instance hasNsmul : SMul ℕ 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • f
      smooth' := (f.smooth _).const_smul c
      decay' :=
        by
        have : c • (f : E → F) = (c : ℝ) • f := by
          ext x
          simp only [Pi.smul_apply, ← nsmul_eq_smul_cast]
        simp only [this]
        exact ((c : ℝ) • f).decay' }⟩
#align schwartz_map.has_nsmul SchwartzMap.hasNsmul

instance hasZsmul : SMul ℤ 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • f
      smooth' := (f.smooth _).const_smul c
      decay' :=
        by
        have : c • (f : E → F) = (c : ℝ) • f := by
          ext x
          simp only [Pi.smul_apply, ← zsmul_eq_smul_cast]
        simp only [this]
        exact ((c : ℝ) • f).decay' }⟩
#align schwartz_map.has_zsmul SchwartzMap.hasZsmul

end Smul

section Zero

instance : Zero 𝓢(E, F) :=
  ⟨{  toFun := fun _ => 0
      smooth' := contDiff_const
      decay' := fun _ _ => ⟨1, fun _ => by simp⟩ }⟩

instance : Inhabited 𝓢(E, F) :=
  ⟨0⟩

theorem coe_zero : ↑(0 : 𝓢(E, F)) = (0 : E → F) :=
  rfl
#align schwartz_map.coe_zero SchwartzMap.coe_zero

@[simp]
theorem coeFn_zero : coeFn (0 : 𝓢(E, F)) = (0 : E → F) :=
  rfl
#align schwartz_map.coe_fn_zero SchwartzMap.coeFn_zero

@[simp]
theorem zero_apply {x : E} : (0 : 𝓢(E, F)) x = 0 :=
  rfl
#align schwartz_map.zero_apply SchwartzMap.zero_apply

theorem seminormAux_zero (k n : ℕ) : (0 : 𝓢(E, F)).seminormAux k n = 0 :=
  le_antisymm (seminormAux_le_bound k n _ rfl.le fun _ => by simp [Pi.zero_def])
    (seminormAux_nonneg _ _ _)
#align schwartz_map.seminorm_aux_zero SchwartzMap.seminormAux_zero

end Zero

section Neg

instance : Neg 𝓢(E, F) :=
  ⟨fun f =>
    ⟨-f, (f.smooth _).neg, fun k n =>
      ⟨f.seminormAux k n, fun x => (decay_neg_aux k n f x).le.trans (f.le_seminormAux k n x)⟩⟩⟩

end Neg

section Add

instance : Add 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f + g, (f.smooth _).add (g.smooth _), fun k n =>
      ⟨f.seminormAux k n + g.seminormAux k n, fun x =>
        (decay_add_le_aux k n f g x).trans
          (add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x))⟩⟩⟩

@[simp]
theorem add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x :=
  rfl
#align schwartz_map.add_apply SchwartzMap.add_apply

theorem seminormAux_add_le (k n : ℕ) (f g : 𝓢(E, F)) :
    (f + g).seminormAux k n ≤ f.seminormAux k n + g.seminormAux k n :=
  (f + g).seminormAux_le_bound k n
    (add_nonneg (seminormAux_nonneg _ _ _) (seminormAux_nonneg _ _ _)) fun x =>
    (decay_add_le_aux k n f g x).trans <|
      add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x)
#align schwartz_map.seminorm_aux_add_le SchwartzMap.seminormAux_add_le

end Add

section Sub

instance : Sub 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f - g, (f.smooth _).sub (g.smooth _), by
      intro k n
      refine' ⟨f.seminorm_aux k n + g.seminorm_aux k n, fun x => _⟩
      refine' le_trans _ (add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x))
      rw [sub_eq_add_neg]
      rw [← decay_neg_aux k n g x]
      convert decay_add_le_aux k n f (-g) x⟩⟩

-- exact fails with deterministic timeout
@[simp]
theorem sub_apply {f g : 𝓢(E, F)} {x : E} : (f - g) x = f x - g x :=
  rfl
#align schwartz_map.sub_apply SchwartzMap.sub_apply

end Sub

section AddCommGroup

instance : AddCommGroup 𝓢(E, F) :=
  FunLike.coe_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓢(E, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl
#align schwartz_map.coe_hom SchwartzMap.coeHom

variable {E F}

theorem coe_coeHom : (coeHom E F : 𝓢(E, F) → E → F) = coeFn :=
  rfl
#align schwartz_map.coe_coe_hom SchwartzMap.coe_coeHom

theorem coeHom_injective : Function.Injective (coeHom E F) :=
  by
  rw [coe_coe_hom]
  exact FunLike.coe_injective
#align schwartz_map.coe_hom_injective SchwartzMap.coeHom_injective

end AddCommGroup

section Module

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

instance : Module 𝕜 𝓢(E, F) :=
  coeHom_injective.Module 𝕜 (coeHom E F) fun _ _ => rfl

end Module

section Seminorms

/-! ### Seminorms on Schwartz space-/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜)

/-- The seminorms of the Schwartz space given by the best constants in the definition of
`𝓢(E, F)`. -/
@[protected]
def seminorm (k n : ℕ) : Seminorm 𝕜 𝓢(E, F) :=
  Seminorm.ofSMulLE (seminormAux k n) (seminormAux_zero k n) (seminormAux_add_le k n)
    (seminormAux_smul_le k n)
#align schwartz_map.seminorm SchwartzMap.seminorm

/-- If one controls the seminorm for every `x`, then one controls the seminorm. -/
theorem seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ M) : Seminorm 𝕜 k n f ≤ M :=
  f.seminormAux_le_bound k n hMp hM
#align schwartz_map.seminorm_le_bound SchwartzMap.seminorm_le_bound

/-- If one controls the seminorm for every `x`, then one controls the seminorm.

Variant for functions `𝓢(ℝ, F)`. -/
theorem seminorm_le_bound' (k n : ℕ) (f : 𝓢(ℝ, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, |x| ^ k * ‖iteratedDeriv n f x‖ ≤ M) : Seminorm 𝕜 k n f ≤ M :=
  by
  refine' seminorm_le_bound 𝕜 k n f hMp _
  simpa only [Real.norm_eq_abs, norm_iteratedFderiv_eq_norm_iteratedDeriv]
#align schwartz_map.seminorm_le_bound' SchwartzMap.seminorm_le_bound'

/-- The seminorm controls the Schwartz estimate for any fixed `x`. -/
theorem le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ Seminorm 𝕜 k n f :=
  f.le_seminormAux k n x
#align schwartz_map.le_seminorm SchwartzMap.le_seminorm

/-- The seminorm controls the Schwartz estimate for any fixed `x`.

Variant for functions `𝓢(ℝ, F)`. -/
theorem le_seminorm' (k n : ℕ) (f : 𝓢(ℝ, F)) (x : ℝ) :
    |x| ^ k * ‖iteratedDeriv n f x‖ ≤ Seminorm 𝕜 k n f :=
  by
  have := le_seminorm 𝕜 k n f x
  rwa [← Real.norm_eq_abs, ← norm_iteratedFderiv_eq_norm_iteratedDeriv]
#align schwartz_map.le_seminorm' SchwartzMap.le_seminorm'

theorem norm_iteratedFderiv_le_seminorm (f : 𝓢(E, F)) (n : ℕ) (x₀ : E) :
    ‖iteratedFderiv ℝ n f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 0 n) f :=
  by
  have := SchwartzMap.le_seminorm 𝕜 0 n f x₀
  rwa [pow_zero, one_mul] at this
#align schwartz_map.norm_iterated_fderiv_le_seminorm SchwartzMap.norm_iteratedFderiv_le_seminorm

theorem norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : ℕ) (x₀ : E) :
    ‖x₀‖ ^ k * ‖f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 k 0) f :=
  by
  have := SchwartzMap.le_seminorm 𝕜 k 0 f x₀
  rwa [norm_iteratedFderiv_zero] at this
#align schwartz_map.norm_pow_mul_le_seminorm SchwartzMap.norm_pow_mul_le_seminorm

theorem norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : ‖f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 0 0) f :=
  by
  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀
  rwa [pow_zero, one_mul] at this
#align schwartz_map.norm_le_seminorm SchwartzMap.norm_le_seminorm

variable (𝕜 E F)

/-- The family of Schwartz seminorms. -/
def schwartzSeminormFamily : SeminormFamily 𝕜 𝓢(E, F) (ℕ × ℕ) := fun m => Seminorm 𝕜 m.1 m.2
#align schwartz_seminorm_family schwartzSeminormFamily

@[simp]
theorem schwartzSeminormFamily_apply (n k : ℕ) :
    schwartzSeminormFamily 𝕜 E F (n, k) = SchwartzMap.seminorm 𝕜 n k :=
  rfl
#align schwartz_map.schwartz_seminorm_family_apply SchwartzMap.schwartzSeminormFamily_apply

@[simp]
theorem schwartzSeminormFamily_apply_zero :
    schwartzSeminormFamily 𝕜 E F 0 = SchwartzMap.seminorm 𝕜 0 0 :=
  rfl
#align schwartz_map.schwartz_seminorm_family_apply_zero SchwartzMap.schwartzSeminormFamily_apply_zero

variable {𝕜 E F}

/-- A more convenient version of `le_sup_seminorm_apply`.

The set `finset.Iic m` is the set of all pairs `(k', n')` with `k' ≤ m.1` and `n' ≤ m.2`.
Note that the constant is far from optimal. -/
theorem one_add_le_sup_seminorm_apply {m : ℕ × ℕ} {k n : ℕ} (hk : k ≤ m.1) (hn : n ≤ m.2)
    (f : 𝓢(E, F)) (x : E) :
    (1 + ‖x‖) ^ k * ‖iteratedFderiv ℝ n f x‖ ≤
      2 ^ m.1 * (Finset.Iic m).sup (fun m => Seminorm 𝕜 m.1 m.2) f :=
  by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, Finset.sum_congr, Finset.sum_mul]
  norm_cast
  rw [← Nat.sum_range_choose m.1]
  push_cast
  rw [Finset.sum_mul]
  have hk' : Finset.range (k + 1) ⊆ Finset.range (m.1 + 1) := by
    rwa [Finset.range_subset, add_le_add_iff_right]
  refine' le_trans (Finset.sum_le_sum_of_subset_of_nonneg hk' fun _ _ _ => by positivity) _
  refine' Finset.sum_le_sum fun i hi => _
  rw [mul_comm (‖x‖ ^ i), mul_assoc]
  refine' mul_le_mul _ _ (by positivity) (by positivity)
  · norm_cast
    exact i.choose_le_choose hk
  exact
    (le_seminorm 𝕜 i n f x).trans
      (Seminorm.le_def.1
        (Finset.le_sup_of_le
          (Finset.mem_Iic.2 <| Prod.mk_le_mk.2 ⟨finset.mem_range_succ_iff.mp hi, hn⟩) le_rfl)
        _)
#align schwartz_map.one_add_le_sup_seminorm_apply SchwartzMap.one_add_le_sup_seminorm_apply

end Seminorms

section Topology

/-! ### The topology on the Schwartz space-/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜 E F)

instance : TopologicalSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).ModuleFilterBasis.topology'

theorem schwartz_withSeminorms : WithSeminorms (schwartzSeminormFamily 𝕜 E F) :=
  by
  have A : WithSeminorms (schwartzSeminormFamily ℝ E F) := ⟨rfl⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at A⊢
  rw [A]
  rfl
#align schwartz_with_seminorms schwartz_withSeminorms

variable {𝕜 E F}

instance : ContinuousSMul 𝕜 𝓢(E, F) :=
  by
  rw [(schwartz_withSeminorms 𝕜 E F).withSeminorms_eq]
  exact (schwartzSeminormFamily 𝕜 E F).ModuleFilterBasis.ContinuousSMul

instance : TopologicalAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).AddGroupFilterBasis.isTopologicalAddGroup

instance : UniformSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).AddGroupFilterBasis.UniformSpace

instance : UniformAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).AddGroupFilterBasis.UniformAddGroup

instance : LocallyConvexSpace ℝ 𝓢(E, F) :=
  (schwartz_withSeminorms ℝ E F).toLocallyConvexSpace

instance : TopologicalSpace.FirstCountableTopology 𝓢(E, F) :=
  (schwartz_withSeminorms ℝ E F).first_countable

end Topology

section Clm

/-! ### Construction of continuous linear maps between Schwartz spaces -/


variable [NormedField 𝕜] [NormedField 𝕜']

variable [NormedAddCommGroup D] [NormedSpace ℝ D]

variable [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]

variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]

variable {σ : 𝕜 →+* 𝕜'}

/-- Create a semilinear map between Schwartz spaces.

Note: This is a helper definition for `mk_clm`. -/
def mkLm (A : (D → E) → F → G) (hadd : ∀ (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
    (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : ∀ f : 𝓢(D, E), ContDiff ℝ ⊤ (A f))
    (hbound :
      ∀ n : ℕ × ℕ,
        ∃ (s : Finset (ℕ × ℕ))(C : ℝ)(hC : 0 ≤ C),
          ∀ (f : 𝓢(D, E)) (x : F),
            ‖x‖ ^ n.fst * ‖iteratedFderiv ℝ n.snd (A f) x‖ ≤
              C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) →ₛₗ[σ] 𝓢(F, G)
    where
  toFun f :=
    { toFun := A f
      smooth' := hsmooth f
      decay' := by
        intro k n
        rcases hbound ⟨k, n⟩ with ⟨s, C, hC, h⟩
        exact ⟨C * (s.sup (schwartzSeminormFamily 𝕜 D E)) f, h f⟩ }
  map_add' f g := ext (hadd f g)
  map_smul' a f := ext (hsmul a f)
#align schwartz_map.mk_lm SchwartzMap.mkLm

/-- Create a continuous semilinear map between Schwartz spaces.

For an example of using this definition, see `fderiv_clm`. -/
def mkClm [RingHomIsometric σ] (A : (D → E) → F → G)
    (hadd : ∀ (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
    (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : ∀ f : 𝓢(D, E), ContDiff ℝ ⊤ (A f))
    (hbound :
      ∀ n : ℕ × ℕ,
        ∃ (s : Finset (ℕ × ℕ))(C : ℝ)(hC : 0 ≤ C),
          ∀ (f : 𝓢(D, E)) (x : F),
            ‖x‖ ^ n.fst * ‖iteratedFderiv ℝ n.snd (A f) x‖ ≤
              C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) →SL[σ] 𝓢(F, G)
    where
  cont := by
    change Continuous (mk_lm A hadd hsmul hsmooth hbound : 𝓢(D, E) →ₛₗ[σ] 𝓢(F, G))
    refine'
      Seminorm.continuous_from_bounded (schwartz_withSeminorms 𝕜 D E)
        (schwartz_withSeminorms 𝕜' F G) _ fun n => _
    rcases hbound n with ⟨s, C, hC, h⟩
    refine' ⟨s, ⟨C, hC⟩, fun f => _⟩
    simp only [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, Algebra.id.smul_eq_mul,
      Subtype.coe_mk]
    exact (mk_lm A hadd hsmul hsmooth hbound f).seminorm_le_bound 𝕜' n.1 n.2 (by positivity) (h f)
  toLinearMap := mkLm A hadd hsmul hsmooth hbound
#align schwartz_map.mk_clm SchwartzMap.mkClm

end Clm

section Derivatives

/-! ### Derivatives of Schwartz functions -/


variable (𝕜)

variable [IsROrC 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The Fréchet derivative on Schwartz space as a continuous `𝕜`-linear map. -/
def fderivClm : 𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F) :=
  mkClm (fderiv ℝ) (fun f g _ => fderiv_add f.DifferentiableAt g.DifferentiableAt)
    (fun a f _ => fderiv_const_smul f.DifferentiableAt a)
    (fun f => (contDiff_top_iff_fderiv.mp f.smooth').2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [schwartz_seminorm_family_apply, Seminorm.comp_apply, Finset.sup_singleton,
        one_smul, norm_iteratedFderiv_fderiv, one_mul] using f.le_seminorm 𝕜 k (n + 1) x⟩
#align schwartz_map.fderiv_clm SchwartzMap.fderivClm

@[simp]
theorem fderivClm_apply (f : 𝓢(E, F)) (x : E) : fderivClm 𝕜 f x = fderiv ℝ f x :=
  rfl
#align schwartz_map.fderiv_clm_apply SchwartzMap.fderivClm_apply

/-- The 1-dimensional derivative on Schwartz space as a continuous `𝕜`-linear map. -/
def derivClm : 𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F) :=
  mkClm (fun f => deriv f) (fun f g _ => deriv_add f.DifferentiableAt g.DifferentiableAt)
    (fun a f _ => deriv_const_smul a f.DifferentiableAt)
    (fun f => (contDiff_top_iff_deriv.mp f.smooth').2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [Real.norm_eq_abs, Finset.sup_singleton, schwartz_seminorm_family_apply, one_mul,
        norm_iteratedFderiv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ'] using
        f.le_seminorm' 𝕜 k (n + 1) x⟩
#align schwartz_map.deriv_clm SchwartzMap.derivClm

@[simp]
theorem derivClm_apply (f : 𝓢(ℝ, F)) (x : ℝ) : derivClm 𝕜 f x = deriv f x :=
  rfl
#align schwartz_map.deriv_clm_apply SchwartzMap.derivClm_apply

end Derivatives

section BoundedContinuousFunction

/-! ### Inclusion into the space of bounded continuous functions -/


open BoundedContinuousFunction

/-- Schwartz functions as bounded continuous functions -/
def toBoundedContinuousFunction (f : 𝓢(E, F)) : E →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f (SchwartzMap.continuous f)
    (SchwartzMap.seminorm ℝ 0 0 f) (norm_le_seminorm ℝ f)
#align schwartz_map.to_bounded_continuous_function SchwartzMap.toBoundedContinuousFunction

@[simp]
theorem toBoundedContinuousFunction_apply (f : 𝓢(E, F)) (x : E) :
    f.toBoundedContinuousFunction x = f x :=
  rfl
#align schwartz_map.to_bounded_continuous_function_apply SchwartzMap.toBoundedContinuousFunction_apply

/-- Schwartz functions as continuous functions -/
def toContinuousMap (f : 𝓢(E, F)) : C(E, F) :=
  f.toBoundedContinuousFunction.toContinuousMap
#align schwartz_map.to_continuous_map SchwartzMap.toContinuousMap

variable (𝕜 E F)

variable [IsROrC 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The inclusion map from Schwartz functions to bounded continuous functions as a linear map. -/
def toBoundedContinuousFunctionLm : 𝓢(E, F) →ₗ[𝕜] E →ᵇ F
    where
  toFun f := f.toBoundedContinuousFunction
  map_add' f g := by
    ext
    exact add_apply
  map_smul' a f := by
    ext
    exact smul_apply
#align schwartz_map.to_bounded_continuous_function_lm SchwartzMap.toBoundedContinuousFunctionLm

@[simp]
theorem toBoundedContinuousFunctionLm_apply (f : 𝓢(E, F)) (x : E) :
    toBoundedContinuousFunctionLm 𝕜 E F f x = f x :=
  rfl
#align schwartz_map.to_bounded_continuous_function_lm_apply SchwartzMap.toBoundedContinuousFunctionLm_apply

/-- The inclusion map from Schwartz functions to bounded continuous functions as a continuous linear
map. -/
def toBoundedContinuousFunctionClm : 𝓢(E, F) →L[𝕜] E →ᵇ F :=
  { toBoundedContinuousFunctionLm 𝕜 E F with
    cont := by
      change Continuous (to_bounded_continuous_function_lm 𝕜 E F)
      refine'
        Seminorm.continuous_from_bounded (schwartz_withSeminorms 𝕜 E F)
          (norm_withSeminorms 𝕜 (E →ᵇ F)) _ fun i => ⟨{0}, 1, fun f => _⟩
      rw [Finset.sup_singleton, one_smul, Seminorm.comp_apply, coe_normSeminorm,
        schwartz_seminorm_family_apply_zero, BoundedContinuousFunction.norm_le (map_nonneg _ _)]
      intro x
      exact norm_le_seminorm 𝕜 _ _ }
#align schwartz_map.to_bounded_continuous_function_clm SchwartzMap.toBoundedContinuousFunctionClm

@[simp]
theorem toBoundedContinuousFunctionClm_apply (f : 𝓢(E, F)) (x : E) :
    toBoundedContinuousFunctionClm 𝕜 E F f x = f x :=
  rfl
#align schwartz_map.to_bounded_continuous_function_clm_apply SchwartzMap.toBoundedContinuousFunctionClm_apply

variable {E}

/-- The Dirac delta distribution -/
def delta (x : E) : 𝓢(E, F) →L[𝕜] F :=
  (BoundedContinuousFunction.evalClm 𝕜 x).comp (toBoundedContinuousFunctionClm 𝕜 E F)
#align schwartz_map.delta SchwartzMap.delta

@[simp]
theorem delta_apply (x₀ : E) (f : 𝓢(E, F)) : delta 𝕜 F x₀ f = f x₀ :=
  rfl
#align schwartz_map.delta_apply SchwartzMap.delta_apply

end BoundedContinuousFunction

end SchwartzMap

