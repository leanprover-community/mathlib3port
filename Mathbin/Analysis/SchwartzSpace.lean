/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll

! This file was ported from Lean 3 source module analysis.schwartz_space
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.Analysis.LocallyConvex.WithSeminorms
import Mathbin.Topology.Algebra.UniformFilterBasis
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Tactic.Positivity

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
constants in the above estimates, which is by abstract theory from
`seminorm_family.module_filter_basis` and `with_seminorms.to_locally_convex_space` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `schwartz_map`: The Schwartz space is the space of smooth functions such that all derivatives
decay faster than any power of `‖x‖`.
* `schwartz_map.seminorm`: The family of seminorms as described above
* `schwartz_map.fderiv_clm`: The differential as a continuous linear map
`𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`

## Main statements

* `schwartz_map.uniform_add_group` and `schwartz_map.locally_convex`: The Schwartz space is a
locally convex topological vector space.

## Implementation details

The implementation of the seminorms is taken almost literally from `continuous_linear_map.op_norm`.

## Notation

* `𝓢(E, F)`: The Schwartz space `schwartz_map E F` localized in `schwartz_space`

## Tags

Schwartz space, tempered distributions
-/


noncomputable section

variable {𝕜 𝕜' E F : Type _}

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

@[ext]
theorem ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g :=
  FunLike.ext f g h
#align schwartz_map.ext SchwartzMap.ext

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
  infₛ { c | 0 ≤ c ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ c }
#align schwartz_map.seminorm_aux SchwartzMap.seminormAux

theorem seminormAux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminormAux k n :=
  le_cinfₛ (bounds_nonempty k n f) fun _ ⟨hx, _⟩ => hx
#align schwartz_map.seminorm_aux_nonneg SchwartzMap.seminormAux_nonneg

theorem le_seminormAux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFderiv ℝ n (⇑f) x‖ ≤ f.seminormAux k n :=
  le_cinfₛ (bounds_nonempty k n f) fun y ⟨_, h⟩ => h x
#align schwartz_map.le_seminorm_aux SchwartzMap.le_seminormAux

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem seminormAux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ M) : f.seminormAux k n ≤ M :=
  cinfₛ_le (bounds_bddBelow k n f) ⟨hMp, hM⟩
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
  Seminorm.ofSmulLe (seminormAux k n) (seminormAux_zero k n) (seminormAux_add_le k n)
    (seminormAux_smul_le k n)
#align schwartz_map.seminorm SchwartzMap.seminorm

/-- If one controls the seminorm for every `x`, then one controls the seminorm. -/
theorem seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ M) : Seminorm 𝕜 k n f ≤ M :=
  f.seminormAux_le_bound k n hMp hM
#align schwartz_map.seminorm_le_bound SchwartzMap.seminorm_le_bound

/-- The seminorm controls the Schwartz estimate for any fixed `x`. -/
theorem le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFderiv ℝ n f x‖ ≤ Seminorm 𝕜 k n f :=
  f.le_seminormAux k n x
#align schwartz_map.le_seminorm SchwartzMap.le_seminorm

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

end Seminorms

section Topology

/-! ### The topology on the Schwartz space-/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜 E F)

/-- The family of Schwartz seminorms. -/
def schwartzSeminormFamily : SeminormFamily 𝕜 𝓢(E, F) (ℕ × ℕ) := fun n => Seminorm 𝕜 n.1 n.2
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

instance : TopologicalSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).ModuleFilterBasis.topology'

theorem schwartzWithSeminorms : WithSeminorms (schwartzSeminormFamily 𝕜 E F) :=
  by
  have A : WithSeminorms (schwartzSeminormFamily ℝ E F) := ⟨rfl⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_infᵢ] at A⊢
  rw [A]
  rfl
#align schwartz_with_seminorms schwartzWithSeminorms

variable {𝕜 E F}

instance : HasContinuousSmul 𝕜 𝓢(E, F) :=
  by
  rw [(schwartzWithSeminorms 𝕜 E F).withSeminorms_eq]
  exact (schwartzSeminormFamily 𝕜 E F).ModuleFilterBasis.HasContinuousSmul

instance : TopologicalAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).AddGroupFilterBasis.is_topological_add_group

instance : UniformSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).AddGroupFilterBasis.UniformSpace

instance : UniformAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).AddGroupFilterBasis.UniformAddGroup

instance : LocallyConvexSpace ℝ 𝓢(E, F) :=
  (schwartzWithSeminorms ℝ E F).toLocallyConvexSpace

instance : TopologicalSpace.FirstCountableTopology 𝓢(E, F) :=
  (schwartzWithSeminorms ℝ E F).first_countable

end Topology

section fderiv

/-! ### Derivatives of Schwartz functions -/


variable {E F}

/-- The derivative of a Schwartz function as a Schwartz function with values in the
continuous linear maps `E→L[ℝ] F`. -/
@[protected]
def fderiv (f : 𝓢(E, F)) : 𝓢(E, E →L[ℝ] F)
    where
  toFun := fderiv ℝ f
  smooth' := (contDiff_top_iff_fderiv.mp f.smooth').2
  decay' := by
    intro k n
    cases' f.decay' k (n + 1) with C hC
    use C
    intro x
    rw [norm_iteratedFderiv_fderiv]
    exact hC x
#align schwartz_map.fderiv SchwartzMap.fderiv

@[simp, norm_cast]
theorem coe_fderiv (f : 𝓢(E, F)) : ⇑f.fderiv = fderiv ℝ f :=
  rfl
#align schwartz_map.coe_fderiv SchwartzMap.coe_fderiv

@[simp]
theorem fderiv_apply (f : 𝓢(E, F)) (x : E) : f.fderiv x = fderiv ℝ f x :=
  rfl
#align schwartz_map.fderiv_apply SchwartzMap.fderiv_apply

variable (𝕜)

variable [IsROrC 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The derivative on Schwartz space as a linear map. -/
def fderivLm : 𝓢(E, F) →ₗ[𝕜] 𝓢(E, E →L[ℝ] F)
    where
  toFun := SchwartzMap.fderiv
  map_add' f g :=
    ext fun _ => fderiv_add f.Differentiable.DifferentiableAt g.Differentiable.DifferentiableAt
  map_smul' a f := ext fun _ => fderiv_const_smul f.Differentiable.DifferentiableAt a
#align schwartz_map.fderiv_lm SchwartzMap.fderivLm

@[simp, norm_cast]
theorem fderivLm_apply (f : 𝓢(E, F)) : fderivLm 𝕜 f = SchwartzMap.fderiv f :=
  rfl
#align schwartz_map.fderiv_lm_apply SchwartzMap.fderivLm_apply

/-- The derivative on Schwartz space as a continuous linear map. -/
def fderivClm : 𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)
    where
  cont := by
    change Continuous (fderiv_lm 𝕜 : 𝓢(E, F) →ₗ[𝕜] 𝓢(E, E →L[ℝ] F))
    refine'
      Seminorm.continuous_from_bounded (schwartzWithSeminorms 𝕜 E F)
        (schwartzWithSeminorms 𝕜 E (E →L[ℝ] F)) _ _
    rintro ⟨k, n⟩
    use {⟨k, n + 1⟩}, 1, one_ne_zero
    intro f
    simp only [schwartz_seminorm_family_apply, Seminorm.comp_apply, Finset.sup_singleton, one_smul]
    refine' (fderiv_lm 𝕜 f).seminorm_le_bound 𝕜 k n (by positivity) _
    intro x
    rw [fderiv_lm_apply, coe_fderiv, norm_iteratedFderiv_fderiv]
    exact f.le_seminorm 𝕜 k (n + 1) x
  toLinearMap := fderivLm 𝕜
#align schwartz_map.fderiv_clm SchwartzMap.fderivClm

@[simp, norm_cast]
theorem fderivClm_apply (f : 𝓢(E, F)) : fderivClm 𝕜 f = SchwartzMap.fderiv f :=
  rfl
#align schwartz_map.fderiv_clm_apply SchwartzMap.fderivClm_apply

end fderiv

section BoundedContinuousFunction

/-! ### Inclusion into the space of bounded continuous functions -/


open BoundedContinuousFunction

/-- Schwartz functions as bounded continuous functions-/
def toBoundedContinuousFunction (f : 𝓢(E, F)) : E →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f (SchwartzMap.continuous f)
    (SchwartzMap.seminorm ℝ 0 0 f) (norm_le_seminorm ℝ f)
#align schwartz_map.to_bounded_continuous_function SchwartzMap.toBoundedContinuousFunction

@[simp]
theorem toBoundedContinuousFunction_apply (f : 𝓢(E, F)) (x : E) :
    f.toBoundedContinuousFunction x = f x :=
  rfl
#align schwartz_map.to_bounded_continuous_function_apply SchwartzMap.toBoundedContinuousFunction_apply

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
        Seminorm.continuous_from_bounded (schwartzWithSeminorms 𝕜 E F)
          (normWithSeminorms 𝕜 (E →ᵇ F)) _ fun i => ⟨{0}, 1, one_ne_zero, fun f => _⟩
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

