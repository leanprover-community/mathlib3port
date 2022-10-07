/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.LocallyConvex.WithSeminorms
import Mathbin.Topology.Algebra.UniformFilterBasis
import Mathbin.Tactic.Positivity

/-!
# Schwartz space

This file defines the Schwartz space. Usually, the Schwartz space is defined as the set of smooth
functions $f : ℝ^n → ℂ$ such that there exists $C_{αβ} > 0$ with $$|x^α ∂^β f(x)| < C_{αβ}$$ for
all $x ∈ ℝ^n$ and for all multiindices $α, β$.
In mathlib, we use a slightly different approach and define define the Schwartz space as all
smooth functions `f : E → F`, where `E` and `F` are real normed vector spaces such that for all
natural numbers `k` and `n` we have uniform bounds `∥x∥^k * ∥iterated_fderiv ℝ n f x∥ < C`.
This approach completely avoids using partial derivatives as well as polynomials.
We construct the topology on the Schwartz space by a family of seminorms, which are the best
constants in the above estimates, which is by abstract theory from
`seminorm_family.module_filter_basis` and `seminorm_family.to_locally_convex_space` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `schwartz_map`: The Schwartz space is the space of smooth functions such that all derivatives
decay faster than any power of `∥x∥`.
* `schwartz_map.seminorm`: The family of seminorms as described above

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
  any power of `∥x∥`. -/
structure SchwartzMap where
  toFun : E → F
  smooth' : ContDiff ℝ ⊤ to_fun
  decay' : ∀ k n : ℕ, ∃ C : ℝ, ∀ x, ∥x∥ ^ k * ∥iteratedFderiv ℝ n to_fun x∥ ≤ C

-- mathport name: «expr𝓢( , )»
localized [SchwartzSpace] notation "𝓢(" E ", " F ")" => SchwartzMap E F

variable {E F}

namespace SchwartzMap

instance : Coe 𝓢(E, F) (E → F) :=
  ⟨toFun⟩

instance funLike : FunLike 𝓢(E, F) E fun _ => F where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by cases f <;> cases g <;> congr

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun 𝓢(E, F) fun _ => E → F :=
  ⟨fun p => p.toFun⟩

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `positivity #[]
/-- All derivatives of a Schwartz function are rapidly decaying. -/
theorem decay (f : 𝓢(E, F)) (k n : ℕ) : ∃ (C : ℝ)(hC : 0 < C), ∀ x, ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ ≤ C := by
  rcases f.decay' k n with ⟨C, hC⟩
  exact
    ⟨max C 1, by trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `positivity #[]",
      fun x => (hC x).trans (le_max_leftₓ _ _)⟩

/-- Every Schwartz function is smooth. -/
theorem smooth (f : 𝓢(E, F)) (n : ℕ∞) : ContDiff ℝ n f :=
  f.smooth'.ofLe le_top

@[ext]
theorem ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g :=
  FunLike.ext f g h

section Aux

theorem bounds_nonempty (k n : ℕ) (f : 𝓢(E, F)) :
    ∃ c : ℝ, c ∈ { c : ℝ | 0 ≤ c ∧ ∀ x : E, ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ ≤ c } :=
  let ⟨M, hMp, hMb⟩ := f.decay k n
  ⟨M, le_of_ltₓ hMp, hMb⟩

theorem bounds_bdd_below (k n : ℕ) (f : 𝓢(E, F)) :
    BddBelow { c | 0 ≤ c ∧ ∀ x, ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ ≤ c } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `positivity #[]
theorem decay_add_le_aux (k n : ℕ) (f g : 𝓢(E, F)) (x : E) :
    ∥x∥ ^ k * ∥iteratedFderiv ℝ n (f + g) x∥ ≤
      ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ + ∥x∥ ^ k * ∥iteratedFderiv ℝ n g x∥ :=
  by
  rw [← mul_addₓ]
  refine'
    mul_le_mul_of_nonneg_left _
      (by trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `positivity #[]")
  convert norm_add_le _ _
  exact iterated_fderiv_add_apply (f.smooth _) (g.smooth _)

theorem decay_neg_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ∥x∥ ^ k * ∥iteratedFderiv ℝ n (-f) x∥ = ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ := by
  nth_rw 3 [← norm_neg]
  congr
  exact iterated_fderiv_neg_apply

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SmulCommClass ℝ 𝕜 F]

theorem decay_smul_aux (k n : ℕ) (f : 𝓢(E, F)) (c : 𝕜) (x : E) :
    ∥x∥ ^ k * ∥iteratedFderiv ℝ n (c • f) x∥ = ∥c∥ * ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ := by
  rw [mul_comm ∥c∥, mul_assoc, iterated_fderiv_const_smul_apply (f.smooth _), norm_smul]

end Aux

section SeminormAux

/-- Helper definition for the seminorms of the Schwartz space. -/
@[protected]
def seminormAux (k n : ℕ) (f : 𝓢(E, F)) : ℝ :=
  inf { c | 0 ≤ c ∧ ∀ x, ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ ≤ c }

theorem seminorm_aux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminormAux k n :=
  le_cInf (bounds_nonempty k n f) fun _ ⟨hx, _⟩ => hx

theorem le_seminorm_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) : ∥x∥ ^ k * ∥iteratedFderiv ℝ n (⇑f) x∥ ≤ f.seminormAux k n :=
  le_cInf (bounds_nonempty k n f) fun y ⟨_, h⟩ => h x

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem seminorm_aux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ ≤ M) : f.seminormAux k n ≤ M :=
  cInf_le (bounds_bdd_below k n f) ⟨hMp, hM⟩

end SeminormAux

/-! ### Algebraic properties -/


section Smul

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SmulCommClass ℝ 𝕜 F] [NormedField 𝕜'] [NormedSpace 𝕜' F]
  [SmulCommClass ℝ 𝕜' F]

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `positivity #[]
instance : HasSmul 𝕜 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • f, smooth' := (f.smooth _).const_smul c,
      decay' := fun k n => by
        refine' ⟨f.seminorm_aux k n * (∥c∥ + 1), fun x => _⟩
        have hc : 0 ≤ ∥c∥ := by
          trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `positivity #[]"
        refine' le_transₓ _ ((mul_le_mul_of_nonneg_right (f.le_seminorm_aux k n x) hc).trans _)
        · apply Eq.leₓ
          rw [mul_comm _ ∥c∥, ← mul_assoc]
          exact decay_smul_aux k n f c x
          
        · apply mul_le_mul_of_nonneg_left _ (f.seminorm_aux_nonneg k n)
          linarith
           }⟩

@[simp]
theorem smul_apply {f : 𝓢(E, F)} {c : 𝕜} {x : E} : (c • f) x = c • f x :=
  rfl

instance [HasSmul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' F] : IsScalarTower 𝕜 𝕜' 𝓢(E, F) :=
  ⟨fun a b f => ext fun x => smul_assoc a b (f x)⟩

instance [SmulCommClass 𝕜 𝕜' F] : SmulCommClass 𝕜 𝕜' 𝓢(E, F) :=
  ⟨fun a b f => ext fun x => smul_comm a b (f x)⟩

theorem seminorm_aux_smul_le (k n : ℕ) (c : 𝕜) (f : 𝓢(E, F)) : (c • f).seminormAux k n ≤ ∥c∥ * f.seminormAux k n := by
  refine'
    (c • f).seminorm_aux_le_bound k n (mul_nonneg (norm_nonneg _) (seminorm_aux_nonneg _ _ _)) fun x =>
      (decay_smul_aux k n f c x).le.trans _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (f.le_seminorm_aux k n x) (norm_nonneg _)

instance hasNsmul : HasSmul ℕ 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • f, smooth' := (f.smooth _).const_smul c,
      decay' := by
        have : c • (f : E → F) = (c : ℝ) • f := by
          ext x
          simp only [Pi.smul_apply, ← nsmul_eq_smul_cast]
        simp only [this]
        exact ((c : ℝ) • f).decay' }⟩

instance hasZsmul : HasSmul ℤ 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • f, smooth' := (f.smooth _).const_smul c,
      decay' := by
        have : c • (f : E → F) = (c : ℝ) • f := by
          ext x
          simp only [Pi.smul_apply, ← zsmul_eq_smul_cast]
        simp only [this]
        exact ((c : ℝ) • f).decay' }⟩

end Smul

section Zero

instance : Zero 𝓢(E, F) :=
  ⟨{ toFun := fun _ => 0, smooth' := cont_diff_const, decay' := fun _ _ => ⟨1, fun _ => by simp⟩ }⟩

instance : Inhabited 𝓢(E, F) :=
  ⟨0⟩

theorem coe_zero : ↑(0 : 𝓢(E, F)) = (0 : E → F) :=
  rfl

@[simp]
theorem coe_fn_zero : coeFn (0 : 𝓢(E, F)) = (0 : E → F) :=
  rfl

@[simp]
theorem zero_apply {x : E} : (0 : 𝓢(E, F)) x = 0 :=
  rfl

theorem seminorm_aux_zero (k n : ℕ) : (0 : 𝓢(E, F)).seminormAux k n = 0 :=
  le_antisymmₓ (seminorm_aux_le_bound k n _ rfl.le fun _ => by simp [Pi.zero_def]) (seminorm_aux_nonneg _ _ _)

end Zero

section Neg

instance : Neg 𝓢(E, F) :=
  ⟨fun f =>
    ⟨-f, (f.smooth _).neg, fun k n =>
      ⟨f.seminormAux k n, fun x => (decay_neg_aux k n f x).le.trans (f.le_seminorm_aux k n x)⟩⟩⟩

end Neg

section Add

instance : Add 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f + g, (f.smooth _).add (g.smooth _), fun k n =>
      ⟨f.seminormAux k n + g.seminormAux k n, fun x =>
        (decay_add_le_aux k n f g x).trans (add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x))⟩⟩⟩

@[simp]
theorem add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x :=
  rfl

theorem seminorm_aux_add_le (k n : ℕ) (f g : 𝓢(E, F)) :
    (f + g).seminormAux k n ≤ f.seminormAux k n + g.seminormAux k n :=
  ((f + g).seminorm_aux_le_bound k n (add_nonneg (seminorm_aux_nonneg _ _ _) (seminorm_aux_nonneg _ _ _))) fun x =>
    (decay_add_le_aux k n f g x).trans <| add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x)

end Add

section Sub

instance : Sub 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f - g, (f.smooth _).sub (g.smooth _), by
      intro k n
      refine' ⟨f.seminorm_aux k n + g.seminorm_aux k n, fun x => _⟩
      refine' le_transₓ _ (add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x))
      rw [sub_eq_add_neg]
      rw [← decay_neg_aux k n g x]
      convert decay_add_le_aux k n f (-g) x⟩⟩

-- exact fails with deterministic timeout
@[simp]
theorem sub_apply {f g : 𝓢(E, F)} {x : E} : (f - g) x = f x - g x :=
  rfl

end Sub

section AddCommGroupₓ

instance : AddCommGroupₓ 𝓢(E, F) :=
  FunLike.coe_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ =>
    rfl

variable (E F)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓢(E, F) →+ E → F where
  toFun := fun f => f
  map_zero' := coe_zero
  map_add' := fun _ _ => rfl

variable {E F}

theorem coe_coe_hom : (coeHom E F : 𝓢(E, F) → E → F) = coeFn :=
  rfl

theorem coe_hom_injective : Function.Injective (coeHom E F) := by
  rw [coe_coe_hom]
  exact FunLike.coe_injective

end AddCommGroupₓ

section Module

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SmulCommClass ℝ 𝕜 F]

instance : Module 𝕜 𝓢(E, F) :=
  coe_hom_injective.Module 𝕜 (coeHom E F) fun _ _ => rfl

end Module

section Seminorms

/-! ### Seminorms on Schwartz space-/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SmulCommClass ℝ 𝕜 F]

variable (𝕜)

/-- The seminorms of the Schwartz space given by the best constants in the definition of
`𝓢(E, F)`. -/
@[protected]
def seminorm (k n : ℕ) : Seminorm 𝕜 𝓢(E, F) :=
  Seminorm.ofSmulLe (seminormAux k n) (seminorm_aux_zero k n) (seminorm_aux_add_le k n) (seminorm_aux_smul_le k n)

/-- If one controls the seminorm for every `x`, then one controls the seminorm. -/
theorem seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ ≤ M) : Seminorm 𝕜 k n f ≤ M :=
  f.seminorm_aux_le_bound k n hMp hM

/-- The seminorm controls the Schwartz estimate for any fixed `x`. -/
theorem le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) : ∥x∥ ^ k * ∥iteratedFderiv ℝ n f x∥ ≤ Seminorm 𝕜 k n f :=
  f.le_seminorm_aux k n x

theorem norm_iterated_fderiv_le_seminorm (f : 𝓢(E, F)) (n : ℕ) (x₀ : E) :
    ∥iteratedFderiv ℝ n f x₀∥ ≤ (SchwartzMap.seminorm 𝕜 0 n) f := by
  have := SchwartzMap.le_seminorm 𝕜 0 n f x₀
  rwa [pow_zeroₓ, one_mulₓ] at this

theorem norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : ℕ) (x₀ : E) : ∥x₀∥ ^ k * ∥f x₀∥ ≤ (SchwartzMap.seminorm 𝕜 k 0) f :=
  by
  have := SchwartzMap.le_seminorm 𝕜 k 0 f x₀
  rwa [norm_iterated_fderiv_zero] at this

end Seminorms

section Topology

/-! ### The topology on the Schwartz space-/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SmulCommClass ℝ 𝕜 F]

variable (𝕜 E F)

/-- The family of Schwartz seminorms. -/
def _root_.schwartz_seminorm_family : SeminormFamily 𝕜 𝓢(E, F) (ℕ × ℕ) := fun n => Seminorm 𝕜 n.1 n.2

instance : TopologicalSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).ModuleFilterBasis.topology'

theorem _root_.schwartz_with_seminorms : WithSeminorms (schwartzSeminormFamily 𝕜 E F) := by
  have A : WithSeminorms (schwartzSeminormFamily ℝ E F) := ⟨rfl⟩
  rw [SeminormFamily.with_seminorms_iff_nhds_eq_infi] at A⊢
  rw [A]
  rfl

variable {𝕜 E F}

instance : HasContinuousSmul 𝕜 𝓢(E, F) := by
  rw [SeminormFamily.with_seminorms_eq (schwartz_with_seminorms 𝕜 E F)]
  exact (schwartzSeminormFamily 𝕜 E F).ModuleFilterBasis.HasContinuousSmul

instance : TopologicalAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).ModuleFilterBasis.toAddGroupFilterBasis.is_topological_add_group

instance : UniformSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).ModuleFilterBasis.toAddGroupFilterBasis.UniformSpace

instance : UniformAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).ModuleFilterBasis.toAddGroupFilterBasis.UniformAddGroup

instance : LocallyConvexSpace ℝ 𝓢(E, F) :=
  SeminormFamily.to_locally_convex_space (schwartz_with_seminorms ℝ E F)

end Topology

end SchwartzMap

