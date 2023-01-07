/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module topology.metric_space.algebra
! leanprover-community/mathlib commit 134625f523e737f650a6ea7f0c82a6177e45e622
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.MulAction
import Mathbin.Topology.MetricSpace.Lipschitz

/-!
# Compatibility of algebraic operations with metric space structures

In this file we define mixin typeclasses `has_lipschitz_mul`, `has_lipschitz_add`,
`has_bounded_smul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure.  The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `has_continuous_mul` instance from `has_lipschitz_mul`, etc.  In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`uniform_group`) is structured differently.

-/


open Nnreal

noncomputable section

variable (α β : Type _) [PseudoMetricSpace α] [PseudoMetricSpace β]

section HasLipschitzMul

/-- Class `has_lipschitz_add M` says that the addition `(+) : X × X → X` is Lipschitz jointly in
the two arguments. -/
class HasLipschitzAdd [AddMonoid β] : Prop where
  lipschitz_add : ∃ C, LipschitzWith C fun p : β × β => p.1 + p.2
#align has_lipschitz_add HasLipschitzAdd

/-- Class `has_lipschitz_mul M` says that the multiplication `(*) : X × X → X` is Lipschitz jointly
in the two arguments. -/
@[to_additive]
class HasLipschitzMul [Monoid β] : Prop where
  lipschitz_mul : ∃ C, LipschitzWith C fun p : β × β => p.1 * p.2
#align has_lipschitz_mul HasLipschitzMul

variable [Monoid β]

/-- The Lipschitz constant of a monoid `β` satisfying `has_lipschitz_mul` -/
@[to_additive "The Lipschitz constant of an `add_monoid` `β` satisfying `has_lipschitz_add`"]
def HasLipschitzMul.c [_i : HasLipschitzMul β] : ℝ≥0 :=
  Classical.choose _i.lipschitz_mul
#align has_lipschitz_mul.C HasLipschitzMul.c

variable {β}

@[to_additive]
theorem lipschitz_with_lipschitz_const_mul_edist [_i : HasLipschitzMul β] :
    LipschitzWith (HasLipschitzMul.c β) fun p : β × β => p.1 * p.2 :=
  Classical.choose_spec _i.lipschitz_mul
#align lipschitz_with_lipschitz_const_mul_edist lipschitz_with_lipschitz_const_mul_edist

variable [HasLipschitzMul β]

@[to_additive]
theorem lipschitz_with_lipschitz_const_mul :
    ∀ p q : β × β, dist (p.1 * p.2) (q.1 * q.2) ≤ HasLipschitzMul.c β * dist p q :=
  by
  rw [← lipschitz_with_iff_dist_le_mul]
  exact lipschitz_with_lipschitz_const_mul_edist
#align lipschitz_with_lipschitz_const_mul lipschitz_with_lipschitz_const_mul

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) HasLipschitzMul.has_continuous_mul : HasContinuousMul β :=
  ⟨lipschitz_with_lipschitz_const_mul_edist.Continuous⟩
#align has_lipschitz_mul.has_continuous_mul HasLipschitzMul.has_continuous_mul

@[to_additive]
instance Submonoid.has_lipschitz_mul (s : Submonoid β) : HasLipschitzMul s
    where lipschitz_mul :=
    ⟨HasLipschitzMul.c β, by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
      convert lipschitz_with_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩
#align submonoid.has_lipschitz_mul Submonoid.has_lipschitz_mul

@[to_additive]
instance MulOpposite.has_lipschitz_mul : HasLipschitzMul βᵐᵒᵖ
    where lipschitz_mul :=
    ⟨HasLipschitzMul.c β, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
      (lipschitz_with_lipschitz_const_mul_edist ⟨x₂.unop, x₁.unop⟩ ⟨y₂.unop, y₁.unop⟩).trans_eq
        (congr_arg _ <| max_comm _ _)⟩
#align mul_opposite.has_lipschitz_mul MulOpposite.has_lipschitz_mul

-- this instance could be deduced from `normed_add_comm_group.has_lipschitz_add`, but we prove it
-- separately here so that it is available earlier in the hierarchy
instance Real.has_lipschitz_add : HasLipschitzAdd ℝ
    where lipschitz_add :=
    ⟨2, by
      rw [lipschitz_with_iff_dist_le_mul]
      intro p q
      simp only [Real.dist_eq, Prod.dist_eq, Prod.fst_sub, Prod.snd_sub, Nnreal.coe_one,
        Nnreal.coe_bit0]
      convert le_trans (abs_add (p.1 - q.1) (p.2 - q.2)) _ using 2
      · abel
      have := le_max_left (|p.1 - q.1|) (|p.2 - q.2|)
      have := le_max_right (|p.1 - q.1|) (|p.2 - q.2|)
      linarith⟩
#align real.has_lipschitz_add Real.has_lipschitz_add

-- this instance has the same proof as `add_submonoid.has_lipschitz_add`, but the former can't
-- directly be applied here since `ℝ≥0` is a subtype of `ℝ`, not an additive submonoid.
instance Nnreal.has_lipschitz_add : HasLipschitzAdd ℝ≥0
    where lipschitz_add :=
    ⟨HasLipschitzAdd.c ℝ, by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
      convert lipschitz_with_lipschitz_const_add_edist ⟨(x₁ : ℝ), x₂⟩ ⟨y₁, y₂⟩ using 1⟩
#align nnreal.has_lipschitz_add Nnreal.has_lipschitz_add

end HasLipschitzMul

section HasBoundedSmul

variable [Zero α] [Zero β] [HasSmul α β]

/-- Mixin typeclass on a scalar action of a metric space `α` on a metric space `β` both with
distinguished points `0`, requiring compatibility of the action in the sense that
`dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂` and
`dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0`. -/
class HasBoundedSmul : Prop where
  dist_smul_pair' : ∀ x : α, ∀ y₁ y₂ : β, dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂
  dist_pair_smul' : ∀ x₁ x₂ : α, ∀ y : β, dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0
#align has_bounded_smul HasBoundedSmul

variable {α β} [HasBoundedSmul α β]

theorem dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂ :=
  HasBoundedSmul.dist_smul_pair' x y₁ y₂
#align dist_smul_pair dist_smul_pair

theorem dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0 :=
  HasBoundedSmul.dist_pair_smul' x₁ x₂ y
#align dist_pair_smul dist_pair_smul

-- see Note [lower instance priority]
/-- The typeclass `has_bounded_smul` on a metric-space scalar action implies continuity of the
action. -/
instance (priority := 100) HasBoundedSmul.has_continuous_smul : HasContinuousSmul α β
    where continuous_smul := by
    rw [Metric.continuous_iff]
    rintro ⟨a, b⟩ ε hε
    have : 0 ≤ dist a 0 := dist_nonneg
    have : 0 ≤ dist b 0 := dist_nonneg
    let δ : ℝ := min 1 ((dist a 0 + dist b 0 + 2)⁻¹ * ε)
    have hδ_pos : 0 < δ :=
      by
      refine' lt_min_iff.mpr ⟨by norm_num, mul_pos _ hε⟩
      rw [inv_pos]
      linarith
    refine' ⟨δ, hδ_pos, _⟩
    rintro ⟨a', b'⟩ hab'
    calc
      _ ≤ _ := dist_triangle _ (a • b') _
      _ ≤ δ * (dist a 0 + dist b 0 + δ) := _
      _ < ε := _
      
    · have : 0 ≤ dist a' a := dist_nonneg
      have := dist_triangle b' b 0
      have := dist_comm (a • b') (a' • b')
      have := dist_comm a a'
      have : dist a' a ≤ dist (a', b') (a, b) := le_max_left _ _
      have : dist b' b ≤ dist (a', b') (a, b) := le_max_right _ _
      have := dist_smul_pair a b' b
      have := dist_pair_smul a a' b'
      nlinarith
    · have : δ ≤ _ := min_le_right _ _
      have : δ ≤ _ := min_le_left _ _
      have : (dist a 0 + dist b 0 + 2)⁻¹ * (ε * (dist a 0 + dist b 0 + δ)) < ε := by
        rw [inv_mul_lt_iff] <;> nlinarith
      nlinarith
#align has_bounded_smul.has_continuous_smul HasBoundedSmul.has_continuous_smul

-- this instance could be deduced from `normed_space.has_bounded_smul`, but we prove it separately
-- here so that it is available earlier in the hierarchy
instance Real.has_bounded_smul : HasBoundedSmul ℝ ℝ
    where
  dist_smul_pair' x y₁ y₂ := by simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le
  dist_pair_smul' x₁ x₂ y := by simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le
#align real.has_bounded_smul Real.has_bounded_smul

instance Nnreal.has_bounded_smul : HasBoundedSmul ℝ≥0 ℝ≥0
    where
  dist_smul_pair' x y₁ y₂ := by convert dist_smul_pair (x : ℝ) (y₁ : ℝ) y₂ using 1
  dist_pair_smul' x₁ x₂ y := by convert dist_pair_smul (x₁ : ℝ) x₂ (y : ℝ) using 1
#align nnreal.has_bounded_smul Nnreal.has_bounded_smul

/-- If a scalar is central, then its right action is bounded when its left action is. -/
instance HasBoundedSmul.op [HasSmul αᵐᵒᵖ β] [IsCentralScalar α β] : HasBoundedSmul αᵐᵒᵖ β
    where
  dist_smul_pair' :=
    MulOpposite.rec' fun x y₁ y₂ => by simpa only [op_smul_eq_smul] using dist_smul_pair x y₁ y₂
  dist_pair_smul' :=
    MulOpposite.rec' fun x₁ =>
      MulOpposite.rec' fun x₂ y => by simpa only [op_smul_eq_smul] using dist_pair_smul x₁ x₂ y
#align has_bounded_smul.op HasBoundedSmul.op

end HasBoundedSmul

instance [Monoid α] [HasLipschitzMul α] : HasLipschitzAdd (Additive α) :=
  ⟨@HasLipschitzMul.lipschitz_mul α _ _ _⟩

instance [AddMonoid α] [HasLipschitzAdd α] : HasLipschitzMul (Multiplicative α) :=
  ⟨@HasLipschitzAdd.lipschitz_add α _ _ _⟩

@[to_additive]
instance [Monoid α] [HasLipschitzMul α] : HasLipschitzMul αᵒᵈ :=
  ‹HasLipschitzMul α›

