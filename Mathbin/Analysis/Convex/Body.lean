/-
Copyright (c) 2022 Paul A. Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul A. Reichert

! This file was ported from Lean 3 source module analysis.convex.body
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Data.Real.Nnreal
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.Topology.Instances.Real

/-!
# convex bodies

This file contains the definition of the type `convex_body V`
consisting of
convex, compact, nonempty subsets of a real topological vector space `V`.

`convex_body V` is a module over the nonnegative reals (`nnreal`).

TODOs:
- endow it with the Hausdorff metric
- define positive convex bodies, requiring the interior to be nonempty
- introduce support sets

## Tags

convex, convex body
-/


open Pointwise

open Nnreal

variable (V : Type _) [TopologicalSpace V] [AddCommGroup V] [HasContinuousAdd V] [Module ℝ V]
  [HasContinuousSmul ℝ V]

/-- Let `V` be a real topological vector space. A subset of `V` is a convex body if and only if
it is convex, compact, and nonempty.
-/
structure ConvexBody where
  carrier : Set V
  convex' : Convex ℝ carrier
  is_compact' : IsCompact carrier
  nonempty' : carrier.Nonempty
#align convex_body ConvexBody

namespace ConvexBody

variable {V}

instance : SetLike (ConvexBody V) V
    where
  coe := ConvexBody.carrier
  coe_injective' K L h := by
    cases K
    cases L
    congr

theorem convex (K : ConvexBody V) : Convex ℝ (K : Set V) :=
  K.convex'
#align convex_body.convex ConvexBody.convex

theorem isCompact (K : ConvexBody V) : IsCompact (K : Set V) :=
  K.is_compact'
#align convex_body.is_compact ConvexBody.isCompact

theorem nonempty (K : ConvexBody V) : (K : Set V).Nonempty :=
  K.nonempty'
#align convex_body.nonempty ConvexBody.nonempty

@[ext]
protected theorem ext {K L : ConvexBody V} (h : (K : Set V) = L) : K = L :=
  SetLike.ext' h
#align convex_body.ext ConvexBody.ext

@[simp]
theorem coe_mk (s : Set V) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : Set V) = s :=
  rfl
#align convex_body.coe_mk ConvexBody.coe_mk

instance : AddMonoid (ConvexBody V)
    where
  -- we cannot write K + L to avoid reducibility issues with the set.has_add instance
  add K L :=
    ⟨Set.image2 (· + ·) K L, K.Convex.add L.Convex, K.IsCompact.add L.IsCompact,
      K.Nonempty.add L.Nonempty⟩
  add_assoc K L M := by
    ext
    simp only [coe_mk, Set.image2_add, add_assoc]
  zero := ⟨0, convex_singleton 0, isCompact_singleton, Set.singleton_nonempty 0⟩
  zero_add K := by
    ext
    simp only [coe_mk, Set.image2_add, zero_add]
  add_zero K := by
    ext
    simp only [coe_mk, Set.image2_add, add_zero]

@[simp]
theorem coe_add (K L : ConvexBody V) : (↑(K + L) : Set V) = (K : Set V) + L :=
  rfl
#align convex_body.coe_add ConvexBody.coe_add

@[simp]
theorem coe_zero : (↑(0 : ConvexBody V) : Set V) = 0 :=
  rfl
#align convex_body.coe_zero ConvexBody.coe_zero

instance : Inhabited (ConvexBody V) :=
  ⟨0⟩

instance : AddCommMonoid (ConvexBody V) :=
  { ConvexBody.addMonoid with
    add_comm := fun K L => by
      ext
      simp only [coe_add, add_comm] }

instance : SMul ℝ (ConvexBody V)
    where smul c K := ⟨c • (K : Set V), K.Convex.smul _, K.IsCompact.smul _, K.Nonempty.smul_set⟩

@[simp]
theorem coe_smul (c : ℝ) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl
#align convex_body.coe_smul ConvexBody.coe_smul

instance : DistribMulAction ℝ (ConvexBody V)
    where
  toHasSmul := ConvexBody.hasSmul
  one_smul K := by
    ext
    simp only [coe_smul, one_smul]
  mul_smul c d K := by
    ext
    simp only [coe_smul, mul_smul]
  smul_add c K L := by
    ext
    simp only [coe_smul, coe_add, smul_add]
  smul_zero c := by
    ext
    simp only [coe_smul, coe_zero, smul_zero]

@[simp]
theorem coe_smul' (c : ℝ≥0) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl
#align convex_body.coe_smul' ConvexBody.coe_smul'

/-- The convex bodies in a fixed space $V$ form a module over the nonnegative reals.
-/
instance : Module ℝ≥0 (ConvexBody V)
    where
  add_smul c d K := by
    ext1
    simp only [coe_smul, coe_add]
    exact Convex.add_smul K.convex (Nnreal.coe_nonneg _) (Nnreal.coe_nonneg _)
  zero_smul K := by
    ext1
    exact Set.zero_smul_set K.nonempty

end ConvexBody

