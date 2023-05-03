/-
Copyright (c) 2022 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade

! This file was ported from Lean 3 source module analysis.convex.cone.proper
! leanprover-community/mathlib commit 620ba06c7f173d79b3cad91294babde6b4eab79c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Adjoint

/-!

We define a proper cone as a nonempty, closed, convex cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once have the definitions of conic programs and
linear programs, the results from this file can be used to prove duality theorems.

## TODO

In the next few PRs (already sorry-free), we will add the definition and prove several properties
of proper cones and finally prove the cone version of Farkas' lemma (2.3.4 in the reference).

The next steps are:
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/


open ContinuousLinearMap Filter

namespace ConvexCone

variable {E : Type _} [AddCommMonoid E] [SMul ℝ E] [TopologicalSpace E] [ContinuousConstSMul ℝ E]
  [ContinuousAdd E]

/-- The closure of a convex cone inside a real inner product space is a convex cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : ConvexCone ℝ E) : ConvexCone ℝ E
    where
  carrier := closure ↑K
  smul_mem' c hc _ h₁ :=
    map_mem_closure (continuous_id'.const_smul c) h₁ fun _ h₂ => K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem
#align convex_cone.closure ConvexCone.closure

@[simp, norm_cast]
theorem coe_closure (K : ConvexCone ℝ E) : (K.closure : Set E) = closure K :=
  rfl
#align convex_cone.coe_closure ConvexCone.coe_closure

protected theorem mem_closure {K : ConvexCone ℝ E} {a : E} :
    a ∈ K.closure ↔ a ∈ closure (K : Set E) :=
  Iff.rfl
#align convex_cone.mem_closure ConvexCone.mem_closure

end ConvexCone

