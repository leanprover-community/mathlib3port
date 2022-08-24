/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.RingTheory.TensorProduct

/-!
# Bimodules

One frequently encounters situations in which several sets of scalars act on a single space, subject
to compatibility condition(s). A distinguished instance of this is the theory of bimodules: one has
two rings `R`, `S` acting on an additive group `M`, with `R` acting covariantly ("on the left")
and `S` acting contravariantly ("on the right"). The compatibility condition is just:
`(r • m) • s = r • (m • s)` for all `r : R`, `s : S`, `m : M`.

This situation can be set up in Mathlib as:
```lean
variables (R S M : Type*) [ring R] [ring S]
variables [add_comm_group M] [module R M] [module Sᵐᵒᵖ M] [smul_comm_class R Sᵐᵒᵖ M]
```
The key fact is:
```lean
example : module (R ⊗[ℕ] Sᵐᵒᵖ) M := tensor_product.algebra.module
```
Note that the corresponding result holds for the canonically isomorphic ring `R ⊗[ℤ] Sᵐᵒᵖ` but it is
preferable to use the `R ⊗[ℕ] Sᵐᵒᵖ` instance since it works without additive inverses.

Bimodules are thus just a special case of `module`s and most of their properties follow from the
theory of `module`s`. In particular a two-sided submodule of a bimodule is simply a term of type
`submodule (R ⊗[ℕ] Sᵐᵒᵖ) M`.

This file is a place to collect results which are specific to bimodules.

## Main definitions

 * `subbimodule.mk`
 * `subbimodule.smul_mem`
 * `subbimodule.smul_mem'`
 * `subbimodule.to_submodule`
 * `subbimodule.to_submodule'`

## Implementation details

For many definitions and lemmas it is preferable to set things up without opposites, i.e., as:
`[module S M] [smul_comm_class R S M]` rather than `[module Sᵐᵒᵖ M] [smul_comm_class R Sᵐᵒᵖ M]`.
The corresponding results for opposites then follow automatically and do not require taking
advantage of the fact that `(Sᵐᵒᵖ)ᵐᵒᵖ` is defeq to `S`.

## TODO

Develop the theory of two-sided ideals, which have type `submodule (R ⊗[ℕ] Rᵐᵒᵖ) R`.

-/


open TensorProduct

attribute [local instance] TensorProduct.Algebra.module

namespace Subbimodule

section Algebra

variable {R A B M : Type _}

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable [Semiringₓ A] [Semiringₓ B] [Module A M] [Module B M]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R A M] [IsScalarTower R B M]

variable [SmulCommClass A B M]

/-- A constructor for a subbimodule which demands closure under the two sets of scalars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `base_change`. -/
@[simps]
def mk (p : AddSubmonoid M) (hA : ∀ (a : A) {m : M}, m ∈ p → a • m ∈ p) (hB : ∀ (b : B) {m : M}, m ∈ p → b • m ∈ p) :
    Submodule (A ⊗[R] B) M :=
  { p with Carrier := p,
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab
        (fun hm => by
          simpa only [zero_smul] using p.zero_mem)
        (fun a b hm => by
          simpa only [TensorProduct.Algebra.smul_def] using hA a (hB b hm))
        fun z w hz hw hm => by
        simpa only [add_smul] using p.add_mem (hz hm) (hw hm) }

theorem smul_mem (p : Submodule (A ⊗[R] B) M) (a : A) {m : M} (hm : m ∈ p) : a • m ∈ p := by
  suffices a • m = a ⊗ₜ[R] (1 : B) • m by
    exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

theorem smul_mem' (p : Submodule (A ⊗[R] B) M) (b : B) {m : M} (hm : m ∈ p) : b • m ∈ p := by
  suffices b • m = (1 : A) ⊗ₜ[R] b • m by
    exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

/-- If `A` and `B` are also `algebra`s over yet another set of scalars `S` then we may "base change"
from `R` to `S`. -/
@[simps]
def baseChange (S : Type _) [CommSemiringₓ S] [Module S M] [Algebra S A] [Algebra S B] [IsScalarTower S A M]
    [IsScalarTower S B M] (p : Submodule (A ⊗[R] B) M) : Submodule (A ⊗[S] B) M :=
  mk p.toAddSubmonoid (smul_mem p) (smul_mem' p)

/-- Forgetting the `B` action, a `submodule` over `A ⊗[R] B` is just a `submodule` over `A`. -/
@[simps]
def toSubmodule (p : Submodule (A ⊗[R] B) M) : Submodule A M :=
  { p with Carrier := p, smul_mem' := smul_mem p }

/-- Forgetting the `A` action, a `submodule` over `A ⊗[R] B` is just a `submodule` over `B`. -/
@[simps]
def toSubmodule' (p : Submodule (A ⊗[R] B) M) : Submodule B M :=
  { p with Carrier := p, smul_mem' := smul_mem' p }

end Algebra

section Ringₓ

variable (R S M : Type _) [Ringₓ R] [Ringₓ S]

variable [AddCommGroupₓ M] [Module R M] [Module S M] [SmulCommClass R S M]

/-- A `submodule` over `R ⊗[ℕ] S` is naturally also a `submodule` over the canonically-isomorphic
ring `R ⊗[ℤ] S`. -/
@[simps]
def toSubbimoduleInt (p : Submodule (R ⊗[ℕ] S) M) : Submodule (R ⊗[ℤ] S) M :=
  baseChange ℤ p

/-- A `submodule` over `R ⊗[ℤ] S` is naturally also a `submodule` over the canonically-isomorphic
ring `R ⊗[ℕ] S`. -/
@[simps]
def toSubbimoduleNat (p : Submodule (R ⊗[ℤ] S) M) : Submodule (R ⊗[ℕ] S) M :=
  baseChange ℕ p

end Ringₓ

end Subbimodule

