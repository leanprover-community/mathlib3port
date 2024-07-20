/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.Module.Equiv.Defs
import Data.DFinsupp.Basic
import Data.Finsupp.Basic

#align_import data.finsupp.to_dfinsupp from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Conversion between `finsupp` and homogenous `dfinsupp`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides conversions between `finsupp` and `dfinsupp`.
It is in its own file since neither `finsupp` or `dfinsupp` depend on each other.

## Main definitions

* "identity" maps between `finsupp` and `dfinsupp`:
  * `finsupp.to_dfinsupp : (ι →₀ M) → (Π₀ i : ι, M)`
  * `dfinsupp.to_finsupp : (Π₀ i : ι, M) → (ι →₀ M)`
  * Bundled equiv versions of the above:
    * `finsupp_equiv_dfinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)`
    * `finsupp_add_equiv_dfinsupp : (ι →₀ M) ≃+ (Π₀ i : ι, M)`
    * `finsupp_lequiv_dfinsupp R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)`
* stronger versions of `finsupp.split`:
  * `sigma_finsupp_equiv_dfinsupp : ((Σ i, η i) →₀ N) ≃ (Π₀ i, (η i →₀ N))`
  * `sigma_finsupp_add_equiv_dfinsupp : ((Σ i, η i) →₀ N) ≃+ (Π₀ i, (η i →₀ N))`
  * `sigma_finsupp_lequiv_dfinsupp : ((Σ i, η i) →₀ N) ≃ₗ[R] (Π₀ i, (η i →₀ N))`

## Theorems

The defining features of these operations is that they preserve the function and support:

* `finsupp.to_dfinsupp_coe`
* `finsupp.to_dfinsupp_support`
* `dfinsupp.to_finsupp_coe`
* `dfinsupp.to_finsupp_support`

and therefore map `finsupp.single` to `dfinsupp.single` and vice versa:

* `finsupp.to_dfinsupp_single`
* `dfinsupp.to_finsupp_single`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to `finsupp.to_dfinsupp`:

* `finsupp_add_equiv_dfinsupp_apply`
* `finsupp_lequiv_dfinsupp_apply`
* `finsupp_add_equiv_dfinsupp_symm_apply`
* `finsupp_lequiv_dfinsupp_symm_apply`

## Implementation notes

We provide `dfinsupp.to_finsupp` and `finsupp_equiv_dfinsupp` computably by adding
`[decidable_eq ι]` and `[Π m : M, decidable (m ≠ 0)]` arguments. To aid with definitional unfolding,
these arguments are also present on the `noncomputable` equivs.
-/


variable {ι : Type _} {R : Type _} {M : Type _}

/-! ### Basic definitions and lemmas -/


section Defs

#print Finsupp.toDFinsupp /-
/-- Interpret a `finsupp` as a homogenous `dfinsupp`. -/
def Finsupp.toDFinsupp [Zero M] (f : ι →₀ M) : Π₀ i : ι, M
    where
  toFun := f
  support' :=
    Trunc.mk
      ⟨f.support.1, fun i => (Classical.em (f i = 0)).symm.imp_left Finsupp.mem_support_iff.mpr⟩
#align finsupp.to_dfinsupp Finsupp.toDFinsupp
-/

#print Finsupp.toDFinsupp_coe /-
@[simp]
theorem Finsupp.toDFinsupp_coe [Zero M] (f : ι →₀ M) : ⇑f.toDFinsupp = f :=
  rfl
#align finsupp.to_dfinsupp_coe Finsupp.toDFinsupp_coe
-/

section

variable [DecidableEq ι] [Zero M]

#print Finsupp.toDFinsupp_single /-
@[simp]
theorem Finsupp.toDFinsupp_single (i : ι) (m : M) :
    (Finsupp.single i m).toDFinsupp = DFinsupp.single i m := by ext;
  simp [Finsupp.single_apply, DFinsupp.single_apply]
#align finsupp.to_dfinsupp_single Finsupp.toDFinsupp_single
-/

variable [∀ m : M, Decidable (m ≠ 0)]

#print toDFinsupp_support /-
@[simp]
theorem toDFinsupp_support (f : ι →₀ M) : f.toDFinsupp.support = f.support := by ext; simp
#align to_dfinsupp_support toDFinsupp_support
-/

#print DFinsupp.toFinsupp /-
/-- Interpret a homogenous `dfinsupp` as a `finsupp`.

Note that the elaborator has a lot of trouble with this definition - it is often necessary to
write `(dfinsupp.to_finsupp f : ι →₀ M)` instead of `f.to_finsupp`, as for some unknown reason
using dot notation or omitting the type ascription prevents the type being resolved correctly. -/
def DFinsupp.toFinsupp (f : Π₀ i : ι, M) : ι →₀ M :=
  ⟨f.support, f, fun i => by simp only [DFinsupp.mem_support_iff]⟩
#align dfinsupp.to_finsupp DFinsupp.toFinsupp
-/

#print DFinsupp.toFinsupp_coe /-
@[simp]
theorem DFinsupp.toFinsupp_coe (f : Π₀ i : ι, M) : ⇑f.toFinsupp = f :=
  rfl
#align dfinsupp.to_finsupp_coe DFinsupp.toFinsupp_coe
-/

#print DFinsupp.toFinsupp_support /-
@[simp]
theorem DFinsupp.toFinsupp_support (f : Π₀ i : ι, M) : f.toFinsupp.support = f.support := by ext;
  simp
#align dfinsupp.to_finsupp_support DFinsupp.toFinsupp_support
-/

#print DFinsupp.toFinsupp_single /-
@[simp]
theorem DFinsupp.toFinsupp_single (i : ι) (m : M) :
    (DFinsupp.single i m : Π₀ i : ι, M).toFinsupp = Finsupp.single i m := by ext;
  simp [Finsupp.single_apply, DFinsupp.single_apply]
#align dfinsupp.to_finsupp_single DFinsupp.toFinsupp_single
-/

#print Finsupp.toDFinsupp_toFinsupp /-
@[simp]
theorem Finsupp.toDFinsupp_toFinsupp (f : ι →₀ M) : f.toDFinsupp.toFinsupp = f :=
  DFunLike.coe_injective rfl
#align finsupp.to_dfinsupp_to_finsupp Finsupp.toDFinsupp_toFinsupp
-/

#print DFinsupp.toFinsupp_toDFinsupp /-
@[simp]
theorem DFinsupp.toFinsupp_toDFinsupp (f : Π₀ i : ι, M) : f.toFinsupp.toDFinsupp = f :=
  DFunLike.coe_injective rfl
#align dfinsupp.to_finsupp_to_dfinsupp DFinsupp.toFinsupp_toDFinsupp
-/

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace Finsupp

#print Finsupp.toDFinsupp_zero /-
@[simp]
theorem toDFinsupp_zero [Zero M] : (0 : ι →₀ M).toDFinsupp = 0 :=
  DFunLike.coe_injective rfl
#align finsupp.to_dfinsupp_zero Finsupp.toDFinsupp_zero
-/

#print Finsupp.toDFinsupp_add /-
@[simp]
theorem toDFinsupp_add [AddZeroClass M] (f g : ι →₀ M) :
    (f + g).toDFinsupp = f.toDFinsupp + g.toDFinsupp :=
  DFunLike.coe_injective rfl
#align finsupp.to_dfinsupp_add Finsupp.toDFinsupp_add
-/

#print Finsupp.toDFinsupp_neg /-
@[simp]
theorem toDFinsupp_neg [AddGroup M] (f : ι →₀ M) : (-f).toDFinsupp = -f.toDFinsupp :=
  DFunLike.coe_injective rfl
#align finsupp.to_dfinsupp_neg Finsupp.toDFinsupp_neg
-/

#print Finsupp.toDFinsupp_sub /-
@[simp]
theorem toDFinsupp_sub [AddGroup M] (f g : ι →₀ M) :
    (f - g).toDFinsupp = f.toDFinsupp - g.toDFinsupp :=
  DFunLike.coe_injective rfl
#align finsupp.to_dfinsupp_sub Finsupp.toDFinsupp_sub
-/

#print Finsupp.toDFinsupp_smul /-
@[simp]
theorem toDFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : R) (f : ι →₀ M) :
    (r • f).toDFinsupp = r • f.toDFinsupp :=
  DFunLike.coe_injective rfl
#align finsupp.to_dfinsupp_smul Finsupp.toDFinsupp_smul
-/

end Finsupp

namespace DFinsupp

variable [DecidableEq ι]

#print DFinsupp.toFinsupp_zero /-
@[simp]
theorem toFinsupp_zero [Zero M] [∀ m : M, Decidable (m ≠ 0)] : toFinsupp 0 = (0 : ι →₀ M) :=
  DFunLike.coe_injective rfl
#align dfinsupp.to_finsupp_zero DFinsupp.toFinsupp_zero
-/

#print DFinsupp.toFinsupp_add /-
@[simp]
theorem toFinsupp_add [AddZeroClass M] [∀ m : M, Decidable (m ≠ 0)] (f g : Π₀ i : ι, M) :
    (toFinsupp (f + g) : ι →₀ M) = toFinsupp f + toFinsupp g :=
  DFunLike.coe_injective <| DFinsupp.coe_add _ _
#align dfinsupp.to_finsupp_add DFinsupp.toFinsupp_add
-/

#print DFinsupp.toFinsupp_neg /-
@[simp]
theorem toFinsupp_neg [AddGroup M] [∀ m : M, Decidable (m ≠ 0)] (f : Π₀ i : ι, M) :
    (toFinsupp (-f) : ι →₀ M) = -toFinsupp f :=
  DFunLike.coe_injective <| DFinsupp.coe_neg _
#align dfinsupp.to_finsupp_neg DFinsupp.toFinsupp_neg
-/

#print DFinsupp.toFinsupp_sub /-
@[simp]
theorem toFinsupp_sub [AddGroup M] [∀ m : M, Decidable (m ≠ 0)] (f g : Π₀ i : ι, M) :
    (toFinsupp (f - g) : ι →₀ M) = toFinsupp f - toFinsupp g :=
  DFunLike.coe_injective <| DFinsupp.coe_sub _ _
#align dfinsupp.to_finsupp_sub DFinsupp.toFinsupp_sub
-/

#print DFinsupp.toFinsupp_smul /-
@[simp]
theorem toFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [∀ m : M, Decidable (m ≠ 0)]
    (r : R) (f : Π₀ i : ι, M) : (toFinsupp (r • f) : ι →₀ M) = r • toFinsupp f :=
  DFunLike.coe_injective <| DFinsupp.coe_smul _ _
#align dfinsupp.to_finsupp_smul DFinsupp.toFinsupp_smul
-/

end DFinsupp

end Lemmas

/-! ### Bundled `equiv`s -/


section Equivs

#print finsuppEquivDFinsupp /-
/-- `finsupp.to_dfinsupp` and `dfinsupp.to_finsupp` together form an equiv. -/
@[simps (config := { fullyApplied := false })]
def finsuppEquivDFinsupp [DecidableEq ι] [Zero M] [∀ m : M, Decidable (m ≠ 0)] :
    (ι →₀ M) ≃ Π₀ i : ι, M where
  toFun := Finsupp.toDFinsupp
  invFun := DFinsupp.toFinsupp
  left_inv := Finsupp.toDFinsupp_toFinsupp
  right_inv := DFinsupp.toFinsupp_toDFinsupp
#align finsupp_equiv_dfinsupp finsuppEquivDFinsupp
-/

#print finsuppAddEquivDFinsupp /-
/-- The additive version of `finsupp.to_finsupp`. Note that this is `noncomputable` because
`finsupp.has_add` is noncomputable. -/
@[simps (config := { fullyApplied := false })]
def finsuppAddEquivDFinsupp [DecidableEq ι] [AddZeroClass M] [∀ m : M, Decidable (m ≠ 0)] :
    (ι →₀ M) ≃+ Π₀ i : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_add' := Finsupp.toDFinsupp_add }
#align finsupp_add_equiv_dfinsupp finsuppAddEquivDFinsupp
-/

variable (R)

#print finsuppLequivDFinsupp /-
/-- The additive version of `finsupp.to_finsupp`. Note that this is `noncomputable` because
`finsupp.has_add` is noncomputable. -/
@[simps (config := { fullyApplied := false })]
def finsuppLequivDFinsupp [DecidableEq ι] [Semiring R] [AddCommMonoid M]
    [∀ m : M, Decidable (m ≠ 0)] [Module R M] : (ι →₀ M) ≃ₗ[R] Π₀ i : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_smul' := Finsupp.toDFinsupp_smul
    map_add' := Finsupp.toDFinsupp_add }
#align finsupp_lequiv_dfinsupp finsuppLequivDFinsupp
-/

section Sigma

/-! ### Stronger versions of `finsupp.split` -/
noncomputable section

variable {η : ι → Type _} {N : Type _} [Semiring R]

open Finsupp

#print sigmaFinsuppEquivDFinsupp /-
/-- `finsupp.split` is an equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
def sigmaFinsuppEquivDFinsupp [Zero N] : ((Σ i, η i) →₀ N) ≃ Π₀ i, η i →₀ N
    where
  toFun f :=
    ⟨split f,
      Trunc.mk
        ⟨(splitSupport f : Finset ι).val, fun i =>
          by
          rw [← Finset.mem_def, mem_split_support_iff_nonzero]
          exact (em _).symm⟩⟩
  invFun f := by
    haveI := Classical.decEq ι
    haveI := fun i => Classical.decEq (η i →₀ N)
    refine'
      on_finset (Finset.sigma f.support fun j => (f j).support) (fun ji => f ji.1 ji.2) fun g hg =>
        finset.mem_sigma.mpr ⟨_, mem_support_iff.mpr hg⟩
    simp only [Ne.def, DFinsupp.mem_support_toFun]
    intro h
    rw [h] at hg
    simpa using hg
  left_inv f := by ext; simp [split]
  right_inv f := by ext; simp [split]
#align sigma_finsupp_equiv_dfinsupp sigmaFinsuppEquivDFinsupp
-/

#print sigmaFinsuppEquivDFinsupp_apply /-
@[simp]
theorem sigmaFinsuppEquivDFinsupp_apply [Zero N] (f : (Σ i, η i) →₀ N) :
    (sigmaFinsuppEquivDFinsupp f : ∀ i, η i →₀ N) = Finsupp.split f :=
  rfl
#align sigma_finsupp_equiv_dfinsupp_apply sigmaFinsuppEquivDFinsupp_apply
-/

#print sigmaFinsuppEquivDFinsupp_symm_apply /-
@[simp]
theorem sigmaFinsuppEquivDFinsupp_symm_apply [Zero N] (f : Π₀ i, η i →₀ N) (s : Σ i, η i) :
    (sigmaFinsuppEquivDFinsupp.symm f : (Σ i, η i) →₀ N) s = f s.1 s.2 :=
  rfl
#align sigma_finsupp_equiv_dfinsupp_symm_apply sigmaFinsuppEquivDFinsupp_symm_apply
-/

#print sigmaFinsuppEquivDFinsupp_support /-
@[simp]
theorem sigmaFinsuppEquivDFinsupp_support [DecidableEq ι] [Zero N]
    [∀ (i : ι) (x : η i →₀ N), Decidable (x ≠ 0)] (f : (Σ i, η i) →₀ N) :
    (sigmaFinsuppEquivDFinsupp f).support = Finsupp.splitSupport f :=
  by
  ext
  rw [DFinsupp.mem_support_toFun]
  exact (Finsupp.mem_splitSupport_iff_nonzero _ _).symm
#align sigma_finsupp_equiv_dfinsupp_support sigmaFinsuppEquivDFinsupp_support
-/

#print sigmaFinsuppEquivDFinsupp_single /-
@[simp]
theorem sigmaFinsuppEquivDFinsupp_single [DecidableEq ι] [Zero N] (a : Σ i, η i) (n : N) :
    sigmaFinsuppEquivDFinsupp (Finsupp.single a n) =
      @DFinsupp.single _ (fun i => η i →₀ N) _ _ a.1 (Finsupp.single a.2 n) :=
  by
  obtain ⟨i, a⟩ := a
  ext j b
  by_cases h : i = j
  · subst h
    classical simp [split_apply, Finsupp.single_apply]
  suffices Finsupp.single (⟨i, a⟩ : Σ i, η i) n ⟨j, b⟩ = 0 by simp [split_apply, dif_neg h, this]
  have H : (⟨i, a⟩ : Σ i, η i) ≠ ⟨j, b⟩ := by simp [h]
  classical rw [Finsupp.single_apply, if_neg H]
#align sigma_finsupp_equiv_dfinsupp_single sigmaFinsuppEquivDFinsupp_single
-/

-- Without this Lean fails to find the `add_zero_class` instance on `Π₀ i, (η i →₀ N)`.
attribute [-instance] Finsupp.instZero

#print sigmaFinsuppEquivDFinsupp_add /-
@[simp]
theorem sigmaFinsuppEquivDFinsupp_add [AddZeroClass N] (f g : (Σ i, η i) →₀ N) :
    sigmaFinsuppEquivDFinsupp (f + g) =
      (sigmaFinsuppEquivDFinsupp f + sigmaFinsuppEquivDFinsupp g : Π₀ i : ι, η i →₀ N) :=
  by ext; rfl
#align sigma_finsupp_equiv_dfinsupp_add sigmaFinsuppEquivDFinsupp_add
-/

#print sigmaFinsuppAddEquivDFinsupp /-
/-- `finsupp.split` is an additive equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
def sigmaFinsuppAddEquivDFinsupp [AddZeroClass N] : ((Σ i, η i) →₀ N) ≃+ Π₀ i, η i →₀ N :=
  { sigmaFinsuppEquivDFinsupp with
    toFun := sigmaFinsuppEquivDFinsupp
    invFun := sigmaFinsuppEquivDFinsupp.symm
    map_add' := sigmaFinsuppEquivDFinsupp_add }
#align sigma_finsupp_add_equiv_dfinsupp sigmaFinsuppAddEquivDFinsupp
-/

attribute [-instance] Finsupp.instAddZeroClass

#print sigmaFinsuppEquivDFinsupp_smul /-
--tofix: r • (sigma_finsupp_equiv_dfinsupp f) doesn't work.
@[simp]
theorem sigmaFinsuppEquivDFinsupp_smul {R} [Monoid R] [AddMonoid N] [DistribMulAction R N] (r : R)
    (f : (Σ i, η i) →₀ N) :
    sigmaFinsuppEquivDFinsupp (r • f) =
      @SMul.smul R (Π₀ i, η i →₀ N) MulAction.toHasSmul r (sigmaFinsuppEquivDFinsupp f) :=
  by ext; rfl
#align sigma_finsupp_equiv_dfinsupp_smul sigmaFinsuppEquivDFinsupp_smul
-/

attribute [-instance] Finsupp.instAddMonoid

#print sigmaFinsuppLequivDFinsupp /-
/-- `finsupp.split` is a linear equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
def sigmaFinsuppLequivDFinsupp [AddCommMonoid N] [Module R N] :
    ((Σ i, η i) →₀ N) ≃ₗ[R] Π₀ i, η i →₀ N :=
  { sigmaFinsuppAddEquivDFinsupp with map_smul' := sigmaFinsuppEquivDFinsupp_smul }
#align sigma_finsupp_lequiv_dfinsupp sigmaFinsuppLequivDFinsupp
-/

end Sigma

end Equivs

