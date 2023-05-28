/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth

! This file was ported from Lean 3 source module algebra.module.equiv
! leanprover-community/mathlib commit ea94d7cd54ad9ca6b7710032868abb7c6a104c9c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.LinearMap

/-!
# (Semi)linear equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define

* `linear_equiv σ M M₂`, `M ≃ₛₗ[σ] M₂`: an invertible semilinear map. Here, `σ` is a `ring_hom`
  from `R` to `R₂` and an `e : M ≃ₛₗ[σ] M₂` satisfies `e (c • x) = (σ c) • (e x)`. The plain
  linear version, with `σ` being `ring_hom.id R`, is denoted by `M ≃ₗ[R] M₂`, and the
  star-linear version (with `σ` being `star_ring_end`) is denoted by `M ≃ₗ⋆[R] M₂`.

## Implementation notes

To ensure that composition works smoothly for semilinear equivalences, we use the typeclasses
`ring_hom_comp_triple`, `ring_hom_inv_pair` and `ring_hom_surjective` from
`algebra/ring/comp_typeclasses`.

The group structure on automorphisms, `linear_equiv.automorphism_group`, is provided elsewhere.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags

linear equiv, linear equivalences, linear isomorphism, linear isomorphic
-/


open Function

universe u u' v w x y z

variable {R : Type _} {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}

variable {k : Type _} {S : Type _} {M : Type _} {M₁ : Type _} {M₂ : Type _} {M₃ : Type _}

variable {N₁ : Type _} {N₂ : Type _} {N₃ : Type _} {N₄ : Type _} {ι : Type _}

section

#print LinearEquiv /-
/-- A linear equivalence is an invertible linear map. -/
@[nolint has_nonempty_instance]
structure LinearEquiv {R : Type _} {S : Type _} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type _) (M₂ : Type _)
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂
#align linear_equiv LinearEquiv
-/

attribute [nolint doc_blame] LinearEquiv.toLinearMap

attribute [nolint doc_blame] LinearEquiv.toAddEquiv

-- mathport name: «expr ≃ₛₗ[ ] »
notation:50 M " ≃ₛₗ[" σ "] " M₂ => LinearEquiv σ M M₂

-- mathport name: «expr ≃ₗ[ ] »
notation:50 M " ≃ₗ[" R "] " M₂ => LinearEquiv (RingHom.id R) M M₂

-- mathport name: «expr ≃ₗ⋆[ ] »
notation:50 M " ≃ₗ⋆[" R "] " M₂ => LinearEquiv (starRingEnd R) M M₂

#print SemilinearEquivClass /-
/-- `semilinear_equiv_class F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear equivs
`M → M₂`.

See also `linear_equiv_class F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearEquivClass (F : Type _) {R S : outParam (Type _)} [Semiring R] [Semiring S]
  (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M M₂ : outParam (Type _)) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
  AddEquivClass F M M₂ where
  map_smulₛₗ : ∀ (f : F) (r : R) (x : M), f (r • x) = σ r • f x
#align semilinear_equiv_class SemilinearEquivClass
-/

-- `R, S, σ, σ'` become metavars, but it's OK since they are outparams.
attribute [nolint dangerous_instance] SemilinearEquivClass.toAddEquivClass

#print LinearEquivClass /-
/-- `linear_equiv_class F R M M₂` asserts `F` is a type of bundled `R`-linear equivs `M → M₂`.
This is an abbreviation for `semilinear_equiv_class F (ring_hom.id R) M M₂`.
-/
abbrev LinearEquivClass (F : Type _) (R M M₂ : outParam (Type _)) [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] :=
  SemilinearEquivClass F (RingHom.id R) M M₂
#align linear_equiv_class LinearEquivClass
-/

end

namespace SemilinearEquivClass

variable (F : Type _) [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R}

-- `σ'` becomes a metavariable, but it's OK since it's an outparam
@[nolint dangerous_instance]
instance (priority := 100) [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [s : SemilinearEquivClass F σ M M₂] : SemilinearMapClass F σ M M₂ :=
  { s with
    coe := (coe : F → M → M₂)
    coe_injective' := @FunLike.coe_injective F _ _ _ }

end SemilinearEquivClass

namespace LinearEquiv

section AddCommMonoid

variable {M₄ : Type _}

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

include R

include σ'

instance : Coe (M ≃ₛₗ[σ] M₂) (M →ₛₗ[σ] M₂) :=
  ⟨toLinearMap⟩

-- see Note [function coercion]
instance : CoeFun (M ≃ₛₗ[σ] M₂) fun _ => M → M₂ :=
  ⟨toFun⟩

/- warning: linear_equiv.coe_mk -> LinearEquiv.coe_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_mk LinearEquiv.coe_mkₓ'. -/
@[simp]
theorem coe_mk {to_fun inv_fun map_add map_smul left_inv right_inv} :
    ⇑(⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₛₗ[σ] M₂) = to_fun :=
  rfl
#align linear_equiv.coe_mk LinearEquiv.coe_mk

#print LinearEquiv.toEquiv /-
-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
@[nolint doc_blame]
def toEquiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂ := fun f => f.toAddEquiv.toEquiv
#align linear_equiv.to_equiv LinearEquiv.toEquiv
-/

/- warning: linear_equiv.to_equiv_injective -> LinearEquiv.toEquiv_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_equiv_injective LinearEquiv.toEquiv_injectiveₓ'. -/
theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂) :=
  fun ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ h => LinearEquiv.mk.inj_eq.mpr (Equiv.mk.inj h)
#align linear_equiv.to_equiv_injective LinearEquiv.toEquiv_injective

/- warning: linear_equiv.to_equiv_inj -> LinearEquiv.toEquiv_inj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_equiv_inj LinearEquiv.toEquiv_injₓ'. -/
@[simp]
theorem toEquiv_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff
#align linear_equiv.to_equiv_inj LinearEquiv.toEquiv_inj

/- warning: linear_equiv.to_linear_map_injective -> LinearEquiv.toLinearMap_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_linear_map_injective LinearEquiv.toLinearMap_injectiveₓ'. -/
theorem toLinearMap_injective : Injective (coe : (M ≃ₛₗ[σ] M₂) → M →ₛₗ[σ] M₂) := fun e₁ e₂ H =>
  toEquiv_injective <| Equiv.ext <| LinearMap.congr_fun H
#align linear_equiv.to_linear_map_injective LinearEquiv.toLinearMap_injective

/- warning: linear_equiv.to_linear_map_inj -> LinearEquiv.toLinearMap_inj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_linear_map_inj LinearEquiv.toLinearMap_injₓ'. -/
@[simp, norm_cast]
theorem toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (e₁ : M →ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
  toLinearMap_injective.eq_iff
#align linear_equiv.to_linear_map_inj LinearEquiv.toLinearMap_inj

instance : SemilinearEquivClass (M ≃ₛₗ[σ] M₂) σ M M₂
    where
  coe := LinearEquiv.toFun
  inv := LinearEquiv.invFun
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr
  left_inv := LinearEquiv.left_inv
  right_inv := LinearEquiv.right_inv
  map_add := map_add'
  map_smulₛₗ := map_smul'

/- warning: linear_equiv.coe_injective -> LinearEquiv.coe_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_injective LinearEquiv.coe_injectiveₓ'. -/
theorem coe_injective : @Injective (M ≃ₛₗ[σ] M₂) (M → M₂) coeFn :=
  FunLike.coe_injective
#align linear_equiv.coe_injective LinearEquiv.coe_injective

end

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [AddCommMonoid M₃] [AddCommMonoid M₄]

variable [AddCommMonoid N₁] [AddCommMonoid N₂]

variable {module_M : Module R M} {module_S_M₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}

variable {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ}

variable (e e' : M ≃ₛₗ[σ] M₂)

theorem toLinearMap_eq_coe : e.toLinearMap = (e : M →ₛₗ[σ] M₂) :=
  rfl
#align linear_equiv.to_linear_map_eq_coe LinearEquiv.toLinearMap_eq_coe

/- warning: linear_equiv.coe_coe -> LinearEquiv.coe_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_coe LinearEquiv.coe_coeₓ'. -/
@[simp, norm_cast]
theorem coe_coe : ⇑(e : M →ₛₗ[σ] M₂) = e :=
  rfl
#align linear_equiv.coe_coe LinearEquiv.coe_coe

/- warning: linear_equiv.coe_to_equiv -> LinearEquiv.coe_toEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_to_equiv LinearEquiv.coe_toEquivₓ'. -/
@[simp]
theorem coe_toEquiv : ⇑e.toEquiv = e :=
  rfl
#align linear_equiv.coe_to_equiv LinearEquiv.coe_toEquiv

/- warning: linear_equiv.coe_to_linear_map -> LinearEquiv.coe_toLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_to_linear_map LinearEquiv.coe_toLinearMapₓ'. -/
@[simp]
theorem coe_toLinearMap : ⇑e.toLinearMap = e :=
  rfl
#align linear_equiv.coe_to_linear_map LinearEquiv.coe_toLinearMap

/- warning: linear_equiv.to_fun_eq_coe -> LinearEquiv.toFun_eq_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_fun_eq_coe LinearEquiv.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe : e.toFun = e :=
  rfl
#align linear_equiv.to_fun_eq_coe LinearEquiv.toFun_eq_coe

section

variable {e e'}

/- warning: linear_equiv.ext -> LinearEquiv.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.ext LinearEquiv.extₓ'. -/
@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  FunLike.ext _ _ h
#align linear_equiv.ext LinearEquiv.ext

/- warning: linear_equiv.ext_iff -> LinearEquiv.ext_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.ext_iff LinearEquiv.ext_iffₓ'. -/
theorem ext_iff : e = e' ↔ ∀ x, e x = e' x :=
  FunLike.ext_iff
#align linear_equiv.ext_iff LinearEquiv.ext_iff

/- warning: linear_equiv.congr_arg -> LinearEquiv.congr_arg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.congr_arg LinearEquiv.congr_argₓ'. -/
protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  FunLike.congr_arg e
#align linear_equiv.congr_arg LinearEquiv.congr_arg

/- warning: linear_equiv.congr_fun -> LinearEquiv.congr_fun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.congr_fun LinearEquiv.congr_funₓ'. -/
protected theorem congr_fun (h : e = e') (x : M) : e x = e' x :=
  FunLike.congr_fun h x
#align linear_equiv.congr_fun LinearEquiv.congr_fun

end

section

variable (M R)

#print LinearEquiv.refl /-
/-- The identity map is a linear equivalence. -/
@[refl]
def refl [Module R M] : M ≃ₗ[R] M :=
  { LinearMap.id, Equiv.refl M with }
#align linear_equiv.refl LinearEquiv.refl
-/

end

/- warning: linear_equiv.refl_apply -> LinearEquiv.refl_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.refl_apply LinearEquiv.refl_applyₓ'. -/
@[simp]
theorem refl_apply [Module R M] (x : M) : refl R M x = x :=
  rfl
#align linear_equiv.refl_apply LinearEquiv.refl_apply

include module_M module_S_M₂ re₁ re₂

#print LinearEquiv.symm /-
/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=
  { e.toLinearMap.inverse e.invFun e.left_inv e.right_inv,
    e.toEquiv.symm with
    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv
    invFun := e.toEquiv.symm.invFun
    map_smul' := fun r x => by rw [map_smulₛₗ] }
#align linear_equiv.symm LinearEquiv.symm
-/

omit module_M module_S_M₂ re₁ re₂

#print LinearEquiv.Simps.symm_apply /-
/-- See Note [custom simps projection] -/
def Simps.symm_apply {R : Type _} {S : Type _} [Semiring R] [Semiring S] {σ : R →+* S}
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] {M : Type _} {M₂ : Type _}
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] (e : M ≃ₛₗ[σ] M₂) : M₂ → M :=
  e.symm
#align linear_equiv.simps.symm_apply LinearEquiv.Simps.symm_apply
-/

initialize_simps_projections LinearEquiv (toFun → apply, invFun → symm_apply)

include σ'

/- warning: linear_equiv.inv_fun_eq_symm -> LinearEquiv.invFun_eq_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.inv_fun_eq_symm LinearEquiv.invFun_eq_symmₓ'. -/
@[simp]
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl
#align linear_equiv.inv_fun_eq_symm LinearEquiv.invFun_eq_symm

omit σ'

/- warning: linear_equiv.coe_to_equiv_symm -> LinearEquiv.coe_toEquiv_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_to_equiv_symm LinearEquiv.coe_toEquiv_symmₓ'. -/
@[simp]
theorem coe_toEquiv_symm : ⇑e.toEquiv.symm = e.symm :=
  rfl
#align linear_equiv.coe_to_equiv_symm LinearEquiv.coe_toEquiv_symm

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {module_N₁ : Module R₁ N₁} {module_N₂ : Module R₁ N₂}

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable {σ₂₁ : R₂ →+* R₁} {σ₃₂ : R₃ →+* R₂} {σ₃₁ : R₃ →+* R₁}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂}

variable [RingHomInvPair σ₁₃ σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInvPair σ₃₁ σ₁₃]

variable (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

include σ₃₁

#print LinearEquiv.trans /-
-- Note: the `ring_hom_comp_triple σ₃₂ σ₂₁ σ₃₁` is unused, but is convenient to carry around
-- implicitly for lemmas like `linear_equiv.self_trans_symm`.
/-- Linear equivalences are transitive. -/
@[trans, nolint unused_arguments]
def trans : M₁ ≃ₛₗ[σ₁₃] M₃ :=
  { e₂₃.toLinearMap.comp e₁₂.toLinearMap, e₁₂.toEquiv.trans e₂₃.toEquiv with }
#align linear_equiv.trans LinearEquiv.trans
-/

omit σ₃₁

-- mathport name: «expr ≪≫ₗ »
infixl:80 " ≪≫ₗ " =>
  @LinearEquiv.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _)
    (RingHom.id _) (RingHom.id _) (RingHom.id _) RingHomCompTriple.ids RingHomCompTriple.ids
    RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids
    RingHomInvPair.ids

variable {e₁₂} {e₂₃}

/- warning: linear_equiv.coe_to_add_equiv -> LinearEquiv.coe_toAddEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_to_add_equiv LinearEquiv.coe_toAddEquivₓ'. -/
@[simp]
theorem coe_toAddEquiv : ⇑e.toAddEquiv = e :=
  rfl
#align linear_equiv.coe_to_add_equiv LinearEquiv.coe_toAddEquiv

/- warning: linear_equiv.to_add_monoid_hom_commutes -> LinearEquiv.toAddMonoidHom_commutes is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_add_monoid_hom_commutes LinearEquiv.toAddMonoidHom_commutesₓ'. -/
/-- The two paths coercion can take to an `add_monoid_hom` are equivalent -/
theorem toAddMonoidHom_commutes : e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom :=
  rfl
#align linear_equiv.to_add_monoid_hom_commutes LinearEquiv.toAddMonoidHom_commutes

include σ₃₁

/- warning: linear_equiv.trans_apply -> LinearEquiv.trans_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.trans_apply LinearEquiv.trans_applyₓ'. -/
@[simp]
theorem trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c) :=
  rfl
#align linear_equiv.trans_apply LinearEquiv.trans_apply

/- warning: linear_equiv.coe_trans -> LinearEquiv.coe_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_trans LinearEquiv.coe_transₓ'. -/
theorem coe_trans :
    (e₁₂.trans e₂₃ : M₁ →ₛₗ[σ₁₃] M₃) = (e₂₃ : M₂ →ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl
#align linear_equiv.coe_trans LinearEquiv.coe_trans

omit σ₃₁

include σ'

/- warning: linear_equiv.apply_symm_apply -> LinearEquiv.apply_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.apply_symm_apply LinearEquiv.apply_symm_applyₓ'. -/
@[simp]
theorem apply_symm_apply (c : M₂) : e (e.symm c) = c :=
  e.right_inv c
#align linear_equiv.apply_symm_apply LinearEquiv.apply_symm_apply

/- warning: linear_equiv.symm_apply_apply -> LinearEquiv.symm_apply_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.symm_apply_apply LinearEquiv.symm_apply_applyₓ'. -/
@[simp]
theorem symm_apply_apply (b : M) : e.symm (e b) = b :=
  e.left_inv b
#align linear_equiv.symm_apply_apply LinearEquiv.symm_apply_apply

omit σ'

include σ₃₁ σ₂₁ σ₃₂

/- warning: linear_equiv.trans_symm -> LinearEquiv.trans_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.trans_symm LinearEquiv.trans_symmₓ'. -/
@[simp]
theorem trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm :=
  rfl
#align linear_equiv.trans_symm LinearEquiv.trans_symm

/- warning: linear_equiv.symm_trans_apply -> LinearEquiv.symm_trans_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.symm_trans_apply LinearEquiv.symm_trans_applyₓ'. -/
theorem symm_trans_apply (c : M₃) :
    (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) :=
  rfl
#align linear_equiv.symm_trans_apply LinearEquiv.symm_trans_apply

omit σ₃₁ σ₂₁ σ₃₂

/- warning: linear_equiv.trans_refl -> LinearEquiv.trans_refl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.trans_refl LinearEquiv.trans_reflₓ'. -/
@[simp]
theorem trans_refl : e.trans (refl S M₂) = e :=
  toEquiv_injective e.toEquiv.trans_refl
#align linear_equiv.trans_refl LinearEquiv.trans_refl

/- warning: linear_equiv.refl_trans -> LinearEquiv.refl_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.refl_trans LinearEquiv.refl_transₓ'. -/
@[simp]
theorem refl_trans : (refl R M).trans e = e :=
  toEquiv_injective e.toEquiv.refl_trans
#align linear_equiv.refl_trans LinearEquiv.refl_trans

include σ'

/- warning: linear_equiv.symm_apply_eq -> LinearEquiv.symm_apply_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.symm_apply_eq LinearEquiv.symm_apply_eqₓ'. -/
theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
#align linear_equiv.symm_apply_eq LinearEquiv.symm_apply_eq

/- warning: linear_equiv.eq_symm_apply -> LinearEquiv.eq_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.eq_symm_apply LinearEquiv.eq_symm_applyₓ'. -/
theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
#align linear_equiv.eq_symm_apply LinearEquiv.eq_symm_apply

omit σ'

/- warning: linear_equiv.eq_comp_symm -> LinearEquiv.eq_comp_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.eq_comp_symm LinearEquiv.eq_comp_symmₓ'. -/
theorem eq_comp_symm {α : Type _} (f : M₂ → α) (g : M₁ → α) : f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g :=
  e₁₂.toEquiv.eq_comp_symm f g
#align linear_equiv.eq_comp_symm LinearEquiv.eq_comp_symm

/- warning: linear_equiv.comp_symm_eq -> LinearEquiv.comp_symm_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.comp_symm_eq LinearEquiv.comp_symm_eqₓ'. -/
theorem comp_symm_eq {α : Type _} (f : M₂ → α) (g : M₁ → α) : g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ :=
  e₁₂.toEquiv.comp_symm_eq f g
#align linear_equiv.comp_symm_eq LinearEquiv.comp_symm_eq

/- warning: linear_equiv.eq_symm_comp -> LinearEquiv.eq_symm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.eq_symm_comp LinearEquiv.eq_symm_compₓ'. -/
theorem eq_symm_comp {α : Type _} (f : α → M₁) (g : α → M₂) : f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g :=
  e₁₂.toEquiv.eq_symm_comp f g
#align linear_equiv.eq_symm_comp LinearEquiv.eq_symm_comp

/- warning: linear_equiv.symm_comp_eq -> LinearEquiv.symm_comp_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.symm_comp_eq LinearEquiv.symm_comp_eqₓ'. -/
theorem symm_comp_eq {α : Type _} (f : α → M₁) (g : α → M₂) : e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f :=
  e₁₂.toEquiv.symm_comp_eq f g
#align linear_equiv.symm_comp_eq LinearEquiv.symm_comp_eq

variable [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃] [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]

include module_M₃

/- warning: linear_equiv.eq_comp_to_linear_map_symm -> LinearEquiv.eq_comp_toLinearMap_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.eq_comp_to_linear_map_symm LinearEquiv.eq_comp_toLinearMap_symmₓ'. -/
theorem eq_comp_toLinearMap_symm (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁₂.toLinearMap = g :=
  by
  constructor <;> intro H <;> ext
  · simp [H, e₁₂.to_equiv.eq_comp_symm f g]
  · simp [← H, ← e₁₂.to_equiv.eq_comp_symm f g]
#align linear_equiv.eq_comp_to_linear_map_symm LinearEquiv.eq_comp_toLinearMap_symm

/- warning: linear_equiv.comp_to_linear_map_symm_eq -> LinearEquiv.comp_toLinearMap_symm_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.comp_to_linear_map_symm_eq LinearEquiv.comp_toLinearMap_symm_eqₓ'. -/
theorem comp_toLinearMap_symm_eq (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    g.comp e₁₂.symm.toLinearMap = f ↔ g = f.comp e₁₂.toLinearMap :=
  by
  constructor <;> intro H <;> ext
  · simp [← H, ← e₁₂.to_equiv.comp_symm_eq f g]
  · simp [H, e₁₂.to_equiv.comp_symm_eq f g]
#align linear_equiv.comp_to_linear_map_symm_eq LinearEquiv.comp_toLinearMap_symm_eq

/- warning: linear_equiv.eq_to_linear_map_symm_comp -> LinearEquiv.eq_toLinearMap_symm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.eq_to_linear_map_symm_comp LinearEquiv.eq_toLinearMap_symm_compₓ'. -/
theorem eq_toLinearMap_symm_comp (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLinearMap.comp f = g :=
  by
  constructor <;> intro H <;> ext
  · simp [H, e₁₂.to_equiv.eq_symm_comp f g]
  · simp [← H, ← e₁₂.to_equiv.eq_symm_comp f g]
#align linear_equiv.eq_to_linear_map_symm_comp LinearEquiv.eq_toLinearMap_symm_comp

/- warning: linear_equiv.to_linear_map_symm_comp_eq -> LinearEquiv.toLinearMap_symm_comp_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_linear_map_symm_comp_eq LinearEquiv.toLinearMap_symm_comp_eqₓ'. -/
theorem toLinearMap_symm_comp_eq (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.toLinearMap.comp f :=
  by
  constructor <;> intro H <;> ext
  · simp [← H, ← e₁₂.to_equiv.symm_comp_eq f g]
  · simp [H, e₁₂.to_equiv.symm_comp_eq f g]
#align linear_equiv.to_linear_map_symm_comp_eq LinearEquiv.toLinearMap_symm_comp_eq

omit module_M₃

/- warning: linear_equiv.refl_symm -> LinearEquiv.refl_symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_19 : Module.{u1, u2} R M _inst_1 _inst_6], Eq.{succ u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_19 _inst_19) (LinearEquiv.symm.{u1, u1, u2, u2} R R M M _inst_1 _inst_1 _inst_6 _inst_6 _inst_19 _inst_19 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (LinearEquiv.refl.{u1, u2} R M _inst_1 _inst_6 _inst_19)) (LinearEquiv.refl.{u1, u2} R M _inst_1 _inst_6 _inst_19)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_6 : AddCommMonoid.{u1} M] [_inst_19 : Module.{u2, u1} R M _inst_1 _inst_6], Eq.{succ u1} (LinearEquiv.{u2, u2, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) M M _inst_6 _inst_6 _inst_19 _inst_19) (LinearEquiv.symm.{u2, u2, u1, u1} R R M M _inst_1 _inst_1 _inst_6 _inst_6 _inst_19 _inst_19 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) (LinearEquiv.refl.{u2, u1} R M _inst_1 _inst_6 _inst_19)) (LinearEquiv.refl.{u2, u1} R M _inst_1 _inst_6 _inst_19)
Case conversion may be inaccurate. Consider using '#align linear_equiv.refl_symm LinearEquiv.refl_symmₓ'. -/
@[simp]
theorem refl_symm [Module R M] : (refl R M).symm = LinearEquiv.refl R M :=
  rfl
#align linear_equiv.refl_symm LinearEquiv.refl_symm

include re₁₂ re₂₁ module_M₁ module_M₂

/- warning: linear_equiv.self_trans_symm -> LinearEquiv.self_trans_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.self_trans_symm LinearEquiv.self_trans_symmₓ'. -/
@[simp]
theorem self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.trans f.symm = LinearEquiv.refl R₁ M₁ := by ext x;
  simp
#align linear_equiv.self_trans_symm LinearEquiv.self_trans_symm

/- warning: linear_equiv.symm_trans_self -> LinearEquiv.symm_trans_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.symm_trans_self LinearEquiv.symm_trans_selfₓ'. -/
@[simp]
theorem symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.symm.trans f = LinearEquiv.refl R₂ M₂ := by ext x;
  simp
#align linear_equiv.symm_trans_self LinearEquiv.symm_trans_self

omit re₁₂ re₂₁ module_M₁ module_M₂

/- warning: linear_equiv.refl_to_linear_map -> LinearEquiv.refl_toLinearMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_19 : Module.{u1, u2} R M _inst_1 _inst_6], Eq.{succ u2} (LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M M _inst_6 _inst_6 _inst_19 _inst_19) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_19 _inst_19) (LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M M _inst_6 _inst_6 _inst_19 _inst_19) (HasLiftT.mk.{succ u2, succ u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_19 _inst_19) (LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M M _inst_6 _inst_6 _inst_19 _inst_19) (CoeTCₓ.coe.{succ u2, succ u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_19 _inst_19) (LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M M _inst_6 _inst_6 _inst_19 _inst_19) (coeBase.{succ u2, succ u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_19 _inst_19) (LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M M _inst_6 _inst_6 _inst_19 _inst_19) (LinearEquiv.LinearMap.hasCoe.{u1, u1, u2, u2} R R M M _inst_1 _inst_1 _inst_6 _inst_6 _inst_19 _inst_19 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1))))) (LinearEquiv.refl.{u1, u2} R M _inst_1 _inst_6 _inst_19)) (LinearMap.id.{u1, u2} R M _inst_1 _inst_6 _inst_19)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_6 : AddCommMonoid.{u1} M] [_inst_19 : Module.{u2, u1} R M _inst_1 _inst_6], Eq.{succ u1} (LinearMap.{u2, u2, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M M _inst_6 _inst_6 _inst_19 _inst_19) (LinearEquiv.toLinearMap.{u2, u2, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) M M _inst_6 _inst_6 _inst_19 _inst_19 (LinearEquiv.refl.{u2, u1} R M _inst_1 _inst_6 _inst_19)) (LinearMap.id.{u2, u1} R M _inst_1 _inst_6 _inst_19)
Case conversion may be inaccurate. Consider using '#align linear_equiv.refl_to_linear_map LinearEquiv.refl_toLinearMapₓ'. -/
@[simp, norm_cast]
theorem refl_toLinearMap [Module R M] : (LinearEquiv.refl R M : M →ₗ[R] M) = LinearMap.id :=
  rfl
#align linear_equiv.refl_to_linear_map LinearEquiv.refl_toLinearMap

/- warning: linear_equiv.comp_coe -> LinearEquiv.comp_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.comp_coe LinearEquiv.comp_coeₓ'. -/
@[simp, norm_cast]
theorem comp_coe [Module R M] [Module R M₂] [Module R M₃] (f : M ≃ₗ[R] M₂) (f' : M₂ ≃ₗ[R] M₃) :
    (f' : M₂ →ₗ[R] M₃).comp (f : M →ₗ[R] M₂) = (f.trans f' : M ≃ₗ[R] M₃) :=
  rfl
#align linear_equiv.comp_coe LinearEquiv.comp_coe

/- warning: linear_equiv.mk_coe -> LinearEquiv.mk_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.mk_coe LinearEquiv.mk_coeₓ'. -/
@[simp]
theorem mk_coe (h₁ h₂ f h₃ h₄) : (LinearEquiv.mk e h₁ h₂ f h₃ h₄ : M ≃ₛₗ[σ] M₂) = e :=
  ext fun _ => rfl
#align linear_equiv.mk_coe LinearEquiv.mk_coe

/- warning: linear_equiv.map_add -> LinearEquiv.map_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_add LinearEquiv.map_addₓ'. -/
protected theorem map_add (a b : M) : e (a + b) = e a + e b :=
  map_add e a b
#align linear_equiv.map_add LinearEquiv.map_add

/- warning: linear_equiv.map_zero -> LinearEquiv.map_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_zero LinearEquiv.map_zeroₓ'. -/
protected theorem map_zero : e 0 = 0 :=
  map_zero e
#align linear_equiv.map_zero LinearEquiv.map_zero

/- warning: linear_equiv.map_smulₛₗ -> LinearEquiv.map_smulₛₗ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_smulₛₗ LinearEquiv.map_smulₛₗₓ'. -/
-- TODO: `simp` isn't picking up `map_smulₛₗ` for `linear_equiv`s without specifying `map_smulₛₗ f`
@[simp]
protected theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = σ c • e x :=
  e.map_smul' c x
#align linear_equiv.map_smulₛₗ LinearEquiv.map_smulₛₗ

include module_N₁ module_N₂

/- warning: linear_equiv.map_smul -> LinearEquiv.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_smul LinearEquiv.map_smulₓ'. -/
theorem map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e (c • x) = c • e x :=
  map_smulₛₗ e c x
#align linear_equiv.map_smul LinearEquiv.map_smul

omit module_N₁ module_N₂

/- warning: linear_equiv.map_eq_zero_iff -> LinearEquiv.map_eq_zero_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_eq_zero_iff LinearEquiv.map_eq_zero_iffₓ'. -/
@[simp]
theorem map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0 :=
  e.toAddEquiv.map_eq_zero_iff
#align linear_equiv.map_eq_zero_iff LinearEquiv.map_eq_zero_iff

/- warning: linear_equiv.map_ne_zero_iff -> LinearEquiv.map_ne_zero_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_ne_zero_iff LinearEquiv.map_ne_zero_iffₓ'. -/
theorem map_ne_zero_iff {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
  e.toAddEquiv.map_ne_zero_iff
#align linear_equiv.map_ne_zero_iff LinearEquiv.map_ne_zero_iff

include module_M module_S_M₂ re₁ re₂

/- warning: linear_equiv.symm_symm -> LinearEquiv.symm_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.symm_symm LinearEquiv.symm_symmₓ'. -/
@[simp]
theorem symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e := by cases e; rfl
#align linear_equiv.symm_symm LinearEquiv.symm_symm

omit module_M module_S_M₂ re₁ re₂

/- warning: linear_equiv.symm_bijective -> LinearEquiv.symm_bijective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.symm_bijective LinearEquiv.symm_bijectiveₓ'. -/
theorem symm_bijective [Module R M] [Module S M₂] [RingHomInvPair σ' σ] [RingHomInvPair σ σ'] :
    Function.Bijective (symm : (M ≃ₛₗ[σ] M₂) → M₂ ≃ₛₗ[σ'] M) :=
  Equiv.bijective
    ⟨(symm : (M ≃ₛₗ[σ] M₂) → M₂ ≃ₛₗ[σ'] M), (symm : (M₂ ≃ₛₗ[σ'] M) → M ≃ₛₗ[σ] M₂), symm_symm,
      symm_symm⟩
#align linear_equiv.symm_bijective LinearEquiv.symm_bijective

/- warning: linear_equiv.mk_coe' -> LinearEquiv.mk_coe' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.mk_coe' LinearEquiv.mk_coe'ₓ'. -/
@[simp]
theorem mk_coe' (f h₁ h₂ h₃ h₄) : (LinearEquiv.mk f h₁ h₂ (⇑e) h₃ h₄ : M₂ ≃ₛₗ[σ'] M) = e.symm :=
  symm_bijective.Injective <| ext fun x => rfl
#align linear_equiv.mk_coe' LinearEquiv.mk_coe'

/- warning: linear_equiv.symm_mk -> LinearEquiv.symm_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.symm_mk LinearEquiv.symm_mkₓ'. -/
@[simp]
theorem symm_mk (f h₁ h₂ h₃ h₄) :
    (⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm =
      {
        (⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ]
              M₂).symm with
        toFun := f
        invFun := e } :=
  rfl
#align linear_equiv.symm_mk LinearEquiv.symm_mk

/- warning: linear_equiv.coe_symm_mk -> LinearEquiv.coe_symm_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_symm_mk LinearEquiv.coe_symm_mkₓ'. -/
@[simp]
theorem coe_symm_mk [Module R M] [Module R M₂]
    {to_fun inv_fun map_add map_smul left_inv right_inv} :
    ⇑(⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun :=
  rfl
#align linear_equiv.coe_symm_mk LinearEquiv.coe_symm_mk

/- warning: linear_equiv.bijective -> LinearEquiv.bijective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.bijective LinearEquiv.bijectiveₓ'. -/
protected theorem bijective : Function.Bijective e :=
  e.toEquiv.Bijective
#align linear_equiv.bijective LinearEquiv.bijective

/- warning: linear_equiv.injective -> LinearEquiv.injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.injective LinearEquiv.injectiveₓ'. -/
protected theorem injective : Function.Injective e :=
  e.toEquiv.Injective
#align linear_equiv.injective LinearEquiv.injective

/- warning: linear_equiv.surjective -> LinearEquiv.surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.surjective LinearEquiv.surjectiveₓ'. -/
protected theorem surjective : Function.Surjective e :=
  e.toEquiv.Surjective
#align linear_equiv.surjective LinearEquiv.surjective

/- warning: linear_equiv.image_eq_preimage -> LinearEquiv.image_eq_preimage is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.image_eq_preimage LinearEquiv.image_eq_preimageₓ'. -/
protected theorem image_eq_preimage (s : Set M) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align linear_equiv.image_eq_preimage LinearEquiv.image_eq_preimage

/- warning: linear_equiv.image_symm_eq_preimage -> LinearEquiv.image_symm_eq_preimage is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.image_symm_eq_preimage LinearEquiv.image_symm_eq_preimageₓ'. -/
protected theorem image_symm_eq_preimage (s : Set M₂) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.symm.image_eq_preimage s
#align linear_equiv.image_symm_eq_preimage LinearEquiv.image_symm_eq_preimage

end

/- warning: ring_equiv.to_semilinear_equiv -> RingEquiv.toSemilinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_equiv.to_semilinear_equiv RingEquiv.toSemilinearEquivₓ'. -/
/-- Interpret a `ring_equiv` `f` as an `f`-semilinear equiv. -/
@[simps]
def RingEquiv.toSemilinearEquiv (f : R ≃+* S) : by
    haveI := RingHomInvPair.of_ringEquiv f <;>
        haveI := RingHomInvPair.symm (↑f : R →+* S) (f.symm : S →+* R) <;>
      exact R ≃ₛₗ[(↑f : R →+* S)] S :=
  { f with
    toFun := f
    map_smul' := f.map_mul }
#align ring_equiv.to_semilinear_equiv RingEquiv.toSemilinearEquiv

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

/- warning: linear_equiv.of_involutive -> LinearEquiv.ofInvolutive is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] {σ : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1)} {σ' : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1)} [_inst_9 : RingHomInvPair.{u1, u1} R R _inst_1 _inst_1 σ σ'] [_inst_10 : RingHomInvPair.{u1, u1} R R _inst_1 _inst_1 σ' σ] {module_M : Module.{u1, u2} R M _inst_1 _inst_6} (f : LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 σ M M _inst_6 _inst_6 module_M module_M), (Function.Involutive.{succ u2} M (coeFn.{succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 σ M M _inst_6 _inst_6 module_M module_M) (fun (_x : LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 σ M M _inst_6 _inst_6 module_M module_M) => M -> M) (LinearMap.hasCoeToFun.{u1, u1, u2, u2} R R M M _inst_1 _inst_1 _inst_6 _inst_6 module_M module_M σ) f)) -> (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 σ σ' _inst_9 _inst_10 M M _inst_6 _inst_6 module_M module_M)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] {σ : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1)} {σ' : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1)} [_inst_9 : RingHomInvPair.{u1, u1} R R _inst_1 _inst_1 σ σ'] [_inst_10 : RingHomInvPair.{u1, u1} R R _inst_1 _inst_1 σ' σ] {module_M : Module.{u1, u2} R M _inst_1 _inst_6} (f : LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 σ M M _inst_6 _inst_6 module_M module_M), (Function.Involutive.{succ u2} M (FunLike.coe.{succ u2, succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R _inst_1 _inst_1 σ M M _inst_6 _inst_6 module_M module_M) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => M) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u2, u2} R R M M _inst_1 _inst_1 _inst_6 _inst_6 module_M module_M σ) f)) -> (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 σ σ' _inst_9 _inst_10 M M _inst_6 _inst_6 module_M module_M)
Case conversion may be inaccurate. Consider using '#align linear_equiv.of_involutive LinearEquiv.ofInvolutiveₓ'. -/
/-- An involutive linear map is a linear equivalence. -/
def ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {module_M : Module R M} (f : M →ₛₗ[σ] M) (hf : Involutive f) : M ≃ₛₗ[σ] M :=
  { f, hf.toPerm f with }
#align linear_equiv.of_involutive LinearEquiv.ofInvolutive

/- warning: linear_equiv.coe_of_involutive -> LinearEquiv.coe_ofInvolutive is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_of_involutive LinearEquiv.coe_ofInvolutiveₓ'. -/
@[simp]
theorem coe_ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {module_M : Module R M} (f : M →ₛₗ[σ] M) (hf : Involutive f) : ⇑(ofInvolutive f hf) = f :=
  rfl
#align linear_equiv.coe_of_involutive LinearEquiv.coe_ofInvolutive

section RestrictScalars

variable (R) [Module R M] [Module R M₂] [Module S M] [Module S M₂]
  [LinearMap.CompatibleSMul M M₂ R S]

#print LinearEquiv.restrictScalars /-
/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `linear_map.restrict_scalars`. -/
@[simps]
def restrictScalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ :=
  { f.toLinearMap.restrictScalars R with
    toFun := f
    invFun := f.symm
    left_inv := f.left_inv
    right_inv := f.right_inv }
#align linear_equiv.restrict_scalars LinearEquiv.restrictScalars
-/

/- warning: linear_equiv.restrict_scalars_injective -> LinearEquiv.restrictScalars_injective is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {S : Type.{u2}} {M : Type.{u3}} {M₂ : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] [_inst_6 : AddCommMonoid.{u3} M] [_inst_8 : AddCommMonoid.{u4} M₂] [_inst_9 : Module.{u1, u3} R M _inst_1 _inst_6] [_inst_10 : Module.{u1, u4} R M₂ _inst_1 _inst_8] [_inst_11 : Module.{u2, u3} S M _inst_2 _inst_6] [_inst_12 : Module.{u2, u4} S M₂ _inst_2 _inst_8] [_inst_13 : LinearMap.CompatibleSMul.{u3, u4, u1, u2} M M₂ _inst_6 _inst_8 R S _inst_2 (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (Module.toMulActionWithZero.{u1, u3} R M _inst_1 _inst_6 _inst_9)))) _inst_11 (SMulZeroClass.toHasSmul.{u1, u4} R M₂ (AddZeroClass.toHasZero.{u4} M₂ (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_8))) (SMulWithZero.toSmulZeroClass.{u1, u4} R M₂ (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u4} M₂ (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_8))) (MulActionWithZero.toSMulWithZero.{u1, u4} R M₂ (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddZeroClass.toHasZero.{u4} M₂ (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_8))) (Module.toMulActionWithZero.{u1, u4} R M₂ _inst_1 _inst_8 _inst_10)))) _inst_12], Function.Injective.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (LinearEquiv.{u2, u2, u3, u4} S S _inst_2 _inst_2 (RingHom.id.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHom.id.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomInvPair.ids.{u2} S _inst_2) (RingHomInvPair.ids.{u2} S _inst_2) M M₂ _inst_6 _inst_8 _inst_11 _inst_12) (LinearEquiv.{u1, u1, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M₂ _inst_6 _inst_8 _inst_9 _inst_10) (LinearEquiv.restrictScalars.{u1, u2, u3, u4} R S M M₂ _inst_1 _inst_2 _inst_6 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13)
but is expected to have type
  forall (R : Type.{u1}) {S : Type.{u2}} {M : Type.{u4}} {M₂ : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] [_inst_6 : AddCommMonoid.{u4} M] [_inst_8 : AddCommMonoid.{u3} M₂] [_inst_9 : Module.{u1, u4} R M _inst_1 _inst_6] [_inst_10 : Module.{u1, u3} R M₂ _inst_1 _inst_8] [_inst_11 : Module.{u2, u4} S M _inst_2 _inst_6] [_inst_12 : Module.{u2, u3} S M₂ _inst_2 _inst_8] [_inst_13 : LinearMap.CompatibleSMul.{u4, u3, u1, u2} M M₂ _inst_6 _inst_8 R S _inst_2 (SMulZeroClass.toSMul.{u1, u4} R M (AddMonoid.toZero.{u4} M (AddCommMonoid.toAddMonoid.{u4} M _inst_6)) (SMulWithZero.toSMulZeroClass.{u1, u4} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u4} M (AddCommMonoid.toAddMonoid.{u4} M _inst_6)) (MulActionWithZero.toSMulWithZero.{u1, u4} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddMonoid.toZero.{u4} M (AddCommMonoid.toAddMonoid.{u4} M _inst_6)) (Module.toMulActionWithZero.{u1, u4} R M _inst_1 _inst_6 _inst_9)))) _inst_11 (SMulZeroClass.toSMul.{u1, u3} R M₂ (AddMonoid.toZero.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_8)) (SMulWithZero.toSMulZeroClass.{u1, u3} R M₂ (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_8)) (MulActionWithZero.toSMulWithZero.{u1, u3} R M₂ (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddMonoid.toZero.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_8)) (Module.toMulActionWithZero.{u1, u3} R M₂ _inst_1 _inst_8 _inst_10)))) _inst_12], Function.Injective.{max (succ u4) (succ u3), max (succ u4) (succ u3)} (LinearEquiv.{u2, u2, u4, u3} S S _inst_2 _inst_2 (RingHom.id.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHom.id.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomInvPair.ids.{u2} S _inst_2) (RingHomInvPair.ids.{u2} S _inst_2) M M₂ _inst_6 _inst_8 _inst_11 _inst_12) (LinearEquiv.{u1, u1, u4, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M₂ _inst_6 _inst_8 _inst_9 _inst_10) (LinearEquiv.restrictScalars.{u1, u2, u4, u3} R S M M₂ _inst_1 _inst_2 _inst_6 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13)
Case conversion may be inaccurate. Consider using '#align linear_equiv.restrict_scalars_injective LinearEquiv.restrictScalars_injectiveₓ'. -/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M ≃ₗ[S] M₂) → M ≃ₗ[R] M₂) := fun f g h =>
  ext (LinearEquiv.congr_fun h : _)
#align linear_equiv.restrict_scalars_injective LinearEquiv.restrictScalars_injective

/- warning: linear_equiv.restrict_scalars_inj -> LinearEquiv.restrictScalars_inj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.restrict_scalars_inj LinearEquiv.restrictScalars_injₓ'. -/
@[simp]
theorem restrictScalars_inj (f g : M ≃ₗ[S] M₂) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff
#align linear_equiv.restrict_scalars_inj LinearEquiv.restrictScalars_inj

end RestrictScalars

section Automorphisms

variable [Module R M]

#print LinearEquiv.automorphismGroup /-
instance automorphismGroup : Group (M ≃ₗ[R] M)
    where
  mul f g := g.trans f
  one := LinearEquiv.refl R M
  inv f := f.symm
  mul_assoc f g h := rfl
  mul_one f := ext fun x => rfl
  one_mul f := ext fun x => rfl
  mul_left_inv f := ext <| f.left_inv
#align linear_equiv.automorphism_group LinearEquiv.automorphismGroup
-/

#print LinearEquiv.automorphismGroup.toLinearMapMonoidHom /-
/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
@[simps]
def automorphismGroup.toLinearMapMonoidHom : (M ≃ₗ[R] M) →* M →ₗ[R] M
    where
  toFun := coe
  map_one' := rfl
  map_mul' _ _ := rfl
#align linear_equiv.automorphism_group.to_linear_map_monoid_hom LinearEquiv.automorphismGroup.toLinearMapMonoidHom
-/

#print LinearEquiv.applyDistribMulAction /-
/-- The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance applyDistribMulAction : DistribMulAction (M ≃ₗ[R] M) M
    where
  smul := (· <| ·)
  smul_zero := LinearEquiv.map_zero
  smul_add := LinearEquiv.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align linear_equiv.apply_distrib_mul_action LinearEquiv.applyDistribMulAction
-/

/- warning: linear_equiv.smul_def -> LinearEquiv.smul_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.smul_def LinearEquiv.smul_defₓ'. -/
@[simp]
protected theorem smul_def (f : M ≃ₗ[R] M) (a : M) : f • a = f a :=
  rfl
#align linear_equiv.smul_def LinearEquiv.smul_def

/- warning: linear_equiv.apply_has_faithful_smul -> LinearEquiv.apply_faithfulSMul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_9 : Module.{u1, u2} R M _inst_1 _inst_6], FaithfulSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (SMulZeroClass.toHasSmul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (DistribSMul.toSmulZeroClass.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribMulAction.toDistribSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (DivInvMonoid.toMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (Group.toDivInvMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (LinearEquiv.automorphismGroup.{u1, u2} R M _inst_1 _inst_6 _inst_9))) (AddCommMonoid.toAddMonoid.{u2} M _inst_6) (LinearEquiv.applyDistribMulAction.{u1, u2} R M _inst_1 _inst_6 _inst_9))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_9 : Module.{u1, u2} R M _inst_1 _inst_6], FaithfulSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (SMulZeroClass.toSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribSMul.toSMulZeroClass.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribMulAction.toDistribSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (DivInvMonoid.toMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (Group.toDivInvMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (LinearEquiv.automorphismGroup.{u1, u2} R M _inst_1 _inst_6 _inst_9))) (AddCommMonoid.toAddMonoid.{u2} M _inst_6) (LinearEquiv.applyDistribMulAction.{u1, u2} R M _inst_1 _inst_6 _inst_9))))
Case conversion may be inaccurate. Consider using '#align linear_equiv.apply_has_faithful_smul LinearEquiv.apply_faithfulSMulₓ'. -/
/-- `linear_equiv.apply_distrib_mul_action` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (M ≃ₗ[R] M) M :=
  ⟨fun _ _ => LinearEquiv.ext⟩
#align linear_equiv.apply_has_faithful_smul LinearEquiv.apply_faithfulSMul

/- warning: linear_equiv.apply_smul_comm_class -> LinearEquiv.apply_smulCommClass is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_9 : Module.{u1, u2} R M _inst_1 _inst_6], SMulCommClass.{u1, u2, u2} R (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (Module.toMulActionWithZero.{u1, u2} R M _inst_1 _inst_6 _inst_9)))) (SMulZeroClass.toHasSmul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (DistribSMul.toSmulZeroClass.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribMulAction.toDistribSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (DivInvMonoid.toMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (Group.toDivInvMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (LinearEquiv.automorphismGroup.{u1, u2} R M _inst_1 _inst_6 _inst_9))) (AddCommMonoid.toAddMonoid.{u2} M _inst_6) (LinearEquiv.applyDistribMulAction.{u1, u2} R M _inst_1 _inst_6 _inst_9))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_9 : Module.{u1, u2} R M _inst_1 _inst_6], SMulCommClass.{u1, u2, u2} R (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (SMulZeroClass.toSMul.{u1, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (Module.toMulActionWithZero.{u1, u2} R M _inst_1 _inst_6 _inst_9)))) (SMulZeroClass.toSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribSMul.toSMulZeroClass.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribMulAction.toDistribSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (DivInvMonoid.toMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (Group.toDivInvMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (LinearEquiv.automorphismGroup.{u1, u2} R M _inst_1 _inst_6 _inst_9))) (AddCommMonoid.toAddMonoid.{u2} M _inst_6) (LinearEquiv.applyDistribMulAction.{u1, u2} R M _inst_1 _inst_6 _inst_9))))
Case conversion may be inaccurate. Consider using '#align linear_equiv.apply_smul_comm_class LinearEquiv.apply_smulCommClassₓ'. -/
instance apply_smulCommClass : SMulCommClass R (M ≃ₗ[R] M) M
    where smul_comm r e m := (e.map_smul r m).symm
#align linear_equiv.apply_smul_comm_class LinearEquiv.apply_smulCommClass

/- warning: linear_equiv.apply_smul_comm_class' -> LinearEquiv.apply_smulCommClass' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_9 : Module.{u1, u2} R M _inst_1 _inst_6], SMulCommClass.{u2, u1, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) R M (SMulZeroClass.toHasSmul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (DistribSMul.toSmulZeroClass.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribMulAction.toDistribSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (DivInvMonoid.toMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (Group.toDivInvMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (LinearEquiv.automorphismGroup.{u1, u2} R M _inst_1 _inst_6 _inst_9))) (AddCommMonoid.toAddMonoid.{u2} M _inst_6) (LinearEquiv.applyDistribMulAction.{u1, u2} R M _inst_1 _inst_6 _inst_9)))) (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (Module.toMulActionWithZero.{u1, u2} R M _inst_1 _inst_6 _inst_9))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_9 : Module.{u1, u2} R M _inst_1 _inst_6], SMulCommClass.{u2, u1, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) R M (SMulZeroClass.toSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribSMul.toSMulZeroClass.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (DistribMulAction.toDistribSMul.{u2, u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) M (DivInvMonoid.toMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (Group.toDivInvMonoid.{u2} (LinearEquiv.{u1, u1, u2, u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_6 _inst_6 _inst_9 _inst_9) (LinearEquiv.automorphismGroup.{u1, u2} R M _inst_1 _inst_6 _inst_9))) (AddCommMonoid.toAddMonoid.{u2} M _inst_6) (LinearEquiv.applyDistribMulAction.{u1, u2} R M _inst_1 _inst_6 _inst_9)))) (SMulZeroClass.toSMul.{u1, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (Module.toMulActionWithZero.{u1, u2} R M _inst_1 _inst_6 _inst_9))))
Case conversion may be inaccurate. Consider using '#align linear_equiv.apply_smul_comm_class' LinearEquiv.apply_smulCommClass'ₓ'. -/
instance apply_smulCommClass' : SMulCommClass (M ≃ₗ[R] M) R M
    where smul_comm := LinearEquiv.map_smul
#align linear_equiv.apply_smul_comm_class' LinearEquiv.apply_smulCommClass'

end Automorphisms

section OfSubsingleton

variable (M M₂) [Module R M] [Module R M₂] [Subsingleton M] [Subsingleton M₂]

#print LinearEquiv.ofSubsingleton /-
/-- Any two modules that are subsingletons are isomorphic. -/
@[simps]
def ofSubsingleton : M ≃ₗ[R] M₂ :=
  { (0 : M →ₗ[R] M₂) with
    toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun x => Subsingleton.elim _ _
    right_inv := fun x => Subsingleton.elim _ _ }
#align linear_equiv.of_subsingleton LinearEquiv.ofSubsingleton
-/

#print LinearEquiv.ofSubsingleton_self /-
@[simp]
theorem ofSubsingleton_self : ofSubsingleton M M = refl R M := by ext; simp
#align linear_equiv.of_subsingleton_self LinearEquiv.ofSubsingleton_self
-/

end OfSubsingleton

end AddCommMonoid

end LinearEquiv

namespace Module

/- warning: module.comp_hom.to_linear_equiv -> Module.compHom.toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align module.comp_hom.to_linear_equiv Module.compHom.toLinearEquivₓ'. -/
/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `module.comp_hom S g` . -/
@[simps]
def compHom.toLinearEquiv {R S : Type _} [Semiring R] [Semiring S] (g : R ≃+* S) :
    haveI := comp_hom S (↑g : R →+* S)
    R ≃ₗ[R] S :=
  { g with
    toFun := (g : R → S)
    invFun := (g.symm : S → R)
    map_smul' := g.map_mul }
#align module.comp_hom.to_linear_equiv Module.compHom.toLinearEquiv

end Module

namespace DistribMulAction

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable [Group S] [DistribMulAction S M] [SMulCommClass S R M]

/- warning: distrib_mul_action.to_linear_equiv -> DistribMulAction.toLinearEquiv is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {S : Type.{u2}} (M : Type.{u3}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u1, u3} R M _inst_1 _inst_2] [_inst_4 : Group.{u2} S] [_inst_5 : DistribMulAction.{u2, u3} S M (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4)) (AddCommMonoid.toAddMonoid.{u3} M _inst_2)] [_inst_6 : SMulCommClass.{u2, u1, u3} S R M (SMulZeroClass.toHasSmul.{u2, u3} S M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (DistribSMul.toSmulZeroClass.{u2, u3} S M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (DistribMulAction.toDistribSMul.{u2, u3} S M (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4)) (AddCommMonoid.toAddMonoid.{u3} M _inst_2) _inst_5))) (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (Module.toMulActionWithZero.{u1, u3} R M _inst_1 _inst_2 _inst_3))))], S -> (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3)
but is expected to have type
  forall (R : Type.{u1}) {S : Type.{u2}} (M : Type.{u3}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u1, u3} R M _inst_1 _inst_2] [_inst_4 : Group.{u2} S] [_inst_5 : DistribMulAction.{u2, u3} S M (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4)) (AddCommMonoid.toAddMonoid.{u3} M _inst_2)] [_inst_6 : SMulCommClass.{u2, u1, u3} S R M (SMulZeroClass.toSMul.{u2, u3} S M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u3} S M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (DistribMulAction.toDistribSMul.{u2, u3} S M (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4)) (AddCommMonoid.toAddMonoid.{u3} M _inst_2) _inst_5))) (SMulZeroClass.toSMul.{u1, u3} R M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u3} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (Module.toMulActionWithZero.{u1, u3} R M _inst_1 _inst_2 _inst_3))))], S -> (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3)
Case conversion may be inaccurate. Consider using '#align distrib_mul_action.to_linear_equiv DistribMulAction.toLinearEquivₓ'. -/
/-- Each element of the group defines a linear equivalence.

This is a stronger version of `distrib_mul_action.to_add_equiv`. -/
@[simps]
def toLinearEquiv (s : S) : M ≃ₗ[R] M :=
  { toAddEquiv M s, toLinearMap R M s with }
#align distrib_mul_action.to_linear_equiv DistribMulAction.toLinearEquiv

/- warning: distrib_mul_action.to_module_aut -> DistribMulAction.toModuleAut is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {S : Type.{u2}} (M : Type.{u3}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u1, u3} R M _inst_1 _inst_2] [_inst_4 : Group.{u2} S] [_inst_5 : DistribMulAction.{u2, u3} S M (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4)) (AddCommMonoid.toAddMonoid.{u3} M _inst_2)] [_inst_6 : SMulCommClass.{u2, u1, u3} S R M (SMulZeroClass.toHasSmul.{u2, u3} S M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (DistribSMul.toSmulZeroClass.{u2, u3} S M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (DistribMulAction.toDistribSMul.{u2, u3} S M (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4)) (AddCommMonoid.toAddMonoid.{u3} M _inst_2) _inst_5))) (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (Module.toMulActionWithZero.{u1, u3} R M _inst_1 _inst_2 _inst_3))))], MonoidHom.{u2, u3} S (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3) (Monoid.toMulOneClass.{u2} S (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4))) (Monoid.toMulOneClass.{u3} (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3) (DivInvMonoid.toMonoid.{u3} (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3) (Group.toDivInvMonoid.{u3} (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3) (LinearEquiv.automorphismGroup.{u1, u3} R M _inst_1 _inst_2 _inst_3))))
but is expected to have type
  forall (R : Type.{u1}) {S : Type.{u2}} (M : Type.{u3}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u1, u3} R M _inst_1 _inst_2] [_inst_4 : Group.{u2} S] [_inst_5 : DistribMulAction.{u2, u3} S M (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4)) (AddCommMonoid.toAddMonoid.{u3} M _inst_2)] [_inst_6 : SMulCommClass.{u2, u1, u3} S R M (SMulZeroClass.toSMul.{u2, u3} S M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u3} S M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (DistribMulAction.toDistribSMul.{u2, u3} S M (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4)) (AddCommMonoid.toAddMonoid.{u3} M _inst_2) _inst_5))) (SMulZeroClass.toSMul.{u1, u3} R M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u3} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) (Module.toMulActionWithZero.{u1, u3} R M _inst_1 _inst_2 _inst_3))))], MonoidHom.{u2, u3} S (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3) (Monoid.toMulOneClass.{u2} S (DivInvMonoid.toMonoid.{u2} S (Group.toDivInvMonoid.{u2} S _inst_4))) (Monoid.toMulOneClass.{u3} (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3) (DivInvMonoid.toMonoid.{u3} (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3) (Group.toDivInvMonoid.{u3} (LinearEquiv.{u1, u1, u3, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M M _inst_2 _inst_2 _inst_3 _inst_3) (LinearEquiv.automorphismGroup.{u1, u3} R M _inst_1 _inst_2 _inst_3))))
Case conversion may be inaccurate. Consider using '#align distrib_mul_action.to_module_aut DistribMulAction.toModuleAutₓ'. -/
/-- Each element of the group defines a module automorphism.

This is a stronger version of `distrib_mul_action.to_add_aut`. -/
@[simps]
def toModuleAut : S →* M ≃ₗ[R] M where
  toFun := toLinearEquiv R M
  map_one' := LinearEquiv.ext <| one_smul _
  map_mul' a b := LinearEquiv.ext <| mul_smul _ _
#align distrib_mul_action.to_module_aut DistribMulAction.toModuleAut

end DistribMulAction

namespace AddEquiv

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂]

variable (e : M ≃+ M₂)

/- warning: add_equiv.to_linear_equiv -> AddEquiv.toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.to_linear_equiv AddEquiv.toLinearEquivₓ'. -/
/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
  { e with map_smul' := h }
#align add_equiv.to_linear_equiv AddEquiv.toLinearEquiv

/- warning: add_equiv.coe_to_linear_equiv -> AddEquiv.coe_toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.coe_to_linear_equiv AddEquiv.coe_toLinearEquivₓ'. -/
@[simp]
theorem coe_toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLinearEquiv h) = e :=
  rfl
#align add_equiv.coe_to_linear_equiv AddEquiv.coe_toLinearEquiv

/- warning: add_equiv.coe_to_linear_equiv_symm -> AddEquiv.coe_toLinearEquiv_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.coe_to_linear_equiv_symm AddEquiv.coe_toLinearEquiv_symmₓ'. -/
@[simp]
theorem coe_toLinearEquiv_symm (h : ∀ (c : R) (x), e (c • x) = c • e x) :
    ⇑(e.toLinearEquiv h).symm = e.symm :=
  rfl
#align add_equiv.coe_to_linear_equiv_symm AddEquiv.coe_toLinearEquiv_symm

/- warning: add_equiv.to_nat_linear_equiv -> AddEquiv.toNatLinearEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {M₂ : Type.{u2}} [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : AddCommMonoid.{u2} M₂], (AddEquiv.{u1, u2} M M₂ (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2))) (AddZeroClass.toHasAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_3)))) -> (LinearEquiv.{0, 0, u1, u2} Nat Nat Nat.semiring Nat.semiring (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHomInvPair.ids.{0} Nat Nat.semiring) (RingHomInvPair.ids.{0} Nat Nat.semiring) M M₂ _inst_2 _inst_3 (AddCommMonoid.natModule.{u1} M _inst_2) (AddCommMonoid.natModule.{u2} M₂ _inst_3))
but is expected to have type
  forall {M : Type.{u1}} {M₂ : Type.{u2}} [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : AddCommMonoid.{u2} M₂], (AddEquiv.{u1, u2} M M₂ (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2))) (AddZeroClass.toAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_3)))) -> (LinearEquiv.{0, 0, u1, u2} Nat Nat Nat.semiring Nat.semiring (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHomInvPair.ids.{0} Nat Nat.semiring) (RingHomInvPair.ids.{0} Nat Nat.semiring) M M₂ _inst_2 _inst_3 (AddCommMonoid.natModule.{u1} M _inst_2) (AddCommMonoid.natModule.{u2} M₂ _inst_3))
Case conversion may be inaccurate. Consider using '#align add_equiv.to_nat_linear_equiv AddEquiv.toNatLinearEquivₓ'. -/
/-- An additive equivalence between commutative additive monoids is a linear equivalence between
ℕ-modules -/
def toNatLinearEquiv : M ≃ₗ[ℕ] M₂ :=
  e.toLinearEquiv fun c a => by erw [e.to_add_monoid_hom.map_nsmul]; rfl
#align add_equiv.to_nat_linear_equiv AddEquiv.toNatLinearEquiv

/- warning: add_equiv.coe_to_nat_linear_equiv -> AddEquiv.coe_toNatLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.coe_to_nat_linear_equiv AddEquiv.coe_toNatLinearEquivₓ'. -/
@[simp]
theorem coe_toNatLinearEquiv : ⇑e.toNatLinearEquiv = e :=
  rfl
#align add_equiv.coe_to_nat_linear_equiv AddEquiv.coe_toNatLinearEquiv

/- warning: add_equiv.to_nat_linear_equiv_to_add_equiv -> AddEquiv.toNatLinearEquiv_toAddEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.to_nat_linear_equiv_to_add_equiv AddEquiv.toNatLinearEquiv_toAddEquivₓ'. -/
@[simp]
theorem toNatLinearEquiv_toAddEquiv : e.toNatLinearEquiv.toAddEquiv = e := by ext; rfl
#align add_equiv.to_nat_linear_equiv_to_add_equiv AddEquiv.toNatLinearEquiv_toAddEquiv

/- warning: linear_equiv.to_add_equiv_to_nat_linear_equiv -> LinearEquiv.toAddEquiv_toNatLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_add_equiv_to_nat_linear_equiv LinearEquiv.toAddEquiv_toNatLinearEquivₓ'. -/
@[simp]
theorem LinearEquiv.toAddEquiv_toNatLinearEquiv (e : M ≃ₗ[ℕ] M₂) :
    e.toAddEquiv.toNatLinearEquiv = e :=
  FunLike.coe_injective rfl
#align linear_equiv.to_add_equiv_to_nat_linear_equiv LinearEquiv.toAddEquiv_toNatLinearEquiv

/- warning: add_equiv.to_nat_linear_equiv_symm -> AddEquiv.toNatLinearEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {M₂ : Type.{u2}} [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : AddCommMonoid.{u2} M₂] (e : AddEquiv.{u1, u2} M M₂ (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2))) (AddZeroClass.toHasAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_3)))), Eq.{max (succ u2) (succ u1)} (LinearEquiv.{0, 0, u2, u1} Nat Nat Nat.semiring Nat.semiring (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHomInvPair.ids.{0} Nat Nat.semiring) (RingHomInvPair.ids.{0} Nat Nat.semiring) M₂ M _inst_3 _inst_2 (AddCommMonoid.natModule.{u2} M₂ _inst_3) (AddCommMonoid.natModule.{u1} M _inst_2)) (LinearEquiv.symm.{0, 0, u1, u2} Nat Nat M M₂ Nat.semiring Nat.semiring _inst_2 _inst_3 (AddCommMonoid.natModule.{u1} M _inst_2) (AddCommMonoid.natModule.{u2} M₂ _inst_3) (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHomInvPair.ids.{0} Nat Nat.semiring) (RingHomInvPair.ids.{0} Nat Nat.semiring) (AddEquiv.toNatLinearEquiv.{u1, u2} M M₂ _inst_2 _inst_3 e)) (AddEquiv.toNatLinearEquiv.{u2, u1} M₂ M _inst_3 _inst_2 (AddEquiv.symm.{u1, u2} M M₂ (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2))) (AddZeroClass.toHasAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_3))) e))
but is expected to have type
  forall {M : Type.{u2}} {M₂ : Type.{u1}} [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u1} M₂] (e : AddEquiv.{u2, u1} M M₂ (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (AddZeroClass.toAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddCommMonoid.toAddMonoid.{u1} M₂ _inst_3)))), Eq.{max (succ u2) (succ u1)} (LinearEquiv.{0, 0, u1, u2} Nat Nat Nat.semiring Nat.semiring (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHomInvPair.ids.{0} Nat Nat.semiring) (RingHomInvPair.ids.{0} Nat Nat.semiring) M₂ M _inst_3 _inst_2 (AddCommMonoid.natModule.{u1} M₂ _inst_3) (AddCommMonoid.natModule.{u2} M _inst_2)) (LinearEquiv.symm.{0, 0, u2, u1} Nat Nat M M₂ Nat.semiring Nat.semiring _inst_2 _inst_3 (AddCommMonoid.natModule.{u2} M _inst_2) (AddCommMonoid.natModule.{u1} M₂ _inst_3) (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHom.id.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (RingHomInvPair.ids.{0} Nat Nat.semiring) (RingHomInvPair.ids.{0} Nat Nat.semiring) (AddEquiv.toNatLinearEquiv.{u2, u1} M M₂ _inst_2 _inst_3 e)) (AddEquiv.toNatLinearEquiv.{u1, u2} M₂ M _inst_3 _inst_2 (AddEquiv.symm.{u2, u1} M M₂ (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (AddZeroClass.toAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddCommMonoid.toAddMonoid.{u1} M₂ _inst_3))) e))
Case conversion may be inaccurate. Consider using '#align add_equiv.to_nat_linear_equiv_symm AddEquiv.toNatLinearEquiv_symmₓ'. -/
@[simp]
theorem toNatLinearEquiv_symm : e.toNatLinearEquiv.symm = e.symm.toNatLinearEquiv :=
  rfl
#align add_equiv.to_nat_linear_equiv_symm AddEquiv.toNatLinearEquiv_symm

#print AddEquiv.toNatLinearEquiv_refl /-
@[simp]
theorem toNatLinearEquiv_refl : (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.refl ℕ M :=
  rfl
#align add_equiv.to_nat_linear_equiv_refl AddEquiv.toNatLinearEquiv_refl
-/

/- warning: add_equiv.to_nat_linear_equiv_trans -> AddEquiv.toNatLinearEquiv_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.to_nat_linear_equiv_trans AddEquiv.toNatLinearEquiv_transₓ'. -/
@[simp]
theorem toNatLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    e.toNatLinearEquiv.trans e₂.toNatLinearEquiv = (e.trans e₂).toNatLinearEquiv :=
  rfl
#align add_equiv.to_nat_linear_equiv_trans AddEquiv.toNatLinearEquiv_trans

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]

variable (e : M ≃+ M₂)

/- warning: add_equiv.to_int_linear_equiv -> AddEquiv.toIntLinearEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : AddCommGroup.{u1} M] [_inst_2 : AddCommGroup.{u2} M₂], (AddEquiv.{u1, u2} M M₂ (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1))))) (AddZeroClass.toHasAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (SubNegMonoid.toAddMonoid.{u2} M₂ (AddGroup.toSubNegMonoid.{u2} M₂ (AddCommGroup.toAddGroup.{u2} M₂ _inst_2)))))) -> (LinearEquiv.{0, 0, u1, u2} Int Int Int.semiring Int.semiring (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.semiring)) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.semiring)) (RingHomInvPair.ids.{0} Int Int.semiring) (RingHomInvPair.ids.{0} Int Int.semiring) M M₂ (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M₂ _inst_2) (AddCommGroup.intModule.{u1} M _inst_1) (AddCommGroup.intModule.{u2} M₂ _inst_2))
but is expected to have type
  forall {M : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : AddCommGroup.{u1} M] [_inst_2 : AddCommGroup.{u2} M₂], (AddEquiv.{u1, u2} M M₂ (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1))))) (AddZeroClass.toAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (SubNegMonoid.toAddMonoid.{u2} M₂ (AddGroup.toSubNegMonoid.{u2} M₂ (AddCommGroup.toAddGroup.{u2} M₂ _inst_2)))))) -> (LinearEquiv.{0, 0, u1, u2} Int Int Int.instSemiringInt Int.instSemiringInt (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)) (RingHomInvPair.ids.{0} Int Int.instSemiringInt) (RingHomInvPair.ids.{0} Int Int.instSemiringInt) M M₂ (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M₂ _inst_2) (AddCommGroup.intModule.{u1} M _inst_1) (AddCommGroup.intModule.{u2} M₂ _inst_2))
Case conversion may be inaccurate. Consider using '#align add_equiv.to_int_linear_equiv AddEquiv.toIntLinearEquivₓ'. -/
/-- An additive equivalence between commutative additive groups is a linear
equivalence between ℤ-modules -/
def toIntLinearEquiv : M ≃ₗ[ℤ] M₂ :=
  e.toLinearEquiv fun c a => e.toAddMonoidHom.map_zsmul a c
#align add_equiv.to_int_linear_equiv AddEquiv.toIntLinearEquiv

/- warning: add_equiv.coe_to_int_linear_equiv -> AddEquiv.coe_toIntLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.coe_to_int_linear_equiv AddEquiv.coe_toIntLinearEquivₓ'. -/
@[simp]
theorem coe_toIntLinearEquiv : ⇑e.toIntLinearEquiv = e :=
  rfl
#align add_equiv.coe_to_int_linear_equiv AddEquiv.coe_toIntLinearEquiv

/- warning: add_equiv.to_int_linear_equiv_to_add_equiv -> AddEquiv.toIntLinearEquiv_toAddEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.to_int_linear_equiv_to_add_equiv AddEquiv.toIntLinearEquiv_toAddEquivₓ'. -/
@[simp]
theorem toIntLinearEquiv_toAddEquiv : e.toIntLinearEquiv.toAddEquiv = e := by ext; rfl
#align add_equiv.to_int_linear_equiv_to_add_equiv AddEquiv.toIntLinearEquiv_toAddEquiv

/- warning: linear_equiv.to_add_equiv_to_int_linear_equiv -> LinearEquiv.toAddEquiv_toIntLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_add_equiv_to_int_linear_equiv LinearEquiv.toAddEquiv_toIntLinearEquivₓ'. -/
@[simp]
theorem LinearEquiv.toAddEquiv_toIntLinearEquiv (e : M ≃ₗ[ℤ] M₂) :
    e.toAddEquiv.toIntLinearEquiv = e :=
  FunLike.coe_injective rfl
#align linear_equiv.to_add_equiv_to_int_linear_equiv LinearEquiv.toAddEquiv_toIntLinearEquiv

/- warning: add_equiv.to_int_linear_equiv_symm -> AddEquiv.toIntLinearEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : AddCommGroup.{u1} M] [_inst_2 : AddCommGroup.{u2} M₂] (e : AddEquiv.{u1, u2} M M₂ (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1))))) (AddZeroClass.toHasAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (SubNegMonoid.toAddMonoid.{u2} M₂ (AddGroup.toSubNegMonoid.{u2} M₂ (AddCommGroup.toAddGroup.{u2} M₂ _inst_2)))))), Eq.{max (succ u2) (succ u1)} (LinearEquiv.{0, 0, u2, u1} Int Int Int.semiring Int.semiring (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.semiring)) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.semiring)) (RingHomInvPair.ids.{0} Int Int.semiring) (RingHomInvPair.ids.{0} Int Int.semiring) M₂ M (AddCommGroup.toAddCommMonoid.{u2} M₂ _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u2} M₂ _inst_2) (AddCommGroup.intModule.{u1} M _inst_1)) (LinearEquiv.symm.{0, 0, u1, u2} Int Int M M₂ Int.semiring Int.semiring (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M₂ _inst_2) (AddCommGroup.intModule.{u1} M _inst_1) (AddCommGroup.intModule.{u2} M₂ _inst_2) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.semiring)) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.semiring)) (RingHomInvPair.ids.{0} Int Int.semiring) (RingHomInvPair.ids.{0} Int Int.semiring) (AddEquiv.toIntLinearEquiv.{u1, u2} M M₂ _inst_1 _inst_2 e)) (AddEquiv.toIntLinearEquiv.{u2, u1} M₂ M _inst_2 _inst_1 (AddEquiv.symm.{u1, u2} M M₂ (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1))))) (AddZeroClass.toHasAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (SubNegMonoid.toAddMonoid.{u2} M₂ (AddGroup.toSubNegMonoid.{u2} M₂ (AddCommGroup.toAddGroup.{u2} M₂ _inst_2))))) e))
but is expected to have type
  forall {M : Type.{u2}} {M₂ : Type.{u1}} [_inst_1 : AddCommGroup.{u2} M] [_inst_2 : AddCommGroup.{u1} M₂] (e : AddEquiv.{u2, u1} M M₂ (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_1))))) (AddZeroClass.toAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (SubNegMonoid.toAddMonoid.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddCommGroup.toAddGroup.{u1} M₂ _inst_2)))))), Eq.{max (succ u2) (succ u1)} (LinearEquiv.{0, 0, u1, u2} Int Int Int.instSemiringInt Int.instSemiringInt (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)) (RingHomInvPair.ids.{0} Int Int.instSemiringInt) (RingHomInvPair.ids.{0} Int Int.instSemiringInt) M₂ M (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_1) (AddCommGroup.intModule.{u1} M₂ _inst_2) (AddCommGroup.intModule.{u2} M _inst_1)) (LinearEquiv.symm.{0, 0, u2, u1} Int Int M M₂ Int.instSemiringInt Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{u2} M _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M₂ _inst_2) (AddCommGroup.intModule.{u2} M _inst_1) (AddCommGroup.intModule.{u1} M₂ _inst_2) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)) (RingHomInvPair.ids.{0} Int Int.instSemiringInt) (RingHomInvPair.ids.{0} Int Int.instSemiringInt) (AddEquiv.toIntLinearEquiv.{u2, u1} M M₂ _inst_1 _inst_2 e)) (AddEquiv.toIntLinearEquiv.{u1, u2} M₂ M _inst_2 _inst_1 (AddEquiv.symm.{u2, u1} M M₂ (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_1))))) (AddZeroClass.toAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (SubNegMonoid.toAddMonoid.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddCommGroup.toAddGroup.{u1} M₂ _inst_2))))) e))
Case conversion may be inaccurate. Consider using '#align add_equiv.to_int_linear_equiv_symm AddEquiv.toIntLinearEquiv_symmₓ'. -/
@[simp]
theorem toIntLinearEquiv_symm : e.toIntLinearEquiv.symm = e.symm.toIntLinearEquiv :=
  rfl
#align add_equiv.to_int_linear_equiv_symm AddEquiv.toIntLinearEquiv_symm

/- warning: add_equiv.to_int_linear_equiv_refl -> AddEquiv.toIntLinearEquiv_refl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddCommGroup.{u1} M], Eq.{succ u1} (LinearEquiv.{0, 0, u1, u1} Int Int Int.semiring Int.semiring (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.semiring)) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.semiring)) (RingHomInvPair.ids.{0} Int Int.semiring) (RingHomInvPair.ids.{0} Int Int.semiring) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1)) (AddEquiv.toIntLinearEquiv.{u1, u1} M M _inst_1 _inst_1 (AddEquiv.refl.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1))))))) (LinearEquiv.refl.{0, u1} Int M Int.semiring (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddCommGroup.{u1} M], Eq.{succ u1} (LinearEquiv.{0, 0, u1, u1} Int Int Int.instSemiringInt Int.instSemiringInt (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)) (RingHom.id.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)) (RingHomInvPair.ids.{0} Int Int.instSemiringInt) (RingHomInvPair.ids.{0} Int Int.instSemiringInt) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1)) (AddEquiv.toIntLinearEquiv.{u1, u1} M M _inst_1 _inst_1 (AddEquiv.refl.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_1))))))) (LinearEquiv.refl.{0, u1} Int M Int.instSemiringInt (AddCommGroup.toAddCommMonoid.{u1} M _inst_1) (AddCommGroup.intModule.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align add_equiv.to_int_linear_equiv_refl AddEquiv.toIntLinearEquiv_reflₓ'. -/
@[simp]
theorem toIntLinearEquiv_refl : (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.refl ℤ M :=
  rfl
#align add_equiv.to_int_linear_equiv_refl AddEquiv.toIntLinearEquiv_refl

/- warning: add_equiv.to_int_linear_equiv_trans -> AddEquiv.toIntLinearEquiv_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.to_int_linear_equiv_trans AddEquiv.toIntLinearEquiv_transₓ'. -/
@[simp]
theorem toIntLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    e.toIntLinearEquiv.trans e₂.toIntLinearEquiv = (e.trans e₂).toIntLinearEquiv :=
  rfl
#align add_equiv.to_int_linear_equiv_trans AddEquiv.toIntLinearEquiv_trans

end AddCommGroup

end AddEquiv

