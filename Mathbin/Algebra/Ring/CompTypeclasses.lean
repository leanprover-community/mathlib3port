/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth

! This file was ported from Lean 3 source module algebra.ring.comp_typeclasses
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Equiv

/-!
# Propositional typeclasses on several ring homs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains three typeclasses used in the definition of (semi)linear maps:
* `ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃`, which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`
* `ring_hom_inv_pair σ₁₂ σ₂₁`, which states that `σ₁₂` and `σ₂₁` are inverses of each other
* `ring_hom_surjective σ`, which states that `σ` is surjective
These typeclasses ensure that objects such as `σ₂₃.comp σ₁₂` never end up in the type of a
semilinear map; instead, the typeclass system directly finds the appropriate `ring_hom` to use.
A typical use-case is conjugate-linear maps, i.e. when `σ = complex.conj`; this system ensures that
composing two conjugate-linear maps is a linear map, and not a `conj.comp conj`-linear map.

Instances of these typeclasses mostly involving `ring_hom.id` are also provided:
* `ring_hom_inv_pair (ring_hom.id R) (ring_hom.id R)`
* `[ring_hom_inv_pair σ₁₂ σ₂₁] : ring_hom_comp_triple σ₁₂ σ₂₁ (ring_hom.id R₁)`
* `ring_hom_comp_triple (ring_hom.id R₁) σ₁₂ σ₁₂`
* `ring_hom_comp_triple σ₁₂ (ring_hom.id R₂) σ₁₂`
* `ring_hom_surjective (ring_hom.id R)`
* `[ring_hom_inv_pair σ₁ σ₂] : ring_hom_surjective σ₁`

## Implementation notes

* For the typeclass `ring_hom_inv_pair σ₁₂ σ₂₁`, `σ₂₁` is marked as an `out_param`,
  as it must typically be found via the typeclass inference system.

* Likewise, for `ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃`, `σ₁₃` is marked as an `out_param`,
  for the same reason.

## Tags

`ring_hom_comp_triple`, `ring_hom_inv_pair`, `ring_hom_surjective`
-/


variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

#print RingHomCompTriple /-
/-- Class that expresses the fact that three ring homomorphisms form a composition triple. This is
used to handle composition of semilinear maps. -/
class RingHomCompTriple (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃) (σ₁₃ : outParam (R₁ →+* R₃)) :
    Prop where
  comp_eq : σ₂₃.comp σ₁₂ = σ₁₃
#align ring_hom_comp_triple RingHomCompTriple
-/

attribute [simp] RingHomCompTriple.comp_eq

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

namespace RingHomCompTriple

#print RingHomCompTriple.comp_apply /-
@[simp]
theorem comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x :=
  RingHom.congr_fun comp_eq x
#align ring_hom_comp_triple.comp_apply RingHomCompTriple.comp_apply
-/

end RingHomCompTriple

#print RingHomInvPair /-
/-- Class that expresses the fact that two ring homomorphisms are inverses of each other. This is
used to handle `symm` for semilinear equivalences. -/
class RingHomInvPair (σ : R₁ →+* R₂) (σ' : outParam (R₂ →+* R₁)) : Prop where
  comp_eq : σ'.comp σ = RingHom.id R₁
  comp_eq₂ : σ.comp σ' = RingHom.id R₂
#align ring_hom_inv_pair RingHomInvPair
-/

attribute [simp] RingHomInvPair.comp_eq

attribute [simp] RingHomInvPair.comp_eq₂

variable {σ : R₁ →+* R₂} {σ' : R₂ →+* R₁}

namespace RingHomInvPair

variable [RingHomInvPair σ σ']

#print RingHomInvPair.comp_apply_eq /-
@[simp]
theorem comp_apply_eq {x : R₁} : σ' (σ x) = x := by rw [← RingHom.comp_apply, comp_eq]; simp
#align ring_hom_inv_pair.comp_apply_eq RingHomInvPair.comp_apply_eq
-/

#print RingHomInvPair.comp_apply_eq₂ /-
@[simp]
theorem comp_apply_eq₂ {x : R₂} : σ (σ' x) = x := by rw [← RingHom.comp_apply, comp_eq₂]; simp
#align ring_hom_inv_pair.comp_apply_eq₂ RingHomInvPair.comp_apply_eq₂
-/

#print RingHomInvPair.ids /-
instance ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=
  ⟨rfl, rfl⟩
#align ring_hom_inv_pair.ids RingHomInvPair.ids
-/

#print RingHomInvPair.triples /-
instance triples {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁) :=
  ⟨by simp only [comp_eq]⟩
#align ring_hom_inv_pair.triples RingHomInvPair.triples
-/

#print RingHomInvPair.triples₂ /-
instance triples₂ {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₂₁ σ₁₂ (RingHom.id R₂) :=
  ⟨by simp only [comp_eq₂]⟩
#align ring_hom_inv_pair.triples₂ RingHomInvPair.triples₂
-/

#print RingHomInvPair.of_ringEquiv /-
/-- Construct a `ring_hom_inv_pair` from both directions of a ring equiv.

This is not an instance, as for equivalences that are involutions, a better instance
would be `ring_hom_inv_pair e e`. Indeed, this declaration is not currently used in mathlib.

See note [reducible non-instances].
-/
@[reducible]
theorem of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPair (↑e : R₁ →+* R₂) ↑e.symm :=
  ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩
#align ring_hom_inv_pair.of_ring_equiv RingHomInvPair.of_ringEquiv
-/

#print RingHomInvPair.symm /-
/--
Swap the direction of a `ring_hom_inv_pair`. This is not an instance as it would loop, and better
instances are often available and may often be preferrable to using this one. Indeed, this
declaration is not currently used in mathlib.

See note [reducible non-instances].
-/
@[reducible]
theorem symm (σ₁₂ : R₁ →+* R₂) (σ₂₁ : R₂ →+* R₁) [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomInvPair σ₂₁ σ₁₂ :=
  ⟨RingHomInvPair.comp_eq₂, RingHomInvPair.comp_eq⟩
#align ring_hom_inv_pair.symm RingHomInvPair.symm
-/

end RingHomInvPair

namespace RingHomCompTriple

#print RingHomCompTriple.ids /-
instance ids : RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂ :=
  ⟨by ext; simp⟩
#align ring_hom_comp_triple.ids RingHomCompTriple.ids
-/

#print RingHomCompTriple.right_ids /-
instance right_ids : RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂ :=
  ⟨by ext; simp⟩
#align ring_hom_comp_triple.right_ids RingHomCompTriple.right_ids
-/

end RingHomCompTriple

#print RingHomSurjective /-
/-- Class expressing the fact that a `ring_hom` is surjective. This is needed in the context
of semilinear maps, where some lemmas require this. -/
class RingHomSurjective (σ : R₁ →+* R₂) : Prop where
  is_surjective : Function.Surjective σ
#align ring_hom_surjective RingHomSurjective
-/

#print RingHom.surjective /-
theorem RingHom.surjective (σ : R₁ →+* R₂) [t : RingHomSurjective σ] : Function.Surjective σ :=
  t.is_surjective
#align ring_hom.is_surjective RingHom.surjective
-/

namespace RingHomSurjective

#print RingHomSurjective.invPair /-
-- The linter gives a false positive, since `σ₂` is an out_param
@[nolint dangerous_instance]
instance (priority := 100) invPair {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁} [RingHomInvPair σ₁ σ₂] :
    RingHomSurjective σ₁ :=
  ⟨fun x => ⟨σ₂ x, RingHomInvPair.comp_apply_eq₂⟩⟩
#align ring_hom_surjective.inv_pair RingHomSurjective.invPair
-/

#print RingHomSurjective.ids /-
instance ids : RingHomSurjective (RingHom.id R₁) :=
  ⟨is_surjective⟩
#align ring_hom_surjective.ids RingHomSurjective.ids
-/

#print RingHomSurjective.comp /-
/-- This cannot be an instance as there is no way to infer `σ₁₂` and `σ₂₃`. -/
theorem comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] :
    RingHomSurjective σ₁₃ :=
  {
    is_surjective := by
      have := σ₂₃.is_surjective.comp σ₁₂.is_surjective
      rwa [← RingHom.coe_comp, RingHomCompTriple.comp_eq] at this  }
#align ring_hom_surjective.comp RingHomSurjective.comp
-/

end RingHomSurjective

