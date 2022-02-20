/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Eric Wieser
-/
import Mathbin.GroupTheory.FreeGroup

/-!
# Free groups structures on arbitrary types

This file defines the universal property of free groups, and proves some things about
groups with this property. For an explicit construction of free groups, see
`group_theory/free_group`.

## Main definitions

* `is_free_group G` - a typeclass to indicate that `G` is free over some generators
* `is_free_group.lift` - the (noncomputable) universal property of the free group
* `is_free_group.to_free_group` - any free group with generators `A` is equivalent to
  `free_group A`.

## Implementation notes

While the typeclass only requires the universal property hold within a single universe `u`, our
explicit construction of `free_group` allows this to be extended universe polymorphically. The
primed definition names in this file refer to the non-polymorphic versions.

-/


noncomputable section

universe u w

/-- `is_free_group G` means that `G` has the universal property of a free group,
That is, it has a family `generators G` of elements, such that a group homomorphism
`G →* X` is uniquely determined by a function `generators G → X`. -/
class IsFreeGroup (G : Type u) [Groupₓ G] : Type (u + 1) where
  Generators : Type u
  of : generators → G
  unique_lift' : ∀ {X : Type u} [Groupₓ X] f : generators → X, ∃! F : G →* X, ∀ a, F (of a) = f a

instance freeGroupIsFreeGroup {A} : IsFreeGroup (FreeGroup A) where
  Generators := A
  of := FreeGroup.of
  unique_lift' := by
    intros X _ f
    have := free_group.lift.symm.bijective.exists_unique f
    simp_rw [Function.funext_iffₓ]  at this
    exact this

namespace IsFreeGroup

variable {G H : Type u} {X : Type w} [Groupₓ G] [Groupₓ H] [Groupₓ X] [IsFreeGroup G]

/-- The equivalence between functions on the generators and group homomorphisms from a free group
given by those generators. -/
@[simps symmApply]
def lift' : (Generators G → H) ≃ (G →* H) where
  toFun := fun f => Classical.some (unique_lift' f)
  invFun := fun F => F ∘ of
  left_inv := fun f => funext (Classical.some_spec (unique_lift' f)).left
  right_inv := fun F => ((Classical.some_spec (unique_lift' (F ∘ of))).right F fun _ => rfl).symm

@[simp]
theorem lift'_of (f : Generators G → H) (a : Generators G) : (lift' f) (of a) = f a :=
  congr_funₓ (lift'.symm_apply_apply f) a

@[simp]
theorem lift'_eq_free_group_lift {A : Type u} : @lift' (FreeGroup A) H _ _ _ = FreeGroup.lift := by
  -- TODO: `apply equiv.symm_bijective.injective`,
  rw [← free_group.lift.symm_symm, ← (@lift' (FreeGroup A) H _ _ _).symm_symm]
  congr 1
  ext
  rfl

@[simp]
theorem of_eq_free_group_of {A : Type u} : @of (FreeGroup A) _ _ = FreeGroup.of :=
  rfl

@[ext]
theorem ext_hom' ⦃f g : G →* H⦄ (h : ∀ a, f (of a) = g (of a)) : f = g :=
  lift'.symm.Injective <| funext h

/-- Being a free group transports across group isomorphisms within a universe. -/
def ofMulEquiv (h : G ≃* H) : IsFreeGroup H where
  Generators := Generators G
  of := h ∘ of
  unique_lift' := by
    intros X _ f
    refine' ⟨(lift' f).comp h.symm.to_monoid_hom, _, _⟩
    · simp
      
    intro F' hF'
    suffices F'.comp h.to_monoid_hom = lift' f by
      rw [← this]
      ext
      apply congr_argₓ
      symm
      apply MulEquiv.apply_symm_apply
    ext
    simp [hF']

/-!
### Universe-polymorphic definitions


The primed definitions and lemmas above require `G` and `H` to be in the same universe `u`.
The lemmas below use `X` in a different universe `w`
-/


variable (G)

/-- Any free group is isomorphic to "the" free group. -/
@[simps]
def toFreeGroup : G ≃* FreeGroup (Generators G) where
  toFun := lift' FreeGroup.of
  invFun := FreeGroup.lift of
  left_inv := by
    suffices (FreeGroup.lift of).comp (lift' FreeGroup.of) = MonoidHom.id G from MonoidHom.congr_fun this
    ext
    simp
  right_inv := by
    suffices (lift' FreeGroup.of).comp (FreeGroup.lift of) = MonoidHom.id (FreeGroup (Generators G)) from
      MonoidHom.congr_fun this
    ext
    simp
  map_mul' := (lift' FreeGroup.of).map_mul

variable {G}

private theorem lift_right_inv_aux (F : G →* X) :
    FreeGroup.lift.symm (F.comp (toFreeGroup G).symm.toMonoidHom) = F ∘ of := by
  ext
  simp

/-- A universe-polymorphic version of `is_free_group.lift'`. -/
@[simps symmApply]
def lift : (Generators G → X) ≃ (G →* X) where
  toFun := fun f => (FreeGroup.lift f).comp (toFreeGroup G).toMonoidHom
  invFun := fun F => F ∘ of
  left_inv := fun f =>
    FreeGroup.lift.Injective
      (by
        ext x
        simp )
  right_inv := fun F => by
    dsimp
    rw [← lift_right_inv_aux]
    simp only [Equivₓ.apply_symm_apply]
    ext x
    dsimp only [MonoidHom.comp_apply, MulEquiv.coe_to_monoid_hom]
    rw [MulEquiv.symm_apply_apply]

@[ext]
theorem ext_hom ⦃f g : G →* X⦄ (h : ∀ a, f (of a) = g (of a)) : f = g :=
  IsFreeGroup.lift.symm.Injective <| funext h

@[simp]
theorem lift_of (f : Generators G → X) (a : Generators G) : (lift f) (of a) = f a :=
  congr_funₓ (lift.symm_apply_apply f) a

@[simp]
theorem lift_eq_free_group_lift {A : Type u} : @lift (FreeGroup A) H _ _ _ = FreeGroup.lift := by
  -- TODO: `apply equiv.symm_bijective.injective`,
  rw [← free_group.lift.symm_symm, ← (@lift (FreeGroup A) H _ _ _).symm_symm]
  congr 1
  ext
  rfl

/-- A universe-polymorphic version of `unique_lift`. -/
theorem unique_lift {X : Type w} [Groupₓ X] (f : Generators G → X) : ∃! F : G →* X, ∀ a, F (of a) = f a := by
  have := lift.symm.bijective.exists_unique f
  simp_rw [Function.funext_iffₓ]  at this
  exact this

end IsFreeGroup

