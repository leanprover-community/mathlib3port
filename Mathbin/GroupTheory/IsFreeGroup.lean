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


noncomputable theory

universe u w

/-- `is_free_group G` means that `G` has the universal property of a free group,
That is, it has a family `generators G` of elements, such that a group homomorphism
`G →* X` is uniquely determined by a function `generators G → X`. -/
class IsFreeGroup(G : Type u)[Groupₓ G] : Type (u + 1) where 
  Generators : Type u 
  of : generators → G 
  unique_lift' : ∀ {X : Type u} [Groupₓ X] f : generators → X, ∃!F : G →* X, ∀ a, F (of a) = f a

-- error in GroupTheory.IsFreeGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance free_group_is_free_group {A} : is_free_group (free_group A) :=
{ generators := A,
  of := free_group.of,
  unique_lift' := begin
    introsI [ident X, "_", ident f],
    have [] [] [":=", expr free_group.lift.symm.bijective.exists_unique f],
    simp_rw [expr function.funext_iff] ["at", ident this],
    exact [expr this]
  end }

namespace IsFreeGroup

variable{G H : Type u}{X : Type w}[Groupₓ G][Groupₓ H][Groupₓ X][IsFreeGroup G]

/-- The equivalence between functions on the generators and group homomorphisms from a free group
given by those generators. -/
@[simps symmApply]
def lift' : (generators G → H) ≃ (G →* H) :=
  { toFun := fun f => Classical.some (unique_lift' f), invFun := fun F => F ∘ of,
    left_inv := fun f => funext (Classical.some_spec (unique_lift' f)).left,
    right_inv := fun F => ((Classical.some_spec (unique_lift' (F ∘ of))).right F fun _ => rfl).symm }

@[simp]
theorem lift'_of (f : generators G → H) (a : generators G) : (lift' f) (of a) = f a :=
  congr_funₓ (lift'.symm_apply_apply f) a

@[simp]
theorem lift'_eq_free_group_lift {A : Type u} : @lift' (FreeGroup A) H _ _ _ = FreeGroup.lift :=
  by 
    rw [←free_group.lift.symm_symm, ←(@lift' (FreeGroup A) H _ _ _).symm_symm]
    congr 1 
    ext 
    rfl

@[simp]
theorem of_eq_free_group_of {A : Type u} : @of (FreeGroup A) _ _ = FreeGroup.of :=
  rfl

@[ext]
theorem ext_hom' ⦃f g : G →* H⦄ (h : ∀ a, f (of a) = g (of a)) : f = g :=
  lift'.symm.Injective$ funext h

/-- Being a free group transports across group isomorphisms within a universe. -/
def of_mul_equiv (h : G ≃* H) : IsFreeGroup H :=
  { Generators := generators G, of := h ∘ of,
    unique_lift' :=
      by 
        intros X _ f 
        refine' ⟨(lift' f).comp h.symm.to_monoid_hom, _, _⟩
        ·
          simp 
        intro F' hF' 
        suffices  : F'.comp h.to_monoid_hom = lift' f
        ·
          rw [←this]
          ext 
          apply congr_argₓ 
          symm 
          apply MulEquiv.apply_symm_apply 
        ext 
        simp [hF'] }

/-!
### Universe-polymorphic definitions


The primed definitions and lemmas above require `G` and `H` to be in the same universe `u`.
The lemmas below use `X` in a different universe `w`
-/


variable(G)

/-- Any free group is isomorphic to "the" free group. -/
@[simps]
def to_free_group : G ≃* FreeGroup (generators G) :=
  { toFun := lift' FreeGroup.of, invFun := FreeGroup.lift of,
    left_inv :=
      suffices (FreeGroup.lift of).comp (lift' FreeGroup.of) = MonoidHom.id G from MonoidHom.congr_fun this 
      by 
        ext 
        simp ,
    right_inv :=
      suffices (lift' FreeGroup.of).comp (FreeGroup.lift of) = MonoidHom.id (FreeGroup (generators G)) from
        MonoidHom.congr_fun this 
      by 
        ext 
        simp ,
    map_mul' := (lift' FreeGroup.of).map_mul }

variable{G}

private theorem lift_right_inv_aux (F : G →* X) :
  FreeGroup.lift.symm (F.comp (to_free_group G).symm.toMonoidHom) = F ∘ of :=
  by 
    ext 
    simp 

/-- A universe-polymorphic version of `is_free_group.lift'`. -/
@[simps symmApply]
def lift : (generators G → X) ≃ (G →* X) :=
  { toFun := fun f => (FreeGroup.lift f).comp (to_free_group G).toMonoidHom, invFun := fun F => F ∘ of,
    left_inv :=
      fun f =>
        FreeGroup.lift.Injective
          (by 
            ext x 
            simp ),
    right_inv :=
      fun F =>
        by 
          dsimp 
          rw [←lift_right_inv_aux]
          simp only [Equiv.apply_symm_apply]
          ext x 
          dsimp only [MonoidHom.comp_apply, MulEquiv.coe_to_monoid_hom]
          rw [MulEquiv.symm_apply_apply] }

@[ext]
theorem ext_hom ⦃f g : G →* X⦄ (h : ∀ a, f (of a) = g (of a)) : f = g :=
  IsFreeGroup.lift.symm.Injective$ funext h

@[simp]
theorem lift_of (f : generators G → X) (a : generators G) : (lift f) (of a) = f a :=
  congr_funₓ (lift.symm_apply_apply f) a

@[simp]
theorem lift_eq_free_group_lift {A : Type u} : @lift (FreeGroup A) H _ _ _ = FreeGroup.lift :=
  by 
    rw [←free_group.lift.symm_symm, ←(@lift (FreeGroup A) H _ _ _).symm_symm]
    congr 1 
    ext 
    rfl

-- error in GroupTheory.IsFreeGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A universe-polymorphic version of `unique_lift`. -/
theorem unique_lift
{X : Type w}
[group X]
(f : generators G → X) : «expr∃! , »((F : «expr →* »(G, X)), ∀ a, «expr = »(F (of a), f a)) :=
begin
  have [] [] [":=", expr lift.symm.bijective.exists_unique f],
  simp_rw [expr function.funext_iff] ["at", ident this],
  exact [expr this]
end

end IsFreeGroup

