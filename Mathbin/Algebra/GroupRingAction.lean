import Mathbin.Algebra.Pointwise 
import Mathbin.Data.Equiv.Ring 
import Mathbin.GroupTheory.GroupAction.Group 
import Mathbin.GroupTheory.Submonoid.Pointwise 
import Mathbin.GroupTheory.Subgroup.Pointwise 
import Mathbin.RingTheory.Subring

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `mul_semiring_action M R`,
and the corresponding typeclass of invariant subrings.

Note that `algebra` does not satisfy the axioms of `mul_semiring_action`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `mul_semiring_action`.

## Tags

group action, invariant subring

-/


universe u v

open_locale BigOperators

/-- Typeclass for multiplicative actions by monoids on semirings.

This combines `distrib_mul_action` with `mul_distrib_mul_action`. -/
class MulSemiringAction(M : Type u)(R : Type v)[Monoidₓ M][Semiringₓ R] extends DistribMulAction M R where 
  smul_one : ∀ g : M, (g • 1 : R) = 1
  smul_mul : ∀ g : M x y : R, (g • x*y) = (g • x)*g • y

section Semiringₓ

variable(M G : Type u)[Monoidₓ M][Groupₓ G]

variable(A R S F : Type v)[AddMonoidₓ A][Semiringₓ R][CommSemiringₓ S][DivisionRing F]

instance (priority := 100)MulSemiringAction.toMulDistribMulAction [h : MulSemiringAction M R] :
  MulDistribMulAction M R :=
  { h with  }

/-- Each element of the monoid defines a semiring homomorphism. -/
@[simps]
def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R →+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribMulAction.toAddMonoidHom R x with  }

theorem to_ring_hom_injective [MulSemiringAction M R] [HasFaithfulScalar M R] :
  Function.Injective (MulSemiringAction.toRingHom M R) :=
  fun m₁ m₂ h => eq_of_smul_eq_smul$ fun r => RingHom.ext_iff.1 h r

/-- Each element of the group defines a semiring isomorphism. -/
@[simps]
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] (x : G) : R ≃+* R :=
  { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with  }

section 

variable{M G R}

/-- A stronger version of `submonoid.distrib_mul_action`. -/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) : MulSemiringAction H R :=
  { H.mul_distrib_mul_action, H.distrib_mul_action with smul := · • · }

/-- A stronger version of `subgroup.distrib_mul_action`. -/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) : MulSemiringAction H R :=
  H.to_submonoid.mul_semiring_action

/-- A stronger version of `subsemiring.distrib_mul_action`. -/
instance Subsemiring.mulSemiringAction {R'} [Semiringₓ R'] [MulSemiringAction R' R] (H : Subsemiring R') :
  MulSemiringAction H R :=
  H.to_submonoid.mul_semiring_action

/-- A stronger version of `subring.distrib_mul_action`. -/
instance Subring.mulSemiringAction {R'} [Ringₓ R'] [MulSemiringAction R' R] (H : Subring R') : MulSemiringAction H R :=
  H.to_subsemiring.mul_semiring_action

end 

section Pointwise

namespace Subsemiring

variable[MulSemiringAction M R]

/-- The action on a subsemiring corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : MulAction M (Subsemiring R) :=
  { smul := fun a S => S.map (MulSemiringAction.toRingHom _ _ a),
    one_smul :=
      fun S =>
        (congr_argₓ (fun f => S.map f)
              (RingHom.ext$
                by 
                  exact one_smul M)).trans
          S.map_id,
    mul_smul :=
      fun a₁ a₂ S =>
        (congr_argₓ (fun f => S.map f)
              (RingHom.ext$
                by 
                  exact mul_smul _ _)).trans
          (S.map_map _ _).symm }

localized [Pointwise] attribute [instance] Subsemiring.pointwiseMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (m : M) (S : Subsemiring R) : «expr↑ » (m • S) = m • (S : Set R) :=
  rfl

@[simp]
theorem pointwise_smul_to_add_submonoid (m : M) (S : Subsemiring R) : (m • S).toAddSubmonoid = m • S.to_add_submonoid :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subsemiring R) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R))

end Subsemiring

namespace Subring

variable{R' : Type _}[Ringₓ R'][MulSemiringAction M R']

/-- The action on a subring corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : MulAction M (Subring R') :=
  { smul := fun a S => S.map (MulSemiringAction.toRingHom _ _ a),
    one_smul :=
      fun S =>
        (congr_argₓ (fun f => S.map f)
              (RingHom.ext$
                by 
                  exact one_smul M)).trans
          S.map_id,
    mul_smul :=
      fun a₁ a₂ S =>
        (congr_argₓ (fun f => S.map f)
              (RingHom.ext$
                by 
                  exact mul_smul _ _)).trans
          (S.map_map _ _).symm }

localized [Pointwise] attribute [instance] Subring.pointwiseMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (m : M) (S : Subring R') : «expr↑ » (m • S) = m • (S : Set R') :=
  rfl

@[simp]
theorem pointwise_smul_to_add_subgroup (m : M) (S : Subring R') : (m • S).toAddSubgroup = m • S.to_add_subgroup :=
  rfl

@[simp]
theorem pointwise_smul_to_subsemiring (m : M) (S : Subring R') : (m • S).toSubsemiring = m • S.to_subsemiring :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (r : R') (S : Subring R') : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R'))

end Subring

end Pointwise

section SimpLemmas

variable{M G A R F}

attribute [simp] smul_one smul_mul' smul_zero smul_add

/-- Note that `smul_inv'` refers to the group case, and `smul_inv` has an additional inverse
on `x`. -/
@[simp]
theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
  (MulSemiringAction.toRingHom M F x).map_inv _

end SimpLemmas

end Semiringₓ

section Ringₓ

variable(M : Type u)[Monoidₓ M]{R : Type v}[Ringₓ R][MulSemiringAction M R]

variable(S : Subring R)

open MulAction

/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class IsInvariantSubring : Prop where 
  smul_mem : ∀ m : M {x : R}, x ∈ S → m • x ∈ S

instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] : MulSemiringAction M S :=
  { smul := fun m x => ⟨m • x, IsInvariantSubring.smul_mem m x.2⟩, one_smul := fun s => Subtype.eq$ one_smul M s,
    mul_smul := fun m₁ m₂ s => Subtype.eq$ mul_smul m₁ m₂ s, smul_add := fun m s₁ s₂ => Subtype.eq$ smul_add m s₁ s₂,
    smul_zero := fun m => Subtype.eq$ smul_zero m, smul_one := fun m => Subtype.eq$ smul_one m,
    smul_mul := fun m s₁ s₂ => Subtype.eq$ smul_mul' m s₁ s₂ }

end Ringₓ

