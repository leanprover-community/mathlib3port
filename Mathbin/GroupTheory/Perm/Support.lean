/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky

! This file was ported from Lean 3 source module group_theory.perm.support
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Card
import Mathbin.Data.Fintype.Basic
import Mathbin.GroupTheory.Perm.Basic

/-!
# Support of a permutation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

In the following, `f g : equiv.perm α`.

* `equiv.perm.disjoint`: two permutations `f` and `g` are `disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `disjoint` iff their `support` are disjoint.
* `equiv.perm.is_swap`: `f = swap x y` for `x ≠ y`.
* `equiv.perm.support`: the elements `x : α` that are not fixed by `f`.

-/


open Equiv Finset

namespace Equiv.Perm

variable {α : Type _}

section Disjoint

#print Equiv.Perm.Disjoint /-
/-- Two permutations `f` and `g` are `disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def Disjoint (f g : Perm α) :=
  ∀ x, f x = x ∨ g x = x
#align equiv.perm.disjoint Equiv.Perm.Disjoint
-/

variable {f g h : Perm α}

#print Equiv.Perm.Disjoint.symm /-
@[symm]
theorem Disjoint.symm : Disjoint f g → Disjoint g f := by simp only [Disjoint, or_comm, imp_self]
#align equiv.perm.disjoint.symm Equiv.Perm.Disjoint.symm
-/

#print Equiv.Perm.Disjoint.symmetric /-
theorem Disjoint.symmetric : Symmetric (@Disjoint α) := fun _ _ => Disjoint.symm
#align equiv.perm.disjoint.symmetric Equiv.Perm.Disjoint.symmetric
-/

instance : IsSymm (Perm α) Disjoint :=
  ⟨Disjoint.symmetric⟩

#print Equiv.Perm.disjoint_comm /-
theorem disjoint_comm : Disjoint f g ↔ Disjoint g f :=
  ⟨Disjoint.symm, Disjoint.symm⟩
#align equiv.perm.disjoint_comm Equiv.Perm.disjoint_comm
-/

/- warning: equiv.perm.disjoint.commute -> Equiv.Perm.Disjoint.commute is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Commute.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) f g)
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Commute.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) f g)
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.commute Equiv.Perm.Disjoint.commuteₓ'. -/
theorem Disjoint.commute (h : Disjoint f g) : Commute f g :=
  Equiv.ext fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim (fun hg => by simp [mul_apply, hf, hg]) fun hg => by
          simp [mul_apply, hf, g.injective hg])
      fun hg =>
      (h (f x)).elim (fun hf => by simp [mul_apply, f.injective hf, hg]) fun hf => by
        simp [mul_apply, hf, hg]
#align equiv.perm.disjoint.commute Equiv.Perm.Disjoint.commute

/- warning: equiv.perm.disjoint_one_left -> Equiv.Perm.disjoint_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Equiv.Perm.{succ u1} α), Equiv.Perm.Disjoint.{u1} α (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) f
but is expected to have type
  forall {α : Type.{u1}} (f : Equiv.Perm.{succ u1} α), Equiv.Perm.Disjoint.{u1} α (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) f
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint_one_left Equiv.Perm.disjoint_one_leftₓ'. -/
@[simp]
theorem disjoint_one_left (f : Perm α) : Disjoint 1 f := fun _ => Or.inl rfl
#align equiv.perm.disjoint_one_left Equiv.Perm.disjoint_one_left

/- warning: equiv.perm.disjoint_one_right -> Equiv.Perm.disjoint_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Equiv.Perm.{succ u1} α), Equiv.Perm.Disjoint.{u1} α f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} (f : Equiv.Perm.{succ u1} α), Equiv.Perm.Disjoint.{u1} α f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint_one_right Equiv.Perm.disjoint_one_rightₓ'. -/
@[simp]
theorem disjoint_one_right (f : Perm α) : Disjoint f 1 := fun _ => Or.inr rfl
#align equiv.perm.disjoint_one_right Equiv.Perm.disjoint_one_right

#print Equiv.Perm.disjoint_iff_eq_or_eq /-
theorem disjoint_iff_eq_or_eq : Disjoint f g ↔ ∀ x : α, f x = x ∨ g x = x :=
  Iff.rfl
#align equiv.perm.disjoint_iff_eq_or_eq Equiv.Perm.disjoint_iff_eq_or_eq
-/

/- warning: equiv.perm.disjoint_refl_iff -> Equiv.Perm.disjoint_refl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α}, Iff (Equiv.Perm.Disjoint.{u1} α f f) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))))
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α}, Iff (Equiv.Perm.Disjoint.{u1} α f f) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint_refl_iff Equiv.Perm.disjoint_refl_iffₓ'. -/
@[simp]
theorem disjoint_refl_iff : Disjoint f f ↔ f = 1 :=
  by
  refine' ⟨fun h => _, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  cases' h x with hx hx <;> simp [hx]
#align equiv.perm.disjoint_refl_iff Equiv.Perm.disjoint_refl_iff

/- warning: equiv.perm.disjoint.inv_left -> Equiv.Perm.Disjoint.inv_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Equiv.Perm.Disjoint.{u1} α (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) f) g)
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Equiv.Perm.Disjoint.{u1} α (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) f) g)
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.inv_left Equiv.Perm.Disjoint.inv_leftₓ'. -/
theorem Disjoint.inv_left (h : Disjoint f g) : Disjoint f⁻¹ g :=
  by
  intro x
  rw [inv_eq_iff_eq, eq_comm]
  exact h x
#align equiv.perm.disjoint.inv_left Equiv.Perm.Disjoint.inv_left

/- warning: equiv.perm.disjoint.inv_right -> Equiv.Perm.Disjoint.inv_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Equiv.Perm.Disjoint.{u1} α f (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) g))
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Equiv.Perm.Disjoint.{u1} α f (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) g))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.inv_right Equiv.Perm.Disjoint.inv_rightₓ'. -/
theorem Disjoint.inv_right (h : Disjoint f g) : Disjoint f g⁻¹ :=
  h.symm.inv_left.symm
#align equiv.perm.disjoint.inv_right Equiv.Perm.Disjoint.inv_right

/- warning: equiv.perm.disjoint_inv_left_iff -> Equiv.Perm.disjoint_inv_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, Iff (Equiv.Perm.Disjoint.{u1} α (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) f) g) (Equiv.Perm.Disjoint.{u1} α f g)
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, Iff (Equiv.Perm.Disjoint.{u1} α (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) f) g) (Equiv.Perm.Disjoint.{u1} α f g)
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint_inv_left_iff Equiv.Perm.disjoint_inv_left_iffₓ'. -/
@[simp]
theorem disjoint_inv_left_iff : Disjoint f⁻¹ g ↔ Disjoint f g :=
  by
  refine' ⟨fun h => _, disjoint.inv_left⟩
  convert h.inv_left
  exact (inv_inv _).symm
#align equiv.perm.disjoint_inv_left_iff Equiv.Perm.disjoint_inv_left_iff

/- warning: equiv.perm.disjoint_inv_right_iff -> Equiv.Perm.disjoint_inv_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, Iff (Equiv.Perm.Disjoint.{u1} α f (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) g)) (Equiv.Perm.Disjoint.{u1} α f g)
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, Iff (Equiv.Perm.Disjoint.{u1} α f (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) g)) (Equiv.Perm.Disjoint.{u1} α f g)
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint_inv_right_iff Equiv.Perm.disjoint_inv_right_iffₓ'. -/
@[simp]
theorem disjoint_inv_right_iff : Disjoint f g⁻¹ ↔ Disjoint f g := by
  rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]
#align equiv.perm.disjoint_inv_right_iff Equiv.Perm.disjoint_inv_right_iff

/- warning: equiv.perm.disjoint.mul_left -> Equiv.Perm.Disjoint.mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α} {h : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f h) -> (Equiv.Perm.Disjoint.{u1} α g h) -> (Equiv.Perm.Disjoint.{u1} α (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g) h)
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α} {h : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f h) -> (Equiv.Perm.Disjoint.{u1} α g h) -> (Equiv.Perm.Disjoint.{u1} α (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g) h)
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.mul_left Equiv.Perm.Disjoint.mul_leftₓ'. -/
theorem Disjoint.mul_left (H1 : Disjoint f h) (H2 : Disjoint g h) : Disjoint (f * g) h := fun x =>
  by cases H1 x <;> cases H2 x <;> simp [*]
#align equiv.perm.disjoint.mul_left Equiv.Perm.Disjoint.mul_left

/- warning: equiv.perm.disjoint.mul_right -> Equiv.Perm.Disjoint.mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α} {h : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Equiv.Perm.Disjoint.{u1} α f h) -> (Equiv.Perm.Disjoint.{u1} α f (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) g h))
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α} {h : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Equiv.Perm.Disjoint.{u1} α f h) -> (Equiv.Perm.Disjoint.{u1} α f (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) g h))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.mul_right Equiv.Perm.Disjoint.mul_rightₓ'. -/
theorem Disjoint.mul_right (H1 : Disjoint f g) (H2 : Disjoint f h) : Disjoint f (g * h) :=
  by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm
#align equiv.perm.disjoint.mul_right Equiv.Perm.Disjoint.mul_right

/- warning: equiv.perm.disjoint_prod_right -> Equiv.Perm.disjoint_prod_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} (l : List.{u1} (Equiv.Perm.{succ u1} α)), (forall (g : Equiv.Perm.{succ u1} α), (Membership.Mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.hasMem.{u1} (Equiv.Perm.{succ u1} α)) g l) -> (Equiv.Perm.Disjoint.{u1} α f g)) -> (Equiv.Perm.Disjoint.{u1} α f (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l))
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} (l : List.{u1} (Equiv.Perm.{succ u1} α)), (forall (g : Equiv.Perm.{succ u1} α), (Membership.mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.instMembershipList.{u1} (Equiv.Perm.{succ u1} α)) g l) -> (Equiv.Perm.Disjoint.{u1} α f g)) -> (Equiv.Perm.Disjoint.{u1} α f (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint_prod_right Equiv.Perm.disjoint_prod_rightₓ'. -/
theorem disjoint_prod_right (l : List (Perm α)) (h : ∀ g ∈ l, Disjoint f g) : Disjoint f l.Prod :=
  by
  induction' l with g l ih
  · exact disjoint_one_right _
  · rw [List.prod_cons]
    exact (h _ (List.mem_cons_self _ _)).mulRight (ih fun g hg => h g (List.mem_cons_of_mem _ hg))
#align equiv.perm.disjoint_prod_right Equiv.Perm.disjoint_prod_right

/- warning: equiv.perm.disjoint_prod_perm -> Equiv.Perm.disjoint_prod_perm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l₁ : List.{u1} (Equiv.Perm.{succ u1} α)} {l₂ : List.{u1} (Equiv.Perm.{succ u1} α)}, (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l₁) -> (List.Perm.{u1} (Equiv.Perm.{succ u1} α) l₁ l₂) -> (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l₁) (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l₂))
but is expected to have type
  forall {α : Type.{u1}} {l₁ : List.{u1} (Equiv.Perm.{succ u1} α)} {l₂ : List.{u1} (Equiv.Perm.{succ u1} α)}, (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l₁) -> (List.Perm.{u1} (Equiv.Perm.{succ u1} α) l₁ l₂) -> (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l₁) (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l₂))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint_prod_perm Equiv.Perm.disjoint_prod_permₓ'. -/
theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp : l₁ ~ l₂) :
    l₁.Prod = l₂.Prod :=
  hp.prod_eq' <| hl.imp fun f g => Disjoint.commute
#align equiv.perm.disjoint_prod_perm Equiv.Perm.disjoint_prod_perm

/- warning: equiv.perm.nodup_of_pairwise_disjoint -> Equiv.Perm.nodup_of_pairwise_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} (Equiv.Perm.{succ u1} α)}, (Not (Membership.Mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.hasMem.{u1} (Equiv.Perm.{succ u1} α)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) l)) -> (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l) -> (List.Nodup.{u1} (Equiv.Perm.{succ u1} α) l)
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} (Equiv.Perm.{succ u1} α)}, (Not (Membership.mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.instMembershipList.{u1} (Equiv.Perm.{succ u1} α)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) l)) -> (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l) -> (List.Nodup.{u1} (Equiv.Perm.{succ u1} α) l)
Case conversion may be inaccurate. Consider using '#align equiv.perm.nodup_of_pairwise_disjoint Equiv.Perm.nodup_of_pairwise_disjointₓ'. -/
theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
    (h2 : l.Pairwise Disjoint) : l.Nodup :=
  by
  refine' List.Pairwise.imp_of_mem _ h2
  rintro σ - h_mem - h_disjoint rfl
  suffices σ = 1 by
    rw [this] at h_mem
    exact h1 h_mem
  exact ext fun a => (or_self_iff _).mp (h_disjoint a)
#align equiv.perm.nodup_of_pairwise_disjoint Equiv.Perm.nodup_of_pairwise_disjoint

#print Equiv.Perm.pow_apply_eq_self_of_apply_eq_self /-
theorem pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℕ, (f ^ n) x = x
  | 0 => rfl
  | n + 1 => by rw [pow_succ', mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self]
#align equiv.perm.pow_apply_eq_self_of_apply_eq_self Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
-/

#print Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self /-
theorem zpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℤ, (f ^ n) x = x
  | (n : ℕ) => pow_apply_eq_self_of_apply_eq_self hfx n
  | -[n+1] => by rw [zpow_negSucc, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]
#align equiv.perm.zpow_apply_eq_self_of_apply_eq_self Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
-/

#print Equiv.Perm.pow_apply_eq_of_apply_apply_eq_self /-
theorem pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
  | 0 => Or.inl rfl
  | n + 1 =>
    (pow_apply_eq_of_apply_apply_eq_self n).elim (fun h => Or.inr (by rw [pow_succ, mul_apply, h]))
      fun h => Or.inl (by rw [pow_succ, mul_apply, h, hffx])
#align equiv.perm.pow_apply_eq_of_apply_apply_eq_self Equiv.Perm.pow_apply_eq_of_apply_apply_eq_self
-/

#print Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self /-
theorem zpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
  | (n : ℕ) => pow_apply_eq_of_apply_apply_eq_self hffx n
  | -[n+1] =>
    by
    rw [zpow_negSucc, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply, ← pow_succ, eq_comm,
      inv_eq_iff_eq, ← mul_apply, ← pow_succ', @eq_comm _ x, or_comm]
    exact pow_apply_eq_of_apply_apply_eq_self hffx _
#align equiv.perm.zpow_apply_eq_of_apply_apply_eq_self Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self
-/

#print Equiv.Perm.Disjoint.mul_apply_eq_iff /-
theorem Disjoint.mul_apply_eq_iff {σ τ : Perm α} (hστ : Disjoint σ τ) {a : α} :
    (σ * τ) a = a ↔ σ a = a ∧ τ a = a :=
  by
  refine' ⟨fun h => _, fun h => by rw [mul_apply, h.2, h.1]⟩
  cases' hστ a with hσ hτ
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
  · exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩
#align equiv.perm.disjoint.mul_apply_eq_iff Equiv.Perm.Disjoint.mul_apply_eq_iff
-/

/- warning: equiv.perm.disjoint.mul_eq_one_iff -> Equiv.Perm.Disjoint.mul_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Equiv.Perm.{succ u1} α} {τ : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α σ τ) -> (Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) σ τ) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) (And (Eq.{succ u1} (Equiv.Perm.{succ u1} α) σ (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) τ (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))))))
but is expected to have type
  forall {α : Type.{u1}} {σ : Equiv.Perm.{succ u1} α} {τ : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α σ τ) -> (Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) σ τ) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (And (Eq.{succ u1} (Equiv.Perm.{succ u1} α) σ (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) τ (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.mul_eq_one_iff Equiv.Perm.Disjoint.mul_eq_one_iffₓ'. -/
theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : Disjoint σ τ) : σ * τ = 1 ↔ σ = 1 ∧ τ = 1 :=
  by simp_rw [ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and]
#align equiv.perm.disjoint.mul_eq_one_iff Equiv.Perm.Disjoint.mul_eq_one_iff

#print Equiv.Perm.Disjoint.zpow_disjoint_zpow /-
theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℤ) :
    Disjoint (σ ^ m) (τ ^ n) := fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m)
    (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)
#align equiv.perm.disjoint.zpow_disjoint_zpow Equiv.Perm.Disjoint.zpow_disjoint_zpow
-/

#print Equiv.Perm.Disjoint.pow_disjoint_pow /-
theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℕ) :
    Disjoint (σ ^ m) (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n
#align equiv.perm.disjoint.pow_disjoint_pow Equiv.Perm.Disjoint.pow_disjoint_pow
-/

end Disjoint

section IsSwap

variable [DecidableEq α]

#print Equiv.Perm.IsSwap /-
/-- `f.is_swap` indicates that the permutation `f` is a transposition of two elements. -/
def IsSwap (f : Perm α) : Prop :=
  ∃ x y, x ≠ y ∧ f = swap x y
#align equiv.perm.is_swap Equiv.Perm.IsSwap
-/

/- warning: equiv.perm.of_subtype_swap_eq -> Equiv.Perm.ofSubtype_swap_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u1} α p] (x : Subtype.{succ u1} α p) (y : Subtype.{succ u1} α p), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (fun (_x : MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) => (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) -> (Equiv.Perm.{succ u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.ofSubtype.{u1} α p (fun (a : α) => _inst_2 a)) (Equiv.swap.{succ u1} (Subtype.{succ u1} α p) (fun (a : Subtype.{succ u1} α p) (b : Subtype.{succ u1} α p) => Subtype.decidableEq.{u1} α (fun (x : α) => p x) (fun (a : α) (b : α) => _inst_1 a b) a b) x y)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α p) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α p) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α p) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α p) α (coeSubtype.{succ u1} α (fun (x : α) => p x))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α p) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α p) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α p) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α p) α (coeSubtype.{succ u1} α (fun (x : α) => p x))))) y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u1} α p] (x : Subtype.{succ u1} α p) (y : Subtype.{succ u1} α p), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) => Equiv.Perm.{succ u1} α) (Equiv.swap.{succ u1} (Subtype.{succ u1} α p) (fun (a : Subtype.{succ u1} α p) (b : Subtype.{succ u1} α p) => Subtype.instDecidableEqSubtype.{u1} α (fun (x : α) => p x) (fun (a : α) (b : α) => _inst_1 a b) a b) x y)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (fun (_x : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) => Equiv.Perm.{succ u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p)))))) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (MonoidHom.monoidHomClass.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) (Equiv.Perm.ofSubtype.{u1} α p (fun (a : α) => _inst_2 a)) (Equiv.swap.{succ u1} (Subtype.{succ u1} α p) (fun (a : Subtype.{succ u1} α p) (b : Subtype.{succ u1} α p) => Subtype.instDecidableEqSubtype.{u1} α (fun (x : α) => p x) (fun (a : α) (b : α) => _inst_1 a b) a b) x y)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) (Subtype.val.{succ u1} α p x) (Subtype.val.{succ u1} α p y))
Case conversion may be inaccurate. Consider using '#align equiv.perm.of_subtype_swap_eq Equiv.Perm.ofSubtype_swap_eqₓ'. -/
@[simp]
theorem ofSubtype_swap_eq {p : α → Prop} [DecidablePred p] (x y : Subtype p) :
    (Equiv.swap x y).ofSubtype = Equiv.swap ↑x ↑y :=
  Equiv.ext fun z => by
    by_cases hz : p z
    · rw [swap_apply_def, of_subtype_apply_of_mem _ hz]
      split_ifs with hzx hzy
      · simp_rw [hzx, Subtype.coe_eta, swap_apply_left]
      · simp_rw [hzy, Subtype.coe_eta, swap_apply_right]
      · rw [swap_apply_of_ne_of_ne]
        rfl
        intro h
        apply hzx
        rw [← h]
        rfl
        intro h
        apply hzy
        rw [← h]
        rfl
    · rw [of_subtype_apply_of_not_mem _ hz, swap_apply_of_ne_of_ne]
      intro h
      apply hz
      rw [h]
      exact Subtype.prop x
      intro h
      apply hz
      rw [h]
      exact Subtype.prop y
#align equiv.perm.of_subtype_swap_eq Equiv.Perm.ofSubtype_swap_eq

/- warning: equiv.perm.is_swap.of_subtype_is_swap -> Equiv.Perm.IsSwap.of_subtype_isSwap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u1} α p] {f : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)}, (Equiv.Perm.IsSwap.{u1} (Subtype.{succ u1} α p) (fun (a : Subtype.{succ u1} α p) (b : Subtype.{succ u1} α p) => Subtype.decidableEq.{u1} α (fun (x : α) => p x) (fun (a : α) (b : α) => _inst_1 a b) a b) f) -> (Equiv.Perm.IsSwap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (fun (_x : MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) => (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) -> (Equiv.Perm.{succ u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.ofSubtype.{u1} α p (fun (a : α) => _inst_2 a)) f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u1} α p] {f : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)}, (Equiv.Perm.IsSwap.{u1} (Subtype.{succ u1} α p) (fun (a : Subtype.{succ u1} α p) (b : Subtype.{succ u1} α p) => Subtype.instDecidableEqSubtype.{u1} α (fun (x : α) => p x) (fun (a : α) (b : α) => _inst_1 a b) a b) f) -> (Equiv.Perm.IsSwap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (fun (_x : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) => Equiv.Perm.{succ u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p)))))) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (MonoidHom.monoidHomClass.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) (Equiv.Perm.ofSubtype.{u1} α p (fun (a : α) => _inst_2 a)) f))
Case conversion may be inaccurate. Consider using '#align equiv.perm.is_swap.of_subtype_is_swap Equiv.Perm.IsSwap.of_subtype_isSwapₓ'. -/
theorem IsSwap.of_subtype_isSwap {p : α → Prop} [DecidablePred p] {f : Perm (Subtype p)}
    (h : f.IsSwap) : (ofSubtype f).IsSwap :=
  let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [Ne.def] at hxy
    exact hxy.1, by
    simp only [hxy.2, of_subtype_swap_eq]
    rfl⟩
#align equiv.perm.is_swap.of_subtype_is_swap Equiv.Perm.IsSwap.of_subtype_isSwap

#print Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self /-
theorem ne_and_ne_of_swap_mul_apply_ne_self {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y ≠ y) :
    f y ≠ y ∧ y ≠ x :=
  by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  by_cases h : f y = x
  · constructor <;> intro <;> simp_all only [if_true, eq_self_iff_true, not_true, Ne.def]
  · split_ifs  at hy <;> cc
#align equiv.perm.ne_and_ne_of_swap_mul_apply_ne_self Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self
-/

end IsSwap

section Support

section Set

variable (p q : Perm α)

#print Equiv.Perm.set_support_inv_eq /-
theorem set_support_inv_eq : { x | p⁻¹ x ≠ x } = { x | p x ≠ x } :=
  by
  ext x
  simp only [Set.mem_setOf_eq, Ne.def]
  rw [inv_def, symm_apply_eq, eq_comm]
#align equiv.perm.set_support_inv_eq Equiv.Perm.set_support_inv_eq
-/

#print Equiv.Perm.set_support_apply_mem /-
theorem set_support_apply_mem {p : Perm α} {a : α} : p a ∈ { x | p x ≠ x } ↔ a ∈ { x | p x ≠ x } :=
  by simp
#align equiv.perm.set_support_apply_mem Equiv.Perm.set_support_apply_mem
-/

#print Equiv.Perm.set_support_zpow_subset /-
theorem set_support_zpow_subset (n : ℤ) : { x | (p ^ n) x ≠ x } ⊆ { x | p x ≠ x } :=
  by
  intro x
  simp only [Set.mem_setOf_eq, Ne.def]
  intro hx H
  simpa [zpow_apply_eq_self_of_apply_eq_self H] using hx
#align equiv.perm.set_support_zpow_subset Equiv.Perm.set_support_zpow_subset
-/

#print Equiv.Perm.set_support_mul_subset /-
theorem set_support_mul_subset : { x | (p * q) x ≠ x } ⊆ { x | p x ≠ x } ∪ { x | q x ≠ x } :=
  by
  intro x
  simp only [perm.coe_mul, Function.comp_apply, Ne.def, Set.mem_union, Set.mem_setOf_eq]
  by_cases hq : q x = x <;> simp [hq]
#align equiv.perm.set_support_mul_subset Equiv.Perm.set_support_mul_subset
-/

end Set

variable [DecidableEq α] [Fintype α] {f g : Perm α}

#print Equiv.Perm.Support /-
/-- The `finset` of nonfixed points of a permutation. -/
def Support (f : Perm α) : Finset α :=
  univ.filterₓ fun x => f x ≠ x
#align equiv.perm.support Equiv.Perm.Support
-/

#print Equiv.Perm.mem_support /-
@[simp]
theorem mem_support {x : α} : x ∈ f.Support ↔ f x ≠ x := by
  rw [support, mem_filter, and_iff_right (mem_univ x)]
#align equiv.perm.mem_support Equiv.Perm.mem_support
-/

#print Equiv.Perm.not_mem_support /-
theorem not_mem_support {x : α} : x ∉ f.Support ↔ f x = x := by simp
#align equiv.perm.not_mem_support Equiv.Perm.not_mem_support
-/

#print Equiv.Perm.coe_support_eq_set_support /-
theorem coe_support_eq_set_support (f : Perm α) : (f.Support : Set α) = { x | f x ≠ x } :=
  by
  ext
  simp
#align equiv.perm.coe_support_eq_set_support Equiv.Perm.coe_support_eq_set_support
-/

/- warning: equiv.perm.support_eq_empty_iff -> Equiv.Perm.support_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {σ : Equiv.Perm.{succ u1} α}, Iff (Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 σ) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) σ (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {σ : Equiv.Perm.{succ u1} α}, Iff (Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 σ) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) σ (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_eq_empty_iff Equiv.Perm.support_eq_empty_iffₓ'. -/
@[simp]
theorem support_eq_empty_iff {σ : Perm α} : σ.Support = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_support, Finset.not_mem_empty, iff_false_iff, Classical.not_not,
    Equiv.Perm.ext_iff, one_apply]
#align equiv.perm.support_eq_empty_iff Equiv.Perm.support_eq_empty_iff

/- warning: equiv.perm.support_one -> Equiv.Perm.support_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_one Equiv.Perm.support_oneₓ'. -/
@[simp]
theorem support_one : (1 : Perm α).Support = ∅ := by rw [support_eq_empty_iff]
#align equiv.perm.support_one Equiv.Perm.support_one

#print Equiv.Perm.support_refl /-
@[simp]
theorem support_refl : Support (Equiv.refl α) = ∅ :=
  support_one
#align equiv.perm.support_refl Equiv.Perm.support_refl
-/

#print Equiv.Perm.support_congr /-
theorem support_congr (h : f.Support ⊆ g.Support) (h' : ∀ x ∈ g.Support, f x = g x) : f = g :=
  by
  ext x
  by_cases hx : x ∈ g.support
  · exact h' x hx
  · rw [not_mem_support.mp hx, ← not_mem_support]
    exact fun H => hx (h H)
#align equiv.perm.support_congr Equiv.Perm.support_congr
-/

/- warning: equiv.perm.support_mul_le -> Equiv.Perm.support_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (f : Equiv.Perm.{succ u1} α) (g : Equiv.Perm.{succ u1} α), LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g)) (HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (f : Equiv.Perm.{succ u1} α) (g : Equiv.Perm.{succ u1} α), LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g)) (HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_mul_le Equiv.Perm.support_mul_leₓ'. -/
theorem support_mul_le (f g : Perm α) : (f * g).Support ≤ f.Support ⊔ g.Support := fun x =>
  by
  rw [sup_eq_union, mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or,
    not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg, hf]
#align equiv.perm.support_mul_le Equiv.Perm.support_mul_le

/- warning: equiv.perm.exists_mem_support_of_mem_support_prod -> Equiv.Perm.exists_mem_support_of_mem_support_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {l : List.{u1} (Equiv.Perm.{succ u1} α)} {x : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l))) -> (Exists.{succ u1} (Equiv.Perm.{succ u1} α) (fun (f : Equiv.Perm.{succ u1} α) => And (Membership.Mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.hasMem.{u1} (Equiv.Perm.{succ u1} α)) f l) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {l : List.{u1} (Equiv.Perm.{succ u1} α)} {x : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l))) -> (Exists.{succ u1} (Equiv.Perm.{succ u1} α) (fun (f : Equiv.Perm.{succ u1} α) => And (Membership.mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.instMembershipList.{u1} (Equiv.Perm.{succ u1} α)) f l) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.exists_mem_support_of_mem_support_prod Equiv.Perm.exists_mem_support_of_mem_support_prodₓ'. -/
theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.Prod.Support) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.Support :=
  by
  contrapose! hx
  simp_rw [mem_support, Classical.not_not] at hx⊢
  induction' l with f l ih generalizing hx
  · rfl
  · rw [List.prod_cons, mul_apply, ih fun g hg => hx g (Or.inr hg), hx f (Or.inl rfl)]
#align equiv.perm.exists_mem_support_of_mem_support_prod Equiv.Perm.exists_mem_support_of_mem_support_prod

#print Equiv.Perm.support_pow_le /-
theorem support_pow_le (σ : Perm α) (n : ℕ) : (σ ^ n).Support ≤ σ.Support := fun x h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)
#align equiv.perm.support_pow_le Equiv.Perm.support_pow_le
-/

/- warning: equiv.perm.support_inv -> Equiv.Perm.support_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (σ : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) σ)) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 σ)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (σ : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) σ)) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 σ)
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_inv Equiv.Perm.support_invₓ'. -/
@[simp]
theorem support_inv (σ : Perm α) : Support σ⁻¹ = σ.Support := by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, iff_self_iff,
    imp_true_iff]
#align equiv.perm.support_inv Equiv.Perm.support_inv

#print Equiv.Perm.apply_mem_support /-
@[simp]
theorem apply_mem_support {x : α} : f x ∈ f.Support ↔ x ∈ f.Support := by
  rw [mem_support, mem_support, Ne.def, Ne.def, not_iff_not, apply_eq_iff_eq]
#align equiv.perm.apply_mem_support Equiv.Perm.apply_mem_support
-/

#print Equiv.Perm.pow_apply_mem_support /-
@[simp]
theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.Support ↔ x ∈ f.Support :=
  by
  induction' n with n ih
  · rfl
  rw [pow_succ, perm.mul_apply, apply_mem_support, ih]
#align equiv.perm.pow_apply_mem_support Equiv.Perm.pow_apply_mem_support
-/

#print Equiv.Perm.zpow_apply_mem_support /-
@[simp]
theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.Support ↔ x ∈ f.Support :=
  by
  cases n
  · rw [Int.ofNat_eq_coe, zpow_ofNat, pow_apply_mem_support]
  · rw [zpow_negSucc, ← support_inv, ← inv_pow, pow_apply_mem_support]
#align equiv.perm.zpow_apply_mem_support Equiv.Perm.zpow_apply_mem_support
-/

#print Equiv.Perm.pow_eq_on_of_mem_support /-
theorem pow_eq_on_of_mem_support (h : ∀ x ∈ f.Support ∩ g.Support, f x = g x) (k : ℕ) :
    ∀ x ∈ f.Support ∩ g.Support, (f ^ k) x = (g ^ k) x :=
  by
  induction' k with k hk
  · simp
  · intro x hx
    rw [pow_succ', mul_apply, pow_succ', mul_apply, h _ hx, hk]
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]
#align equiv.perm.pow_eq_on_of_mem_support Equiv.Perm.pow_eq_on_of_mem_support
-/

/- warning: equiv.perm.disjoint_iff_disjoint_support -> Equiv.Perm.disjoint_iff_disjoint_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, Iff (Equiv.Perm.Disjoint.{u1} α f g) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, Iff (Equiv.Perm.Disjoint.{u1} α f g) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint_iff_disjoint_support Equiv.Perm.disjoint_iff_disjoint_supportₓ'. -/
theorem disjoint_iff_disjoint_support : Disjoint f g ↔ Disjoint f.Support g.Support := by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, Finset.ext_iff, not_and_or]
#align equiv.perm.disjoint_iff_disjoint_support Equiv.Perm.disjoint_iff_disjoint_support

/- warning: equiv.perm.disjoint.disjoint_support -> Equiv.Perm.Disjoint.disjoint_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.disjoint_support Equiv.Perm.Disjoint.disjoint_supportₓ'. -/
theorem Disjoint.disjoint_support (h : Disjoint f g) : Disjoint f.Support g.Support :=
  disjoint_iff_disjoint_support.1 h
#align equiv.perm.disjoint.disjoint_support Equiv.Perm.Disjoint.disjoint_support

/- warning: equiv.perm.disjoint.support_mul -> Equiv.Perm.Disjoint.support_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g)) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.support_mul Equiv.Perm.Disjoint.support_mulₓ'. -/
theorem Disjoint.support_mul (h : Disjoint f g) : (f * g).Support = f.Support ∪ g.Support :=
  by
  refine' le_antisymm (support_mul_le _ _) fun a => _
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_arg f hg).symm.trans h, hg⟩
#align equiv.perm.disjoint.support_mul Equiv.Perm.Disjoint.support_mul

/- warning: equiv.perm.support_prod_of_pairwise_disjoint -> Equiv.Perm.support_prod_of_pairwise_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (l : List.{u1} (Equiv.Perm.{succ u1} α)), (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l) -> (Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l)) (List.foldr.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))))) (Bot.bot.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasBot.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b)))) (List.map.{u1, u1} (Equiv.Perm.{succ u1} α) (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (l : List.{u1} (Equiv.Perm.{succ u1} α)), (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l) -> (Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l)) (List.foldr.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (fun (x._@.Mathlib.GroupTheory.Perm.Support._hyg.4050 : Finset.{u1} α) (x._@.Mathlib.GroupTheory.Perm.Support._hyg.4052 : Finset.{u1} α) => HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) x._@.Mathlib.GroupTheory.Perm.Support._hyg.4050 x._@.Mathlib.GroupTheory.Perm.Support._hyg.4052) (Bot.bot.{u1} (Finset.{u1} α) (BooleanAlgebra.toBot.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b)))) (List.map.{u1, u1} (Equiv.Perm.{succ u1} α) (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) l)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_prod_of_pairwise_disjoint Equiv.Perm.support_prod_of_pairwise_disjointₓ'. -/
theorem support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.Prod.Support = (l.map Support).foldr (· ⊔ ·) ⊥ :=
  by
  induction' l with hd tl hl
  · simp
  · rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.support_mul, hl h.right]
#align equiv.perm.support_prod_of_pairwise_disjoint Equiv.Perm.support_prod_of_pairwise_disjoint

/- warning: equiv.perm.support_prod_le -> Equiv.Perm.support_prod_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (l : List.{u1} (Equiv.Perm.{succ u1} α)), LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l)) (List.foldr.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))))) (Bot.bot.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasBot.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b)))) (List.map.{u1, u1} (Equiv.Perm.{succ u1} α) (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (l : List.{u1} (Equiv.Perm.{succ u1} α)), LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l)) (List.foldr.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (fun (x._@.Mathlib.GroupTheory.Perm.Support._hyg.4161 : Finset.{u1} α) (x._@.Mathlib.GroupTheory.Perm.Support._hyg.4163 : Finset.{u1} α) => HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) x._@.Mathlib.GroupTheory.Perm.Support._hyg.4161 x._@.Mathlib.GroupTheory.Perm.Support._hyg.4163) (Bot.bot.{u1} (Finset.{u1} α) (BooleanAlgebra.toBot.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b)))) (List.map.{u1, u1} (Equiv.Perm.{succ u1} α) (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) l))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_prod_le Equiv.Perm.support_prod_leₓ'. -/
theorem support_prod_le (l : List (Perm α)) : l.Prod.Support ≤ (l.map Support).foldr (· ⊔ ·) ⊥ :=
  by
  induction' l with hd tl hl
  · simp
  · rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine' (support_mul_le hd tl.prod).trans _
    exact sup_le_sup le_rfl hl
#align equiv.perm.support_prod_le Equiv.Perm.support_prod_le

#print Equiv.Perm.support_zpow_le /-
theorem support_zpow_le (σ : Perm α) (n : ℤ) : (σ ^ n).Support ≤ σ.Support := fun x h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)
#align equiv.perm.support_zpow_le Equiv.Perm.support_zpow_le
-/

#print Equiv.Perm.support_swap /-
@[simp]
theorem support_swap {x y : α} (h : x ≠ y) : Support (swap x y) = {x, y} :=
  by
  ext z
  by_cases hx : z = x
  any_goals simpa [hx] using h.symm
  by_cases hy : z = y <;> · simp [swap_apply_of_ne_of_ne, hx, hy] <;> cc
#align equiv.perm.support_swap Equiv.Perm.support_swap
-/

#print Equiv.Perm.support_swap_iff /-
theorem support_swap_iff (x y : α) : Support (swap x y) = {x, y} ↔ x ≠ y :=
  by
  refine' ⟨fun h H => _, support_swap⟩
  subst H
  simp only [swap_self, support_refl, pair_eq_singleton] at h
  have : x ∈ ∅ := by
    rw [h]
    exact mem_singleton.mpr rfl
  simpa
#align equiv.perm.support_swap_iff Equiv.Perm.support_swap_iff
-/

/- warning: equiv.perm.support_swap_mul_swap -> Equiv.Perm.support_swap_mul_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {x : α} {y : α} {z : α}, (List.Nodup.{u1} α (List.cons.{u1} α x (List.cons.{u1} α y (List.cons.{u1} α z (List.nil.{u1} α))))) -> (Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) y z))) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) y (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) z))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {x : α} {y : α} {z : α}, (List.Nodup.{u1} α (List.cons.{u1} α x (List.cons.{u1} α y (List.cons.{u1} α z (List.nil.{u1} α))))) -> (Eq.{succ u1} (Finset.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) y z))) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) y (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) z))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_swap_mul_swap Equiv.Perm.support_swap_mul_swapₓ'. -/
theorem support_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) :
    Support (swap x y * swap y z) = {x, y, z} :=
  by
  simp only [List.not_mem_nil, and_true_iff, List.mem_cons, not_false_iff, List.nodup_cons,
    List.mem_singleton, and_self_iff, List.nodup_nil] at h
  push_neg  at h
  apply le_antisymm
  · convert support_mul_le _ _
    rw [support_swap h.left.left, support_swap h.right]
    ext
    simp [or_comm, or_left_comm]
  · intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right, h.left.right.symm,
        h.right.symm]
#align equiv.perm.support_swap_mul_swap Equiv.Perm.support_swap_mul_swap

/- warning: equiv.perm.support_swap_mul_ge_support_diff -> Equiv.Perm.support_swap_mul_ge_support_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (f : Equiv.Perm.{succ u1} α) (x : α) (y : α), LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) y))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (f : Equiv.Perm.{succ u1} α) (x : α) (y : α), LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) y))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) f))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_swap_mul_ge_support_diff Equiv.Perm.support_swap_mul_ge_support_diffₓ'. -/
theorem support_swap_mul_ge_support_diff (f : Perm α) (x y : α) :
    f.Support \ {x, y} ≤ (swap x y * f).Support :=
  by
  intro
  simp only [and_imp, perm.coe_mul, Function.comp_apply, Ne.def, mem_support, mem_insert, mem_sdiff,
    mem_singleton]
  push_neg
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  exact ha H
#align equiv.perm.support_swap_mul_ge_support_diff Equiv.Perm.support_swap_mul_ge_support_diff

#print Equiv.Perm.support_swap_mul_eq /-
theorem support_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).Support = f.Support \ {x} :=
  by
  by_cases hx : f x = x
  · simp [hx, sdiff_singleton_eq_erase, not_mem_support.mpr hx, erase_eq_of_not_mem]
  ext z
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]
#align equiv.perm.support_swap_mul_eq Equiv.Perm.support_swap_mul_eq
-/

/- warning: equiv.perm.mem_support_swap_mul_imp_mem_support_ne -> Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {x : α} {y : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f x)) f))) -> (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)) (Ne.{succ u1} α y x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {x : α} {y : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) f x)) f))) -> (And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)) (Ne.{succ u1} α y x))
Case conversion may be inaccurate. Consider using '#align equiv.perm.mem_support_swap_mul_imp_mem_support_ne Equiv.Perm.mem_support_swap_mul_imp_mem_support_neₓ'. -/
theorem mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y ∈ Support (swap x (f x) * f)) :
    y ∈ Support f ∧ y ≠ x :=
  by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  by_cases h : f y = x
  · constructor <;> intro <;> simp_all only [if_true, eq_self_iff_true, not_true, Ne.def]
  · split_ifs  at hy <;> cc
#align equiv.perm.mem_support_swap_mul_imp_mem_support_ne Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne

#print Equiv.Perm.Disjoint.mem_imp /-
theorem Disjoint.mem_imp (h : Disjoint f g) {x : α} (hx : x ∈ f.Support) : x ∉ g.Support :=
  disjoint_left.mp h.disjoint_support hx
#align equiv.perm.disjoint.mem_imp Equiv.Perm.Disjoint.mem_imp
-/

#print Equiv.Perm.eq_on_support_mem_disjoint /-
theorem eq_on_support_mem_disjoint {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    ∀ x ∈ f.Support, f x = l.Prod x :=
  by
  induction' l with hd tl IH
  · simpa using h
  · intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    ·
      rw [List.prod_cons, mul_apply,
        not_mem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← not_mem_support]
      refine' (hl.left _ h).symm.mem_imp _
      simpa using hx
#align equiv.perm.eq_on_support_mem_disjoint Equiv.Perm.eq_on_support_mem_disjoint
-/

#print Equiv.Perm.Disjoint.mono /-
theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.Support ≤ f.Support)
    (hg : y.Support ≤ g.Support) : Disjoint x y :=
  by
  rw [disjoint_iff_disjoint_support] at h⊢
  exact h.mono hf hg
#align equiv.perm.disjoint.mono Equiv.Perm.Disjoint.mono
-/

/- warning: equiv.perm.support_le_prod_of_mem -> Equiv.Perm.support_le_prod_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {l : List.{u1} (Equiv.Perm.{succ u1} α)}, (Membership.Mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.hasMem.{u1} (Equiv.Perm.{succ u1} α)) f l) -> (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l) -> (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {l : List.{u1} (Equiv.Perm.{succ u1} α)}, (Membership.mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.instMembershipList.{u1} (Equiv.Perm.{succ u1} α)) f l) -> (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l) -> (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_le_prod_of_mem Equiv.Perm.support_le_prod_of_memₓ'. -/
theorem support_le_prod_of_mem {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    f.Support ≤ l.Prod.Support := by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]
#align equiv.perm.support_le_prod_of_mem Equiv.Perm.support_le_prod_of_mem

section ExtendDomain

variable {β : Type _} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

/- warning: equiv.perm.support_extend_domain -> Equiv.Perm.support_extend_domain is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {β : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} β] [_inst_4 : Fintype.{u2} β] {p : β -> Prop} [_inst_5 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)) {g : Equiv.Perm.{succ u1} α}, Eq.{succ u2} (Finset.{u2} β) (Equiv.Perm.Support.{u2} β (fun (a : β) (b : β) => _inst_3 a b) _inst_4 (Equiv.Perm.extendDomain.{u1, u2} α β g p (fun (a : β) => _inst_5 a) f)) (Finset.map.{u1, u2} α β (Equiv.asEmbedding.{succ u1, succ u2} α β p f) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u2} α] {β : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} β] [_inst_4 : Fintype.{u1} β] {p : β -> Prop} [_inst_5 : DecidablePred.{succ u1} β p] (f : Equiv.{succ u2, succ u1} α (Subtype.{succ u1} β p)) {g : Equiv.Perm.{succ u2} α}, Eq.{succ u1} (Finset.{u1} β) (Equiv.Perm.Support.{u1} β (fun (a : β) (b : β) => _inst_3 a b) _inst_4 (Equiv.Perm.extendDomain.{u2, u1} α β g p (fun (a : β) => _inst_5 a) f)) (Finset.map.{u2, u1} α β (Equiv.asEmbedding.{succ u1, succ u2} β α p f) (Equiv.Perm.Support.{u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
Case conversion may be inaccurate. Consider using '#align equiv.perm.support_extend_domain Equiv.Perm.support_extend_domainₓ'. -/
@[simp]
theorem support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    Support (g.extendDomain f) = g.Support.map f.asEmbedding :=
  by
  ext b
  simp only [exists_prop, Function.Embedding.coeFn_mk, to_embedding_apply, mem_map, Ne.def,
    Function.Embedding.trans_apply, mem_support]
  by_cases pb : p b
  · rw [extend_domain_apply_subtype _ _ pb]
    constructor
    · rintro h
      refine' ⟨f.symm ⟨b, pb⟩, _, by simp⟩
      contrapose! h
      simp [h]
    · rintro ⟨a, ha, hb⟩
      contrapose! ha
      obtain rfl : a = f.symm ⟨b, pb⟩ := by
        rw [eq_symm_apply]
        exact Subtype.coe_injective hb
      rw [eq_symm_apply]
      exact Subtype.coe_injective ha
  · rw [extend_domain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff_iff, not_and, eq_self_iff_true, not_true]
    rintro a ha rfl
    exact pb (Subtype.prop _)
#align equiv.perm.support_extend_domain Equiv.Perm.support_extend_domain

/- warning: equiv.perm.card_support_extend_domain -> Equiv.Perm.card_support_extend_domain is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {β : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} β] [_inst_4 : Fintype.{u2} β] {p : β -> Prop} [_inst_5 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)) {g : Equiv.Perm.{succ u1} α}, Eq.{1} Nat (Finset.card.{u2} β (Equiv.Perm.Support.{u2} β (fun (a : β) (b : β) => _inst_3 a b) _inst_4 (Equiv.Perm.extendDomain.{u1, u2} α β g p (fun (a : β) => _inst_5 a) f))) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u2} α] {β : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} β] [_inst_4 : Fintype.{u1} β] {p : β -> Prop} [_inst_5 : DecidablePred.{succ u1} β p] (f : Equiv.{succ u2, succ u1} α (Subtype.{succ u1} β p)) {g : Equiv.Perm.{succ u2} α}, Eq.{1} Nat (Finset.card.{u1} β (Equiv.Perm.Support.{u1} β (fun (a : β) (b : β) => _inst_3 a b) _inst_4 (Equiv.Perm.extendDomain.{u2, u1} α β g p (fun (a : β) => _inst_5 a) f))) (Finset.card.{u2} α (Equiv.Perm.Support.{u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))
Case conversion may be inaccurate. Consider using '#align equiv.perm.card_support_extend_domain Equiv.Perm.card_support_extend_domainₓ'. -/
theorem card_support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    (g.extendDomain f).Support.card = g.Support.card := by simp
#align equiv.perm.card_support_extend_domain Equiv.Perm.card_support_extend_domain

end ExtendDomain

section Card

/- warning: equiv.perm.card_support_eq_zero -> Equiv.Perm.card_support_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α}, Iff (Eq.{1} Nat (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α}, Iff (Eq.{1} Nat (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.card_support_eq_zero Equiv.Perm.card_support_eq_zeroₓ'. -/
@[simp]
theorem card_support_eq_zero {f : Perm α} : f.Support.card = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, support_eq_empty_iff]
#align equiv.perm.card_support_eq_zero Equiv.Perm.card_support_eq_zero

/- warning: equiv.perm.one_lt_card_support_of_ne_one -> Equiv.Perm.one_lt_card_support_of_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α}, (Ne.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α}, (Ne.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.one_lt_card_support_of_ne_one Equiv.Perm.one_lt_card_support_of_ne_oneₓ'. -/
theorem one_lt_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < f.Support.card :=
  by
  simp_rw [one_lt_card_iff, mem_support, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h
#align equiv.perm.one_lt_card_support_of_ne_one Equiv.Perm.one_lt_card_support_of_ne_one

#print Equiv.Perm.card_support_ne_one /-
theorem card_support_ne_one (f : Perm α) : f.Support.card ≠ 1 :=
  by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_support_of_ne_one h)
#align equiv.perm.card_support_ne_one Equiv.Perm.card_support_ne_one
-/

/- warning: equiv.perm.card_support_le_one -> Equiv.Perm.card_support_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α}, Iff (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α}, Iff (LE.le.{0} Nat instLENat (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.card_support_le_one Equiv.Perm.card_support_le_oneₓ'. -/
@[simp]
theorem card_support_le_one {f : Perm α} : f.Support.card ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq, Nat.lt_succ_iff, le_zero_iff, card_support_eq_zero, or_iff_not_imp_right,
    imp_iff_right f.card_support_ne_one]
#align equiv.perm.card_support_le_one Equiv.Perm.card_support_le_one

/- warning: equiv.perm.two_le_card_support_of_ne_one -> Equiv.Perm.two_le_card_support_of_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α}, (Ne.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) -> (LE.le.{0} Nat Nat.hasLe (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α}, (Ne.{succ u1} (Equiv.Perm.{succ u1} α) f (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) -> (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.two_le_card_support_of_ne_one Equiv.Perm.two_le_card_support_of_ne_oneₓ'. -/
theorem two_le_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ f.Support.card :=
  one_lt_card_support_of_ne_one h
#align equiv.perm.two_le_card_support_of_ne_one Equiv.Perm.two_le_card_support_of_ne_one

#print Equiv.Perm.card_support_swap_mul /-
theorem card_support_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) :
    (swap x (f x) * f).Support.card < f.Support.card :=
  Finset.card_lt_card
    ⟨fun z hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩
#align equiv.perm.card_support_swap_mul Equiv.Perm.card_support_swap_mul
-/

#print Equiv.Perm.card_support_swap /-
theorem card_support_swap {x y : α} (hxy : x ≠ y) : (swap x y).Support.card = 2 :=
  show (swap x y).Support.card = Finset.card ⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
    congr_arg card <| by simp [support_swap hxy, *, Finset.ext_iff]
#align equiv.perm.card_support_swap Equiv.Perm.card_support_swap
-/

#print Equiv.Perm.card_support_eq_two /-
@[simp]
theorem card_support_eq_two {f : Perm α} : f.Support.card = 2 ↔ IsSwap f :=
  by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine' ⟨x, y, hmem, _⟩
    ext a
    have key : ∀ b, f b ≠ b ↔ _ := fun b => by rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or_distrib.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy
#align equiv.perm.card_support_eq_two Equiv.Perm.card_support_eq_two
-/

/- warning: equiv.perm.disjoint.card_support_mul -> Equiv.Perm.Disjoint.card_support_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Eq.{1} Nat (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {f : Equiv.Perm.{succ u1} α} {g : Equiv.Perm.{succ u1} α}, (Equiv.Perm.Disjoint.{u1} α f g) -> (Eq.{1} Nat (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 f)) (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 g))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.disjoint.card_support_mul Equiv.Perm.Disjoint.card_support_mulₓ'. -/
theorem Disjoint.card_support_mul (h : Disjoint f g) :
    (f * g).Support.card = f.Support.card + g.Support.card :=
  by
  rw [← Finset.card_disjoint_union]
  · congr
    ext
    simp [h.support_mul]
  · simpa using h.disjoint_support
#align equiv.perm.disjoint.card_support_mul Equiv.Perm.Disjoint.card_support_mul

/- warning: equiv.perm.card_support_prod_list_of_pairwise_disjoint -> Equiv.Perm.card_support_prod_list_of_pairwise_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {l : List.{u1} (Equiv.Perm.{succ u1} α)}, (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l) -> (Eq.{1} Nat (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l))) (List.sum.{0} Nat Nat.hasAdd Nat.hasZero (List.map.{u1, 0} (Equiv.Perm.{succ u1} α) Nat (Function.comp.{succ u1, succ u1, 1} (Equiv.Perm.{succ u1} α) (Finset.{u1} α) Nat (Finset.card.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2)) l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {l : List.{u1} (Equiv.Perm.{succ u1} α)}, (List.Pairwise.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.Disjoint.{u1} α) l) -> (Eq.{1} Nat (Finset.card.{u1} α (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l))) (List.sum.{0} Nat instAddNat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (List.map.{u1, 0} (Equiv.Perm.{succ u1} α) Nat (Function.comp.{succ u1, succ u1, 1} (Equiv.Perm.{succ u1} α) (Finset.{u1} α) Nat (Finset.card.{u1} α) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2)) l)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.card_support_prod_list_of_pairwise_disjoint Equiv.Perm.card_support_prod_list_of_pairwise_disjointₓ'. -/
theorem card_support_prod_list_of_pairwise_disjoint {l : List (Perm α)} (h : l.Pairwise Disjoint) :
    l.Prod.Support.card = (l.map (Finset.card ∘ Support)).Sum :=
  by
  induction' l with a t ih
  · exact card_support_eq_zero.mpr rfl
  · obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul
#align equiv.perm.card_support_prod_list_of_pairwise_disjoint Equiv.Perm.card_support_prod_list_of_pairwise_disjoint

end Card

end Support

#print Equiv.Perm.support_subtype_perm /-
@[simp]
theorem support_subtype_perm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    (f.subtypePerm h : Perm { x // x ∈ s }).Support = s.attach.filterₓ fun x => f x ≠ x :=
  by
  ext
  simp [Subtype.ext_iff]
#align equiv.perm.support_subtype_perm Equiv.Perm.support_subtype_perm
-/

end Equiv.Perm

