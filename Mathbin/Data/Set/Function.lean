/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov

! This file was ported from Lean 3 source module data.set.function
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Prod
import Mathbin.Logic.Function.Conjugate

/-!
# Functions over sets

## Main definitions

### Predicate

* `set.eq_on f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `set.maps_to f s t` : `f` sends every point of `s` to a point of `t`;
* `set.inj_on f s` : restriction of `f` to `s` is injective;
* `set.surj_on f s t` : every point in `s` has a preimage in `s`;
* `set.bij_on f s t` : `f` is a bijection between `s` and `t`;
* `set.left_inv_on f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `set.right_inv_on f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `set.inv_on f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `set.left_inv_on f' f s` and `set.right_inv_on f' f t`.

### Functions

* `set.restrict f s` : restrict the domain of `f` to the set `s`;
* `set.cod_restrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `set.maps_to.restrict f s t h`: given `h : maps_to f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/


universe u v w x y

variable {α : Type u} {β : Type v} {π : α → Type v} {γ : Type w} {ι : Sort x}

open Function

namespace Set

/-! ### Restrict -/


#print Set.restrict /-
/-- Restrict domain of a function `f` to a set `s`. Same as `subtype.restrict` but this version
takes an argument `↥s` instead of `subtype s`. -/
def restrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x
#align set.restrict Set.restrict
-/

/- warning: set.restrict_eq -> Set.restrict_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f) (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> β) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f) (Function.comp.{succ u2, succ u2, succ u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) α β f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)))
Case conversion may be inaccurate. Consider using '#align set.restrict_eq Set.restrict_eqₓ'. -/
theorem restrict_eq (f : α → β) (s : Set α) : s.restrict f = f ∘ coe :=
  rfl
#align set.restrict_eq Set.restrict_eq

/- warning: set.restrict_apply -> Set.restrict_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), Eq.{succ u2} β (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f x) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (x : Set.Elem.{u2} α s), Eq.{succ u1} β (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f x) (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x))
Case conversion may be inaccurate. Consider using '#align set.restrict_apply Set.restrict_applyₓ'. -/
@[simp]
theorem restrict_apply (f : α → β) (s : Set α) (x : s) : s.restrict f x = f x :=
  rfl
#align set.restrict_apply Set.restrict_apply

/- warning: set.restrict_eq_iff -> Set.restrict_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {π : α -> Type.{u2}} {f : forall (a : α), π a} {s : Set.{u1} α} {g : forall (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), π ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a)}, Iff (Eq.{max (succ u1) (succ u2)} (forall (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), π ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a)) (Set.restrict.{u1, u2} α (fun (a : α) => π a) s f) g) (forall (a : α) (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s), Eq.{succ u2} (π a) (f a) (g (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) a ha)))
but is expected to have type
  forall {α : Type.{u2}} {π : α -> Type.{u1}} {f : forall (a : α), π a} {s : Set.{u2} α} {g : forall (a : Set.Elem.{u2} α s), π (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a)}, Iff (Eq.{max (succ u2) (succ u1)} (forall (a : Set.Elem.{u2} α s), π (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a)) (Set.restrict.{u2, u1} α (fun (a : α) => π a) s f) g) (forall (a : α) (ha : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s), Eq.{succ u1} (π a) (f a) (g (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a ha)))
Case conversion may be inaccurate. Consider using '#align set.restrict_eq_iff Set.restrict_eq_iffₓ'. -/
theorem restrict_eq_iff {f : ∀ a, π a} {s : Set α} {g : ∀ a : s, π a} :
    restrict s f = g ↔ ∀ (a) (ha : a ∈ s), f a = g ⟨a, ha⟩ :=
  funext_iff.trans Subtype.forall
#align set.restrict_eq_iff Set.restrict_eq_iff

/- warning: set.eq_restrict_iff -> Set.eq_restrict_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {π : α -> Type.{u2}} {s : Set.{u1} α} {f : forall (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), π ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a)} {g : forall (a : α), π a}, Iff (Eq.{max (succ u1) (succ u2)} (forall (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), π ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a)) f (Set.restrict.{u1, u2} α π s g)) (forall (a : α) (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s), Eq.{succ u2} (π ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) a ha))) (f (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) a ha)) (g a))
but is expected to have type
  forall {α : Type.{u2}} {π : α -> Type.{u1}} {s : Set.{u2} α} {f : forall (a : Set.Elem.{u2} α s), π (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a)} {g : forall (a : α), π a}, Iff (Eq.{max (succ u2) (succ u1)} (forall (a : Set.Elem.{u2} α s), π (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a)) f (Set.restrict.{u2, u1} α (fun (a : α) => π a) s g)) (forall (a : α) (ha : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s), Eq.{succ u1} (π (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a ha))) (f (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a ha)) (g a))
Case conversion may be inaccurate. Consider using '#align set.eq_restrict_iff Set.eq_restrict_iffₓ'. -/
theorem eq_restrict_iff {s : Set α} {f : ∀ a : s, π a} {g : ∀ a, π a} :
    f = restrict s g ↔ ∀ (a) (ha : a ∈ s), f ⟨a, ha⟩ = g a :=
  funext_iff.trans Subtype.forall
#align set.eq_restrict_iff Set.eq_restrict_iff

/- warning: set.range_restrict -> Set.range_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)) (Set.image.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, succ u2} β (Set.Elem.{u2} α s) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)) (Set.image.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.range_restrict Set.range_restrictₓ'. -/
@[simp]
theorem range_restrict (f : α → β) (s : Set α) : Set.range (s.restrict f) = f '' s :=
  (range_comp _ _).trans <| congr_arg ((· '' ·) f) Subtype.range_coe
#align set.range_restrict Set.range_restrict

/- warning: set.image_restrict -> Set.image_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} (Set.Elem.{u2} α s) β (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f) (Set.preimage.{u2, u2} (Set.Elem.{u2} α s) α (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) t)) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) t s))
Case conversion may be inaccurate. Consider using '#align set.image_restrict Set.image_restrictₓ'. -/
theorem image_restrict (f : α → β) (s t : Set α) : s.restrict f '' (coe ⁻¹' t) = f '' (t ∩ s) := by
  rw [restrict, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]
#align set.image_restrict Set.image_restrict

/- warning: set.restrict_dite -> Set.restrict_dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)] (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> β) (g : forall (a : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> β), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Set.restrict.{u1, u2} α (fun (a : α) => β) s (fun (a : α) => dite.{succ u2} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (_inst_1 a) (fun (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a h) (fun (h : Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) => g a h))) (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a) (Subtype.property.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)] (f : forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> β) (g : forall (a : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> β), Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> β) (Set.restrict.{u2, u1} α (fun (a : α) => β) s (fun (a : α) => dite.{succ u1} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (_inst_1 a) (fun (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => f a h) (fun (h : Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) => g a h))) (fun (a : Set.Elem.{u2} α s) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a))
Case conversion may be inaccurate. Consider using '#align set.restrict_dite Set.restrict_diteₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a «expr ∉ » s) -/
@[simp]
theorem restrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ (a) (_ : a ∉ s), β) :
    (s.restrict fun a => if h : a ∈ s then f a h else g a h) = fun a => f a a.2 :=
  funext fun a => dif_pos a.2
#align set.restrict_dite Set.restrict_dite

/- warning: set.restrict_dite_compl -> Set.restrict_dite_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)] (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> β) (g : forall (a : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> β), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> β) (Set.restrict.{u1, u2} α (fun (a : α) => β) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (fun (a : α) => dite.{succ u2} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (_inst_1 a) (fun (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a h) (fun (h : Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) => g a h))) (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) => g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))))) a) (Subtype.property.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)] (f : forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> β) (g : forall (a : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> β), Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) -> β) (Set.restrict.{u2, u1} α (fun (a : α) => β) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (fun (a : α) => dite.{succ u1} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (_inst_1 a) (fun (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => f a h) (fun (h : Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) => g a h))) (fun (a : Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) => g (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) a) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) a))
Case conversion may be inaccurate. Consider using '#align set.restrict_dite_compl Set.restrict_dite_complₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a «expr ∉ » s) -/
@[simp]
theorem restrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ (a) (_ : a ∉ s), β) :
    (sᶜ.restrict fun a => if h : a ∈ s then f a h else g a h) = fun a => g a a.2 :=
  funext fun a => dif_neg a.2
#align set.restrict_dite_compl Set.restrict_dite_compl

/- warning: set.restrict_ite -> Set.restrict_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (g : α -> β) (s : Set.{u1} α) [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)], Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Set.restrict.{u1, u2} α (fun (a : α) => β) s (fun (a : α) => ite.{succ u2} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (_inst_1 a) (f a) (g a))) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (g : α -> β) (s : Set.{u2} α) [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)], Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> β) (Set.restrict.{u2, u1} α (fun (a : α) => β) s (fun (a : α) => ite.{succ u1} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (_inst_1 a) (f a) (g a))) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)
Case conversion may be inaccurate. Consider using '#align set.restrict_ite Set.restrict_iteₓ'. -/
@[simp]
theorem restrict_ite (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (s.restrict fun a => if a ∈ s then f a else g a) = s.restrict f :=
  restrict_dite _ _
#align set.restrict_ite Set.restrict_ite

/- warning: set.restrict_ite_compl -> Set.restrict_ite_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (g : α -> β) (s : Set.{u1} α) [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)], Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> β) (Set.restrict.{u1, u2} α (fun (a : α) => β) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (fun (a : α) => ite.{succ u2} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (_inst_1 a) (f a) (g a))) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (g : α -> β) (s : Set.{u2} α) [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)], Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) -> β) (Set.restrict.{u2, u1} α (fun (a : α) => β) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (fun (a : α) => ite.{succ u1} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (_inst_1 a) (f a) (g a))) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) g)
Case conversion may be inaccurate. Consider using '#align set.restrict_ite_compl Set.restrict_ite_complₓ'. -/
@[simp]
theorem restrict_ite_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (sᶜ.restrict fun a => if a ∈ s then f a else g a) = sᶜ.restrict g :=
  restrict_dite_compl _ _
#align set.restrict_ite_compl Set.restrict_ite_compl

/- warning: set.restrict_piecewise -> Set.restrict_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (g : α -> β) (s : Set.{u1} α) [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)], Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Set.restrict.{u1, u2} α (fun (a : α) => β) s (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j))) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (g : α -> β) (s : Set.{u2} α) [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)], Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> β) (Set.restrict.{u2, u1} α (fun (a : α) => β) s (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j))) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)
Case conversion may be inaccurate. Consider using '#align set.restrict_piecewise Set.restrict_piecewiseₓ'. -/
@[simp]
theorem restrict_piecewise (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    s.restrict (piecewise s f g) = s.restrict f :=
  restrict_ite _ _ _
#align set.restrict_piecewise Set.restrict_piecewise

/- warning: set.restrict_piecewise_compl -> Set.restrict_piecewise_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (g : α -> β) (s : Set.{u1} α) [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)], Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> β) (Set.restrict.{u1, u2} α (fun (a : α) => β) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j))) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (g : α -> β) (s : Set.{u2} α) [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)], Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) -> β) (Set.restrict.{u2, u1} α (fun (a : α) => β) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j))) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) g)
Case conversion may be inaccurate. Consider using '#align set.restrict_piecewise_compl Set.restrict_piecewise_complₓ'. -/
@[simp]
theorem restrict_piecewise_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    sᶜ.restrict (piecewise s f g) = sᶜ.restrict g :=
  restrict_ite_compl _ _ _
#align set.restrict_piecewise_compl Set.restrict_piecewise_compl

/- warning: set.restrict_extend_range -> Set.restrict_extend_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : α -> γ) (g' : β -> γ), Eq.{max (succ u2) (succ u3)} ((coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) -> γ) (Set.restrict.{u2, u3} β (fun (ᾰ : β) => γ) (Set.range.{u2, succ u1} β α f) (Function.extend.{succ u1, succ u2, succ u3} α β γ f g g')) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) => g (Exists.choose.{succ u1} α (fun (y : α) => Eq.{succ u2} β (f y) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} β (fun (a : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (Set.range.{u2, succ u1} β α f))) β (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} β (fun (a : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (Set.range.{u2, succ u1} β α f))) β (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} β (fun (a : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (Set.range.{u2, succ u1} β α f))) β (coeBase.{succ u2, succ u2} (Subtype.{succ u2} β (fun (a : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (Set.range.{u2, succ u1} β α f))) β (coeSubtype.{succ u2} β (fun (a : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (Set.range.{u2, succ u1} β α f)))))) x)) (Subtype.coe_prop.{u2} β (Set.range.{u2, succ u1} β α f) x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : α -> β) (g : α -> γ) (g' : β -> γ), Eq.{max (succ u3) (succ u2)} ((Set.Elem.{u3} β (Set.range.{u3, succ u1} β α f)) -> γ) (Set.restrict.{u3, u2} β (fun (ᾰ : β) => γ) (Set.range.{u3, succ u1} β α f) (Function.extend.{succ u1, succ u3, succ u2} α β γ f g g')) (fun (x : Set.Elem.{u3} β (Set.range.{u3, succ u1} β α f)) => g (Exists.choose.{succ u1} α (fun (y : α) => Eq.{succ u3} β (f y) (Subtype.val.{succ u3} β (fun (a : β) => Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a (Set.range.{u3, succ u1} β α f)) x)) (Subtype.coe_prop.{u3} β (Set.range.{u3, succ u1} β α f) x)))
Case conversion may be inaccurate. Consider using '#align set.restrict_extend_range Set.restrict_extend_rangeₓ'. -/
theorem restrict_extend_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f).restrict (extend f g g') = fun x => g x.coe_prop.some := by convert restrict_dite _ _
#align set.restrict_extend_range Set.restrict_extend_range

/- warning: set.restrict_extend_compl_range -> Set.restrict_extend_compl_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : α -> γ) (g' : β -> γ), Eq.{max (succ u2) (succ u3)} ((coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f))) -> γ) (Set.restrict.{u2, u3} β (fun (ᾰ : β) => γ) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f)) (Function.extend.{succ u1, succ u2, succ u3} α β γ f g g')) (Function.comp.{succ u2, succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f))) β γ g' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f))) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f))) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f))) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f))) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f)))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : α -> β) (g : α -> γ) (g' : β -> γ), Eq.{max (succ u3) (succ u2)} ((Set.Elem.{u3} β (HasCompl.compl.{u3} (Set.{u3} β) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} β) (Set.instBooleanAlgebraSet.{u3} β)) (Set.range.{u3, succ u1} β α f))) -> γ) (Set.restrict.{u3, u2} β (fun (ᾰ : β) => γ) (HasCompl.compl.{u3} (Set.{u3} β) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} β) (Set.instBooleanAlgebraSet.{u3} β)) (Set.range.{u3, succ u1} β α f)) (Function.extend.{succ u1, succ u3, succ u2} α β γ f g g')) (Function.comp.{succ u3, succ u3, succ u2} (Subtype.{succ u3} β (fun (x : β) => Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x (HasCompl.compl.{u3} (Set.{u3} β) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} β) (Set.instBooleanAlgebraSet.{u3} β)) (Set.range.{u3, succ u1} β α f)))) β γ g' (Subtype.val.{succ u3} β (fun (x : β) => Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x (HasCompl.compl.{u3} (Set.{u3} β) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} β) (Set.instBooleanAlgebraSet.{u3} β)) (Set.range.{u3, succ u1} β α f)))))
Case conversion may be inaccurate. Consider using '#align set.restrict_extend_compl_range Set.restrict_extend_compl_rangeₓ'. -/
@[simp]
theorem restrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    range fᶜ.restrict (extend f g g') = g' ∘ coe := by convert restrict_dite_compl _ _
#align set.restrict_extend_compl_range Set.restrict_extend_compl_range

/- warning: set.range_extend_subset -> Set.range_extend_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : α -> γ) (g' : β -> γ), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.range.{u3, succ u2} γ β (Function.extend.{succ u1, succ u2, succ u3} α β γ f g g')) (Union.union.{u3} (Set.{u3} γ) (Set.hasUnion.{u3} γ) (Set.range.{u3, succ u1} γ α g) (Set.image.{u2, u3} β γ g' (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : α -> γ) (g' : β -> γ), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet_1.{u3} γ) (Set.range.{u3, succ u2} γ β (Function.extend.{succ u1, succ u2, succ u3} α β γ f g g')) (Union.union.{u3} (Set.{u3} γ) (Set.instUnionSet_1.{u3} γ) (Set.range.{u3, succ u1} γ α g) (Set.image.{u2, u3} β γ g' (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.range.{u2, succ u1} β α f))))
Case conversion may be inaccurate. Consider using '#align set.range_extend_subset Set.range_extend_subsetₓ'. -/
theorem range_extend_subset (f : α → β) (g : α → γ) (g' : β → γ) :
    range (extend f g g') ⊆ range g ∪ g' '' range fᶜ := by
  classical
    rintro _ ⟨y, rfl⟩
    rw [extend_def]
    split_ifs
    exacts[Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]
#align set.range_extend_subset Set.range_extend_subset

/- warning: set.range_extend -> Set.range_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (g : α -> γ) (g' : β -> γ), Eq.{succ u3} (Set.{u3} γ) (Set.range.{u3, succ u2} γ β (Function.extend.{succ u1, succ u2, succ u3} α β γ f g g')) (Union.union.{u3} (Set.{u3} γ) (Set.hasUnion.{u3} γ) (Set.range.{u3, succ u1} γ α g) (Set.image.{u2, u3} β γ g' (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u3, succ u2} α β f) -> (forall (g : α -> γ) (g' : β -> γ), Eq.{succ u1} (Set.{u1} γ) (Set.range.{u1, succ u2} γ β (Function.extend.{succ u3, succ u2, succ u1} α β γ f g g')) (Union.union.{u1} (Set.{u1} γ) (Set.instUnionSet_1.{u1} γ) (Set.range.{u1, succ u3} γ α g) (Set.image.{u2, u1} β γ g' (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.range.{u2, succ u3} β α f)))))
Case conversion may be inaccurate. Consider using '#align set.range_extend Set.range_extendₓ'. -/
theorem range_extend {f : α → β} (hf : Injective f) (g : α → γ) (g' : β → γ) :
    range (extend f g g') = range g ∪ g' '' range fᶜ :=
  by
  refine' (range_extend_subset _ _ _).antisymm _
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts[⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]
#align set.range_extend Set.range_extend

/- warning: set.cod_restrict -> Set.codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> α) (s : Set.{u1} α), (forall (x : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f x) s) -> ι -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (f : ι -> α) (s : Set.{u1} α), (forall (x : ι), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (f x) s) -> ι -> (Set.Elem.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.cod_restrict Set.codRestrictₓ'. -/
/-- Restrict codomain of a function `f` to a set `s`. Same as `subtype.coind` but this version
has codomain `↥s` instead of `subtype s`. -/
def codRestrict (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) : ι → s := fun x => ⟨f x, h x⟩
#align set.cod_restrict Set.codRestrict

/- warning: set.coe_cod_restrict_apply -> Set.val_codRestrict_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> α) (s : Set.{u1} α) (h : forall (x : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f x) s) (x : ι), Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) (Set.codRestrict.{u1, u2} α ι f s h x)) (f x)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (f : ι -> α) (s : Set.{u2} α) (h : forall (x : ι), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (f x) s) (x : ι), Eq.{succ u2} α (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (Set.codRestrict.{u2, u1} α ι f s h x)) (f x)
Case conversion may be inaccurate. Consider using '#align set.coe_cod_restrict_apply Set.val_codRestrict_applyₓ'. -/
@[simp]
theorem val_codRestrict_apply (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) (x : ι) :
    (codRestrict f s h x : α) = f x :=
  rfl
#align set.coe_cod_restrict_apply Set.val_codRestrict_apply

/- warning: set.restrict_comp_cod_restrict -> Set.restrict_comp_codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> α} {g : α -> β} {b : Set.{u1} α} (h : forall (x : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f x) b), Eq.{max u3 (succ u2)} (ι -> β) (Function.comp.{u3, succ u1, succ u2} ι (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) b) β (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) b g) (Set.codRestrict.{u1, u3} α ι f b h)) (Function.comp.{u3, succ u1, succ u2} ι α β g f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Type.{u1}} {f : ι -> α} {g : α -> β} {b : Set.{u3} α} (h : forall (x : ι), Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) (f x) b), Eq.{max (succ u2) (succ u1)} (ι -> β) (Function.comp.{succ u1, succ u3, succ u2} ι (Set.Elem.{u3} α b) β (Set.restrict.{u3, u2} α (fun (ᾰ : α) => β) b g) (Set.codRestrict.{u3, u1} α ι f b h)) (Function.comp.{succ u1, succ u3, succ u2} ι α β g f)
Case conversion may be inaccurate. Consider using '#align set.restrict_comp_cod_restrict Set.restrict_comp_codRestrictₓ'. -/
@[simp]
theorem restrict_comp_codRestrict {f : ι → α} {g : α → β} {b : Set α} (h : ∀ x, f x ∈ b) :
    b.restrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl
#align set.restrict_comp_cod_restrict Set.restrict_comp_codRestrict

/- warning: set.injective_cod_restrict -> Set.injective_codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {s : Set.{u1} α} (h : forall (x : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f x) s), Iff (Function.Injective.{u2, succ u1} ι (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Set.codRestrict.{u1, u2} α ι f s h)) (Function.Injective.{u2, succ u1} ι α f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {f : ι -> α} {s : Set.{u2} α} (h : forall (x : ι), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (f x) s), Iff (Function.Injective.{succ u1, succ u2} ι (Set.Elem.{u2} α s) (Set.codRestrict.{u2, u1} α ι f s h)) (Function.Injective.{succ u1, succ u2} ι α f)
Case conversion may be inaccurate. Consider using '#align set.injective_cod_restrict Set.injective_codRestrictₓ'. -/
@[simp]
theorem injective_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    Injective (codRestrict f s h) ↔ Injective f := by
  simp only [injective, Subtype.ext_iff, coe_cod_restrict_apply]
#align set.injective_cod_restrict Set.injective_codRestrict

alias injective_cod_restrict ↔ _ _root_.function.injective.cod_restrict

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ f₃ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β}

/-! ### Equality on a set -/


#print Set.EqOn /-
/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x
#align set.eq_on Set.EqOn
-/

/- warning: set.eq_on_empty -> Set.eqOn_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f₁ : α -> β) (f₂ : α -> β), Set.EqOn.{u1, u2} α β f₁ f₂ (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f₁ : α -> β) (f₂ : α -> β), Set.EqOn.{u2, u1} α β f₁ f₂ (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))
Case conversion may be inaccurate. Consider using '#align set.eq_on_empty Set.eqOn_emptyₓ'. -/
@[simp]
theorem eqOn_empty (f₁ f₂ : α → β) : EqOn f₁ f₂ ∅ := fun x => False.elim
#align set.eq_on_empty Set.eqOn_empty

/- warning: set.restrict_eq_restrict_iff -> Set.restrict_eq_restrict_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, Iff (Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f₁) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f₂)) (Set.EqOn.{u1, u2} α β f₁ f₂ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, Iff (Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> β) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f₁) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f₂)) (Set.EqOn.{u2, u1} α β f₁ f₂ s)
Case conversion may be inaccurate. Consider using '#align set.restrict_eq_restrict_iff Set.restrict_eq_restrict_iffₓ'. -/
@[simp]
theorem restrict_eq_restrict_iff : restrict s f₁ = restrict s f₂ ↔ EqOn f₁ f₂ s :=
  restrict_eq_iff
#align set.restrict_eq_restrict_iff Set.restrict_eq_restrict_iff

/- warning: set.eq_on.symm -> Set.EqOn.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.EqOn.{u1, u2} α β f₂ f₁ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Set.EqOn.{u2, u1} α β f₂ f₁ s)
Case conversion may be inaccurate. Consider using '#align set.eq_on.symm Set.EqOn.symmₓ'. -/
@[symm]
theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun x hx => (h hx).symm
#align set.eq_on.symm Set.EqOn.symm

/- warning: set.eq_on_comm -> Set.eqOn_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, Iff (Set.EqOn.{u1, u2} α β f₁ f₂ s) (Set.EqOn.{u1, u2} α β f₂ f₁ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, Iff (Set.EqOn.{u2, u1} α β f₁ f₂ s) (Set.EqOn.{u2, u1} α β f₂ f₁ s)
Case conversion may be inaccurate. Consider using '#align set.eq_on_comm Set.eqOn_commₓ'. -/
theorem eqOn_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s :=
  ⟨EqOn.symm, EqOn.symm⟩
#align set.eq_on_comm Set.eqOn_comm

/- warning: set.eq_on_refl -> Set.eqOn_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Set.EqOn.{u1, u2} α β f f s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Set.EqOn.{u2, u1} α β f f s
Case conversion may be inaccurate. Consider using '#align set.eq_on_refl Set.eqOn_reflₓ'. -/
@[refl]
theorem eqOn_refl (f : α → β) (s : Set α) : EqOn f f s := fun _ _ => rfl
#align set.eq_on_refl Set.eqOn_refl

/- warning: set.eq_on.trans -> Set.EqOn.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} {f₃ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.EqOn.{u1, u2} α β f₂ f₃ s) -> (Set.EqOn.{u1, u2} α β f₁ f₃ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} {f₃ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Set.EqOn.{u2, u1} α β f₂ f₃ s) -> (Set.EqOn.{u2, u1} α β f₁ f₃ s)
Case conversion may be inaccurate. Consider using '#align set.eq_on.trans Set.EqOn.transₓ'. -/
@[trans]
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun x hx =>
  (h₁ hx).trans (h₂ hx)
#align set.eq_on.trans Set.EqOn.trans

/- warning: set.eq_on.image_eq -> Set.EqOn.image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f₁ s) (Set.image.{u1, u2} α β f₂ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f₁ s) (Set.image.{u2, u1} α β f₂ s))
Case conversion may be inaccurate. Consider using '#align set.eq_on.image_eq Set.EqOn.image_eqₓ'. -/
theorem EqOn.image_eq (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s :=
  image_congr HEq
#align set.eq_on.image_eq Set.EqOn.image_eq

/- warning: set.eq_on.inter_preimage_eq -> Set.EqOn.inter_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (forall (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f₁ t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f₂ t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (forall (t : Set.{u1} β), Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s (Set.preimage.{u2, u1} α β f₁ t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s (Set.preimage.{u2, u1} α β f₂ t)))
Case conversion may be inaccurate. Consider using '#align set.eq_on.inter_preimage_eq Set.EqOn.inter_preimage_eqₓ'. -/
theorem EqOn.inter_preimage_eq (heq : EqOn f₁ f₂ s) (t : Set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t :=
  ext fun x => and_congr_right_iff.2 fun hx => by rw [mem_preimage, mem_preimage, HEq hx]
#align set.eq_on.inter_preimage_eq Set.EqOn.inter_preimage_eq

/- warning: set.eq_on.mono -> Set.EqOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s₂) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s₂) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s₂) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s₁)
Case conversion may be inaccurate. Consider using '#align set.eq_on.mono Set.EqOn.monoₓ'. -/
theorem EqOn.mono (hs : s₁ ⊆ s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun x hx => hf (hs hx)
#align set.eq_on.mono Set.EqOn.mono

/- warning: set.eq_on_union -> Set.eqOn_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, Iff (Set.EqOn.{u1, u2} α β f₁ f₂ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (And (Set.EqOn.{u1, u2} α β f₁ f₂ s₁) (Set.EqOn.{u1, u2} α β f₁ f₂ s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, Iff (Set.EqOn.{u2, u1} α β f₁ f₂ (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂)) (And (Set.EqOn.{u2, u1} α β f₁ f₂ s₁) (Set.EqOn.{u2, u1} α β f₁ f₂ s₂))
Case conversion may be inaccurate. Consider using '#align set.eq_on_union Set.eqOn_unionₓ'. -/
@[simp]
theorem eqOn_union : EqOn f₁ f₂ (s₁ ∪ s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂ :=
  ball_or_left
#align set.eq_on_union Set.eqOn_union

/- warning: set.eq_on.union -> Set.EqOn.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s₁) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s₂) -> (Set.EqOn.{u1, u2} α β f₁ f₂ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s₁) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s₂) -> (Set.EqOn.{u2, u1} α β f₁ f₂ (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂))
Case conversion may be inaccurate. Consider using '#align set.eq_on.union Set.EqOn.unionₓ'. -/
theorem EqOn.union (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ (s₁ ∪ s₂) :=
  eqOn_union.2 ⟨h₁, h₂⟩
#align set.eq_on.union Set.EqOn.union

/- warning: set.eq_on.comp_left -> Set.EqOn.comp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} {g : β -> γ}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.EqOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f₁) (Function.comp.{succ u1, succ u2, succ u3} α β γ g f₂) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {s : Set.{u3} α} {f₁ : α -> β} {f₂ : α -> β} {g : β -> γ}, (Set.EqOn.{u3, u2} α β f₁ f₂ s) -> (Set.EqOn.{u3, u1} α γ (Function.comp.{succ u3, succ u2, succ u1} α β γ g f₁) (Function.comp.{succ u3, succ u2, succ u1} α β γ g f₂) s)
Case conversion may be inaccurate. Consider using '#align set.eq_on.comp_left Set.EqOn.comp_leftₓ'. -/
theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun a ha =>
  congr_arg _ <| h ha
#align set.eq_on.comp_left Set.EqOn.comp_left

/- warning: set.eq_on_range -> Set.eqOn_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> α} {g₁ : α -> β} {g₂ : α -> β}, Iff (Set.EqOn.{u1, u2} α β g₁ g₂ (Set.range.{u1, u3} α ι f)) (Eq.{max u3 (succ u2)} (ι -> β) (Function.comp.{u3, succ u1, succ u2} ι α β g₁ f) (Function.comp.{u3, succ u1, succ u2} ι α β g₂ f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} {f : ι -> α} {g₁ : α -> β} {g₂ : α -> β}, Iff (Set.EqOn.{u2, u1} α β g₁ g₂ (Set.range.{u2, u3} α ι f)) (Eq.{max (succ u1) u3} (ι -> β) (Function.comp.{u3, succ u2, succ u1} ι α β g₁ f) (Function.comp.{u3, succ u2, succ u1} ι α β g₂ f))
Case conversion may be inaccurate. Consider using '#align set.eq_on_range Set.eqOn_rangeₓ'. -/
@[simp]
theorem eqOn_range {ι : Sort _} {f : ι → α} {g₁ g₂ : α → β} :
    EqOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f :=
  forall_range_iff.trans <| funext_iff.symm
#align set.eq_on_range Set.eqOn_range

alias eq_on_range ↔ eq_on.comp_eq _

/-! ### Congruence lemmas -/


section Order

variable [Preorder α] [Preorder β]

/- warning: monotone_on.congr -> MonotoneOn.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f₁ s) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f₂ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f₁ s) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f₂ s)
Case conversion may be inaccurate. Consider using '#align monotone_on.congr MonotoneOn.congrₓ'. -/
theorem MonotoneOn.congr (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂) : MonotoneOn f₂ s :=
  by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
#align monotone_on.congr MonotoneOn.congr

/- warning: antitone_on.congr -> AntitoneOn.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f₁ s) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f₂ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f₁ s) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f₂ s)
Case conversion may be inaccurate. Consider using '#align antitone_on.congr AntitoneOn.congrₓ'. -/
theorem AntitoneOn.congr (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂) : AntitoneOn f₂ s :=
  h₁.dual_right.congr h
#align antitone_on.congr AntitoneOn.congr

/- warning: strict_mono_on.congr -> StrictMonoOn.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f₁ s) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f₂ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (StrictMonoOn.{u2, u1} α β _inst_1 _inst_2 f₁ s) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (StrictMonoOn.{u2, u1} α β _inst_1 _inst_2 f₂ s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.congr StrictMonoOn.congrₓ'. -/
theorem StrictMonoOn.congr (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂) : StrictMonoOn f₂ s :=
  by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
#align strict_mono_on.congr StrictMonoOn.congr

/- warning: strict_anti_on.congr -> StrictAntiOn.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f₁ s) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f₂ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (StrictAntiOn.{u2, u1} α β _inst_1 _inst_2 f₁ s) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (StrictAntiOn.{u2, u1} α β _inst_1 _inst_2 f₂ s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.congr StrictAntiOn.congrₓ'. -/
theorem StrictAntiOn.congr (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂) : StrictAntiOn f₂ s :=
  h₁.dual_right.congr h
#align strict_anti_on.congr StrictAntiOn.congr

/- warning: set.eq_on.congr_monotone_on -> Set.EqOn.congr_monotoneOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Iff (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f₁ s) (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f₂ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Iff (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f₁ s) (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f₂ s))
Case conversion may be inaccurate. Consider using '#align set.eq_on.congr_monotone_on Set.EqOn.congr_monotoneOnₓ'. -/
theorem EqOn.congr_monotoneOn (h : s.EqOn f₁ f₂) : MonotoneOn f₁ s ↔ MonotoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_monotone_on Set.EqOn.congr_monotoneOn

/- warning: set.eq_on.congr_antitone_on -> Set.EqOn.congr_antitoneOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Iff (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f₁ s) (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f₂ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Iff (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f₁ s) (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f₂ s))
Case conversion may be inaccurate. Consider using '#align set.eq_on.congr_antitone_on Set.EqOn.congr_antitoneOnₓ'. -/
theorem EqOn.congr_antitoneOn (h : s.EqOn f₁ f₂) : AntitoneOn f₁ s ↔ AntitoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_antitone_on Set.EqOn.congr_antitoneOn

/- warning: set.eq_on.congr_strict_mono_on -> Set.EqOn.congr_strictMonoOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Iff (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f₁ s) (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f₂ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Iff (StrictMonoOn.{u2, u1} α β _inst_1 _inst_2 f₁ s) (StrictMonoOn.{u2, u1} α β _inst_1 _inst_2 f₂ s))
Case conversion may be inaccurate. Consider using '#align set.eq_on.congr_strict_mono_on Set.EqOn.congr_strictMonoOnₓ'. -/
theorem EqOn.congr_strictMonoOn (h : s.EqOn f₁ f₂) : StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_strict_mono_on Set.EqOn.congr_strictMonoOn

/- warning: set.eq_on.congr_strict_anti_on -> Set.EqOn.congr_strictAntiOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Iff (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f₁ s) (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f₂ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Iff (StrictAntiOn.{u2, u1} α β _inst_1 _inst_2 f₁ s) (StrictAntiOn.{u2, u1} α β _inst_1 _inst_2 f₂ s))
Case conversion may be inaccurate. Consider using '#align set.eq_on.congr_strict_anti_on Set.EqOn.congr_strictAntiOnₓ'. -/
theorem EqOn.congr_strictAntiOn (h : s.EqOn f₁ f₂) : StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_strict_anti_on Set.EqOn.congr_strictAntiOn

end Order

/-! ### Mono lemmas-/


section Mono

variable [Preorder α] [Preorder β]

/- warning: monotone_on.mono -> MonotoneOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₂ : Set.{u1} α} {f : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s) -> (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₂ : Set.{u2} α} {f : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₂ s) -> (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s₂)
Case conversion may be inaccurate. Consider using '#align monotone_on.mono MonotoneOn.monoₓ'. -/
theorem MonotoneOn.mono (h : MonotoneOn f s) (h' : s₂ ⊆ s) : MonotoneOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)
#align monotone_on.mono MonotoneOn.mono

/- warning: antitone_on.mono -> AntitoneOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₂ : Set.{u1} α} {f : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s) -> (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₂ : Set.{u2} α} {f : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₂ s) -> (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s₂)
Case conversion may be inaccurate. Consider using '#align antitone_on.mono AntitoneOn.monoₓ'. -/
theorem AntitoneOn.mono (h : AntitoneOn f s) (h' : s₂ ⊆ s) : AntitoneOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)
#align antitone_on.mono AntitoneOn.mono

/- warning: strict_mono_on.mono -> StrictMonoOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₂ : Set.{u1} α} {f : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s) -> (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f s₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₂ : Set.{u2} α} {f : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (StrictMonoOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₂ s) -> (StrictMonoOn.{u2, u1} α β _inst_1 _inst_2 f s₂)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.mono StrictMonoOn.monoₓ'. -/
theorem StrictMonoOn.mono (h : StrictMonoOn f s) (h' : s₂ ⊆ s) : StrictMonoOn f s₂ :=
  fun x hx y hy => h (h' hx) (h' hy)
#align strict_mono_on.mono StrictMonoOn.mono

/- warning: strict_anti_on.mono -> StrictAntiOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₂ : Set.{u1} α} {f : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s) -> (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f s₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₂ : Set.{u2} α} {f : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (StrictAntiOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₂ s) -> (StrictAntiOn.{u2, u1} α β _inst_1 _inst_2 f s₂)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.mono StrictAntiOn.monoₓ'. -/
theorem StrictAntiOn.mono (h : StrictAntiOn f s) (h' : s₂ ⊆ s) : StrictAntiOn f s₂ :=
  fun x hx y hy => h (h' hx) (h' hy)
#align strict_anti_on.mono StrictAntiOn.mono

/- warning: monotone_on.monotone -> MonotoneOn.monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Monotone.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.preorder.{u1} α _inst_1 (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) _inst_2 (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (Monotone.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.preorder.{u2} α _inst_1 (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} α s) α β f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))))
Case conversion may be inaccurate. Consider using '#align monotone_on.monotone MonotoneOn.monotoneₓ'. -/
protected theorem MonotoneOn.monotone (h : MonotoneOn f s) : Monotone (f ∘ coe : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
#align monotone_on.monotone MonotoneOn.monotone

/- warning: antitone_on.monotone -> AntitoneOn.monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Antitone.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.preorder.{u1} α _inst_1 (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) _inst_2 (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (Antitone.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.preorder.{u2} α _inst_1 (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} α s) α β f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))))
Case conversion may be inaccurate. Consider using '#align antitone_on.monotone AntitoneOn.monotoneₓ'. -/
protected theorem AntitoneOn.monotone (h : AntitoneOn f s) : Antitone (f ∘ coe : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
#align antitone_on.monotone AntitoneOn.monotone

/- warning: strict_mono_on.strict_mono -> StrictMonoOn.strictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (StrictMono.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.preorder.{u1} α _inst_1 (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) _inst_2 (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (StrictMonoOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (StrictMono.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.preorder.{u2} α _inst_1 (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} α s) α β f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))))
Case conversion may be inaccurate. Consider using '#align strict_mono_on.strict_mono StrictMonoOn.strictMonoₓ'. -/
protected theorem StrictMonoOn.strictMono (h : StrictMonoOn f s) : StrictMono (f ∘ coe : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
#align strict_mono_on.strict_mono StrictMonoOn.strictMono

/- warning: strict_anti_on.strict_anti -> StrictAntiOn.strictAnti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (StrictAnti.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.preorder.{u1} α _inst_1 (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) _inst_2 (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β], (StrictAntiOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (StrictAnti.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.preorder.{u2} α _inst_1 (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} α s) α β f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))))
Case conversion may be inaccurate. Consider using '#align strict_anti_on.strict_anti StrictAntiOn.strictAntiₓ'. -/
protected theorem StrictAntiOn.strictAnti (h : StrictAntiOn f s) : StrictAnti (f ∘ coe : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
#align strict_anti_on.strict_anti StrictAntiOn.strictAnti

end Mono

/-! ### maps to -/


#print Set.MapsTo /-
/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f x ∈ t
#align set.maps_to Set.MapsTo
-/

#print Set.MapsTo.restrict /-
/-- Given a map `f` sending `s : set α` into `t : set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `subtype.map`. -/
def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  Subtype.map f h
#align set.maps_to.restrict Set.MapsTo.restrict
-/

/- warning: set.maps_to.coe_restrict_apply -> Set.MapsTo.val_restrict_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} (h : Set.MapsTo.{u1, u2} α β f s t) (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), Eq.{succ u2} β ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t))))) (Set.MapsTo.restrict.{u1, u2} α β f s t h x)) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} (h : Set.MapsTo.{u2, u1} α β f s t) (x : Set.Elem.{u2} α s), Eq.{succ u1} β (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t) (Set.MapsTo.restrict.{u2, u1} α β f s t h x)) (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x))
Case conversion may be inaccurate. Consider using '#align set.maps_to.coe_restrict_apply Set.MapsTo.val_restrict_applyₓ'. -/
@[simp]
theorem MapsTo.val_restrict_apply (h : MapsTo f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl
#align set.maps_to.coe_restrict_apply Set.MapsTo.val_restrict_apply

/- warning: set.cod_restrict_restrict -> Set.codRestrict_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} (h : forall (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)) t), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t)) (Set.codRestrict.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f) t h) (Set.MapsTo.restrict.{u1, u2} α β f s t (fun (x : α) (hx : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => h (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x hx)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} (h : forall (x : Set.Elem.{u2} α s), Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) t), Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> (Set.Elem.{u1} β t)) (Set.codRestrict.{u1, u2} β (Set.Elem.{u2} α s) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f) t h) (Set.MapsTo.restrict.{u2, u1} α β f s t (fun (x : α) (hx : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => h (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x hx)))
Case conversion may be inaccurate. Consider using '#align set.cod_restrict_restrict Set.codRestrict_restrictₓ'. -/
/-- Restricting the domain and then the codomain is the same as `maps_to.restrict`. -/
@[simp]
theorem codRestrict_restrict (h : ∀ x : s, f x ∈ t) :
    codRestrict (s.restrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩ :=
  rfl
#align set.cod_restrict_restrict Set.codRestrict_restrict

/- warning: set.maps_to.restrict_eq_cod_restrict -> Set.MapsTo.restrict_eq_codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} (h : Set.MapsTo.{u1, u2} α β f s t), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t)) (Set.MapsTo.restrict.{u1, u2} α β f s t h) (Set.codRestrict.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f) t (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => h (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x) (Subtype.property.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} (h : Set.MapsTo.{u2, u1} α β f s t), Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> (Set.Elem.{u1} β t)) (Set.MapsTo.restrict.{u2, u1} α β f s t h) (Set.codRestrict.{u1, u2} β (Set.Elem.{u2} α s) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f) t (fun (x : Set.Elem.{u2} α s) => h (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)))
Case conversion may be inaccurate. Consider using '#align set.maps_to.restrict_eq_cod_restrict Set.MapsTo.restrict_eq_codRestrictₓ'. -/
/-- Reverse of `set.cod_restrict_restrict`. -/
theorem MapsTo.restrict_eq_codRestrict (h : MapsTo f s t) :
    h.restrict f s t = codRestrict (s.restrict f) t fun x => h x.2 :=
  rfl
#align set.maps_to.restrict_eq_cod_restrict Set.MapsTo.restrict_eq_codRestrict

/- warning: set.maps_to.coe_restrict -> Set.MapsTo.coe_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} (h : Set.MapsTo.{u1, u2} α β f s t), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Function.comp.{succ u1, succ u2, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t)))))) (Set.MapsTo.restrict.{u1, u2} α β f s t h)) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} (h : Set.MapsTo.{u2, u1} α β f s t), Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> β) (Function.comp.{succ u2, succ u1, succ u1} (Set.Elem.{u2} α s) (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t)) β (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t)) (Set.MapsTo.restrict.{u2, u1} α β f s t h)) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)
Case conversion may be inaccurate. Consider using '#align set.maps_to.coe_restrict Set.MapsTo.coe_restrictₓ'. -/
theorem MapsTo.coe_restrict (h : Set.MapsTo f s t) : coe ∘ h.restrict f s t = s.restrict f :=
  rfl
#align set.maps_to.coe_restrict Set.MapsTo.coe_restrict

/- warning: set.maps_to.range_restrict -> Set.MapsTo.range_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u2} β) (h : Set.MapsTo.{u1, u2} α β f s t), Eq.{succ u2} (Set.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t)) (Set.range.{u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Set.MapsTo.restrict.{u1, u2} α β f s t h)) (Set.preimage.{u2, u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t)))))) (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u1} β) (h : Set.MapsTo.{u2, u1} α β f s t), Eq.{succ u1} (Set.{u1} (Set.Elem.{u1} β t)) (Set.range.{u1, succ u2} (Set.Elem.{u1} β t) (Set.Elem.{u2} α s) (Set.MapsTo.restrict.{u2, u1} α β f s t h)) (Set.preimage.{u1, u1} (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t)) β (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t)) (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.maps_to.range_restrict Set.MapsTo.range_restrictₓ'. -/
theorem MapsTo.range_restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    range (h.restrict f s t) = coe ⁻¹' (f '' s) :=
  Set.range_subtype_map f h
#align set.maps_to.range_restrict Set.MapsTo.range_restrict

/- warning: set.maps_to_iff_exists_map_subtype -> Set.mapsTo_iff_exists_map_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, Iff (Set.MapsTo.{u1, u2} α β f s t) (Exists.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t)) (fun (g : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t)) => forall (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), Eq.{succ u2} β (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t))))) (g x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, Iff (Set.MapsTo.{u2, u1} α β f s t) (Exists.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> (Set.Elem.{u1} β t)) (fun (g : (Set.Elem.{u2} α s) -> (Set.Elem.{u1} β t)) => forall (x : Set.Elem.{u2} α s), Eq.{succ u1} β (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t) (g x))))
Case conversion may be inaccurate. Consider using '#align set.maps_to_iff_exists_map_subtype Set.mapsTo_iff_exists_map_subtypeₓ'. -/
theorem mapsTo_iff_exists_map_subtype : MapsTo f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx =>
    by
    erw [hg ⟨x, hx⟩]
    apply Subtype.coe_prop⟩
#align set.maps_to_iff_exists_map_subtype Set.mapsTo_iff_exists_map_subtype

/- warning: set.maps_to' -> Set.mapsTo' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, Iff (Set.MapsTo.{u1, u2} α β f s t) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, Iff (Set.MapsTo.{u2, u1} α β f s t) (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) (Set.image.{u2, u1} α β f s) t)
Case conversion may be inaccurate. Consider using '#align set.maps_to' Set.mapsTo'ₓ'. -/
theorem mapsTo' : MapsTo f s t ↔ f '' s ⊆ t :=
  image_subset_iff.symm
#align set.maps_to' Set.mapsTo'

/- warning: set.maps_to.subset_preimage -> Set.MapsTo.subset_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.MapsTo.{u1, u2} α β f s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.MapsTo.{u2, u1} α β f s t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s (Set.preimage.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align set.maps_to.subset_preimage Set.MapsTo.subset_preimageₓ'. -/
theorem MapsTo.subset_preimage {f : α → β} {s : Set α} {t : Set β} (hf : MapsTo f s t) :
    s ⊆ f ⁻¹' t :=
  hf
#align set.maps_to.subset_preimage Set.MapsTo.subset_preimage

/- warning: set.maps_to_singleton -> Set.mapsTo_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Set.{u2} β} {f : α -> β} {x : α}, Iff (Set.MapsTo.{u1, u2} α β f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) t) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Set.{u1} β} {f : α -> β} {x : α}, Iff (Set.MapsTo.{u2, u1} α β f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x) t) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) t)
Case conversion may be inaccurate. Consider using '#align set.maps_to_singleton Set.mapsTo_singletonₓ'. -/
@[simp]
theorem mapsTo_singleton {x : α} : MapsTo f {x} t ↔ f x ∈ t :=
  singleton_subset_iff
#align set.maps_to_singleton Set.mapsTo_singleton

#print Set.mapsTo_empty /-
theorem mapsTo_empty (f : α → β) (t : Set β) : MapsTo f ∅ t :=
  empty_subset _
#align set.maps_to_empty Set.mapsTo_empty
-/

/- warning: set.maps_to.image_subset -> Set.MapsTo.image_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) (Set.image.{u2, u1} α β f s) t)
Case conversion may be inaccurate. Consider using '#align set.maps_to.image_subset Set.MapsTo.image_subsetₓ'. -/
theorem MapsTo.image_subset (h : MapsTo f s t) : f '' s ⊆ t :=
  mapsTo'.1 h
#align set.maps_to.image_subset Set.MapsTo.image_subset

/- warning: set.maps_to.congr -> Set.MapsTo.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.MapsTo.{u1, u2} α β f₁ s t) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.MapsTo.{u1, u2} α β f₂ s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.MapsTo.{u2, u1} α β f₁ s t) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Set.MapsTo.{u2, u1} α β f₂ s t)
Case conversion may be inaccurate. Consider using '#align set.maps_to.congr Set.MapsTo.congrₓ'. -/
theorem MapsTo.congr (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s) : MapsTo f₂ s t := fun x hx =>
  h hx ▸ h₁ hx
#align set.maps_to.congr Set.MapsTo.congr

/- warning: set.eq_on.comp_right -> Set.EqOn.comp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {g₁ : β -> γ} {g₂ : β -> γ}, (Set.EqOn.{u2, u3} β γ g₁ g₂ t) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.EqOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g₁ f) (Function.comp.{succ u1, succ u2, succ u3} α β γ g₂ f) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{u1} α} {t : Set.{u3} β} {f : α -> β} {g₁ : β -> γ} {g₂ : β -> γ}, (Set.EqOn.{u3, u2} β γ g₁ g₂ t) -> (Set.MapsTo.{u1, u3} α β f s t) -> (Set.EqOn.{u1, u2} α γ (Function.comp.{succ u1, succ u3, succ u2} α β γ g₁ f) (Function.comp.{succ u1, succ u3, succ u2} α β γ g₂ f) s)
Case conversion may be inaccurate. Consider using '#align set.eq_on.comp_right Set.EqOn.comp_rightₓ'. -/
theorem EqOn.comp_right (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) :=
  fun a ha => hg <| hf ha
#align set.eq_on.comp_right Set.EqOn.comp_right

/- warning: set.eq_on.maps_to_iff -> Set.EqOn.mapsTo_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Iff (Set.MapsTo.{u1, u2} α β f₁ s t) (Set.MapsTo.{u1, u2} α β f₂ s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Iff (Set.MapsTo.{u2, u1} α β f₁ s t) (Set.MapsTo.{u2, u1} α β f₂ s t))
Case conversion may be inaccurate. Consider using '#align set.eq_on.maps_to_iff Set.EqOn.mapsTo_iffₓ'. -/
theorem EqOn.mapsTo_iff (H : EqOn f₁ f₂ s) : MapsTo f₁ s t ↔ MapsTo f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.maps_to_iff Set.EqOn.mapsTo_iff

/- warning: set.maps_to.comp -> Set.MapsTo.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {p : Set.{u3} γ} {f : α -> β} {g : β -> γ}, (Set.MapsTo.{u2, u3} β γ g t p) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.MapsTo.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s p)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{u1} α} {t : Set.{u3} β} {p : Set.{u2} γ} {f : α -> β} {g : β -> γ}, (Set.MapsTo.{u3, u2} β γ g t p) -> (Set.MapsTo.{u1, u3} α β f s t) -> (Set.MapsTo.{u1, u2} α γ (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) s p)
Case conversion may be inaccurate. Consider using '#align set.maps_to.comp Set.MapsTo.compₓ'. -/
theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun x h =>
  h₁ (h₂ h)
#align set.maps_to.comp Set.MapsTo.comp

#print Set.mapsTo_id /-
theorem mapsTo_id (s : Set α) : MapsTo id s s := fun x => id
#align set.maps_to_id Set.mapsTo_id
-/

#print Set.MapsTo.iterate /-
theorem MapsTo.iterate {f : α → α} {s : Set α} (h : MapsTo f s s) : ∀ n, MapsTo (f^[n]) s s
  | 0 => fun _ => id
  | n + 1 => (maps_to.iterate n).comp h
#align set.maps_to.iterate Set.MapsTo.iterate
-/

#print Set.MapsTo.iterate_restrict /-
theorem MapsTo.iterate_restrict {f : α → α} {s : Set α} (h : MapsTo f s s) (n : ℕ) :
    h.restrict f s s^[n] = (h.iterate n).restrict _ _ _ :=
  by
  funext x
  rw [Subtype.ext_iff, maps_to.coe_restrict_apply]
  induction' n with n ihn generalizing x
  · rfl
  · simp [Nat.iterate, ihn]
#align set.maps_to.iterate_restrict Set.MapsTo.iterate_restrict
-/

/- warning: set.maps_to.mono -> Set.MapsTo.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s₁ t₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s₁) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t₁ t₂) -> (Set.MapsTo.{u1, u2} α β f s₂ t₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s₁ t₁) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₂ s₁) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t₁ t₂) -> (Set.MapsTo.{u2, u1} α β f s₂ t₂)
Case conversion may be inaccurate. Consider using '#align set.maps_to.mono Set.MapsTo.monoₓ'. -/
theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) : MapsTo f s₂ t₂ :=
  fun x hx => ht (hf <| hs hx)
#align set.maps_to.mono Set.MapsTo.mono

/- warning: set.maps_to.mono_left -> Set.MapsTo.mono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s₁ t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s₁) -> (Set.MapsTo.{u1, u2} α β f s₂ t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s₁ t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₂ s₁) -> (Set.MapsTo.{u2, u1} α β f s₂ t)
Case conversion may be inaccurate. Consider using '#align set.maps_to.mono_left Set.MapsTo.mono_leftₓ'. -/
theorem MapsTo.mono_left (hf : MapsTo f s₁ t) (hs : s₂ ⊆ s₁) : MapsTo f s₂ t := fun x hx =>
  hf (hs hx)
#align set.maps_to.mono_left Set.MapsTo.mono_left

/- warning: set.maps_to.mono_right -> Set.MapsTo.mono_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t₁) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t₁ t₂) -> (Set.MapsTo.{u1, u2} α β f s t₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t₁) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t₁ t₂) -> (Set.MapsTo.{u2, u1} α β f s t₂)
Case conversion may be inaccurate. Consider using '#align set.maps_to.mono_right Set.MapsTo.mono_rightₓ'. -/
theorem MapsTo.mono_right (hf : MapsTo f s t₁) (ht : t₁ ⊆ t₂) : MapsTo f s t₂ := fun x hx =>
  ht (hf hx)
#align set.maps_to.mono_right Set.MapsTo.mono_right

/- warning: set.maps_to.union_union -> Set.MapsTo.union_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s₁ t₁) -> (Set.MapsTo.{u1, u2} α β f s₂ t₂) -> (Set.MapsTo.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s₁ t₁) -> (Set.MapsTo.{u2, u1} α β f s₂ t₂) -> (Set.MapsTo.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.maps_to.union_union Set.MapsTo.union_unionₓ'. -/
theorem MapsTo.union_union (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∪ s₂) (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr <| h₂ hx
#align set.maps_to.union_union Set.MapsTo.union_union

/- warning: set.maps_to.union -> Set.MapsTo.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s₁ t) -> (Set.MapsTo.{u1, u2} α β f s₂ t) -> (Set.MapsTo.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s₁ t) -> (Set.MapsTo.{u2, u1} α β f s₂ t) -> (Set.MapsTo.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂) t)
Case conversion may be inaccurate. Consider using '#align set.maps_to.union Set.MapsTo.unionₓ'. -/
theorem MapsTo.union (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t) : MapsTo f (s₁ ∪ s₂) t :=
  union_self t ▸ h₁.union_union h₂
#align set.maps_to.union Set.MapsTo.union

/- warning: set.maps_to_union -> Set.mapsTo_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, Iff (Set.MapsTo.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) t) (And (Set.MapsTo.{u1, u2} α β f s₁ t) (Set.MapsTo.{u1, u2} α β f s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, Iff (Set.MapsTo.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂) t) (And (Set.MapsTo.{u2, u1} α β f s₁ t) (Set.MapsTo.{u2, u1} α β f s₂ t))
Case conversion may be inaccurate. Consider using '#align set.maps_to_union Set.mapsTo_unionₓ'. -/
@[simp]
theorem mapsTo_union : MapsTo f (s₁ ∪ s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t :=
  ⟨fun h =>
    ⟨h.mono (subset_union_left s₁ s₂) (Subset.refl t),
      h.mono (subset_union_right s₁ s₂) (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩
#align set.maps_to_union Set.mapsTo_union

/- warning: set.maps_to.inter -> Set.MapsTo.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t₁) -> (Set.MapsTo.{u1, u2} α β f s t₂) -> (Set.MapsTo.{u1, u2} α β f s (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t₁) -> (Set.MapsTo.{u2, u1} α β f s t₂) -> (Set.MapsTo.{u2, u1} α β f s (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.maps_to.inter Set.MapsTo.interₓ'. -/
theorem MapsTo.inter (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂) : MapsTo f s (t₁ ∩ t₂) := fun x hx =>
  ⟨h₁ hx, h₂ hx⟩
#align set.maps_to.inter Set.MapsTo.inter

/- warning: set.maps_to.inter_inter -> Set.MapsTo.inter_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s₁ t₁) -> (Set.MapsTo.{u1, u2} α β f s₂ t₂) -> (Set.MapsTo.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s₁ t₁) -> (Set.MapsTo.{u2, u1} α β f s₂ t₂) -> (Set.MapsTo.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.maps_to.inter_inter Set.MapsTo.inter_interₓ'. -/
theorem MapsTo.inter_inter (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun x hx => ⟨h₁ hx.1, h₂ hx.2⟩
#align set.maps_to.inter_inter Set.MapsTo.inter_inter

/- warning: set.maps_to_inter -> Set.mapsTo_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, Iff (Set.MapsTo.{u1, u2} α β f s (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂)) (And (Set.MapsTo.{u1, u2} α β f s t₁) (Set.MapsTo.{u1, u2} α β f s t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, Iff (Set.MapsTo.{u2, u1} α β f s (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂)) (And (Set.MapsTo.{u2, u1} α β f s t₁) (Set.MapsTo.{u2, u1} α β f s t₂))
Case conversion may be inaccurate. Consider using '#align set.maps_to_inter Set.mapsTo_interₓ'. -/
@[simp]
theorem mapsTo_inter : MapsTo f s (t₁ ∩ t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂ :=
  ⟨fun h =>
    ⟨h.mono (Subset.refl s) (inter_subset_left t₁ t₂),
      h.mono (Subset.refl s) (inter_subset_right t₁ t₂)⟩,
    fun h => h.1.inter h.2⟩
#align set.maps_to_inter Set.mapsTo_inter

/- warning: set.maps_to_univ -> Set.mapsTo_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Set.MapsTo.{u1, u2} α β f s (Set.univ.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Set.MapsTo.{u2, u1} α β f s (Set.univ.{u1} β)
Case conversion may be inaccurate. Consider using '#align set.maps_to_univ Set.mapsTo_univₓ'. -/
theorem mapsTo_univ (f : α → β) (s : Set α) : MapsTo f s univ := fun x h => trivial
#align set.maps_to_univ Set.mapsTo_univ

/- warning: set.maps_to_image -> Set.mapsTo_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Set.MapsTo.{u1, u2} α β f s (Set.image.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Set.MapsTo.{u2, u1} α β f s (Set.image.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.maps_to_image Set.mapsTo_imageₓ'. -/
theorem mapsTo_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) := by rw [maps_to']
#align set.maps_to_image Set.mapsTo_image

#print Set.mapsTo_preimage /-
theorem mapsTo_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t :=
  Subset.refl _
#align set.maps_to_preimage Set.mapsTo_preimage
-/

/- warning: set.maps_to_range -> Set.mapsTo_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Set.MapsTo.{u1, u2} α β f s (Set.range.{u2, succ u1} β α f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Set.MapsTo.{u2, u1} α β f s (Set.range.{u1, succ u2} β α f)
Case conversion may be inaccurate. Consider using '#align set.maps_to_range Set.mapsTo_rangeₓ'. -/
theorem mapsTo_range (f : α → β) (s : Set α) : MapsTo f s (range f) :=
  (mapsTo_image f s).mono (Subset.refl s) (image_subset_range _ _)
#align set.maps_to_range Set.mapsTo_range

#print Set.maps_image_to /-
@[simp]
theorem maps_image_to (f : α → β) (g : γ → α) (s : Set γ) (t : Set β) :
    MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h d ⟨c, hc⟩ => hc.2 ▸ h hc.1⟩
#align set.maps_image_to Set.maps_image_to
-/

#print Set.maps_univ_to /-
@[simp]
theorem maps_univ_to (f : α → β) (s : Set β) : MapsTo f univ s ↔ ∀ a, f a ∈ s :=
  ⟨fun h a => h (mem_univ _), fun h x _ => h x⟩
#align set.maps_univ_to Set.maps_univ_to
-/

/- warning: set.maps_range_to -> Set.maps_range_to is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : γ -> α) (s : Set.{u2} β), Iff (Set.MapsTo.{u1, u2} α β f (Set.range.{u1, succ u3} α γ g) s) (Set.MapsTo.{u3, u2} γ β (Function.comp.{succ u3, succ u1, succ u2} γ α β f g) (Set.univ.{u3} γ) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} (f : α -> β) (g : γ -> α) (s : Set.{u3} β), Iff (Set.MapsTo.{u2, u3} α β f (Set.range.{u2, succ u1} α γ g) s) (Set.MapsTo.{u1, u3} γ β (Function.comp.{succ u1, succ u2, succ u3} γ α β f g) (Set.univ.{u1} γ) s)
Case conversion may be inaccurate. Consider using '#align set.maps_range_to Set.maps_range_toₓ'. -/
@[simp]
theorem maps_range_to (f : α → β) (g : γ → α) (s : Set β) :
    MapsTo f (range g) s ↔ MapsTo (f ∘ g) univ s := by rw [← image_univ, maps_image_to]
#align set.maps_range_to Set.maps_range_to

/- warning: set.surjective_maps_to_image_restrict -> Set.surjective_mapsTo_image_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Function.Surjective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β f s)) (Set.MapsTo.restrict.{u1, u2} α β f s (Set.image.{u1, u2} α β f s) (Set.mapsTo_image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Function.Surjective.{succ u2, succ u1} (Set.Elem.{u2} α s) (Set.Elem.{u1} β (Set.image.{u2, u1} α β f s)) (Set.MapsTo.restrict.{u2, u1} α β f s (Set.image.{u2, u1} α β f s) (Set.mapsTo_image.{u1, u2} α β f s))
Case conversion may be inaccurate. Consider using '#align set.surjective_maps_to_image_restrict Set.surjective_mapsTo_image_restrictₓ'. -/
theorem surjective_mapsTo_image_restrict (f : α → β) (s : Set α) :
    Surjective ((mapsTo_image f s).restrict f s (f '' s)) := fun ⟨y, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩
#align set.surjective_maps_to_image_restrict Set.surjective_mapsTo_image_restrict

/- warning: set.maps_to.mem_iff -> Set.MapsTo.mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t) -> (Set.MapsTo.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t)) -> (forall {x : α}, Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t) -> (Set.MapsTo.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) t)) -> (forall {x : α}, Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) t) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))
Case conversion may be inaccurate. Consider using '#align set.maps_to.mem_iff Set.MapsTo.mem_iffₓ'. -/
theorem MapsTo.mem_iff (h : MapsTo f s t) (hc : MapsTo f (sᶜ) (tᶜ)) {x} : f x ∈ t ↔ x ∈ s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩
#align set.maps_to.mem_iff Set.MapsTo.mem_iff

/-! ### Restriction onto preimage -/


section

variable (t f)

#print Set.restrictPreimage /-
/-- The restriction of a function onto the preimage of a set. -/
@[simps]
def restrictPreimage : f ⁻¹' t → t :=
  (Set.mapsTo_preimage f t).restrict _ _ _
#align set.restrict_preimage Set.restrictPreimage
-/

#print Set.range_restrictPreimage /-
theorem range_restrictPreimage : range (t.restrictPreimage f) = coe ⁻¹' range f :=
  by
  delta Set.restrictPreimage
  rw [maps_to.range_restrict, Set.image_preimage_eq_inter_range, Set.preimage_inter,
    Subtype.coe_preimage_self, Set.univ_inter]
#align set.range_restrict_preimage Set.range_restrictPreimage
-/

variable {f} {U : ι → Set β}

/- warning: set.restrict_preimage_injective -> Set.restrictPreimage_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Set.{u2} β) {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Function.Injective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f t)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (Set.restrictPreimage.{u1, u2} α β t f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : Set.{u1} β) {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Function.Injective.{succ u2, succ u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f t)) (Set.Elem.{u1} β t) (Set.restrictPreimage.{u2, u1} α β t f))
Case conversion may be inaccurate. Consider using '#align set.restrict_preimage_injective Set.restrictPreimage_injectiveₓ'. -/
theorem restrictPreimage_injective (hf : Injective f) : Injective (t.restrictPreimage f) :=
  fun x y e => Subtype.mk.injArrow e fun e => Subtype.coe_injective (hf e)
#align set.restrict_preimage_injective Set.restrictPreimage_injective

/- warning: set.restrict_preimage_surjective -> Set.restrictPreimage_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Set.{u2} β) {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (Function.Surjective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f t)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (Set.restrictPreimage.{u1, u2} α β t f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : Set.{u1} β) {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (Function.Surjective.{succ u2, succ u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f t)) (Set.Elem.{u1} β t) (Set.restrictPreimage.{u2, u1} α β t f))
Case conversion may be inaccurate. Consider using '#align set.restrict_preimage_surjective Set.restrictPreimage_surjectiveₓ'. -/
theorem restrictPreimage_surjective (hf : Surjective f) : Surjective (t.restrictPreimage f) :=
  fun x =>
  ⟨⟨_, show f (hf x).some ∈ t from (hf x).some_spec.symm ▸ x.2⟩, Subtype.ext (hf x).some_spec⟩
#align set.restrict_preimage_surjective Set.restrictPreimage_surjective

/- warning: set.restrict_preimage_bijective -> Set.restrictPreimage_bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Set.{u2} β) {f : α -> β}, (Function.Bijective.{succ u1, succ u2} α β f) -> (Function.Bijective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f t)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (Set.restrictPreimage.{u1, u2} α β t f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : Set.{u1} β) {f : α -> β}, (Function.Bijective.{succ u2, succ u1} α β f) -> (Function.Bijective.{succ u2, succ u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f t)) (Set.Elem.{u1} β t) (Set.restrictPreimage.{u2, u1} α β t f))
Case conversion may be inaccurate. Consider using '#align set.restrict_preimage_bijective Set.restrictPreimage_bijectiveₓ'. -/
theorem restrictPreimage_bijective (hf : Bijective f) : Bijective (t.restrictPreimage f) :=
  ⟨t.restrict_preimage_injective hf.1, t.restrict_preimage_surjective hf.2⟩
#align set.restrict_preimage_bijective Set.restrictPreimage_bijective

alias Set.restrictPreimage_injective ← _root_.function.injective.restrict_preimage

alias Set.restrictPreimage_surjective ← _root_.function.surjective.restrict_preimage

alias Set.restrictPreimage_bijective ← _root_.function.bijective.restrict_preimage

end

/-! ### Injectivity on a set -/


#print Set.InjOn /-
/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂
#align set.inj_on Set.InjOn
-/

/- warning: set.subsingleton.inj_on -> Set.Subsingleton.injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (forall (f : α -> β), Set.InjOn.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α}, (Set.Subsingleton.{u2} α s) -> (forall (f : α -> β), Set.InjOn.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.subsingleton.inj_on Set.Subsingleton.injOnₓ'. -/
theorem Subsingleton.injOn (hs : s.Subsingleton) (f : α → β) : InjOn f s := fun x hx y hy h =>
  hs hx hy
#align set.subsingleton.inj_on Set.Subsingleton.injOn

/- warning: set.inj_on_empty -> Set.injOn_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Set.InjOn.{u1, u2} α β f (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Set.InjOn.{u2, u1} α β f (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))
Case conversion may be inaccurate. Consider using '#align set.inj_on_empty Set.injOn_emptyₓ'. -/
@[simp]
theorem injOn_empty (f : α → β) : InjOn f ∅ :=
  subsingleton_empty.InjOn f
#align set.inj_on_empty Set.injOn_empty

/- warning: set.inj_on_singleton -> Set.injOn_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (a : α), Set.InjOn.{u1, u2} α β f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (a : α), Set.InjOn.{u2, u1} α β f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a)
Case conversion may be inaccurate. Consider using '#align set.inj_on_singleton Set.injOn_singletonₓ'. -/
@[simp]
theorem injOn_singleton (f : α → β) (a : α) : InjOn f {a} :=
  subsingleton_singleton.InjOn f
#align set.inj_on_singleton Set.injOn_singleton

/- warning: set.inj_on.eq_iff -> Set.InjOn.eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {x : α} {y : α}, (Set.InjOn.{u1, u2} α β f s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Iff (Eq.{succ u2} β (f x) (f y)) (Eq.{succ u1} α x y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {x : α} {y : α}, (Set.InjOn.{u2, u1} α β f s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Iff (Eq.{succ u1} β (f x) (f y)) (Eq.{succ u2} α x y))
Case conversion may be inaccurate. Consider using '#align set.inj_on.eq_iff Set.InjOn.eq_iffₓ'. -/
theorem InjOn.eq_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩
#align set.inj_on.eq_iff Set.InjOn.eq_iff

/- warning: set.inj_on.ne_iff -> Set.InjOn.ne_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {x : α} {y : α}, (Set.InjOn.{u1, u2} α β f s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Iff (Ne.{succ u2} β (f x) (f y)) (Ne.{succ u1} α x y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {x : α} {y : α}, (Set.InjOn.{u2, u1} α β f s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Iff (Ne.{succ u1} β (f x) (f y)) (Ne.{succ u2} α x y))
Case conversion may be inaccurate. Consider using '#align set.inj_on.ne_iff Set.InjOn.ne_iffₓ'. -/
theorem InjOn.ne_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x ≠ f y ↔ x ≠ y :=
  (h.eq_iff hx hy).Not
#align set.inj_on.ne_iff Set.InjOn.ne_iff

alias inj_on.ne_iff ↔ _ inj_on.ne

/- warning: set.inj_on.congr -> Set.InjOn.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.InjOn.{u1, u2} α β f₁ s) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.InjOn.{u1, u2} α β f₂ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.InjOn.{u2, u1} α β f₁ s) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Set.InjOn.{u2, u1} α β f₂ s)
Case conversion may be inaccurate. Consider using '#align set.inj_on.congr Set.InjOn.congrₓ'. -/
theorem InjOn.congr (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s) : InjOn f₂ s := fun x hx y hy =>
  h hx ▸ h hy ▸ h₁ hx hy
#align set.inj_on.congr Set.InjOn.congr

/- warning: set.eq_on.inj_on_iff -> Set.EqOn.injOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Iff (Set.InjOn.{u1, u2} α β f₁ s) (Set.InjOn.{u1, u2} α β f₂ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Iff (Set.InjOn.{u2, u1} α β f₁ s) (Set.InjOn.{u2, u1} α β f₂ s))
Case conversion may be inaccurate. Consider using '#align set.eq_on.inj_on_iff Set.EqOn.injOn_iffₓ'. -/
theorem EqOn.injOn_iff (H : EqOn f₁ f₂ s) : InjOn f₁ s ↔ InjOn f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.inj_on_iff Set.EqOn.injOn_iff

/- warning: set.inj_on.mono -> Set.InjOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {f : α -> β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (Set.InjOn.{u1, u2} α β f s₂) -> (Set.InjOn.{u1, u2} α β f s₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {f : α -> β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s₂) -> (Set.InjOn.{u2, u1} α β f s₂) -> (Set.InjOn.{u2, u1} α β f s₁)
Case conversion may be inaccurate. Consider using '#align set.inj_on.mono Set.InjOn.monoₓ'. -/
theorem InjOn.mono (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun x hx y hy H =>
  ht (h hx) (h hy) H
#align set.inj_on.mono Set.InjOn.mono

/- warning: set.inj_on_union -> Set.injOn_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {f : α -> β}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s₁ s₂) -> (Iff (Set.InjOn.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (And (Set.InjOn.{u1, u2} α β f s₁) (And (Set.InjOn.{u1, u2} α β f s₂) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s₁) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s₂) -> (Ne.{succ u2} β (f x) (f y)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {f : α -> β}, (Disjoint.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) s₁ s₂) -> (Iff (Set.InjOn.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂)) (And (Set.InjOn.{u2, u1} α β f s₁) (And (Set.InjOn.{u2, u1} α β f s₂) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s₁) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s₂) -> (Ne.{succ u1} β (f x) (f y)))))))
Case conversion may be inaccurate. Consider using '#align set.inj_on_union Set.injOn_unionₓ'. -/
theorem injOn_union (h : Disjoint s₁ s₂) :
    InjOn f (s₁ ∪ s₂) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ ∀ x ∈ s₁, ∀ y ∈ s₂, f x ≠ f y :=
  by
  refine' ⟨fun H => ⟨H.mono <| subset_union_left _ _, H.mono <| subset_union_right _ _, _⟩, _⟩
  · intro x hx y hy hxy
    obtain rfl : x = y
    exact H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts[h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]
#align set.inj_on_union Set.injOn_union

/- warning: set.inj_on_insert -> Set.injOn_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Iff (Set.InjOn.{u1, u2} α β f (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (And (Set.InjOn.{u1, u2} α β f s) (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f a) (Set.image.{u1, u2} α β f s)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {a : α}, (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (Iff (Set.InjOn.{u2, u1} α β f (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) (And (Set.InjOn.{u2, u1} α β f s) (Not (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f a) (Set.image.{u2, u1} α β f s)))))
Case conversion may be inaccurate. Consider using '#align set.inj_on_insert Set.injOn_insertₓ'. -/
theorem injOn_insert {f : α → β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s :=
  by
  have : Disjoint s {a} := disjoint_iff_inf_le.mpr fun x ⟨hxs, (hxa : x = a)⟩ => has (hxa ▸ hxs)
  rw [← union_singleton, inj_on_union this]
  simp
#align set.inj_on_insert Set.injOn_insert

/- warning: set.injective_iff_inj_on_univ -> Set.injective_iff_injOn_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Iff (Function.Injective.{succ u1, succ u2} α β f) (Set.InjOn.{u1, u2} α β f (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, Iff (Function.Injective.{succ u2, succ u1} α β f) (Set.InjOn.{u2, u1} α β f (Set.univ.{u2} α))
Case conversion may be inaccurate. Consider using '#align set.injective_iff_inj_on_univ Set.injective_iff_injOn_univₓ'. -/
theorem injective_iff_injOn_univ : Injective f ↔ InjOn f univ :=
  ⟨fun h x hx y hy hxy => h hxy, fun h _ _ heq => h trivial trivial HEq⟩
#align set.injective_iff_inj_on_univ Set.injective_iff_injOn_univ

/- warning: set.inj_on_of_injective -> Set.injOn_of_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u1} α), Set.InjOn.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u2} α), Set.InjOn.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.inj_on_of_injective Set.injOn_of_injectiveₓ'. -/
theorem injOn_of_injective (h : Injective f) (s : Set α) : InjOn f s := fun x hx y hy hxy => h hxy
#align set.inj_on_of_injective Set.injOn_of_injective

alias inj_on_of_injective ← _root_.function.injective.inj_on

/- warning: set.inj_on.comp -> Set.InjOn.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {g : β -> γ}, (Set.InjOn.{u2, u3} β γ g t) -> (Set.InjOn.{u1, u2} α β f s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.InjOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{u1} α} {t : Set.{u3} β} {f : α -> β} {g : β -> γ}, (Set.InjOn.{u3, u2} β γ g t) -> (Set.InjOn.{u1, u3} α β f s) -> (Set.MapsTo.{u1, u3} α β f s t) -> (Set.InjOn.{u1, u2} α γ (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align set.inj_on.comp Set.InjOn.compₓ'. -/
theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
  fun x hx y hy heq => hf hx hy <| hg (h hx) (h hy) HEq
#align set.inj_on.comp Set.InjOn.comp

/- warning: function.injective.inj_on_range -> Function.Injective.injOn_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : β -> γ}, (Function.Injective.{succ u1, succ u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) -> (Set.InjOn.{u2, u3} β γ g (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {f : α -> β} {g : β -> γ}, (Function.Injective.{succ u3, succ u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f)) -> (Set.InjOn.{u1, u2} β γ g (Set.range.{u1, succ u3} β α f))
Case conversion may be inaccurate. Consider using '#align function.injective.inj_on_range Function.Injective.injOn_rangeₓ'. -/
theorem Function.Injective.injOn_range (h : Injective (g ∘ f)) : InjOn g (range f) :=
  by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H
  exact congr_arg f (h H)
#align function.injective.inj_on_range Function.Injective.injOn_range

/- warning: set.inj_on_iff_injective -> Set.injOn_iff_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β}, Iff (Set.InjOn.{u1, u2} α β f s) (Function.Injective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β}, Iff (Set.InjOn.{u2, u1} α β f s) (Function.Injective.{succ u2, succ u1} (Set.Elem.{u2} α s) β (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f))
Case conversion may be inaccurate. Consider using '#align set.inj_on_iff_injective Set.injOn_iff_injectiveₓ'. -/
theorem injOn_iff_injective : InjOn f s ↔ Injective (s.restrict f) :=
  ⟨fun H a b h => Subtype.eq <| H a.2 b.2 h, fun H a as b bs h =>
    congr_arg Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩
#align set.inj_on_iff_injective Set.injOn_iff_injective

alias inj_on_iff_injective ↔ inj_on.injective _

/- warning: set.maps_to.restrict_inj -> Set.MapsTo.restrict_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} (h : Set.MapsTo.{u1, u2} α β f s t), Iff (Function.Injective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (Set.MapsTo.restrict.{u1, u2} α β f s t h)) (Set.InjOn.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} (h : Set.MapsTo.{u2, u1} α β f s t), Iff (Function.Injective.{succ u2, succ u1} (Set.Elem.{u2} α s) (Set.Elem.{u1} β t) (Set.MapsTo.restrict.{u2, u1} α β f s t h)) (Set.InjOn.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.maps_to.restrict_inj Set.MapsTo.restrict_injₓ'. -/
theorem MapsTo.restrict_inj (h : MapsTo f s t) : Injective (h.restrict f s t) ↔ InjOn f s := by
  rw [h.restrict_eq_cod_restrict, injective_cod_restrict, inj_on_iff_injective]
#align set.maps_to.restrict_inj Set.MapsTo.restrict_inj

#print Set.exists_injOn_iff_injective /-
theorem exists_injOn_iff_injective [Nonempty β] :
    (∃ f : α → β, InjOn f s) ↔ ∃ f : s → β, Injective f :=
  ⟨fun ⟨f, hf⟩ => ⟨_, hf.Injective⟩, fun ⟨f, hf⟩ =>
    by
    lift f to α → β using trivial
    exact ⟨f, inj_on_iff_injective.2 hf⟩⟩
#align set.exists_inj_on_iff_injective Set.exists_injOn_iff_injective
-/

#print Set.injOn_preimage /-
theorem injOn_preimage {B : Set (Set β)} (hB : B ⊆ 𝒫 range f) : InjOn (preimage f) B :=
  fun s hs t ht hst => (preimage_eq_preimage' (hB hs) (hB ht)).1 hst
#align set.inj_on_preimage Set.injOn_preimage
-/

/- warning: set.inj_on.mem_of_mem_image -> Set.InjOn.mem_of_mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {f : α -> β} {x : α}, (Set.InjOn.{u1, u2} α β f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) (Set.image.{u1, u2} α β f s₁)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {f : α -> β} {x : α}, (Set.InjOn.{u2, u1} α β f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) (Set.image.{u2, u1} α β f s₁)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s₁)
Case conversion may be inaccurate. Consider using '#align set.inj_on.mem_of_mem_image Set.InjOn.mem_of_mem_imageₓ'. -/
theorem InjOn.mem_of_mem_image {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) :
    x ∈ s₁ :=
  let ⟨x', h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'
#align set.inj_on.mem_of_mem_image Set.InjOn.mem_of_mem_image

/- warning: set.inj_on.mem_image_iff -> Set.InjOn.mem_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {f : α -> β} {x : α}, (Set.InjOn.{u1, u2} α β f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) (Set.image.{u1, u2} α β f s₁)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s₁))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {f : α -> β} {x : α}, (Set.InjOn.{u2, u1} α β f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) (Set.image.{u2, u1} α β f s₁)) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s₁))
Case conversion may be inaccurate. Consider using '#align set.inj_on.mem_image_iff Set.InjOn.mem_image_iffₓ'. -/
theorem InjOn.mem_image_iff {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (hx : x ∈ s) :
    f x ∈ f '' s₁ ↔ x ∈ s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩
#align set.inj_on.mem_image_iff Set.InjOn.mem_image_iff

/- warning: set.inj_on.preimage_image_inter -> Set.InjOn.preimage_image_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {f : α -> β}, (Set.InjOn.{u1, u2} α β f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, u2} α β f (Set.image.{u1, u2} α β f s₁)) s) s₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {f : α -> β}, (Set.InjOn.{u2, u1} α β f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) (Set.preimage.{u2, u1} α β f (Set.image.{u2, u1} α β f s₁)) s) s₁)
Case conversion may be inaccurate. Consider using '#align set.inj_on.preimage_image_inter Set.InjOn.preimage_image_interₓ'. -/
theorem InjOn.preimage_image_inter (hf : InjOn f s) (hs : s₁ ⊆ s) : f ⁻¹' (f '' s₁) ∩ s = s₁ :=
  ext fun x => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩
#align set.inj_on.preimage_image_inter Set.InjOn.preimage_image_inter

/- warning: set.eq_on.cancel_left -> Set.EqOn.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β} {g : β -> γ}, (Set.EqOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f₁) (Function.comp.{succ u1, succ u2, succ u3} α β γ g f₂) s) -> (Set.InjOn.{u2, u3} β γ g t) -> (Set.MapsTo.{u1, u2} α β f₁ s t) -> (Set.MapsTo.{u1, u2} α β f₂ s t) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {s : Set.{u3} α} {t : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β} {g : β -> γ}, (Set.EqOn.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f₁) (Function.comp.{succ u3, succ u1, succ u2} α β γ g f₂) s) -> (Set.InjOn.{u1, u2} β γ g t) -> (Set.MapsTo.{u3, u1} α β f₁ s t) -> (Set.MapsTo.{u3, u1} α β f₂ s t) -> (Set.EqOn.{u3, u1} α β f₁ f₂ s)
Case conversion may be inaccurate. Consider using '#align set.eq_on.cancel_left Set.EqOn.cancel_leftₓ'. -/
theorem EqOn.cancel_left (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
    (hf₂ : s.MapsTo f₂ t) : s.EqOn f₁ f₂ := fun a ha => hg (hf₁ ha) (hf₂ ha) (h ha)
#align set.eq_on.cancel_left Set.EqOn.cancel_left

/- warning: set.inj_on.cancel_left -> Set.InjOn.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β} {g : β -> γ}, (Set.InjOn.{u2, u3} β γ g t) -> (Set.MapsTo.{u1, u2} α β f₁ s t) -> (Set.MapsTo.{u1, u2} α β f₂ s t) -> (Iff (Set.EqOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f₁) (Function.comp.{succ u1, succ u2, succ u3} α β γ g f₂) s) (Set.EqOn.{u1, u2} α β f₁ f₂ s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{u1} α} {t : Set.{u3} β} {f₁ : α -> β} {f₂ : α -> β} {g : β -> γ}, (Set.InjOn.{u3, u2} β γ g t) -> (Set.MapsTo.{u1, u3} α β f₁ s t) -> (Set.MapsTo.{u1, u3} α β f₂ s t) -> (Iff (Set.EqOn.{u1, u2} α γ (Function.comp.{succ u1, succ u3, succ u2} α β γ g f₁) (Function.comp.{succ u1, succ u3, succ u2} α β γ g f₂) s) (Set.EqOn.{u1, u3} α β f₁ f₂ s))
Case conversion may be inaccurate. Consider using '#align set.inj_on.cancel_left Set.InjOn.cancel_leftₓ'. -/
theorem InjOn.cancel_left (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩
#align set.inj_on.cancel_left Set.InjOn.cancel_left

/- warning: set.inj_on.image_inter -> Set.InjOn.image_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Set.InjOn.{u1, u2} α β f u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t u) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α} {u : Set.{u2} α}, (Set.InjOn.{u2, u1} α β f u) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s u) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) t u) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s t)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align set.inj_on.image_inter Set.InjOn.image_interₓ'. -/
theorem InjOn.image_inter {s t u : Set α} (hf : u.InjOn f) (hs : s ⊆ u) (ht : t ⊆ u) :
    f '' (s ∩ t) = f '' s ∩ f '' t :=
  by
  apply subset.antisymm (image_inter_subset _ _ _)
  rintro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩
#align set.inj_on.image_inter Set.InjOn.image_inter

/- warning: disjoint.image -> Disjoint.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α} {f : α -> β}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Set.InjOn.{u1, u2} α β f u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t u) -> (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u2} α} {u : Set.{u2} α} {f : α -> β}, (Disjoint.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) s t) -> (Set.InjOn.{u2, u1} α β f u) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s u) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) t u) -> (Disjoint.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align disjoint.image Disjoint.imageₓ'. -/
theorem Disjoint.image {s t u : Set α} {f : α → β} (h : Disjoint s t) (hf : InjOn f u) (hs : s ⊆ u)
    (ht : t ⊆ u) : Disjoint (f '' s) (f '' t) :=
  by
  rw [disjoint_iff_inter_eq_empty] at h⊢
  rw [← hf.image_inter hs ht, h, image_empty]
#align disjoint.image Disjoint.image

/-! ### Surjectivity on a set -/


#print Set.SurjOn /-
/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  t ⊆ f '' s
#align set.surj_on Set.SurjOn
-/

/- warning: set.surj_on.subset_range -> Set.SurjOn.subset_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.SurjOn.{u1, u2} α β f s t) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.SurjOn.{u2, u1} α β f s t) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align set.surj_on.subset_range Set.SurjOn.subset_rangeₓ'. -/
theorem SurjOn.subset_range (h : SurjOn f s t) : t ⊆ range f :=
  Subset.trans h <| image_subset_range f s
#align set.surj_on.subset_range Set.SurjOn.subset_range

/- warning: set.surj_on_iff_exists_map_subtype -> Set.surjOn_iff_exists_map_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, Iff (Set.SurjOn.{u1, u2} α β f s t) (Exists.{succ u2} (Set.{u2} β) (fun (t' : Set.{u2} β) => Exists.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t')) (fun (g : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t')) => And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t t') (And (Function.Surjective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t') g) (forall (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), Eq.{succ u2} β (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t') β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t') β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t') β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t') β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t'))))) (g x)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, Iff (Set.SurjOn.{u2, u1} α β f s t) (Exists.{succ u1} (Set.{u1} β) (fun (t' : Set.{u1} β) => Exists.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> (Set.Elem.{u1} β t')) (fun (g : (Set.Elem.{u2} α s) -> (Set.Elem.{u1} β t')) => And (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t t') (And (Function.Surjective.{succ u2, succ u1} (Set.Elem.{u2} α s) (Set.Elem.{u1} β t') g) (forall (x : Set.Elem.{u2} α s), Eq.{succ u1} β (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t') (g x)))))))
Case conversion may be inaccurate. Consider using '#align set.surj_on_iff_exists_map_subtype Set.surjOn_iff_exists_map_subtypeₓ'. -/
theorem surjOn_iff_exists_map_subtype :
    SurjOn f s t ↔ ∃ (t' : Set β)(g : s → t'), t ⊆ t' ∧ Surjective g ∧ ∀ x : s, f x = g x :=
  ⟨fun h =>
    ⟨_, (mapsTo_image f s).restrict f s _, h, surjective_mapsTo_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩
#align set.surj_on_iff_exists_map_subtype Set.surjOn_iff_exists_map_subtype

/- warning: set.surj_on_empty -> Set.surjOn_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Set.SurjOn.{u1, u2} α β f s (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Set.SurjOn.{u2, u1} α β f s (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.surj_on_empty Set.surjOn_emptyₓ'. -/
theorem surjOn_empty (f : α → β) (s : Set α) : SurjOn f s ∅ :=
  empty_subset _
#align set.surj_on_empty Set.surjOn_empty

/- warning: set.surj_on_image -> Set.surjOn_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Set.SurjOn.{u1, u2} α β f s (Set.image.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Set.SurjOn.{u2, u1} α β f s (Set.image.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.surj_on_image Set.surjOn_imageₓ'. -/
theorem surjOn_image (f : α → β) (s : Set α) : SurjOn f s (f '' s) :=
  subset.rfl
#align set.surj_on_image Set.surjOn_image

/- warning: set.surj_on.comap_nonempty -> Set.SurjOn.comap_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.SurjOn.{u1, u2} α β f s t) -> (Set.Nonempty.{u2} β t) -> (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.SurjOn.{u2, u1} α β f s t) -> (Set.Nonempty.{u1} β t) -> (Set.Nonempty.{u2} α s)
Case conversion may be inaccurate. Consider using '#align set.surj_on.comap_nonempty Set.SurjOn.comap_nonemptyₓ'. -/
theorem SurjOn.comap_nonempty (h : SurjOn f s t) (ht : t.Nonempty) : s.Nonempty :=
  (ht.mono h).of_image
#align set.surj_on.comap_nonempty Set.SurjOn.comap_nonempty

/- warning: set.surj_on.congr -> Set.SurjOn.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.SurjOn.{u1, u2} α β f₁ s t) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.SurjOn.{u1, u2} α β f₂ s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.SurjOn.{u2, u1} α β f₁ s t) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Set.SurjOn.{u2, u1} α β f₂ s t)
Case conversion may be inaccurate. Consider using '#align set.surj_on.congr Set.SurjOn.congrₓ'. -/
theorem SurjOn.congr (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s) : SurjOn f₂ s t := by
  rwa [surj_on, ← H.image_eq]
#align set.surj_on.congr Set.SurjOn.congr

/- warning: set.eq_on.surj_on_iff -> Set.EqOn.surjOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Iff (Set.SurjOn.{u1, u2} α β f₁ s t) (Set.SurjOn.{u1, u2} α β f₂ s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Iff (Set.SurjOn.{u2, u1} α β f₁ s t) (Set.SurjOn.{u2, u1} α β f₂ s t))
Case conversion may be inaccurate. Consider using '#align set.eq_on.surj_on_iff Set.EqOn.surjOn_iffₓ'. -/
theorem EqOn.surjOn_iff (h : EqOn f₁ f₂ s) : SurjOn f₁ s t ↔ SurjOn f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩
#align set.eq_on.surj_on_iff Set.EqOn.surjOn_iff

/- warning: set.surj_on.mono -> Set.SurjOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t₁ t₂) -> (Set.SurjOn.{u1, u2} α β f s₁ t₂) -> (Set.SurjOn.{u1, u2} α β f s₂ t₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t₁ t₂) -> (Set.SurjOn.{u2, u1} α β f s₁ t₂) -> (Set.SurjOn.{u2, u1} α β f s₂ t₁)
Case conversion may be inaccurate. Consider using '#align set.surj_on.mono Set.SurjOn.monoₓ'. -/
theorem SurjOn.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
  Subset.trans ht <| Subset.trans hf <| image_subset _ hs
#align set.surj_on.mono Set.SurjOn.mono

/- warning: set.surj_on.union -> Set.SurjOn.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.SurjOn.{u1, u2} α β f s t₁) -> (Set.SurjOn.{u1, u2} α β f s t₂) -> (Set.SurjOn.{u1, u2} α β f s (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.SurjOn.{u2, u1} α β f s t₁) -> (Set.SurjOn.{u2, u1} α β f s t₂) -> (Set.SurjOn.{u2, u1} α β f s (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.surj_on.union Set.SurjOn.unionₓ'. -/
theorem SurjOn.union (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂) : SurjOn f s (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx
#align set.surj_on.union Set.SurjOn.union

/- warning: set.surj_on.union_union -> Set.SurjOn.union_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.SurjOn.{u1, u2} α β f s₁ t₁) -> (Set.SurjOn.{u1, u2} α β f s₂ t₂) -> (Set.SurjOn.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.SurjOn.{u2, u1} α β f s₁ t₁) -> (Set.SurjOn.{u2, u1} α β f s₂ t₂) -> (Set.SurjOn.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.surj_on.union_union Set.SurjOn.union_unionₓ'. -/
theorem SurjOn.union_union (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) :
    SurjOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  (h₁.mono (subset_union_left _ _) (Subset.refl _)).union
    (h₂.mono (subset_union_right _ _) (Subset.refl _))
#align set.surj_on.union_union Set.SurjOn.union_union

/- warning: set.surj_on.inter_inter -> Set.SurjOn.inter_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.SurjOn.{u1, u2} α β f s₁ t₁) -> (Set.SurjOn.{u1, u2} α β f s₂ t₂) -> (Set.InjOn.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) -> (Set.SurjOn.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.SurjOn.{u2, u1} α β f s₁ t₁) -> (Set.SurjOn.{u2, u1} α β f s₂ t₂) -> (Set.InjOn.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂)) -> (Set.SurjOn.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.surj_on.inter_inter Set.SurjOn.inter_interₓ'. -/
theorem SurjOn.inter_inter (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) HEq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩
#align set.surj_on.inter_inter Set.SurjOn.inter_inter

/- warning: set.surj_on.inter -> Set.SurjOn.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.SurjOn.{u1, u2} α β f s₁ t) -> (Set.SurjOn.{u1, u2} α β f s₂ t) -> (Set.InjOn.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) -> (Set.SurjOn.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.SurjOn.{u2, u1} α β f s₁ t) -> (Set.SurjOn.{u2, u1} α β f s₂ t) -> (Set.InjOn.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂)) -> (Set.SurjOn.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s₂) t)
Case conversion may be inaccurate. Consider using '#align set.surj_on.inter Set.SurjOn.interₓ'. -/
theorem SurjOn.inter (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h
#align set.surj_on.inter Set.SurjOn.inter

/- warning: set.surj_on.comp -> Set.SurjOn.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {p : Set.{u3} γ} {f : α -> β} {g : β -> γ}, (Set.SurjOn.{u2, u3} β γ g t p) -> (Set.SurjOn.{u1, u2} α β f s t) -> (Set.SurjOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s p)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{u1} α} {t : Set.{u3} β} {p : Set.{u2} γ} {f : α -> β} {g : β -> γ}, (Set.SurjOn.{u3, u2} β γ g t p) -> (Set.SurjOn.{u1, u3} α β f s t) -> (Set.SurjOn.{u1, u2} α γ (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) s p)
Case conversion may be inaccurate. Consider using '#align set.surj_on.comp Set.SurjOn.compₓ'. -/
theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
  Subset.trans hg <| Subset.trans (image_subset g hf) <| image_comp g f s ▸ Subset.refl _
#align set.surj_on.comp Set.SurjOn.comp

/- warning: set.surjective_iff_surj_on_univ -> Set.surjective_iff_surjOn_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Iff (Function.Surjective.{succ u1, succ u2} α β f) (Set.SurjOn.{u1, u2} α β f (Set.univ.{u1} α) (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, Iff (Function.Surjective.{succ u2, succ u1} α β f) (Set.SurjOn.{u2, u1} α β f (Set.univ.{u2} α) (Set.univ.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.surjective_iff_surj_on_univ Set.surjective_iff_surjOn_univₓ'. -/
theorem surjective_iff_surjOn_univ : Surjective f ↔ SurjOn f univ univ := by
  simp [surjective, surj_on, subset_def]
#align set.surjective_iff_surj_on_univ Set.surjective_iff_surjOn_univ

/- warning: set.surj_on_iff_surjective -> Set.surjOn_iff_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β}, Iff (Set.SurjOn.{u1, u2} α β f s (Set.univ.{u2} β)) (Function.Surjective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β}, Iff (Set.SurjOn.{u2, u1} α β f s (Set.univ.{u1} β)) (Function.Surjective.{succ u2, succ u1} (Set.Elem.{u2} α s) β (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f))
Case conversion may be inaccurate. Consider using '#align set.surj_on_iff_surjective Set.surjOn_iff_surjectiveₓ'. -/
theorem surjOn_iff_surjective : SurjOn f s univ ↔ Surjective (s.restrict f) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩
#align set.surj_on_iff_surjective Set.surjOn_iff_surjective

/- warning: set.surj_on.image_eq_of_maps_to -> Set.SurjOn.image_eq_of_mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.SurjOn.{u1, u2} α β f s t) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.SurjOn.{u2, u1} α β f s t) -> (Set.MapsTo.{u2, u1} α β f s t) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) t)
Case conversion may be inaccurate. Consider using '#align set.surj_on.image_eq_of_maps_to Set.SurjOn.image_eq_of_mapsToₓ'. -/
theorem SurjOn.image_eq_of_mapsTo (h₁ : SurjOn f s t) (h₂ : MapsTo f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁
#align set.surj_on.image_eq_of_maps_to Set.SurjOn.image_eq_of_mapsTo

#print Set.image_eq_iff_surjOn_mapsTo /-
theorem image_eq_iff_surjOn_mapsTo : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t :=
  by
  refine' ⟨_, fun h => h.1.image_eq_of_maps_to h.2⟩
  rintro rfl
  exact ⟨s.surj_on_image f, s.maps_to_image f⟩
#align set.image_eq_iff_surj_on_maps_to Set.image_eq_iff_surjOn_mapsTo
-/

/- warning: set.surj_on.maps_to_compl -> Set.SurjOn.mapsTo_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.SurjOn.{u1, u2} α β f s t) -> (Function.Injective.{succ u1, succ u2} α β f) -> (Set.MapsTo.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.SurjOn.{u2, u1} α β f s t) -> (Function.Injective.{succ u2, succ u1} α β f) -> (Set.MapsTo.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) t))
Case conversion may be inaccurate. Consider using '#align set.surj_on.maps_to_compl Set.SurjOn.mapsTo_complₓ'. -/
theorem SurjOn.mapsTo_compl (h : SurjOn f s t) (h' : Injective f) : MapsTo f (sᶜ) (tᶜ) :=
  fun x hs ht =>
  let ⟨x', hx', HEq⟩ := h ht
  hs <| h' HEq ▸ hx'
#align set.surj_on.maps_to_compl Set.SurjOn.mapsTo_compl

/- warning: set.maps_to.surj_on_compl -> Set.MapsTo.surjOn_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (Set.SurjOn.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (Set.SurjOn.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) t))
Case conversion may be inaccurate. Consider using '#align set.maps_to.surj_on_compl Set.MapsTo.surjOn_complₓ'. -/
theorem MapsTo.surjOn_compl (h : MapsTo f s t) (h' : Surjective f) : SurjOn f (sᶜ) (tᶜ) :=
  h'.forall.2 fun x ht => (mem_image_of_mem _) fun hs => ht (h hs)
#align set.maps_to.surj_on_compl Set.MapsTo.surjOn_compl

/- warning: set.eq_on.cancel_right -> Set.EqOn.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {g₁ : β -> γ} {g₂ : β -> γ}, (Set.EqOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g₁ f) (Function.comp.{succ u1, succ u2, succ u3} α β γ g₂ f) s) -> (Set.SurjOn.{u1, u2} α β f s t) -> (Set.EqOn.{u2, u3} β γ g₁ g₂ t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {s : Set.{u3} α} {t : Set.{u1} β} {f : α -> β} {g₁ : β -> γ} {g₂ : β -> γ}, (Set.EqOn.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g₁ f) (Function.comp.{succ u3, succ u1, succ u2} α β γ g₂ f) s) -> (Set.SurjOn.{u3, u1} α β f s t) -> (Set.EqOn.{u1, u2} β γ g₁ g₂ t)
Case conversion may be inaccurate. Consider using '#align set.eq_on.cancel_right Set.EqOn.cancel_rightₓ'. -/
theorem EqOn.cancel_right (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t) : t.EqOn g₁ g₂ :=
  by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha
#align set.eq_on.cancel_right Set.EqOn.cancel_right

/- warning: set.surj_on.cancel_right -> Set.SurjOn.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {g₁ : β -> γ} {g₂ : β -> γ}, (Set.SurjOn.{u1, u2} α β f s t) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Iff (Set.EqOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g₁ f) (Function.comp.{succ u1, succ u2, succ u3} α β γ g₂ f) s) (Set.EqOn.{u2, u3} β γ g₁ g₂ t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {s : Set.{u3} α} {t : Set.{u2} β} {f : α -> β} {g₁ : β -> γ} {g₂ : β -> γ}, (Set.SurjOn.{u3, u2} α β f s t) -> (Set.MapsTo.{u3, u2} α β f s t) -> (Iff (Set.EqOn.{u3, u1} α γ (Function.comp.{succ u3, succ u2, succ u1} α β γ g₁ f) (Function.comp.{succ u3, succ u2, succ u1} α β γ g₂ f) s) (Set.EqOn.{u2, u1} β γ g₁ g₂ t))
Case conversion may be inaccurate. Consider using '#align set.surj_on.cancel_right Set.SurjOn.cancel_rightₓ'. -/
theorem SurjOn.cancel_right (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ t.EqOn g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.compRight hf'⟩
#align set.surj_on.cancel_right Set.SurjOn.cancel_right

/- warning: set.eq_on_comp_right_iff -> Set.eqOn_comp_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {f : α -> β} {g₁ : β -> γ} {g₂ : β -> γ}, Iff (Set.EqOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g₁ f) (Function.comp.{succ u1, succ u2, succ u3} α β γ g₂ f) s) (Set.EqOn.{u2, u3} β γ g₁ g₂ (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {s : Set.{u3} α} {f : α -> β} {g₁ : β -> γ} {g₂ : β -> γ}, Iff (Set.EqOn.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g₁ f) (Function.comp.{succ u3, succ u1, succ u2} α β γ g₂ f) s) (Set.EqOn.{u1, u2} β γ g₁ g₂ (Set.image.{u3, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.eq_on_comp_right_iff Set.eqOn_comp_right_iffₓ'. -/
theorem eqOn_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
  (s.surj_on_image f).cancel_right <| s.maps_to_image f
#align set.eq_on_comp_right_iff Set.eqOn_comp_right_iff

/-! ### Bijectivity -/


#print Set.BijOn /-
/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t
#align set.bij_on Set.BijOn
-/

/- warning: set.bij_on.maps_to -> Set.BijOn.mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s t) -> (Set.MapsTo.{u1, u2} α β f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s t) -> (Set.MapsTo.{u2, u1} α β f s t)
Case conversion may be inaccurate. Consider using '#align set.bij_on.maps_to Set.BijOn.mapsToₓ'. -/
theorem BijOn.mapsTo (h : BijOn f s t) : MapsTo f s t :=
  h.left
#align set.bij_on.maps_to Set.BijOn.mapsTo

/- warning: set.bij_on.inj_on -> Set.BijOn.injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s t) -> (Set.InjOn.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s t) -> (Set.InjOn.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.bij_on.inj_on Set.BijOn.injOnₓ'. -/
theorem BijOn.injOn (h : BijOn f s t) : InjOn f s :=
  h.right.left
#align set.bij_on.inj_on Set.BijOn.injOn

/- warning: set.bij_on.surj_on -> Set.BijOn.surjOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s t) -> (Set.SurjOn.{u1, u2} α β f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s t) -> (Set.SurjOn.{u2, u1} α β f s t)
Case conversion may be inaccurate. Consider using '#align set.bij_on.surj_on Set.BijOn.surjOnₓ'. -/
theorem BijOn.surjOn (h : BijOn f s t) : SurjOn f s t :=
  h.right.right
#align set.bij_on.surj_on Set.BijOn.surjOn

/- warning: set.bij_on.mk -> Set.BijOn.mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t) -> (Set.InjOn.{u1, u2} α β f s) -> (Set.SurjOn.{u1, u2} α β f s t) -> (Set.BijOn.{u1, u2} α β f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t) -> (Set.InjOn.{u2, u1} α β f s) -> (Set.SurjOn.{u2, u1} α β f s t) -> (Set.BijOn.{u2, u1} α β f s t)
Case conversion may be inaccurate. Consider using '#align set.bij_on.mk Set.BijOn.mkₓ'. -/
theorem BijOn.mk (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t) : BijOn f s t :=
  ⟨h₁, h₂, h₃⟩
#align set.bij_on.mk Set.BijOn.mk

/- warning: set.bij_on_empty -> Set.bijOn_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Set.BijOn.{u1, u2} α β f (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Set.BijOn.{u2, u1} α β f (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.bij_on_empty Set.bijOn_emptyₓ'. -/
theorem bijOn_empty (f : α → β) : BijOn f ∅ ∅ :=
  ⟨mapsTo_empty f ∅, injOn_empty f, surjOn_empty f ∅⟩
#align set.bij_on_empty Set.bijOn_empty

/- warning: set.bij_on.inter_maps_to -> Set.BijOn.inter_mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s₁ t₁) -> (Set.MapsTo.{u1, u2} α β f s₂ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ (Set.preimage.{u1, u2} α β f t₂)) s₂) -> (Set.BijOn.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s₁ t₁) -> (Set.MapsTo.{u2, u1} α β f s₂ t₂) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ (Set.preimage.{u2, u1} α β f t₂)) s₂) -> (Set.BijOn.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.bij_on.inter_maps_to Set.BijOn.inter_mapsToₓ'. -/
theorem BijOn.inter_mapsTo (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ ∩ f ⁻¹' t₂ ⊆ s₂) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.MapsTo.inter_inter h₂, h₁.InjOn.mono <| inter_subset_left _ _, fun y hy =>
    let ⟨x, hx, hxy⟩ := h₁.SurjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.recOn hy.2⟩⟩, hxy⟩⟩
#align set.bij_on.inter_maps_to Set.BijOn.inter_mapsTo

/- warning: set.maps_to.inter_bij_on -> Set.MapsTo.inter_bijOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s₁ t₁) -> (Set.BijOn.{u1, u2} α β f s₂ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₂ (Set.preimage.{u1, u2} α β f t₁)) s₁) -> (Set.BijOn.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s₁ t₁) -> (Set.BijOn.{u2, u1} α β f s₂ t₂) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₂ (Set.preimage.{u2, u1} α β f t₁)) s₁) -> (Set.BijOn.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.maps_to.inter_bij_on Set.MapsTo.inter_bijOnₓ'. -/
theorem MapsTo.inter_bijOn (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ ∩ f ⁻¹' t₁ ⊆ s₁) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_maps_to h₁ h₃
#align set.maps_to.inter_bij_on Set.MapsTo.inter_bijOn

/- warning: set.bij_on.inter -> Set.BijOn.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s₁ t₁) -> (Set.BijOn.{u1, u2} α β f s₂ t₂) -> (Set.InjOn.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) -> (Set.BijOn.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s₁ t₁) -> (Set.BijOn.{u2, u1} α β f s₂ t₂) -> (Set.InjOn.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂)) -> (Set.BijOn.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.bij_on.inter Set.BijOn.interₓ'. -/
theorem BijOn.inter (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.MapsTo.inter_inter h₂.MapsTo, h₁.InjOn.mono <| inter_subset_left _ _,
    h₁.SurjOn.inter_inter h₂.SurjOn h⟩
#align set.bij_on.inter Set.BijOn.inter

/- warning: set.bij_on.union -> Set.BijOn.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s₁ t₁) -> (Set.BijOn.{u1, u2} α β f s₂ t₂) -> (Set.InjOn.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) -> (Set.BijOn.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s₁ t₁) -> (Set.BijOn.{u2, u1} α β f s₂ t₂) -> (Set.InjOn.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂)) -> (Set.BijOn.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.bij_on.union Set.BijOn.unionₓ'. -/
theorem BijOn.union (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨h₁.MapsTo.union_union h₂.MapsTo, h, h₁.SurjOn.union_union h₂.SurjOn⟩
#align set.bij_on.union Set.BijOn.union

/- warning: set.bij_on.subset_range -> Set.BijOn.subset_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s t) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s t) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align set.bij_on.subset_range Set.BijOn.subset_rangeₓ'. -/
theorem BijOn.subset_range (h : BijOn f s t) : t ⊆ range f :=
  h.SurjOn.subset_range
#align set.bij_on.subset_range Set.BijOn.subset_range

/- warning: set.inj_on.bij_on_image -> Set.InjOn.bijOn_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β}, (Set.InjOn.{u1, u2} α β f s) -> (Set.BijOn.{u1, u2} α β f s (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β}, (Set.InjOn.{u2, u1} α β f s) -> (Set.BijOn.{u2, u1} α β f s (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.inj_on.bij_on_image Set.InjOn.bijOn_imageₓ'. -/
theorem InjOn.bijOn_image (h : InjOn f s) : BijOn f s (f '' s) :=
  BijOn.mk (mapsTo_image f s) h (Subset.refl _)
#align set.inj_on.bij_on_image Set.InjOn.bijOn_image

/- warning: set.bij_on.congr -> Set.BijOn.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.BijOn.{u1, u2} α β f₁ s t) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.BijOn.{u1, u2} α β f₂ s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.BijOn.{u2, u1} α β f₁ s t) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Set.BijOn.{u2, u1} α β f₂ s t)
Case conversion may be inaccurate. Consider using '#align set.bij_on.congr Set.BijOn.congrₓ'. -/
theorem BijOn.congr (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s) : BijOn f₂ s t :=
  BijOn.mk (h₁.MapsTo.congr h) (h₁.InjOn.congr h) (h₁.SurjOn.congr h)
#align set.bij_on.congr Set.BijOn.congr

/- warning: set.eq_on.bij_on_iff -> Set.EqOn.bijOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Iff (Set.BijOn.{u1, u2} α β f₁ s t) (Set.BijOn.{u1, u2} α β f₂ s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β}, (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Iff (Set.BijOn.{u2, u1} α β f₁ s t) (Set.BijOn.{u2, u1} α β f₂ s t))
Case conversion may be inaccurate. Consider using '#align set.eq_on.bij_on_iff Set.EqOn.bijOn_iffₓ'. -/
theorem EqOn.bijOn_iff (H : EqOn f₁ f₂ s) : BijOn f₁ s t ↔ BijOn f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.bij_on_iff Set.EqOn.bijOn_iff

/- warning: set.bij_on.image_eq -> Set.BijOn.image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s t) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s t) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) t)
Case conversion may be inaccurate. Consider using '#align set.bij_on.image_eq Set.BijOn.image_eqₓ'. -/
theorem BijOn.image_eq (h : BijOn f s t) : f '' s = t :=
  h.SurjOn.image_eq_of_maps_to h.MapsTo
#align set.bij_on.image_eq Set.BijOn.image_eq

/- warning: set.bij_on.comp -> Set.BijOn.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {p : Set.{u3} γ} {f : α -> β} {g : β -> γ}, (Set.BijOn.{u2, u3} β γ g t p) -> (Set.BijOn.{u1, u2} α β f s t) -> (Set.BijOn.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s p)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{u1} α} {t : Set.{u3} β} {p : Set.{u2} γ} {f : α -> β} {g : β -> γ}, (Set.BijOn.{u3, u2} β γ g t p) -> (Set.BijOn.{u1, u3} α β f s t) -> (Set.BijOn.{u1, u2} α γ (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) s p)
Case conversion may be inaccurate. Consider using '#align set.bij_on.comp Set.BijOn.compₓ'. -/
theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  BijOn.mk (hg.MapsTo.comp hf.MapsTo) (hg.InjOn.comp hf.InjOn hf.MapsTo) (hg.SurjOn.comp hf.SurjOn)
#align set.bij_on.comp Set.BijOn.comp

/- warning: set.bij_on.bijective -> Set.BijOn.bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} (h : Set.BijOn.{u1, u2} α β f s t), Function.Bijective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (Set.MapsTo.restrict.{u1, u2} α β f s t (Set.BijOn.mapsTo.{u1, u2} α β s t f h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} (h : Set.BijOn.{u2, u1} α β f s t), Function.Bijective.{succ u2, succ u1} (Set.Elem.{u2} α s) (Set.Elem.{u1} β t) (Set.MapsTo.restrict.{u2, u1} α β f s t (Set.BijOn.mapsTo.{u1, u2} α β s t f h))
Case conversion may be inaccurate. Consider using '#align set.bij_on.bijective Set.BijOn.bijectiveₓ'. -/
theorem BijOn.bijective (h : BijOn f s t) : Bijective (h.MapsTo.restrict f s t) :=
  ⟨fun x y h' => Subtype.ext <| h.InjOn x.2 y.2 <| Subtype.ext_iff.1 h', fun ⟨y, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.SurjOn hy
    ⟨⟨x, hx⟩, Subtype.eq hxy⟩⟩
#align set.bij_on.bijective Set.BijOn.bijective

/- warning: set.bijective_iff_bij_on_univ -> Set.bijective_iff_bijOn_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Iff (Function.Bijective.{succ u1, succ u2} α β f) (Set.BijOn.{u1, u2} α β f (Set.univ.{u1} α) (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, Iff (Function.Bijective.{succ u2, succ u1} α β f) (Set.BijOn.{u2, u1} α β f (Set.univ.{u2} α) (Set.univ.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.bijective_iff_bij_on_univ Set.bijective_iff_bijOn_univₓ'. -/
theorem bijective_iff_bijOn_univ : Bijective f ↔ BijOn f univ univ :=
  Iff.intro
    (fun h =>
      let ⟨inj, surj⟩ := h
      ⟨mapsTo_univ f _, inj.InjOn _, Iff.mp surjective_iff_surjOn_univ surj⟩)
    fun h =>
    let ⟨map, inj, surj⟩ := h
    ⟨Iff.mpr injective_iff_injOn_univ inj, Iff.mpr surjective_iff_surjOn_univ surj⟩
#align set.bijective_iff_bij_on_univ Set.bijective_iff_bijOn_univ

/- warning: set.bij_on.compl -> Set.BijOn.compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.BijOn.{u1, u2} α β f s t) -> (Function.Bijective.{succ u1, succ u2} α β f) -> (Set.BijOn.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.BijOn.{u2, u1} α β f s t) -> (Function.Bijective.{succ u2, succ u1} α β f) -> (Set.BijOn.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) t))
Case conversion may be inaccurate. Consider using '#align set.bij_on.compl Set.BijOn.complₓ'. -/
theorem BijOn.compl (hst : BijOn f s t) (hf : Bijective f) : BijOn f (sᶜ) (tᶜ) :=
  ⟨hst.SurjOn.maps_to_compl hf.1, hf.1.InjOn _, hst.MapsTo.surj_on_compl hf.2⟩
#align set.bij_on.compl Set.BijOn.compl

/-! ### left inverse -/


#print Set.LeftInvOn /-
/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
def LeftInvOn (f' : β → α) (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f' (f x) = x
#align set.left_inv_on Set.LeftInvOn
-/

/- warning: set.left_inv_on.eq_on -> Set.LeftInvOn.eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (Set.EqOn.{u1, u1} α α (Function.comp.{succ u1, succ u2, succ u1} α β α f' f) (id.{succ u1} α) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (Set.EqOn.{u2, u2} α α (Function.comp.{succ u2, succ u1, succ u2} α β α f' f) (id.{succ u2} α) s)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.eq_on Set.LeftInvOn.eqOnₓ'. -/
theorem LeftInvOn.eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s :=
  h
#align set.left_inv_on.eq_on Set.LeftInvOn.eqOn

/- warning: set.left_inv_on.eq -> Set.LeftInvOn.eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (forall {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u1} α (f' (f x)) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (forall {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Eq.{succ u2} α (f' (f x)) x))
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.eq Set.LeftInvOn.eqₓ'. -/
theorem LeftInvOn.eq (h : LeftInvOn f' f s) {x} (hx : x ∈ s) : f' (f x) = x :=
  h hx
#align set.left_inv_on.eq Set.LeftInvOn.eq

/- warning: set.left_inv_on.congr_left -> Set.LeftInvOn.congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {f₁' : β -> α} {f₂' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f₁' f s) -> (forall {t : Set.{u2} β}, (Set.MapsTo.{u1, u2} α β f s t) -> (Set.EqOn.{u2, u1} β α f₁' f₂' t) -> (Set.LeftInvOn.{u1, u2} α β f₂' f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {f₁' : β -> α} {f₂' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f₁' f s) -> (forall {t : Set.{u1} β}, (Set.MapsTo.{u2, u1} α β f s t) -> (Set.EqOn.{u1, u2} β α f₁' f₂' t) -> (Set.LeftInvOn.{u2, u1} α β f₂' f s))
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.congr_left Set.LeftInvOn.congr_leftₓ'. -/
theorem LeftInvOn.congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
    (heq : EqOn f₁' f₂' t) : LeftInvOn f₂' f s := fun x hx => HEq (h₁' hx) ▸ h₁ hx
#align set.left_inv_on.congr_left Set.LeftInvOn.congr_left

/- warning: set.left_inv_on.congr_right -> Set.LeftInvOn.congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f₁ : α -> β} {f₂ : α -> β} {f₁' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f₁' f₁ s) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.LeftInvOn.{u1, u2} α β f₁' f₂ s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f₁ : α -> β} {f₂ : α -> β} {f₁' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f₁' f₁ s) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Set.LeftInvOn.{u2, u1} α β f₁' f₂ s)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.congr_right Set.LeftInvOn.congr_rightₓ'. -/
theorem LeftInvOn.congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s :=
  fun x hx => HEq hx ▸ h₁ hx
#align set.left_inv_on.congr_right Set.LeftInvOn.congr_right

/- warning: set.left_inv_on.inj_on -> Set.LeftInvOn.injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {f₁' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f₁' f s) -> (Set.InjOn.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {f₁' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f₁' f s) -> (Set.InjOn.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.inj_on Set.LeftInvOn.injOnₓ'. -/
theorem LeftInvOn.injOn (h : LeftInvOn f₁' f s) : InjOn f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
    x₁ = f₁' (f x₁) := Eq.symm <| h h₁
    _ = f₁' (f x₂) := congr_arg f₁' HEq
    _ = x₂ := h h₂
    
#align set.left_inv_on.inj_on Set.LeftInvOn.injOn

/- warning: set.left_inv_on.surj_on -> Set.LeftInvOn.surjOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.SurjOn.{u2, u1} β α f' t s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (Set.MapsTo.{u2, u1} α β f s t) -> (Set.SurjOn.{u1, u2} β α f' t s)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.surj_on Set.LeftInvOn.surjOnₓ'. -/
theorem LeftInvOn.surjOn (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s := fun x hx =>
  ⟨f x, hf hx, h hx⟩
#align set.left_inv_on.surj_on Set.LeftInvOn.surjOn

/- warning: set.left_inv_on.maps_to -> Set.LeftInvOn.mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (Set.SurjOn.{u1, u2} α β f s t) -> (Set.MapsTo.{u2, u1} β α f' t s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (Set.SurjOn.{u2, u1} α β f s t) -> (Set.MapsTo.{u1, u2} β α f' t s)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.maps_to Set.LeftInvOn.mapsToₓ'. -/
theorem LeftInvOn.mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) : MapsTo f' t s := fun y hy =>
  by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]
#align set.left_inv_on.maps_to Set.LeftInvOn.mapsTo

/- warning: set.left_inv_on.comp -> Set.LeftInvOn.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {g : β -> γ} {f' : β -> α} {g' : γ -> β}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (Set.LeftInvOn.{u2, u3} β γ g' g t) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.LeftInvOn.{u1, u3} α γ (Function.comp.{succ u3, succ u2, succ u1} γ β α f' g') (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {s : Set.{u3} α} {t : Set.{u2} β} {f : α -> β} {g : β -> γ} {f' : β -> α} {g' : γ -> β}, (Set.LeftInvOn.{u3, u2} α β f' f s) -> (Set.LeftInvOn.{u2, u1} β γ g' g t) -> (Set.MapsTo.{u3, u2} α β f s t) -> (Set.LeftInvOn.{u3, u1} α γ (Function.comp.{succ u1, succ u2, succ u3} γ β α f' g') (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.comp Set.LeftInvOn.compₓ'. -/
theorem LeftInvOn.comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
    LeftInvOn (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h
    
#align set.left_inv_on.comp Set.LeftInvOn.comp

/- warning: set.left_inv_on.mono -> Set.LeftInvOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s) -> (Set.LeftInvOn.{u1, u2} α β f' f s₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s) -> (Set.LeftInvOn.{u2, u1} α β f' f s₁)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.mono Set.LeftInvOn.monoₓ'. -/
theorem LeftInvOn.mono (hf : LeftInvOn f' f s) (ht : s₁ ⊆ s) : LeftInvOn f' f s₁ := fun x hx =>
  hf (ht hx)
#align set.left_inv_on.mono Set.LeftInvOn.mono

/- warning: set.left_inv_on.image_inter' -> Set.LeftInvOn.image_inter' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.preimage.{u2, u1} β α f' s₁) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) (Set.preimage.{u1, u2} β α f' s₁) (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.image_inter' Set.LeftInvOn.image_inter'ₓ'. -/
theorem LeftInvOn.image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s :=
  by
  apply subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩
#align set.left_inv_on.image_inter' Set.LeftInvOn.image_inter'

/- warning: set.left_inv_on.image_inter -> Set.LeftInvOn.image_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.preimage.{u2, u1} β α f' (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s)) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) (Set.preimage.{u1, u2} β α f' (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s)) (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.image_inter Set.LeftInvOn.image_interₓ'. -/
theorem LeftInvOn.image_inter (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s :=
  by
  rw [hf.image_inter']
  refine' subset.antisymm _ (inter_subset_inter_left _ (preimage_mono <| inter_subset_left _ _))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩
#align set.left_inv_on.image_inter Set.LeftInvOn.image_inter

/- warning: set.left_inv_on.image_image -> Set.LeftInvOn.image_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α f' (Set.image.{u1, u2} α β f s)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α f' (Set.image.{u2, u1} α β f s)) s)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.image_image Set.LeftInvOn.image_imageₓ'. -/
theorem LeftInvOn.image_image (hf : LeftInvOn f' f s) : f' '' (f '' s) = s := by
  rw [image_image, image_congr hf, image_id']
#align set.left_inv_on.image_image Set.LeftInvOn.image_image

/- warning: set.left_inv_on.image_image' -> Set.LeftInvOn.image_image' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α f' (Set.image.{u1, u2} α β f s₁)) s₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s) -> (Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α f' (Set.image.{u2, u1} α β f s₁)) s₁)
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.image_image' Set.LeftInvOn.image_image'ₓ'. -/
theorem LeftInvOn.image_image' (hf : LeftInvOn f' f s) (hs : s₁ ⊆ s) : f' '' (f '' s₁) = s₁ :=
  (hf.mono hs).image_image
#align set.left_inv_on.image_image' Set.LeftInvOn.image_image'

/-! ### Right inverse -/


#print Set.RightInvOn /-
/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
@[reducible]
def RightInvOn (f' : β → α) (f : α → β) (t : Set β) : Prop :=
  LeftInvOn f f' t
#align set.right_inv_on Set.RightInvOn
-/

/- warning: set.right_inv_on.eq_on -> Set.RightInvOn.eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u1, u2} α β f' f t) -> (Set.EqOn.{u2, u2} β β (Function.comp.{succ u2, succ u1, succ u2} β α β f f') (id.{succ u2} β) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u2, u1} α β f' f t) -> (Set.EqOn.{u1, u1} β β (Function.comp.{succ u1, succ u2, succ u1} β α β f f') (id.{succ u1} β) t)
Case conversion may be inaccurate. Consider using '#align set.right_inv_on.eq_on Set.RightInvOn.eqOnₓ'. -/
theorem RightInvOn.eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t :=
  h
#align set.right_inv_on.eq_on Set.RightInvOn.eqOn

/- warning: set.right_inv_on.eq -> Set.RightInvOn.eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u1, u2} α β f' f t) -> (forall {y : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (Eq.{succ u2} β (f (f' y)) y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u2, u1} α β f' f t) -> (forall {y : β}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t) -> (Eq.{succ u1} β (f (f' y)) y))
Case conversion may be inaccurate. Consider using '#align set.right_inv_on.eq Set.RightInvOn.eqₓ'. -/
theorem RightInvOn.eq (h : RightInvOn f' f t) {y} (hy : y ∈ t) : f (f' y) = y :=
  h hy
#align set.right_inv_on.eq Set.RightInvOn.eq

/- warning: set.left_inv_on.right_inv_on_image -> Set.LeftInvOn.rightInvOn_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f' f s) -> (Set.RightInvOn.{u1, u2} α β f' f (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {f' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f' f s) -> (Set.RightInvOn.{u2, u1} α β f' f (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.left_inv_on.right_inv_on_image Set.LeftInvOn.rightInvOn_imageₓ'. -/
theorem LeftInvOn.rightInvOn_image (h : LeftInvOn f' f s) : RightInvOn f' f (f '' s) :=
  fun y ⟨x, hx, Eq⟩ => Eq ▸ congr_arg f <| h.Eq hx
#align set.left_inv_on.right_inv_on_image Set.LeftInvOn.rightInvOn_image

/- warning: set.right_inv_on.congr_left -> Set.RightInvOn.congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Set.{u2} β} {f : α -> β} {f₁' : β -> α} {f₂' : β -> α}, (Set.RightInvOn.{u1, u2} α β f₁' f t) -> (Set.EqOn.{u2, u1} β α f₁' f₂' t) -> (Set.RightInvOn.{u1, u2} α β f₂' f t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Set.{u1} β} {f : α -> β} {f₁' : β -> α} {f₂' : β -> α}, (Set.RightInvOn.{u2, u1} α β f₁' f t) -> (Set.EqOn.{u1, u2} β α f₁' f₂' t) -> (Set.RightInvOn.{u2, u1} α β f₂' f t)
Case conversion may be inaccurate. Consider using '#align set.right_inv_on.congr_left Set.RightInvOn.congr_leftₓ'. -/
theorem RightInvOn.congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) :
    RightInvOn f₂' f t :=
  h₁.congr_right HEq
#align set.right_inv_on.congr_left Set.RightInvOn.congr_left

/- warning: set.right_inv_on.congr_right -> Set.RightInvOn.congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β} {f' : β -> α}, (Set.RightInvOn.{u1, u2} α β f' f₁ t) -> (Set.MapsTo.{u2, u1} β α f' t s) -> (Set.EqOn.{u1, u2} α β f₁ f₂ s) -> (Set.RightInvOn.{u1, u2} α β f' f₂ t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β} {f' : β -> α}, (Set.RightInvOn.{u2, u1} α β f' f₁ t) -> (Set.MapsTo.{u1, u2} β α f' t s) -> (Set.EqOn.{u2, u1} α β f₁ f₂ s) -> (Set.RightInvOn.{u2, u1} α β f' f₂ t)
Case conversion may be inaccurate. Consider using '#align set.right_inv_on.congr_right Set.RightInvOn.congr_rightₓ'. -/
theorem RightInvOn.congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s) :
    RightInvOn f' f₂ t :=
  LeftInvOn.congr_left h₁ hg HEq
#align set.right_inv_on.congr_right Set.RightInvOn.congr_right

/- warning: set.right_inv_on.surj_on -> Set.RightInvOn.surjOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u1, u2} α β f' f t) -> (Set.MapsTo.{u2, u1} β α f' t s) -> (Set.SurjOn.{u1, u2} α β f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u2, u1} α β f' f t) -> (Set.MapsTo.{u1, u2} β α f' t s) -> (Set.SurjOn.{u2, u1} α β f s t)
Case conversion may be inaccurate. Consider using '#align set.right_inv_on.surj_on Set.RightInvOn.surjOnₓ'. -/
theorem RightInvOn.surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t :=
  hf.SurjOn hf'
#align set.right_inv_on.surj_on Set.RightInvOn.surjOn

/- warning: set.right_inv_on.maps_to -> Set.RightInvOn.mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u1, u2} α β f' f t) -> (Set.SurjOn.{u2, u1} β α f' t s) -> (Set.MapsTo.{u1, u2} α β f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u2, u1} α β f' f t) -> (Set.SurjOn.{u1, u2} β α f' t s) -> (Set.MapsTo.{u2, u1} α β f s t)
Case conversion may be inaccurate. Consider using '#align set.right_inv_on.maps_to Set.RightInvOn.mapsToₓ'. -/
theorem RightInvOn.mapsTo (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t :=
  h.MapsTo hf
#align set.right_inv_on.maps_to Set.RightInvOn.mapsTo

/- warning: set.right_inv_on.comp -> Set.RightInvOn.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {t : Set.{u2} β} {p : Set.{u3} γ} {f : α -> β} {g : β -> γ} {f' : β -> α} {g' : γ -> β}, (Set.RightInvOn.{u1, u2} α β f' f t) -> (Set.RightInvOn.{u2, u3} β γ g' g p) -> (Set.MapsTo.{u3, u2} γ β g' p t) -> (Set.RightInvOn.{u1, u3} α γ (Function.comp.{succ u3, succ u2, succ u1} γ β α f' g') (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) p)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {t : Set.{u2} β} {p : Set.{u1} γ} {f : α -> β} {g : β -> γ} {f' : β -> α} {g' : γ -> β}, (Set.RightInvOn.{u3, u2} α β f' f t) -> (Set.RightInvOn.{u2, u1} β γ g' g p) -> (Set.MapsTo.{u1, u2} γ β g' p t) -> (Set.RightInvOn.{u3, u1} α γ (Function.comp.{succ u1, succ u2, succ u3} γ β α f' g') (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) p)
Case conversion may be inaccurate. Consider using '#align set.right_inv_on.comp Set.RightInvOn.compₓ'. -/
theorem RightInvOn.comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
    RightInvOn (f' ∘ g') (g ∘ f) p :=
  hg.comp hf g'pt
#align set.right_inv_on.comp Set.RightInvOn.comp

/- warning: set.right_inv_on.mono -> Set.RightInvOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Set.{u2} β} {t₁ : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u1, u2} α β f' f t) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t₁ t) -> (Set.RightInvOn.{u1, u2} α β f' f t₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Set.{u1} β} {t₁ : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.RightInvOn.{u2, u1} α β f' f t) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t₁ t) -> (Set.RightInvOn.{u2, u1} α β f' f t₁)
Case conversion may be inaccurate. Consider using '#align set.right_inv_on.mono Set.RightInvOn.monoₓ'. -/
theorem RightInvOn.mono (hf : RightInvOn f' f t) (ht : t₁ ⊆ t) : RightInvOn f' f t₁ :=
  hf.mono ht
#align set.right_inv_on.mono Set.RightInvOn.mono

/- warning: set.inj_on.right_inv_on_of_left_inv_on -> Set.InjOn.rightInvOn_of_leftInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.InjOn.{u1, u2} α β f s) -> (Set.LeftInvOn.{u2, u1} β α f f' t) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.MapsTo.{u2, u1} β α f' t s) -> (Set.RightInvOn.{u2, u1} β α f f' s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.InjOn.{u2, u1} α β f s) -> (Set.LeftInvOn.{u1, u2} β α f f' t) -> (Set.MapsTo.{u2, u1} α β f s t) -> (Set.MapsTo.{u1, u2} β α f' t s) -> (Set.RightInvOn.{u1, u2} β α f f' s)
Case conversion may be inaccurate. Consider using '#align set.inj_on.right_inv_on_of_left_inv_on Set.InjOn.rightInvOn_of_leftInvOnₓ'. -/
theorem InjOn.rightInvOn_of_leftInvOn (hf : InjOn f s) (hf' : LeftInvOn f f' t) (h₁ : MapsTo f s t)
    (h₂ : MapsTo f' t s) : RightInvOn f f' s := fun x h => hf (h₂ <| h₁ h) h (hf' (h₁ h))
#align set.inj_on.right_inv_on_of_left_inv_on Set.InjOn.rightInvOn_of_leftInvOn

/- warning: set.eq_on_of_left_inv_on_of_right_inv_on -> Set.eqOn_of_leftInvOn_of_rightInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f₁' : β -> α} {f₂' : β -> α}, (Set.LeftInvOn.{u1, u2} α β f₁' f s) -> (Set.RightInvOn.{u1, u2} α β f₂' f t) -> (Set.MapsTo.{u2, u1} β α f₂' t s) -> (Set.EqOn.{u2, u1} β α f₁' f₂' t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f₁' : β -> α} {f₂' : β -> α}, (Set.LeftInvOn.{u2, u1} α β f₁' f s) -> (Set.RightInvOn.{u2, u1} α β f₂' f t) -> (Set.MapsTo.{u1, u2} β α f₂' t s) -> (Set.EqOn.{u1, u2} β α f₁' f₂' t)
Case conversion may be inaccurate. Consider using '#align set.eq_on_of_left_inv_on_of_right_inv_on Set.eqOn_of_leftInvOn_of_rightInvOnₓ'. -/
theorem eqOn_of_leftInvOn_of_rightInvOn (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
    (h : MapsTo f₂' t s) : EqOn f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)
    
#align set.eq_on_of_left_inv_on_of_right_inv_on Set.eqOn_of_leftInvOn_of_rightInvOn

/- warning: set.surj_on.left_inv_on_of_right_inv_on -> Set.SurjOn.leftInvOn_of_rightInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.SurjOn.{u1, u2} α β f s t) -> (Set.RightInvOn.{u2, u1} β α f f' s) -> (Set.LeftInvOn.{u2, u1} β α f f' t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.SurjOn.{u2, u1} α β f s t) -> (Set.RightInvOn.{u1, u2} β α f f' s) -> (Set.LeftInvOn.{u1, u2} β α f f' t)
Case conversion may be inaccurate. Consider using '#align set.surj_on.left_inv_on_of_right_inv_on Set.SurjOn.leftInvOn_of_rightInvOnₓ'. -/
theorem SurjOn.leftInvOn_of_rightInvOn (hf : SurjOn f s t) (hf' : RightInvOn f f' s) :
    LeftInvOn f f' t := fun y hy => by
  let ⟨x, hx, HEq⟩ := hf hy
  rw [← HEq, hf' hx]
#align set.surj_on.left_inv_on_of_right_inv_on Set.SurjOn.leftInvOn_of_rightInvOn

/-! ### Two-side inverses -/


#print Set.InvOn /-
/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t
#align set.inv_on Set.InvOn
-/

/- warning: set.inv_on.symm -> Set.InvOn.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.InvOn.{u1, u2} α β f' f s t) -> (Set.InvOn.{u2, u1} β α f f' t s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.InvOn.{u2, u1} α β f' f s t) -> (Set.InvOn.{u1, u2} β α f f' t s)
Case conversion may be inaccurate. Consider using '#align set.inv_on.symm Set.InvOn.symmₓ'. -/
theorem InvOn.symm (h : InvOn f' f s t) : InvOn f f' t s :=
  ⟨h.right, h.left⟩
#align set.inv_on.symm Set.InvOn.symm

/- warning: set.inv_on.mono -> Set.InvOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {t : Set.{u2} β} {t₁ : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.InvOn.{u1, u2} α β f' f s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t₁ t) -> (Set.InvOn.{u1, u2} α β f' f s₁ t₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {t : Set.{u1} β} {t₁ : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.InvOn.{u2, u1} α β f' f s t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t₁ t) -> (Set.InvOn.{u2, u1} α β f' f s₁ t₁)
Case conversion may be inaccurate. Consider using '#align set.inv_on.mono Set.InvOn.monoₓ'. -/
theorem InvOn.mono (h : InvOn f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : InvOn f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩
#align set.inv_on.mono Set.InvOn.mono

/- warning: set.inv_on.bij_on -> Set.InvOn.bijOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {f' : β -> α}, (Set.InvOn.{u1, u2} α β f' f s t) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.MapsTo.{u2, u1} β α f' t s) -> (Set.BijOn.{u1, u2} α β f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {f' : β -> α}, (Set.InvOn.{u2, u1} α β f' f s t) -> (Set.MapsTo.{u2, u1} α β f s t) -> (Set.MapsTo.{u1, u2} β α f' t s) -> (Set.BijOn.{u2, u1} α β f s t)
Case conversion may be inaccurate. Consider using '#align set.inv_on.bij_on Set.InvOn.bijOnₓ'. -/
/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `maps_to` arguments can be deduced from
`surj_on` statements using `left_inv_on.maps_to` and `right_inv_on.maps_to`. -/
theorem InvOn.bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  ⟨hf, h.left.InjOn, h.right.SurjOn hf'⟩
#align set.inv_on.bij_on Set.InvOn.bijOn

end Set

/-! ### `inv_fun_on` is a left/right inverse -/


namespace Function

variable [Nonempty α] {s : Set α} {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

#print Function.invFunOn /-
/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `function.injective.inv_of_mem_range`. -/
noncomputable def invFunOn (f : α → β) (s : Set α) (b : β) : α :=
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›
#align function.inv_fun_on Function.invFunOn
-/

/- warning: function.inv_fun_on_pos -> Function.invFunOn_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α] {s : Set.{u1} α} {f : α -> β} {b : β}, (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Eq.{succ u2} β (f a) b))) -> (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Function.invFunOn.{u1, u2} α β _inst_1 f s b) s) (Eq.{succ u2} β (f (Function.invFunOn.{u1, u2} α β _inst_1 f s b)) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α] {s : Set.{u2} α} {f : α -> β} {b : β}, (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (Eq.{succ u1} β (f a) b))) -> (And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Function.invFunOn.{u2, u1} α β _inst_1 f s b) s) (Eq.{succ u1} β (f (Function.invFunOn.{u2, u1} α β _inst_1 f s b)) b))
Case conversion may be inaccurate. Consider using '#align function.inv_fun_on_pos Function.invFunOn_posₓ'. -/
theorem invFunOn_pos (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s ∧ f (invFunOn f s b) = b := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_pos h] <;> exact Classical.choose_spec h
#align function.inv_fun_on_pos Function.invFunOn_pos

/- warning: function.inv_fun_on_mem -> Function.invFunOn_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α] {s : Set.{u1} α} {f : α -> β} {b : β}, (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Eq.{succ u2} β (f a) b))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Function.invFunOn.{u1, u2} α β _inst_1 f s b) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α] {s : Set.{u2} α} {f : α -> β} {b : β}, (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (Eq.{succ u1} β (f a) b))) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Function.invFunOn.{u2, u1} α β _inst_1 f s b) s)
Case conversion may be inaccurate. Consider using '#align function.inv_fun_on_mem Function.invFunOn_memₓ'. -/
theorem invFunOn_mem (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s :=
  (invFunOn_pos h).left
#align function.inv_fun_on_mem Function.invFunOn_mem

/- warning: function.inv_fun_on_eq -> Function.invFunOn_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α] {s : Set.{u1} α} {f : α -> β} {b : β}, (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Eq.{succ u2} β (f a) b))) -> (Eq.{succ u2} β (f (Function.invFunOn.{u1, u2} α β _inst_1 f s b)) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α] {s : Set.{u2} α} {f : α -> β} {b : β}, (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (Eq.{succ u1} β (f a) b))) -> (Eq.{succ u1} β (f (Function.invFunOn.{u2, u1} α β _inst_1 f s b)) b)
Case conversion may be inaccurate. Consider using '#align function.inv_fun_on_eq Function.invFunOn_eqₓ'. -/
theorem invFunOn_eq (h : ∃ a ∈ s, f a = b) : f (invFunOn f s b) = b :=
  (invFunOn_pos h).right
#align function.inv_fun_on_eq Function.invFunOn_eq

/- warning: function.inv_fun_on_neg -> Function.invFunOn_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α] {s : Set.{u1} α} {f : α -> β} {b : β}, (Not (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Eq.{succ u2} β (f a) b)))) -> (Eq.{succ u1} α (Function.invFunOn.{u1, u2} α β _inst_1 f s b) (Classical.choice.{succ u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α] {s : Set.{u2} α} {f : α -> β} {b : β}, (Not (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (Eq.{succ u1} β (f a) b)))) -> (Eq.{succ u2} α (Function.invFunOn.{u2, u1} α β _inst_1 f s b) (Classical.choice.{succ u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align function.inv_fun_on_neg Function.invFunOn_negₓ'. -/
theorem invFunOn_neg (h : ¬∃ a ∈ s, f a = b) : invFunOn f s b = Classical.choice ‹Nonempty α› := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_neg h]
#align function.inv_fun_on_neg Function.invFunOn_neg

/- warning: function.inv_fun_on_apply_mem -> Function.invFunOn_apply_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α] {s : Set.{u1} α} {f : α -> β} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Function.invFunOn.{u1, u2} α β _inst_1 f s (f a)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α] {s : Set.{u2} α} {f : α -> β} {a : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Function.invFunOn.{u2, u1} α β _inst_1 f s (f a)) s)
Case conversion may be inaccurate. Consider using '#align function.inv_fun_on_apply_mem Function.invFunOn_apply_memₓ'. -/
@[simp]
theorem invFunOn_apply_mem (h : a ∈ s) : invFunOn f s (f a) ∈ s :=
  invFunOn_mem ⟨a, h, rfl⟩
#align function.inv_fun_on_apply_mem Function.invFunOn_apply_mem

/- warning: function.inv_fun_on_apply_eq -> Function.invFunOn_apply_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α] {s : Set.{u1} α} {f : α -> β} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u2} β (f (Function.invFunOn.{u1, u2} α β _inst_1 f s (f a))) (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α] {s : Set.{u2} α} {f : α -> β} {a : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Eq.{succ u1} β (f (Function.invFunOn.{u2, u1} α β _inst_1 f s (f a))) (f a))
Case conversion may be inaccurate. Consider using '#align function.inv_fun_on_apply_eq Function.invFunOn_apply_eqₓ'. -/
theorem invFunOn_apply_eq (h : a ∈ s) : f (invFunOn f s (f a)) = f a :=
  invFunOn_eq ⟨a, h, rfl⟩
#align function.inv_fun_on_apply_eq Function.invFunOn_apply_eq

end Function

open Function

namespace Set

variable {s s₁ s₂ : Set α} {t : Set β} {f : α → β}

/- warning: set.inj_on.left_inv_on_inv_fun_on -> Set.InjOn.leftInvOn_invFunOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} [_inst_1 : Nonempty.{succ u1} α], (Set.InjOn.{u1, u2} α β f s) -> (Set.LeftInvOn.{u1, u2} α β (Function.invFunOn.{u1, u2} α β _inst_1 f s) f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} [_inst_1 : Nonempty.{succ u2} α], (Set.InjOn.{u2, u1} α β f s) -> (Set.LeftInvOn.{u2, u1} α β (Function.invFunOn.{u2, u1} α β _inst_1 f s) f s)
Case conversion may be inaccurate. Consider using '#align set.inj_on.left_inv_on_inv_fun_on Set.InjOn.leftInvOn_invFunOnₓ'. -/
theorem InjOn.leftInvOn_invFunOn [Nonempty α] (h : InjOn f s) : LeftInvOn (invFunOn f s) f s :=
  fun a ha => h (invFunOn_apply_mem ha) ha (invFunOn_apply_eq ha)
#align set.inj_on.left_inv_on_inv_fun_on Set.InjOn.leftInvOn_invFunOn

/- warning: set.inj_on.inv_fun_on_image -> Set.InjOn.invFunOn_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {f : α -> β} [_inst_1 : Nonempty.{succ u1} α], (Set.InjOn.{u1, u2} α β f s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (Function.invFunOn.{u1, u2} α β _inst_1 f s₂) (Set.image.{u1, u2} α β f s₁)) s₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {f : α -> β} [_inst_1 : Nonempty.{succ u2} α], (Set.InjOn.{u2, u1} α β f s₂) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s₂) -> (Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (Function.invFunOn.{u2, u1} α β _inst_1 f s₂) (Set.image.{u2, u1} α β f s₁)) s₁)
Case conversion may be inaccurate. Consider using '#align set.inj_on.inv_fun_on_image Set.InjOn.invFunOn_imageₓ'. -/
theorem InjOn.invFunOn_image [Nonempty α] (h : InjOn f s₂) (ht : s₁ ⊆ s₂) :
    invFunOn f s₂ '' (f '' s₁) = s₁ :=
  h.left_inv_on_inv_fun_on.image_image' ht
#align set.inj_on.inv_fun_on_image Set.InjOn.invFunOn_image

/- warning: set.surj_on.right_inv_on_inv_fun_on -> Set.SurjOn.rightInvOn_invFunOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} [_inst_1 : Nonempty.{succ u1} α], (Set.SurjOn.{u1, u2} α β f s t) -> (Set.RightInvOn.{u1, u2} α β (Function.invFunOn.{u1, u2} α β _inst_1 f s) f t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} [_inst_1 : Nonempty.{succ u2} α], (Set.SurjOn.{u2, u1} α β f s t) -> (Set.RightInvOn.{u2, u1} α β (Function.invFunOn.{u2, u1} α β _inst_1 f s) f t)
Case conversion may be inaccurate. Consider using '#align set.surj_on.right_inv_on_inv_fun_on Set.SurjOn.rightInvOn_invFunOnₓ'. -/
theorem SurjOn.rightInvOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    RightInvOn (invFunOn f s) f t := fun y hy => inv_fun_on_eq <| mem_image_iff_bex.1 <| h hy
#align set.surj_on.right_inv_on_inv_fun_on Set.SurjOn.rightInvOn_invFunOn

/- warning: set.bij_on.inv_on_inv_fun_on -> Set.BijOn.invOn_invFunOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} [_inst_1 : Nonempty.{succ u1} α], (Set.BijOn.{u1, u2} α β f s t) -> (Set.InvOn.{u1, u2} α β (Function.invFunOn.{u1, u2} α β _inst_1 f s) f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} [_inst_1 : Nonempty.{succ u2} α], (Set.BijOn.{u2, u1} α β f s t) -> (Set.InvOn.{u2, u1} α β (Function.invFunOn.{u2, u1} α β _inst_1 f s) f s t)
Case conversion may be inaccurate. Consider using '#align set.bij_on.inv_on_inv_fun_on Set.BijOn.invOn_invFunOnₓ'. -/
theorem BijOn.invOn_invFunOn [Nonempty α] (h : BijOn f s t) : InvOn (invFunOn f s) f s t :=
  ⟨h.InjOn.left_inv_on_inv_fun_on, h.SurjOn.right_inv_on_inv_fun_on⟩
#align set.bij_on.inv_on_inv_fun_on Set.BijOn.invOn_invFunOn

/- warning: set.surj_on.inv_on_inv_fun_on -> Set.SurjOn.invOn_invFunOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} [_inst_1 : Nonempty.{succ u1} α], (Set.SurjOn.{u1, u2} α β f s t) -> (Set.InvOn.{u1, u2} α β (Function.invFunOn.{u1, u2} α β _inst_1 f s) f (Set.image.{u2, u1} β α (Function.invFunOn.{u1, u2} α β _inst_1 f s) t) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} [_inst_1 : Nonempty.{succ u2} α], (Set.SurjOn.{u2, u1} α β f s t) -> (Set.InvOn.{u2, u1} α β (Function.invFunOn.{u2, u1} α β _inst_1 f s) f (Set.image.{u1, u2} β α (Function.invFunOn.{u2, u1} α β _inst_1 f s) t) t)
Case conversion may be inaccurate. Consider using '#align set.surj_on.inv_on_inv_fun_on Set.SurjOn.invOn_invFunOnₓ'. -/
theorem SurjOn.invOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    InvOn (invFunOn f s) f (invFunOn f s '' t) t :=
  by
  refine' ⟨_, h.right_inv_on_inv_fun_on⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.right_inv_on_inv_fun_on hy]
#align set.surj_on.inv_on_inv_fun_on Set.SurjOn.invOn_invFunOn

/- warning: set.surj_on.maps_to_inv_fun_on -> Set.SurjOn.mapsTo_invFunOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} [_inst_1 : Nonempty.{succ u1} α], (Set.SurjOn.{u1, u2} α β f s t) -> (Set.MapsTo.{u2, u1} β α (Function.invFunOn.{u1, u2} α β _inst_1 f s) t s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} [_inst_1 : Nonempty.{succ u2} α], (Set.SurjOn.{u2, u1} α β f s t) -> (Set.MapsTo.{u1, u2} β α (Function.invFunOn.{u2, u1} α β _inst_1 f s) t s)
Case conversion may be inaccurate. Consider using '#align set.surj_on.maps_to_inv_fun_on Set.SurjOn.mapsTo_invFunOnₓ'. -/
theorem SurjOn.mapsTo_invFunOn [Nonempty α] (h : SurjOn f s t) : MapsTo (invFunOn f s) t s :=
  fun y hy => mem_preimage.2 <| inv_fun_on_mem <| mem_image_iff_bex.1 <| h hy
#align set.surj_on.maps_to_inv_fun_on Set.SurjOn.mapsTo_invFunOn

/- warning: set.surj_on.bij_on_subset -> Set.SurjOn.bijOn_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} [_inst_1 : Nonempty.{succ u1} α], (Set.SurjOn.{u1, u2} α β f s t) -> (Set.BijOn.{u1, u2} α β f (Set.image.{u2, u1} β α (Function.invFunOn.{u1, u2} α β _inst_1 f s) t) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} [_inst_1 : Nonempty.{succ u2} α], (Set.SurjOn.{u2, u1} α β f s t) -> (Set.BijOn.{u2, u1} α β f (Set.image.{u1, u2} β α (Function.invFunOn.{u2, u1} α β _inst_1 f s) t) t)
Case conversion may be inaccurate. Consider using '#align set.surj_on.bij_on_subset Set.SurjOn.bijOn_subsetₓ'. -/
theorem SurjOn.bijOn_subset [Nonempty α] (h : SurjOn f s t) : BijOn f (invFunOn f s '' t) t :=
  by
  refine' h.inv_on_inv_fun_on.bij_on _ (maps_to_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.right_inv_on_inv_fun_on hy]
#align set.surj_on.bij_on_subset Set.SurjOn.bijOn_subset

/- warning: set.surj_on_iff_exists_bij_on_subset -> Set.surjOn_iff_exists_bijOn_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, Iff (Set.SurjOn.{u1, u2} α β f s t) (Exists.{succ u1} (Set.{u1} α) (fun (s' : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s' s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s' s) => Set.BijOn.{u1, u2} α β f s' t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, Iff (Set.SurjOn.{u2, u1} α β f s t) (Exists.{succ u2} (Set.{u2} α) (fun (s' : Set.{u2} α) => Exists.{0} (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s' s) (fun (H : HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s' s) => Set.BijOn.{u2, u1} α β f s' t)))
Case conversion may be inaccurate. Consider using '#align set.surj_on_iff_exists_bij_on_subset Set.surjOn_iff_exists_bijOn_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (s' «expr ⊆ » s) -/
theorem surjOn_iff_exists_bijOn_subset : SurjOn f s t ↔ ∃ (s' : _)(_ : s' ⊆ s), BijOn f s' t :=
  by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bij_on_empty f⟩
    · intro h
      haveI : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.maps_to_inv_fun_on.image_subset, h.bij_on_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surj_on.mono hs' (subset.refl _)
#align set.surj_on_iff_exists_bij_on_subset Set.surjOn_iff_exists_bijOn_subset

/- warning: set.preimage_inv_fun_of_mem -> Set.preimage_invFun_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [n : Nonempty.{succ u1} α] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Classical.choice.{succ u1} α n) s) -> (Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u1} β α (Function.invFun.{succ u1, succ u2} α β n f) s) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.image.{u1, u2} α β f s) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [n : Nonempty.{succ u2} α] {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {s : Set.{u2} α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Classical.choice.{succ u2} α n) s) -> (Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, u2} β α (Function.invFun.{succ u2, succ u1} α β n f) s) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet_1.{u1} β) (Set.image.{u2, u1} α β f s) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) (Set.range.{u1, succ u2} β α f)))))
Case conversion may be inaccurate. Consider using '#align set.preimage_inv_fun_of_mem Set.preimage_invFun_of_memₓ'. -/
theorem preimage_invFun_of_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∈ s) : invFun f ⁻¹' s = f '' s ∪ range fᶜ :=
  by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · simp [left_inverse_inv_fun hf _, hf.mem_set_image]
  · simp [mem_preimage, inv_fun_neg hx, h, hx]
#align set.preimage_inv_fun_of_mem Set.preimage_invFun_of_mem

/- warning: set.preimage_inv_fun_of_not_mem -> Set.preimage_invFun_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [n : Nonempty.{succ u1} α] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {s : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Classical.choice.{succ u1} α n) s)) -> (Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u1} β α (Function.invFun.{succ u1, succ u2} α β n f) s) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [n : Nonempty.{succ u2} α] {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {s : Set.{u2} α}, (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Classical.choice.{succ u2} α n) s)) -> (Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, u2} β α (Function.invFun.{succ u2, succ u1} α β n f) s) (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.preimage_inv_fun_of_not_mem Set.preimage_invFun_of_not_memₓ'. -/
theorem preimage_invFun_of_not_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s :=
  by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, left_inverse_inv_fun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, inv_fun_neg hx, h, this]
#align set.preimage_inv_fun_of_not_mem Set.preimage_invFun_of_not_mem

end Set

/-! ### Monotone -/


namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β}

/- warning: monotone.restrict -> Monotone.restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u1} α), Monotone.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.preorder.{u1} α _inst_1 (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) _inst_2 (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u2} α), Monotone.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.preorder.{u2} α _inst_1 (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) _inst_2 (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f))
Case conversion may be inaccurate. Consider using '#align monotone.restrict Monotone.restrictₓ'. -/
protected theorem restrict (h : Monotone f) (s : Set α) : Monotone (s.restrict f) := fun x y hxy =>
  h hxy
#align monotone.restrict Monotone.restrict

/- warning: monotone.cod_restrict -> Monotone.codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u2} β} (hs : forall (x : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) s), Monotone.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 (Subtype.preorder.{u2} β _inst_2 (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)) (Set.codRestrict.{u2, succ u1} β α f s hs))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u1} β} (hs : forall (x : α), Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) s), Monotone.{u2, u1} α (Set.Elem.{u1} β s) _inst_1 (Subtype.preorder.{u1} β _inst_2 (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s)) (Set.codRestrict.{u1, u2} β α f s hs))
Case conversion may be inaccurate. Consider using '#align monotone.cod_restrict Monotone.codRestrictₓ'. -/
protected theorem codRestrict (h : Monotone f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    Monotone (s.codRestrict f hs) :=
  h
#align monotone.cod_restrict Monotone.codRestrict

/- warning: monotone.range_factorization -> Monotone.rangeFactorization is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) _inst_1 (Subtype.preorder.{u2} β _inst_2 (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, succ u1} β α f))) (Set.rangeFactorization.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f)) _inst_1 (Subtype.preorder.{u1} β _inst_2 (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.range.{u1, succ u2} β α f))) (Set.rangeFactorization.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align monotone.range_factorization Monotone.rangeFactorizationₓ'. -/
protected theorem rangeFactorization (h : Monotone f) : Monotone (Set.rangeFactorization f) :=
  h
#align monotone.range_factorization Monotone.rangeFactorization

end Monotone

/-! ### Piecewise defined function -/


namespace Set

variable {δ : α → Sort y} (s : Set α) (f g : ∀ i, δ i)

#print Set.piecewise_empty /-
@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Set α))] : piecewise ∅ f g = g :=
  by
  ext i
  simp [piecewise]
#align set.piecewise_empty Set.piecewise_empty
-/

#print Set.piecewise_univ /-
@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (Set.univ : Set α))] : piecewise Set.univ f g = f :=
  by
  ext i
  simp [piecewise]
#align set.piecewise_univ Set.piecewise_univ
-/

#print Set.piecewise_insert_self /-
@[simp]
theorem piecewise_insert_self {j : α} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]
#align set.piecewise_insert_self Set.piecewise_insert_self
-/

variable [∀ j, Decidable (j ∈ s)]

/- warning: set.compl.decidable_mem -> Set.Compl.decidableMem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s)] (j : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align set.compl.decidable_mem Set.Compl.decidableMemₓ'. -/
instance Compl.decidableMem (j : α) : Decidable (j ∈ sᶜ) :=
  Not.decidable
#align set.compl.decidable_mem Set.Compl.decidableMem

#print Set.piecewise_insert /-
theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j) :=
  by
  simp [piecewise]
  ext i
  by_cases h : i = j
  · rw [h]
    simp
  · by_cases h' : i ∈ s <;> simp [h, h']
#align set.piecewise_insert Set.piecewise_insert
-/

#print Set.piecewise_eq_of_mem /-
@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
  if_pos hi
#align set.piecewise_eq_of_mem Set.piecewise_eq_of_mem
-/

#print Set.piecewise_eq_of_not_mem /-
@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
  if_neg hi
#align set.piecewise_eq_of_not_mem Set.piecewise_eq_of_not_mem
-/

/- warning: set.piecewise_singleton -> Set.piecewise_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (x : α) [_inst_2 : forall (y : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))] [_inst_3 : DecidableEq.{succ u1} α] (f : α -> β) (g : α -> β), Eq.{max (succ u1) (succ u2)} (α -> β) (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) f g (fun (j : α) => _inst_2 j)) (Function.update.{succ u1, succ u2} α (fun (i : α) => β) (fun (a : α) (b : α) => _inst_3 a b) g x (f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (x : α) [_inst_2 : forall (y : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x))] [_inst_3 : DecidableEq.{succ u2} α] (f : α -> β) (g : α -> β), Eq.{max (succ u2) (succ u1)} (α -> β) (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x) f g (fun (j : α) => _inst_2 j)) (Function.update.{succ u2, succ u1} α (fun (i : α) => β) (fun (a : α) (b : α) => _inst_3 a b) g x (f x))
Case conversion may be inaccurate. Consider using '#align set.piecewise_singleton Set.piecewise_singletonₓ'. -/
theorem piecewise_singleton (x : α) [∀ y, Decidable (y ∈ ({x} : Set α))] [DecidableEq α]
    (f g : α → β) : piecewise {x} f g = Function.update g x (f x) :=
  by
  ext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy]
#align set.piecewise_singleton Set.piecewise_singleton

/- warning: set.piecewise_eq_on -> Set.piecewise_eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] (f : α -> β) (g : α -> β), Set.EqOn.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j)) f s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j s)] (f : α -> β) (g : α -> β), Set.EqOn.{u2, u1} α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j)) f s
Case conversion may be inaccurate. Consider using '#align set.piecewise_eq_on Set.piecewise_eqOnₓ'. -/
theorem piecewise_eqOn (f g : α → β) : EqOn (s.piecewise f g) f s := fun _ =>
  piecewise_eq_of_mem _ _ _
#align set.piecewise_eq_on Set.piecewise_eqOn

/- warning: set.piecewise_eq_on_compl -> Set.piecewise_eqOn_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] (f : α -> β) (g : α -> β), Set.EqOn.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j)) g (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j s)] (f : α -> β) (g : α -> β), Set.EqOn.{u2, u1} α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j)) g (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)
Case conversion may be inaccurate. Consider using '#align set.piecewise_eq_on_compl Set.piecewise_eqOn_complₓ'. -/
theorem piecewise_eqOn_compl (f g : α → β) : EqOn (s.piecewise f g) g (sᶜ) := fun _ =>
  piecewise_eq_of_not_mem _ _ _
#align set.piecewise_eq_on_compl Set.piecewise_eqOn_compl

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (i «expr ∉ » s) -/
#print Set.piecewise_le /-
theorem piecewise_le {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g i) (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ≤ g i) :
    s.piecewise f₁ f₂ ≤ g := fun i => if h : i ∈ s then by simp [*] else by simp [*]
#align set.piecewise_le Set.piecewise_le
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (i «expr ∉ » s) -/
#print Set.le_piecewise /-
theorem le_piecewise {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, g i ≤ f₁ i) (h₂ : ∀ (i) (_ : i ∉ s), g i ≤ f₂ i) :
    g ≤ s.piecewise f₁ f₂ :=
  @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂
#align set.le_piecewise Set.le_piecewise
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (i «expr ∉ » s) -/
#print Set.piecewise_le_piecewise /-
theorem piecewise_le_piecewise {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α}
    [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g₁ i)
    (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ≤ g₂ i) : s.piecewise f₁ f₂ ≤ s.piecewise g₁ g₂ := by
  apply piecewise_le <;> intros <;> simp [*]
#align set.piecewise_le_piecewise Set.piecewise_le_piecewise
-/

#print Set.piecewise_insert_of_ne /-
@[simp]
theorem piecewise_insert_of_ne {i j : α} (h : i ≠ j) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]
#align set.piecewise_insert_of_ne Set.piecewise_insert_of_ne
-/

/- warning: set.piecewise_compl -> Set.piecewise_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] [_inst_2 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))], Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Set.piecewise.{u1, u2} α (fun (i : α) => δ i) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f g (fun (j : α) => _inst_2 j)) (Set.piecewise.{u1, u2} α (fun (i : α) => δ i) s g f (fun (j : α) => _inst_1 j))
but is expected to have type
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s)] [_inst_2 : forall (i : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))], Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Set.piecewise.{u1, u2} α (fun (i : α) => δ i) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) f g (fun (j : α) => _inst_2 j)) (Set.piecewise.{u1, u2} α (fun (i : α) => δ i) s g f (fun (j : α) => _inst_1 j))
Case conversion may be inaccurate. Consider using '#align set.piecewise_compl Set.piecewise_complₓ'. -/
@[simp]
theorem piecewise_compl [∀ i, Decidable (i ∈ sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
  funext fun x => if hx : x ∈ s then by simp [hx] else by simp [hx]
#align set.piecewise_compl Set.piecewise_compl

/- warning: set.piecewise_range_comp -> Set.piecewise_range_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} (f : ι -> α) [_inst_2 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j (Set.range.{u1, u3} α ι f))] (g₁ : α -> β) (g₂ : α -> β), Eq.{max u3 (succ u2)} (ι -> β) (Function.comp.{u3, succ u1, succ u2} ι α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) (Set.range.{u1, u3} α ι f) g₁ g₂ (fun (j : α) => _inst_2 j)) f) (Function.comp.{u3, succ u1, succ u2} ι α β g₁ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} (f : ι -> α) [_inst_2 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j (Set.range.{u2, u3} α ι f))] (g₁ : α -> β) (g₂ : α -> β), Eq.{max (succ u1) u3} (ι -> β) (Function.comp.{u3, succ u2, succ u1} ι α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) (Set.range.{u2, u3} α ι f) g₁ g₂ (fun (j : α) => _inst_2 j)) f) (Function.comp.{u3, succ u2, succ u1} ι α β g₁ f)
Case conversion may be inaccurate. Consider using '#align set.piecewise_range_comp Set.piecewise_range_compₓ'. -/
@[simp]
theorem piecewise_range_comp {ι : Sort _} (f : ι → α) [∀ j, Decidable (j ∈ range f)]
    (g₁ g₂ : α → β) : (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
  eq_on.comp_eq <| piecewise_eqOn _ _ _
#align set.piecewise_range_comp Set.piecewise_range_comp

/- warning: set.maps_to.piecewise_ite -> Set.MapsTo.piecewise_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {f₁ : α -> β} {f₂ : α -> β} [_inst_2 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s)], (Set.MapsTo.{u1, u2} α β f₁ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t)) -> (Set.MapsTo.{u1, u2} α β f₂ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₂ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₂ (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t))) -> (Set.MapsTo.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f₁ f₂ (fun (j : α) => _inst_2 j)) (Set.ite.{u1} α s s₁ s₂) (Set.ite.{u2} β t t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β} {f₁ : α -> β} {f₂ : α -> β} [_inst_2 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s)], (Set.MapsTo.{u2, u1} α β f₁ (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t)) -> (Set.MapsTo.{u2, u1} α β f₂ (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₂ (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₂ (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) t))) -> (Set.MapsTo.{u2, u1} α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f₁ f₂ (fun (j : α) => _inst_2 j)) (Set.ite.{u2} α s s₁ s₂) (Set.ite.{u1} β t t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.maps_to.piecewise_ite Set.MapsTo.piecewise_iteₓ'. -/
theorem MapsTo.piecewise_ite {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α → β}
    [∀ i, Decidable (i ∈ s)] (h₁ : MapsTo f₁ (s₁ ∩ s) (t₁ ∩ t))
    (h₂ : MapsTo f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ)) : MapsTo (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) :=
  by
  refine' (h₁.congr _).union_union (h₂.congr _)
  exacts[(piecewise_eq_on s f₁ f₂).symm.mono (inter_subset_right _ _),
    (piecewise_eq_on_compl s f₁ f₂).symm.mono (inter_subset_right _ _)]
#align set.maps_to.piecewise_ite Set.MapsTo.piecewise_ite

/- warning: set.eq_on_piecewise -> Set.eqOn_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] {f : α -> β} {f' : α -> β} {g : α -> β} {t : Set.{u1} α}, Iff (Set.EqOn.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f f' (fun (j : α) => _inst_1 j)) g t) (And (Set.EqOn.{u1, u2} α β f g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (Set.EqOn.{u1, u2} α β f' g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j s)] {f : α -> β} {f' : α -> β} {g : α -> β} {t : Set.{u2} α}, Iff (Set.EqOn.{u2, u1} α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f f' (fun (j : α) => _inst_1 j)) g t) (And (Set.EqOn.{u2, u1} α β f g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) t s)) (Set.EqOn.{u2, u1} α β f' g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) t (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s))))
Case conversion may be inaccurate. Consider using '#align set.eq_on_piecewise Set.eqOn_piecewiseₓ'. -/
theorem eqOn_piecewise {f f' g : α → β} {t} :
    EqOn (s.piecewise f f') g t ↔ EqOn f g (t ∩ s) ∧ EqOn f' g (t ∩ sᶜ) :=
  by
  simp only [eq_on, ← forall_and]
  refine' forall_congr' fun a => _; by_cases a ∈ s <;> simp [*]
#align set.eq_on_piecewise Set.eqOn_piecewise

/- warning: set.eq_on.piecewise_ite' -> Set.EqOn.piecewise_ite' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] {f : α -> β} {f' : α -> β} {g : α -> β} {t : Set.{u1} α} {t' : Set.{u1} α}, (Set.EqOn.{u1, u2} α β f g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) -> (Set.EqOn.{u1, u2} α β f' g (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t' (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) -> (Set.EqOn.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f f' (fun (j : α) => _inst_1 j)) g (Set.ite.{u1} α s t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j s)] {f : α -> β} {f' : α -> β} {g : α -> β} {t : Set.{u2} α} {t' : Set.{u2} α}, (Set.EqOn.{u2, u1} α β f g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) t s)) -> (Set.EqOn.{u2, u1} α β f' g (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) t' (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s))) -> (Set.EqOn.{u2, u1} α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f f' (fun (j : α) => _inst_1 j)) g (Set.ite.{u2} α s t t'))
Case conversion may be inaccurate. Consider using '#align set.eq_on.piecewise_ite' Set.EqOn.piecewise_ite'ₓ'. -/
theorem EqOn.piecewise_ite' {f f' g : α → β} {t t'} (h : EqOn f g (t ∩ s))
    (h' : EqOn f' g (t' ∩ sᶜ)) : EqOn (s.piecewise f f') g (s.ite t t') := by
  simp [eq_on_piecewise, *]
#align set.eq_on.piecewise_ite' Set.EqOn.piecewise_ite'

/- warning: set.eq_on.piecewise_ite -> Set.EqOn.piecewise_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] {f : α -> β} {f' : α -> β} {g : α -> β} {t : Set.{u1} α} {t' : Set.{u1} α}, (Set.EqOn.{u1, u2} α β f g t) -> (Set.EqOn.{u1, u2} α β f' g t') -> (Set.EqOn.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f f' (fun (j : α) => _inst_1 j)) g (Set.ite.{u1} α s t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j s)] {f : α -> β} {f' : α -> β} {g : α -> β} {t : Set.{u2} α} {t' : Set.{u2} α}, (Set.EqOn.{u2, u1} α β f g t) -> (Set.EqOn.{u2, u1} α β f' g t') -> (Set.EqOn.{u2, u1} α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f f' (fun (j : α) => _inst_1 j)) g (Set.ite.{u2} α s t t'))
Case conversion may be inaccurate. Consider using '#align set.eq_on.piecewise_ite Set.EqOn.piecewise_iteₓ'. -/
theorem EqOn.piecewise_ite {f f' g : α → β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t') :
    EqOn (s.piecewise f f') g (s.ite t t') :=
  (h.mono (inter_subset_left _ _)).piecewise_ite' s (h'.mono (inter_subset_left _ _))
#align set.eq_on.piecewise_ite Set.EqOn.piecewise_ite

#print Set.piecewise_preimage /-
theorem piecewise_preimage (f g : α → β) (t) : s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
  ext fun x => by by_cases x ∈ s <;> simp [*, Set.ite]
#align set.piecewise_preimage Set.piecewise_preimage
-/

/- warning: set.apply_piecewise -> Set.apply_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] {δ' : α -> Sort.{u3}} (h : forall (i : α), (δ i) -> (δ' i)) {x : α}, Eq.{u3} (δ' x) (h x (Set.piecewise.{u1, u2} α δ s f g (fun (j : α) => _inst_1 j) x)) (Set.piecewise.{u1, u3} α δ' s (fun (x : α) => h x (f x)) (fun (x : α) => h x (g x)) (fun (j : α) => _inst_1 j) x)
but is expected to have type
  forall {α : Type.{u1}} {δ : α -> Sort.{u3}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s)] {δ' : α -> Sort.{u2}} (h : forall (i : α), (δ i) -> (δ' i)) {x : α}, Eq.{u2} (δ' x) (h x (Set.piecewise.{u1, u3} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) x)) (Set.piecewise.{u1, u2} α (fun (x : α) => δ' x) s (fun (x : α) => h x (f x)) (fun (x : α) => h x (g x)) (fun (j : α) => _inst_1 j) x)
Case conversion may be inaccurate. Consider using '#align set.apply_piecewise Set.apply_piecewiseₓ'. -/
theorem apply_piecewise {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) {x : α} :
    h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x := by
  by_cases hx : x ∈ s <;> simp [hx]
#align set.apply_piecewise Set.apply_piecewise

/- warning: set.apply_piecewise₂ -> Set.apply_piecewise₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] {δ' : α -> Sort.{u3}} {δ'' : α -> Sort.{u4}} (f' : forall (i : α), δ' i) (g' : forall (i : α), δ' i) (h : forall (i : α), (δ i) -> (δ' i) -> (δ'' i)) {x : α}, Eq.{u4} (δ'' x) (h x (Set.piecewise.{u1, u2} α δ s f g (fun (j : α) => _inst_1 j) x) (Set.piecewise.{u1, u3} α δ' s f' g' (fun (j : α) => _inst_1 j) x)) (Set.piecewise.{u1, u4} α δ'' s (fun (x : α) => h x (f x) (f' x)) (fun (x : α) => h x (g x) (g' x)) (fun (j : α) => _inst_1 j) x)
but is expected to have type
  forall {α : Type.{u1}} {δ : α -> Sort.{u4}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s)] {δ' : α -> Sort.{u3}} {δ'' : α -> Sort.{u2}} (f' : forall (i : α), δ' i) (g' : forall (i : α), δ' i) (h : forall (i : α), (δ i) -> (δ' i) -> (δ'' i)) {x : α}, Eq.{u2} (δ'' x) (h x (Set.piecewise.{u1, u4} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) x) (Set.piecewise.{u1, u3} α (fun (i : α) => δ' i) s f' g' (fun (j : α) => _inst_1 j) x)) (Set.piecewise.{u1, u2} α (fun (x : α) => δ'' x) s (fun (x : α) => h x (f x) (f' x)) (fun (x : α) => h x (g x) (g' x)) (fun (j : α) => _inst_1 j) x)
Case conversion may be inaccurate. Consider using '#align set.apply_piecewise₂ Set.apply_piecewise₂ₓ'. -/
theorem apply_piecewise₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i)
    {x : α} :
    h x (s.piecewise f g x) (s.piecewise f' g' x) =
      s.piecewise (fun x => h x (f x) (f' x)) (fun x => h x (g x) (g' x)) x :=
  by by_cases hx : x ∈ s <;> simp [hx]
#align set.apply_piecewise₂ Set.apply_piecewise₂

/- warning: set.piecewise_op -> Set.piecewise_op is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] {δ' : α -> Sort.{u3}} (h : forall (i : α), (δ i) -> (δ' i)), Eq.{imax (succ u1) u3} (forall (i : α), δ' i) (Set.piecewise.{u1, u3} α (fun (x : α) => δ' x) s (fun (x : α) => h x (f x)) (fun (x : α) => h x (g x)) (fun (j : α) => _inst_1 j)) (fun (x : α) => h x (Set.piecewise.{u1, u2} α δ s f g (fun (j : α) => _inst_1 j) x))
but is expected to have type
  forall {α : Type.{u1}} {δ : α -> Sort.{u3}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s)] {δ' : α -> Sort.{u2}} (h : forall (i : α), (δ i) -> (δ' i)), Eq.{imax (succ u1) u2} (forall (i : α), δ' i) (Set.piecewise.{u1, u2} α (fun (x : α) => δ' x) s (fun (x : α) => h x (f x)) (fun (x : α) => h x (g x)) (fun (j : α) => _inst_1 j)) (fun (x : α) => h x (Set.piecewise.{u1, u3} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) x))
Case conversion may be inaccurate. Consider using '#align set.piecewise_op Set.piecewise_opₓ'. -/
theorem piecewise_op {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) :
    (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x) :=
  funext fun x => (apply_piecewise _ _ _ _).symm
#align set.piecewise_op Set.piecewise_op

/- warning: set.piecewise_op₂ -> Set.piecewise_op₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] {δ' : α -> Sort.{u3}} {δ'' : α -> Sort.{u4}} (f' : forall (i : α), δ' i) (g' : forall (i : α), δ' i) (h : forall (i : α), (δ i) -> (δ' i) -> (δ'' i)), Eq.{imax (succ u1) u4} (forall (i : α), δ'' i) (Set.piecewise.{u1, u4} α (fun (x : α) => δ'' x) s (fun (x : α) => h x (f x) (f' x)) (fun (x : α) => h x (g x) (g' x)) (fun (j : α) => _inst_1 j)) (fun (x : α) => h x (Set.piecewise.{u1, u2} α δ s f g (fun (j : α) => _inst_1 j) x) (Set.piecewise.{u1, u3} α δ' s f' g' (fun (j : α) => _inst_1 j) x))
but is expected to have type
  forall {α : Type.{u1}} {δ : α -> Sort.{u4}} (s : Set.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s)] {δ' : α -> Sort.{u3}} {δ'' : α -> Sort.{u2}} (f' : forall (i : α), δ' i) (g' : forall (i : α), δ' i) (h : forall (i : α), (δ i) -> (δ' i) -> (δ'' i)), Eq.{imax (succ u1) u2} (forall (i : α), δ'' i) (Set.piecewise.{u1, u2} α (fun (x : α) => δ'' x) s (fun (x : α) => h x (f x) (f' x)) (fun (x : α) => h x (g x) (g' x)) (fun (j : α) => _inst_1 j)) (fun (x : α) => h x (Set.piecewise.{u1, u4} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) x) (Set.piecewise.{u1, u3} α (fun (i : α) => δ' i) s f' g' (fun (j : α) => _inst_1 j) x))
Case conversion may be inaccurate. Consider using '#align set.piecewise_op₂ Set.piecewise_op₂ₓ'. -/
theorem piecewise_op₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) :
    (s.piecewise (fun x => h x (f x) (f' x)) fun x => h x (g x) (g' x)) = fun x =>
      h x (s.piecewise f g x) (s.piecewise f' g' x) :=
  funext fun x => (apply_piecewise₂ _ _ _ _ _ _).symm
#align set.piecewise_op₂ Set.piecewise_op₂

#print Set.piecewise_same /-
@[simp]
theorem piecewise_same : s.piecewise f f = f :=
  by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]
#align set.piecewise_same Set.piecewise_same
-/

/- warning: set.range_piecewise -> Set.range_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] (f : α -> β) (g : α -> β), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β α (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β g (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s)] (f : α -> β) (g : α -> β), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β α (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j))) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet_1.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β g (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)))
Case conversion may be inaccurate. Consider using '#align set.range_piecewise Set.range_piecewiseₓ'. -/
theorem range_piecewise (f g : α → β) : range (s.piecewise f g) = f '' s ∪ g '' sᶜ :=
  by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    by_cases h : x ∈ s <;> [left, right] <;> use x <;> simp [h]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all
#align set.range_piecewise Set.range_piecewise

/- warning: set.injective_piecewise_iff -> Set.injective_piecewise_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)] {f : α -> β} {g : α -> β}, Iff (Function.Injective.{succ u1, succ u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j))) (And (Set.InjOn.{u1, u2} α β f s) (And (Set.InjOn.{u1, u2} α β g (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s)) -> (Ne.{succ u2} β (f x) (g y))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j s)] {f : α -> β} {g : α -> β}, Iff (Function.Injective.{succ u2, succ u1} α β (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j))) (And (Set.InjOn.{u2, u1} α β f s) (And (Set.InjOn.{u2, u1} α β g (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (y : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s)) -> (Ne.{succ u1} β (f x) (g y))))))
Case conversion may be inaccurate. Consider using '#align set.injective_piecewise_iff Set.injective_piecewise_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (y «expr ∉ » s) -/
theorem injective_piecewise_iff {f g : α → β} :
    Injective (s.piecewise f g) ↔
      InjOn f s ∧ InjOn g (sᶜ) ∧ ∀ x ∈ s, ∀ (y) (_ : y ∉ s), f x ≠ g y :=
  by
  rw [injective_iff_inj_on_univ, ← union_compl_self s, inj_on_union (@disjoint_compl_right _ _ s),
    (piecewise_eq_on s f g).inj_on_iff, (piecewise_eq_on_compl s f g).inj_on_iff]
  refine' and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congr fun x hx y hy => _)
  rw [piecewise_eq_of_mem s f g hx, piecewise_eq_of_not_mem s f g hy]
#align set.injective_piecewise_iff Set.injective_piecewise_iff

#print Set.piecewise_mem_pi /-
theorem piecewise_mem_pi {δ : α → Type _} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ pi t t')
    (hg : g ∈ pi t t') : s.piecewise f g ∈ pi t t' :=
  by
  intro i ht
  by_cases hs : i ∈ s <;> simp [hf i ht, hg i ht, hs]
#align set.piecewise_mem_pi Set.piecewise_mem_pi
-/

/- warning: set.pi_piecewise -> Set.pi_piecewise is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (s : Set.{u1} ι) (s' : Set.{u1} ι) (t : forall (i : ι), Set.{u2} (α i)) (t' : forall (i : ι), Set.{u2} (α i)) [_inst_2 : forall (x : ι), Decidable (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) x s')], Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s (Set.piecewise.{u1, succ u2} ι (fun (i : ι) => Set.{u2} (α i)) s' t t' (fun (j : ι) => _inst_2 j))) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInter.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Inter.inter.{u1} (Set.{u1} ι) (Set.hasInter.{u1} ι) s s') t) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (SDiff.sdiff.{u1} (Set.{u1} ι) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} ι) (Set.booleanAlgebra.{u1} ι)) s s') t'))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (s : Set.{u2} ι) (s' : Set.{u2} ι) (t : forall (i : ι), Set.{u1} (α i)) (t' : forall (i : ι), Set.{u1} (α i)) [_inst_2 : forall (x : ι), Decidable (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s')], Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s (Set.piecewise.{u2, succ u1} ι (fun (i : ι) => Set.{u1} (α i)) s' t t' (fun (j : ι) => _inst_2 j))) (Inter.inter.{max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInterSet_1.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Inter.inter.{u2} (Set.{u2} ι) (Set.instInterSet_1.{u2} ι) s s') t) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (SDiff.sdiff.{u2} (Set.{u2} ι) (Set.instSDiffSet.{u2} ι) s s') t'))
Case conversion may be inaccurate. Consider using '#align set.pi_piecewise Set.pi_piecewiseₓ'. -/
@[simp]
theorem pi_piecewise {ι : Type _} {α : ι → Type _} (s s' : Set ι) (t t' : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s')] : pi s (s'.piecewise t t') = pi (s ∩ s') t ∩ pi (s \ s') t' :=
  by
  ext x
  simp only [mem_pi, mem_inter_iff, ← forall_and]
  refine' forall_congr' fun i => _
  by_cases hi : i ∈ s' <;> simp [*]
#align set.pi_piecewise Set.pi_piecewise

/- warning: set.univ_pi_piecewise -> Set.univ_pi_piecewise is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (s : Set.{u1} ι) (t : forall (i : ι), Set.{u2} (α i)) [_inst_2 : forall (x : ι), Decidable (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) x s)], Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (Set.piecewise.{u1, succ u2} ι (fun (i : ι) => Set.{u2} (α i)) s t (fun (_x : ι) => Set.univ.{u2} (α _x)) (fun (j : ι) => _inst_2 j))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (s : Set.{u2} ι) (t : forall (i : ι), Set.{u1} (α i)) [_inst_2 : forall (x : ι), Decidable (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s)], Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (Set.piecewise.{u2, succ u1} ι (fun (i : ι) => Set.{u1} (α i)) s t (fun (_x : ι) => Set.univ.{u1} (α _x)) (fun (j : ι) => _inst_2 j))) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t)
Case conversion may be inaccurate. Consider using '#align set.univ_pi_piecewise Set.univ_pi_piecewiseₓ'. -/
theorem univ_pi_piecewise {ι : Type _} {α : ι → Type _} (s : Set ι) (t : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s)] : pi univ (s.piecewise t fun _ => univ) = pi s t := by simp
#align set.univ_pi_piecewise Set.univ_pi_piecewise

end Set

/- warning: strict_mono_on.inj_on -> StrictMonoOn.injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (StrictMonoOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 f s) -> (Set.InjOn.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (StrictMonoOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) _inst_2 f s) -> (Set.InjOn.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.inj_on StrictMonoOn.injOnₓ'. -/
theorem StrictMonoOn.injOn [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
    (H : StrictMonoOn f s) : s.InjOn f := fun x hx y hy hxy =>
  show Ordering.eq.Compares x y from (H.Compares hx hy).1 hxy
#align strict_mono_on.inj_on StrictMonoOn.injOn

/- warning: strict_anti_on.inj_on -> StrictAntiOn.injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (StrictAntiOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 f s) -> (Set.InjOn.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (StrictAntiOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) _inst_2 f s) -> (Set.InjOn.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.inj_on StrictAntiOn.injOnₓ'. -/
theorem StrictAntiOn.injOn [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
    (H : StrictAntiOn f s) : s.InjOn f :=
  @StrictMonoOn.injOn α βᵒᵈ _ _ f s H
#align strict_anti_on.inj_on StrictAntiOn.injOn

/- warning: strict_mono_on.comp -> StrictMonoOn.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (StrictMonoOn.{u2, u3} β γ _inst_2 _inst_3 g t) -> (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (StrictMonoOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {t : Set.{u2} β}, (StrictMonoOn.{u2, u1} β γ _inst_2 _inst_3 g t) -> (StrictMonoOn.{u3, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u3, u2} α β f s t) -> (StrictMonoOn.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.comp StrictMonoOn.compₓ'. -/
theorem StrictMonoOn.comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun x hx y hy hxy => hg (hs hx) (hs hy) <| hf hx hy hxy
#align strict_mono_on.comp StrictMonoOn.comp

/- warning: strict_mono_on.comp_strict_anti_on -> StrictMonoOn.comp_strictAntiOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (StrictMonoOn.{u2, u3} β γ _inst_2 _inst_3 g t) -> (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (StrictAntiOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {t : Set.{u2} β}, (StrictMonoOn.{u2, u1} β γ _inst_2 _inst_3 g t) -> (StrictAntiOn.{u3, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u3, u2} α β f s t) -> (StrictAntiOn.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.comp_strict_anti_on StrictMonoOn.comp_strictAntiOnₓ'. -/
theorem StrictMonoOn.comp_strictAntiOn [Preorder α] [Preorder β] [Preorder γ] {g : β → γ}
    {f : α → β} {s : Set α} {t : Set β} (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun x hx y hy hxy =>
  hg (hs hy) (hs hx) <| hf hx hy hxy
#align strict_mono_on.comp_strict_anti_on StrictMonoOn.comp_strictAntiOn

/- warning: strict_anti_on.comp -> StrictAntiOn.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (StrictAntiOn.{u2, u3} β γ _inst_2 _inst_3 g t) -> (StrictAntiOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (StrictMonoOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {t : Set.{u2} β}, (StrictAntiOn.{u2, u1} β γ _inst_2 _inst_3 g t) -> (StrictAntiOn.{u3, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u3, u2} α β f s t) -> (StrictMonoOn.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.comp StrictAntiOn.compₓ'. -/
theorem StrictAntiOn.comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun x hx y hy hxy => hg (hs hy) (hs hx) <| hf hx hy hxy
#align strict_anti_on.comp StrictAntiOn.comp

/- warning: strict_anti_on.comp_strict_mono_on -> StrictAntiOn.comp_strictMonoOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] {g : β -> γ} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, (StrictAntiOn.{u2, u3} β γ _inst_2 _inst_3 g t) -> (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (StrictAntiOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {g : β -> γ} {f : α -> β} {s : Set.{u3} α} {t : Set.{u2} β}, (StrictAntiOn.{u2, u1} β γ _inst_2 _inst_3 g t) -> (StrictMonoOn.{u3, u2} α β _inst_1 _inst_2 f s) -> (Set.MapsTo.{u3, u2} α β f s t) -> (StrictAntiOn.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.comp_strict_mono_on StrictAntiOn.comp_strictMonoOnₓ'. -/
theorem StrictAntiOn.comp_strictMonoOn [Preorder α] [Preorder β] [Preorder γ] {g : β → γ}
    {f : α → β} {s : Set α} {t : Set β} (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun x hx y hy hxy =>
  hg (hs hx) (hs hy) <| hf hx hy hxy
#align strict_anti_on.comp_strict_mono_on StrictAntiOn.comp_strictMonoOn

/- warning: strict_mono_restrict -> strictMono_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (StrictMono.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.preorder.{u1} α _inst_1 (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) _inst_2 (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)) (StrictMonoOn.{u1, u2} α β _inst_1 _inst_2 f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, Iff (StrictMono.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.preorder.{u2} α _inst_1 (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) _inst_2 (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)) (StrictMonoOn.{u2, u1} α β _inst_1 _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align strict_mono_restrict strictMono_restrictₓ'. -/
@[simp]
theorem strictMono_restrict [Preorder α] [Preorder β] {f : α → β} {s : Set α} :
    StrictMono (s.restrict f) ↔ StrictMonoOn f s := by simp [Set.restrict, StrictMono, StrictMonoOn]
#align strict_mono_restrict strictMono_restrict

alias strictMono_restrict ↔ _root_.strict_mono.of_restrict _root_.strict_mono_on.restrict

/- warning: strict_mono.cod_restrict -> StrictMono.codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (StrictMono.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u2} β} (hs : forall (x : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) s), StrictMono.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 (Subtype.preorder.{u2} β _inst_2 (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)) (Set.codRestrict.{u2, succ u1} β α f s hs))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (StrictMono.{u2, u1} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u1} β} (hs : forall (x : α), Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) s), StrictMono.{u2, u1} α (Set.Elem.{u1} β s) _inst_1 (Subtype.preorder.{u1} β _inst_2 (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s)) (Set.codRestrict.{u1, u2} β α f s hs))
Case conversion may be inaccurate. Consider using '#align strict_mono.cod_restrict StrictMono.codRestrictₓ'. -/
theorem StrictMono.codRestrict [Preorder α] [Preorder β] {f : α → β} (hf : StrictMono f) {s : Set β}
    (hs : ∀ x, f x ∈ s) : StrictMono (Set.codRestrict f s hs) :=
  hf
#align strict_mono.cod_restrict StrictMono.codRestrict

namespace Function

open Set

variable {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : Set α}

theorem Injective.comp_inj_on (hg : Injective g) (hf : s.InjOn f) : s.InjOn (g ∘ f) :=
  (hg.InjOn univ).comp hf (mapsTo_univ _ _)
#align function.injective.comp_inj_on Function.Injective.comp_inj_on

/- warning: function.surjective.surj_on -> Function.Surjective.surjOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u2} β), Set.SurjOn.{u1, u2} α β f (Set.univ.{u1} α) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u1} β), Set.SurjOn.{u2, u1} α β f (Set.univ.{u2} α) s)
Case conversion may be inaccurate. Consider using '#align function.surjective.surj_on Function.Surjective.surjOnₓ'. -/
theorem Surjective.surjOn (hf : Surjective f) (s : Set β) : SurjOn f univ s :=
  (surjective_iff_surjOn_univ.1 hf).mono (Subset.refl _) (subset_univ _)
#align function.surjective.surj_on Function.Surjective.surjOn

#print Function.LeftInverse.leftInvOn /-
theorem LeftInverse.leftInvOn {g : β → α} (h : LeftInverse f g) (s : Set β) : LeftInvOn f g s :=
  fun x hx => h x
#align function.left_inverse.left_inv_on Function.LeftInverse.leftInvOn
-/

#print Function.RightInverse.rightInvOn /-
theorem RightInverse.rightInvOn {g : β → α} (h : RightInverse f g) (s : Set α) : RightInvOn f g s :=
  fun x hx => h x
#align function.right_inverse.right_inv_on Function.RightInverse.rightInvOn
-/

#print Function.LeftInverse.rightInvOn_range /-
theorem LeftInverse.rightInvOn_range {g : β → α} (h : LeftInverse f g) : RightInvOn f g (range g) :=
  forall_range_iff.2 fun i => congr_arg g (h i)
#align function.left_inverse.right_inv_on_range Function.LeftInverse.rightInvOn_range
-/

namespace Semiconj

/- warning: function.semiconj.maps_to_image -> Function.Semiconj.mapsTo_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (Set.MapsTo.{u1, u1} α α fa s t) -> (Set.MapsTo.{u2, u2} β β fb (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (Set.MapsTo.{u2, u2} α α fa s t) -> (Set.MapsTo.{u1, u1} β β fb (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align function.semiconj.maps_to_image Function.Semiconj.mapsTo_imageₓ'. -/
theorem mapsTo_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f '' s) (f '' t) :=
  fun y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩
#align function.semiconj.maps_to_image Function.Semiconj.mapsTo_image

/- warning: function.semiconj.maps_to_range -> Function.Semiconj.mapsTo_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (Set.MapsTo.{u2, u2} β β fb (Set.range.{u2, succ u1} β α f) (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (Set.MapsTo.{u1, u1} β β fb (Set.range.{u1, succ u2} β α f) (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align function.semiconj.maps_to_range Function.Semiconj.mapsTo_rangeₓ'. -/
theorem mapsTo_range (h : Semiconj f fa fb) : MapsTo fb (range f) (range f) := fun y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩
#align function.semiconj.maps_to_range Function.Semiconj.mapsTo_range

/- warning: function.semiconj.surj_on_image -> Function.Semiconj.surjOn_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (Set.SurjOn.{u1, u1} α α fa s t) -> (Set.SurjOn.{u2, u2} β β fb (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (Set.SurjOn.{u2, u2} α α fa s t) -> (Set.SurjOn.{u1, u1} β β fb (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align function.semiconj.surj_on_image Function.Semiconj.surjOn_imageₓ'. -/
theorem surjOn_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f '' s) (f '' t) :=
  by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)
#align function.semiconj.surj_on_image Function.Semiconj.surjOn_image

/- warning: function.semiconj.surj_on_range -> Function.Semiconj.surjOn_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (Function.Surjective.{succ u1, succ u1} α α fa) -> (Set.SurjOn.{u2, u2} β β fb (Set.range.{u2, succ u1} β α f) (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (Function.Surjective.{succ u2, succ u2} α α fa) -> (Set.SurjOn.{u1, u1} β β fb (Set.range.{u1, succ u2} β α f) (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align function.semiconj.surj_on_range Function.Semiconj.surjOn_rangeₓ'. -/
theorem surjOn_range (h : Semiconj f fa fb) (ha : Surjective fa) : SurjOn fb (range f) (range f) :=
  by
  rw [← image_univ]
  exact h.surj_on_image (ha.surj_on univ)
#align function.semiconj.surj_on_range Function.Semiconj.surjOn_range

/- warning: function.semiconj.inj_on_image -> Function.Semiconj.injOn_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β} {s : Set.{u1} α}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (Set.InjOn.{u1, u1} α α fa s) -> (Set.InjOn.{u1, u2} α β f (Set.image.{u1, u1} α α fa s)) -> (Set.InjOn.{u2, u2} β β fb (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β} {s : Set.{u2} α}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (Set.InjOn.{u2, u2} α α fa s) -> (Set.InjOn.{u2, u1} α β f (Set.image.{u2, u2} α α fa s)) -> (Set.InjOn.{u1, u1} β β fb (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align function.semiconj.inj_on_image Function.Semiconj.injOn_imageₓ'. -/
theorem injOn_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s)) :
    InjOn fb (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)
#align function.semiconj.inj_on_image Function.Semiconj.injOn_image

/- warning: function.semiconj.inj_on_range -> Function.Semiconj.injOn_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (Function.Injective.{succ u1, succ u1} α α fa) -> (Set.InjOn.{u1, u2} α β f (Set.range.{u1, succ u1} α α fa)) -> (Set.InjOn.{u2, u2} β β fb (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (Function.Injective.{succ u2, succ u2} α α fa) -> (Set.InjOn.{u2, u1} α β f (Set.range.{u2, succ u2} α α fa)) -> (Set.InjOn.{u1, u1} β β fb (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align function.semiconj.inj_on_range Function.Semiconj.injOn_rangeₓ'. -/
theorem injOn_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa)) :
    InjOn fb (range f) := by
  rw [← image_univ] at *
  exact h.inj_on_image (ha.inj_on univ) hf
#align function.semiconj.inj_on_range Function.Semiconj.injOn_range

/- warning: function.semiconj.bij_on_image -> Function.Semiconj.bijOn_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (Set.BijOn.{u1, u1} α α fa s t) -> (Set.InjOn.{u1, u2} α β f t) -> (Set.BijOn.{u2, u2} β β fb (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (Set.BijOn.{u2, u2} α α fa s t) -> (Set.InjOn.{u2, u1} α β f t) -> (Set.BijOn.{u1, u1} β β fb (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align function.semiconj.bij_on_image Function.Semiconj.bijOn_imageₓ'. -/
theorem bijOn_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) :
    BijOn fb (f '' s) (f '' t) :=
  ⟨h.maps_to_image ha.MapsTo, h.inj_on_image ha.InjOn (ha.image_eq.symm ▸ hf),
    h.surj_on_image ha.SurjOn⟩
#align function.semiconj.bij_on_image Function.Semiconj.bijOn_image

/- warning: function.semiconj.bij_on_range -> Function.Semiconj.bijOn_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (Function.Bijective.{succ u1, succ u1} α α fa) -> (Function.Injective.{succ u1, succ u2} α β f) -> (Set.BijOn.{u2, u2} β β fb (Set.range.{u2, succ u1} β α f) (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (Function.Bijective.{succ u2, succ u2} α α fa) -> (Function.Injective.{succ u2, succ u1} α β f) -> (Set.BijOn.{u1, u1} β β fb (Set.range.{u1, succ u2} β α f) (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align function.semiconj.bij_on_range Function.Semiconj.bijOn_rangeₓ'. -/
theorem bijOn_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) :
    BijOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.bij_on_image (bijective_iff_bij_on_univ.1 ha) (hf.inj_on univ)
#align function.semiconj.bij_on_range Function.Semiconj.bijOn_range

/- warning: function.semiconj.maps_to_preimage -> Function.Semiconj.mapsTo_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (forall {s : Set.{u2} β} {t : Set.{u2} β}, (Set.MapsTo.{u2, u2} β β fb s t) -> (Set.MapsTo.{u1, u1} α α fa (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (forall {s : Set.{u1} β} {t : Set.{u1} β}, (Set.MapsTo.{u1, u1} β β fb s t) -> (Set.MapsTo.{u2, u2} α α fa (Set.preimage.{u2, u1} α β f s) (Set.preimage.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align function.semiconj.maps_to_preimage Function.Semiconj.mapsTo_preimageₓ'. -/
theorem mapsTo_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) :
    MapsTo fa (f ⁻¹' s) (f ⁻¹' t) := fun x hx => by simp only [mem_preimage, h x, hb hx]
#align function.semiconj.maps_to_preimage Function.Semiconj.mapsTo_preimage

/- warning: function.semiconj.inj_on_preimage -> Function.Semiconj.injOn_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u1, u2} α β f fa fb) -> (forall {s : Set.{u2} β}, (Set.InjOn.{u2, u2} β β fb s) -> (Set.InjOn.{u1, u2} α β f (Set.preimage.{u1, u2} α β f s)) -> (Set.InjOn.{u1, u1} α α fa (Set.preimage.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {fa : α -> α} {fb : β -> β} {f : α -> β}, (Function.Semiconj.{u2, u1} α β f fa fb) -> (forall {s : Set.{u1} β}, (Set.InjOn.{u1, u1} β β fb s) -> (Set.InjOn.{u2, u1} α β f (Set.preimage.{u2, u1} α β f s)) -> (Set.InjOn.{u2, u2} α α fa (Set.preimage.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align function.semiconj.inj_on_preimage Function.Semiconj.injOn_preimageₓ'. -/
theorem injOn_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
    (hf : InjOn f (f ⁻¹' s)) : InjOn fa (f ⁻¹' s) :=
  by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq, h.eq] at this
  exact hf hx hy (hb hx hy this)
#align function.semiconj.inj_on_preimage Function.Semiconj.injOn_preimage

end Semiconj

/- warning: function.update_comp_eq_of_not_mem_range' -> Function.update_comp_eq_of_not_mem_range' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Type.{u2}} {γ : β -> Sort.{u3}} [_inst_1 : DecidableEq.{succ u2} β] (g : forall (b : β), γ b) {f : α -> β} {i : β} (a : γ i), (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i (Set.range.{u2, u1} β α f))) -> (Eq.{imax u1 u3} (forall (j : α), (fun (b : β) => γ b) (f j)) (fun (j : α) => Function.update.{succ u2, u3} β (fun (b : β) => γ b) (fun (a : β) (b : β) => _inst_1 a b) g i a (f j)) (fun (j : α) => g (f j)))
but is expected to have type
  forall {α : Sort.{u3}} {β : Type.{u2}} {γ : β -> Sort.{u1}} [_inst_1 : DecidableEq.{succ u2} β] (g : forall (b : β), γ b) {f : α -> β} {i : β} (a : γ i), (Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i (Set.range.{u2, u3} β α f))) -> (Eq.{imax u3 u1} (forall (j : α), γ (f j)) (fun (j : α) => Function.update.{succ u2, u1} β (fun (b : β) => γ b) (fun (a : β) (b : β) => _inst_1 a b) g i a (f j)) (fun (j : α) => g (f j)))
Case conversion may be inaccurate. Consider using '#align function.update_comp_eq_of_not_mem_range' Function.update_comp_eq_of_not_mem_range'ₓ'. -/
theorem update_comp_eq_of_not_mem_range' {α β : Sort _} {γ : β → Sort _} [DecidableEq β]
    (g : ∀ b, γ b) {f : α → β} {i : β} (a : γ i) (h : i ∉ Set.range f) :
    (fun j => (Function.update g i a) (f j)) = fun j => g (f j) :=
  (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩
#align function.update_comp_eq_of_not_mem_range' Function.update_comp_eq_of_not_mem_range'

/- warning: function.update_comp_eq_of_not_mem_range -> Function.update_comp_eq_of_not_mem_range is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Type.{u2}} {γ : Sort.{u3}} [_inst_1 : DecidableEq.{succ u2} β] (g : β -> γ) {f : α -> β} {i : β} (a : γ), (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i (Set.range.{u2, u1} β α f))) -> (Eq.{imax u1 u3} (α -> γ) (Function.comp.{u1, succ u2, u3} α β γ (Function.update.{succ u2, u3} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_1 a b) g i a) f) (Function.comp.{u1, succ u2, u3} α β γ g f))
but is expected to have type
  forall {α : Sort.{u3}} {β : Type.{u2}} {γ : Sort.{u1}} [_inst_1 : DecidableEq.{succ u2} β] (g : β -> γ) {f : α -> β} {i : β} (a : γ), (Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i (Set.range.{u2, u3} β α f))) -> (Eq.{imax u3 u1} (α -> γ) (Function.comp.{u3, succ u2, u1} α β γ (Function.update.{succ u2, u1} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_1 a b) g i a) f) (Function.comp.{u3, succ u2, u1} α β γ g f))
Case conversion may be inaccurate. Consider using '#align function.update_comp_eq_of_not_mem_range Function.update_comp_eq_of_not_mem_rangeₓ'. -/
/-- Non-dependent version of `function.update_comp_eq_of_not_mem_range'` -/
theorem update_comp_eq_of_not_mem_range {α β γ : Sort _} [DecidableEq β] (g : β → γ) {f : α → β}
    {i : β} (a : γ) (h : i ∉ Set.range f) : Function.update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_not_mem_range' g a h
#align function.update_comp_eq_of_not_mem_range Function.update_comp_eq_of_not_mem_range

/- warning: function.insert_inj_on -> Function.insert_injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Set.InjOn.{u1, u1} α (Set.{u1} α) (fun (a : α) => Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Set.InjOn.{u1, u1} α (Set.{u1} α) (fun (a : α) => Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)
Case conversion may be inaccurate. Consider using '#align function.insert_inj_on Function.insert_injOnₓ'. -/
theorem insert_injOn (s : Set α) : sᶜ.InjOn fun a => insert a s := fun a ha b _ => (insert_inj ha).1
#align function.insert_inj_on Function.insert_injOn

theorem monotone_on_of_right_inv_on_of_maps_to [PartialOrder α] [LinearOrder β] {φ : β → α}
    {ψ : α → β} {t : Set β} {s : Set α} (hφ : MonotoneOn φ t) (φψs : Set.RightInvOn ψ φ s)
    (ψts : Set.MapsTo ψ s t) : MonotoneOn ψ s :=
  by
  rintro x xs y ys l
  rcases le_total (ψ x) (ψ y) with (ψxy | ψyx)
  · exact ψxy
  · cases le_antisymm l (φψs.eq ys ▸ φψs.eq xs ▸ hφ (ψts ys) (ψts xs) ψyx)
    rfl
#align
  function.monotone_on_of_right_inv_on_of_maps_to Function.monotone_on_of_right_inv_on_of_maps_to

theorem antitone_on_of_right_inv_on_of_maps_to [PartialOrder α] [LinearOrder β] {φ : β → α}
    {ψ : α → β} {t : Set β} {s : Set α} (hφ : AntitoneOn φ t) (φψs : Set.RightInvOn ψ φ s)
    (ψts : Set.MapsTo ψ s t) : AntitoneOn ψ s :=
  (monotone_on_of_right_inv_on_of_maps_to hφ.dual_left φψs ψts).dual_right
#align
  function.antitone_on_of_right_inv_on_of_maps_to Function.antitone_on_of_right_inv_on_of_maps_to

end Function

