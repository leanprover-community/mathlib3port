/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.set_like.basic
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Basic
import Mathbin.Tactic.Monotonicity.Basic

/-!
# Typeclass for types with a set-like extensionality property

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The `has_mem` typeclass is used to let terms of a type have elements.
Many instances of `has_mem` have a set-like extensionality property:
things are equal iff they have the same elements.  The `set_like`
typeclass provides a unified interface to define a `has_mem` that is
extensional in this way.

The main use of `set_like` is for algebraic subobjects (such as
`submonoid` and `submodule`), whose non-proof data consists only of a
carrier set.  In such a situation, the projection to the carrier set
is injective.

In general, a type `A` is `set_like` with elements of type `B` if it
has an injective map to `set B`.  This module provides standard
boilerplate for every `set_like`: a `coe_sort`, a `coe` to set, a
`partial_order`, and various extensionality and simp lemmas.

A typical subobject should be declared as:
```
structure my_subobject (X : Type*) [object_typeclass X] :=
(carrier : set X)
(op_mem' : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace my_subobject

variables {X : Type*} [object_typeclass X] {x : X}

instance : set_like (my_subobject X) X :=
⟨my_subobject.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : my_subobject X} : x ∈ p.carrier ↔ x ∈ (p : set X) := iff.rfl

@[ext] theorem ext {p q : my_subobject X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := set_like.ext h

/-- Copy of a `my_subobject` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : my_subobject X) (s : set X) (hs : s = ↑p) : my_subobject X :=
{ carrier := s,
  op_mem' := hs.symm ▸ p.op_mem' }

@[simp] lemma coe_copy (p : my_subobject X) (s : set X) (hs : s = ↑p) :
  (p.copy s hs : set X) = s := rfl

lemma copy_eq (p : my_subobject X) (s : set X) (hs : s = ↑p) : p.copy s hs = p :=
set_like.coe_injective hs

end my_subobject
```

An alternative to `set_like` could have been an extensional `has_mem` typeclass:
```
class has_ext_mem (α : out_param $ Type u) (β : Type v) extends has_mem α β :=
(ext_iff : ∀ {s t : β}, s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
```
While this is equivalent, `set_like` conveniently uses a carrier set projection directly.

## Tags

subobjects
-/


#print SetLike /-
/-- A class to indicate that there is a canonical injection between `A` and `set B`.

This has the effect of giving terms of `A` elements of type `B` (through a `has_mem`
instance) and a compatible coercion to `Type*` as a subtype.

Note: if `set_like.coe` is a projection, implementers should create a simp lemma such as
```
@[simp] lemma mem_carrier {p : my_subobject X} : x ∈ p.carrier ↔ x ∈ (p : set X) := iff.rfl
```
to normalize terms.

If you declare an unbundled subclass of `set_like`, for example:
```
class mul_mem_class (S : Type*) (M : Type*) [has_mul M] [set_like S M] where
  ...
```
Then you should *not* repeat the `out_param` declaration, `set_like` will supply the value instead.
This ensures in Lean 4 your subclass will not have issues with synthesis of the `[has_mul M]`
parameter starting before the value of `M` is known.
-/
@[protect_proj]
class SetLike (A : Type _) (B : outParam <| Type _) where
  coe : A → Set B
  coe_injective' : Function.Injective coe
#align set_like SetLike
-/

namespace SetLike

variable {A : Type _} {B : Type _} [i : SetLike A B]

include i

instance : CoeTC A (Set B) :=
  ⟨SetLike.coe⟩

instance (priority := 100) : Membership B A :=
  ⟨fun x p => x ∈ (p : Set B)⟩

-- `dangerous_instance` does not know that `B` is used only as an `out_param`
@[nolint dangerous_instance]
instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

variable (p q : A)

#print SetLike.coe_sort_coe /-
@[simp, norm_cast]
theorem coe_sort_coe : ((p : Set B) : Type _) = p :=
  rfl
#align set_like.coe_sort_coe SetLike.coe_sort_coe
-/

variable {p q}

#print SetLike.exists /-
protected theorem exists {q : p → Prop} : (∃ x, q x) ↔ ∃ x ∈ p, q ⟨x, ‹_›⟩ :=
  SetCoe.exists
#align set_like.exists SetLike.exists
-/

#print SetLike.forall /-
protected theorem forall {q : p → Prop} : (∀ x, q x) ↔ ∀ x ∈ p, q ⟨x, ‹_›⟩ :=
  SetCoe.forall
#align set_like.forall SetLike.forall
-/

/- warning: set_like.coe_injective -> SetLike.coe_injective is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B], Function.Injective.{succ u1, succ u2} A (Set.{u2} B) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B], Function.Injective.{succ u2, succ u1} A (Set.{u1} B) (SetLike.coe.{u2, u1} A B i)
Case conversion may be inaccurate. Consider using '#align set_like.coe_injective SetLike.coe_injectiveₓ'. -/
theorem coe_injective : Function.Injective (coe : A → Set B) := fun x y h =>
  SetLike.coe_injective' h
#align set_like.coe_injective SetLike.coe_injective

#print SetLike.coe_set_eq /-
@[simp, norm_cast]
theorem coe_set_eq : (p : Set B) = q ↔ p = q :=
  coe_injective.eq_iff
#align set_like.coe_set_eq SetLike.coe_set_eq
-/

#print SetLike.ext' /-
theorem ext' (h : (p : Set B) = q) : p = q :=
  coe_injective h
#align set_like.ext' SetLike.ext'
-/

/- warning: set_like.ext'_iff -> SetLike.ext'_iff is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {p : A} {q : A}, Iff (Eq.{succ u1} A p q) (Eq.{succ u2} (Set.{u2} B) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))) p) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))) q))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B] {p : A} {q : A}, Iff (Eq.{succ u2} A p q) (Eq.{succ u1} (Set.{u1} B) (SetLike.coe.{u2, u1} A B i p) (SetLike.coe.{u2, u1} A B i q))
Case conversion may be inaccurate. Consider using '#align set_like.ext'_iff SetLike.ext'_iffₓ'. -/
theorem ext'_iff : p = q ↔ (p : Set B) = q :=
  coe_set_eq.symm
#align set_like.ext'_iff SetLike.ext'_iff

#print SetLike.ext /-
/-- Note: implementers of `set_like` must copy this lemma in order to tag it with `@[ext]`. -/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  coe_injective <| Set.ext h
#align set_like.ext SetLike.ext
-/

/- warning: set_like.ext_iff -> SetLike.ext_iff is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {p : A} {q : A}, Iff (Eq.{succ u1} A p q) (forall (x : B), Iff (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p) (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x q))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B] {p : A} {q : A}, Iff (Eq.{succ u2} A p q) (forall (x : B), Iff (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x p) (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x q))
Case conversion may be inaccurate. Consider using '#align set_like.ext_iff SetLike.ext_iffₓ'. -/
theorem ext_iff : p = q ↔ ∀ x, x ∈ p ↔ x ∈ q :=
  coe_injective.eq_iff.symm.trans Set.ext_iff
#align set_like.ext_iff SetLike.ext_iff

#print SetLike.mem_coe /-
@[simp]
theorem mem_coe {x : B} : x ∈ (p : Set B) ↔ x ∈ p :=
  Iff.rfl
#align set_like.mem_coe SetLike.mem_coe
-/

#print SetLike.coe_eq_coe /-
@[simp, norm_cast]
theorem coe_eq_coe {x y : p} : (x : B) = y ↔ x = y :=
  Subtype.ext_iff_val.symm
#align set_like.coe_eq_coe SetLike.coe_eq_coe
-/

/- warning: set_like.coe_mk clashes with [anonymous] -> [anonymous]
warning: set_like.coe_mk -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {p : A} (x : B) (hx : Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p), Eq.{succ u2} B ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} B (fun (x : B) => Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p)) B (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} B (fun (x : B) => Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p)) B (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} B (fun (x : B) => Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p)) B (coeBase.{succ u2, succ u2} (Subtype.{succ u2} B (fun (x : B) => Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p)) B (coeSubtype.{succ u2} B (fun (x : B) => Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p))))) (Subtype.mk.{succ u2} B (fun (x : B) => Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p) x hx)) x
but is expected to have type
  forall {A : Type.{u1}} {B : Type.{u2}}, (Nat -> A -> B) -> Nat -> (List.{u1} A) -> (List.{u2} B)
Case conversion may be inaccurate. Consider using '#align set_like.coe_mk [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (x : B) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : B) = x :=
  rfl
#align set_like.coe_mk [anonymous]

#print SetLike.coe_mem /-
@[simp]
theorem coe_mem (x : p) : (x : B) ∈ p :=
  x.2
#align set_like.coe_mem SetLike.coe_mem
-/

#print SetLike.eta /-
@[simp]
protected theorem eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x :=
  Subtype.eta x hx
#align set_like.eta SetLike.eta
-/

-- `dangerous_instance` does not know that `B` is used only as an `out_param`
@[nolint dangerous_instance]
instance (priority := 100) : PartialOrder A :=
  { PartialOrder.lift (coe : A → Set B) coe_injective with le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K }

/- warning: set_like.le_def -> SetLike.le_def is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {S : A} {T : A}, Iff (LE.le.{u1} A (Preorder.toLE.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i))) S T) (forall {{x : B}}, (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x S) -> (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x T))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B] {S : A} {T : A}, Iff (LE.le.{u2} A (Preorder.toLE.{u2} A (PartialOrder.toPreorder.{u2} A (SetLike.instPartialOrder.{u2, u1} A B i))) S T) (forall {{x : B}}, (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x S) -> (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x T))
Case conversion may be inaccurate. Consider using '#align set_like.le_def SetLike.le_defₓ'. -/
theorem le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T :=
  Iff.rfl
#align set_like.le_def SetLike.le_def

/- warning: set_like.coe_subset_coe -> SetLike.coe_subset_coe is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {S : A} {T : A}, Iff (HasSubset.Subset.{u2} (Set.{u2} B) (Set.hasSubset.{u2} B) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))) S) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))) T)) (LE.le.{u1} A (Preorder.toLE.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i))) S T)
but is expected to have type
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {S : A} {T : A}, Iff (HasSubset.Subset.{u2} (Set.{u2} B) (Set.instHasSubsetSet.{u2} B) (SetLike.coe.{u1, u2} A B i S) (SetLike.coe.{u1, u2} A B i T)) (LE.le.{u1} A (Preorder.toLE.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.instPartialOrder.{u1, u2} A B i))) S T)
Case conversion may be inaccurate. Consider using '#align set_like.coe_subset_coe SetLike.coe_subset_coeₓ'. -/
@[simp, norm_cast]
theorem coe_subset_coe {S T : A} : (S : Set B) ⊆ T ↔ S ≤ T :=
  Iff.rfl
#align set_like.coe_subset_coe SetLike.coe_subset_coe

/- warning: set_like.coe_mono -> SetLike.coe_mono is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B], Monotone.{u1, u2} A (Set.{u2} B) (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i)) (PartialOrder.toPreorder.{u2} (Set.{u2} B) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} B) (Lattice.toSemilatticeInf.{u2} (Set.{u2} B) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} B) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} B) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} B) (Set.booleanAlgebra.{u2} B))))))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B], Monotone.{u2, u1} A (Set.{u1} B) (PartialOrder.toPreorder.{u2} A (SetLike.instPartialOrder.{u2, u1} A B i)) (PartialOrder.toPreorder.{u1} (Set.{u1} B) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} B) (Lattice.toSemilatticeInf.{u1} (Set.{u1} B) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} B) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} B) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} B) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} B) (Set.instBooleanAlgebraSet.{u1} B)))))))) (SetLike.coe.{u2, u1} A B i)
Case conversion may be inaccurate. Consider using '#align set_like.coe_mono SetLike.coe_monoₓ'. -/
@[mono]
theorem coe_mono : Monotone (coe : A → Set B) := fun a b => coe_subset_coe.mpr
#align set_like.coe_mono SetLike.coe_mono

/- warning: set_like.coe_ssubset_coe -> SetLike.coe_ssubset_coe is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {S : A} {T : A}, Iff (HasSSubset.SSubset.{u2} (Set.{u2} B) (Set.hasSsubset.{u2} B) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))) S) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))) T)) (LT.lt.{u1} A (Preorder.toLT.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i))) S T)
but is expected to have type
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {S : A} {T : A}, Iff (HasSSubset.SSubset.{u2} (Set.{u2} B) (Set.instHasSSubsetSet.{u2} B) (SetLike.coe.{u1, u2} A B i S) (SetLike.coe.{u1, u2} A B i T)) (LT.lt.{u1} A (Preorder.toLT.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.instPartialOrder.{u1, u2} A B i))) S T)
Case conversion may be inaccurate. Consider using '#align set_like.coe_ssubset_coe SetLike.coe_ssubset_coeₓ'. -/
@[simp, norm_cast]
theorem coe_ssubset_coe {S T : A} : (S : Set B) ⊂ T ↔ S < T :=
  Iff.rfl
#align set_like.coe_ssubset_coe SetLike.coe_ssubset_coe

/- warning: set_like.coe_strict_mono -> SetLike.coe_strictMono is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B], StrictMono.{u1, u2} A (Set.{u2} B) (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i)) (PartialOrder.toPreorder.{u2} (Set.{u2} B) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} B) (Lattice.toSemilatticeInf.{u2} (Set.{u2} B) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} B) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} B) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} B) (Set.booleanAlgebra.{u2} B))))))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) A (Set.{u2} B) (HasLiftT.mk.{succ u1, succ u2} A (Set.{u2} B) (CoeTCₓ.coe.{succ u1, succ u2} A (Set.{u2} B) (SetLike.Set.hasCoeT.{u1, u2} A B i))))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B], StrictMono.{u2, u1} A (Set.{u1} B) (PartialOrder.toPreorder.{u2} A (SetLike.instPartialOrder.{u2, u1} A B i)) (PartialOrder.toPreorder.{u1} (Set.{u1} B) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} B) (Lattice.toSemilatticeInf.{u1} (Set.{u1} B) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} B) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} B) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} B) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} B) (Set.instBooleanAlgebraSet.{u1} B)))))))) (SetLike.coe.{u2, u1} A B i)
Case conversion may be inaccurate. Consider using '#align set_like.coe_strict_mono SetLike.coe_strictMonoₓ'. -/
@[mono]
theorem coe_strictMono : StrictMono (coe : A → Set B) := fun a b => coe_ssubset_coe.mpr
#align set_like.coe_strict_mono SetLike.coe_strictMono

/- warning: set_like.not_le_iff_exists -> SetLike.not_le_iff_exists is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {p : A} {q : A}, Iff (Not (LE.le.{u1} A (Preorder.toLE.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i))) p q)) (Exists.{succ u2} B (fun (x : B) => Exists.{0} (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p) (fun (H : Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p) => Not (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x q))))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B] {p : A} {q : A}, Iff (Not (LE.le.{u2} A (Preorder.toLE.{u2} A (PartialOrder.toPreorder.{u2} A (SetLike.instPartialOrder.{u2, u1} A B i))) p q)) (Exists.{succ u1} B (fun (x : B) => And (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x p) (Not (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x q))))
Case conversion may be inaccurate. Consider using '#align set_like.not_le_iff_exists SetLike.not_le_iff_existsₓ'. -/
theorem not_le_iff_exists : ¬p ≤ q ↔ ∃ x ∈ p, x ∉ q :=
  Set.not_subset
#align set_like.not_le_iff_exists SetLike.not_le_iff_exists

/- warning: set_like.exists_of_lt -> SetLike.exists_of_lt is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {p : A} {q : A}, (LT.lt.{u1} A (Preorder.toLT.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i))) p q) -> (Exists.{succ u2} B (fun (x : B) => Exists.{0} (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x q) (fun (H : Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x q) => Not (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p))))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B] {p : A} {q : A}, (LT.lt.{u2} A (Preorder.toLT.{u2} A (PartialOrder.toPreorder.{u2} A (SetLike.instPartialOrder.{u2, u1} A B i))) p q) -> (Exists.{succ u1} B (fun (x : B) => And (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x q) (Not (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x p))))
Case conversion may be inaccurate. Consider using '#align set_like.exists_of_lt SetLike.exists_of_ltₓ'. -/
theorem exists_of_lt : p < q → ∃ x ∈ q, x ∉ p :=
  Set.exists_of_ssubset
#align set_like.exists_of_lt SetLike.exists_of_lt

/- warning: set_like.lt_iff_le_and_exists -> SetLike.lt_iff_le_and_exists is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [i : SetLike.{u1, u2} A B] {p : A} {q : A}, Iff (LT.lt.{u1} A (Preorder.toLT.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i))) p q) (And (LE.le.{u1} A (Preorder.toLE.{u1} A (PartialOrder.toPreorder.{u1} A (SetLike.partialOrder.{u1, u2} A B i))) p q) (Exists.{succ u2} B (fun (x : B) => Exists.{0} (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x q) (fun (H : Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x q) => Not (Membership.Mem.{u2, u1} B A (SetLike.hasMem.{u1, u2} A B i) x p)))))
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [i : SetLike.{u2, u1} A B] {p : A} {q : A}, Iff (LT.lt.{u2} A (Preorder.toLT.{u2} A (PartialOrder.toPreorder.{u2} A (SetLike.instPartialOrder.{u2, u1} A B i))) p q) (And (LE.le.{u2} A (Preorder.toLE.{u2} A (PartialOrder.toPreorder.{u2} A (SetLike.instPartialOrder.{u2, u1} A B i))) p q) (Exists.{succ u1} B (fun (x : B) => And (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x q) (Not (Membership.mem.{u1, u2} B A (SetLike.instMembership.{u2, u1} A B i) x p)))))
Case conversion may be inaccurate. Consider using '#align set_like.lt_iff_le_and_exists SetLike.lt_iff_le_and_existsₓ'. -/
theorem lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p := by
  rw [lt_iff_le_not_le, not_le_iff_exists]
#align set_like.lt_iff_le_and_exists SetLike.lt_iff_le_and_exists

end SetLike

