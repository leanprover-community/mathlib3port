/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module logic.unique
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Basic
import Mathbin.Logic.IsEmpty

/-!
# Types with a unique term

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/512
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a typeclass `unique`,
which expresses that a type has a unique term.
In other words, a type that is `inhabited` and a `subsingleton`.

## Main declaration

* `unique`: a typeclass that expresses that a type has a unique term.

## Main statements

* `unique.mk'`: an inhabited subsingleton type is `unique`. This can not be an instance because it
  would lead to loops in typeclass inference.

* `function.surjective.unique`: if the domain of a surjective function is `unique`, then its
  codomain is `unique` as well.

* `function.injective.subsingleton`: if the codomain of an injective function is `subsingleton`,
  then its domain is `subsingleton` as well.

* `function.injective.unique`: if the codomain of an injective function is `subsingleton` and its
  domain is `inhabited`, then its domain is `unique`.

## Implementation details

The typeclass `unique α` is implemented as a type,
rather than a `Prop`-valued predicate,
for good definitional properties of the default term.

-/


universe u v w

variable {α : Sort u} {β : Sort v} {γ : Sort w}

#print Unique /-
/-- `unique α` expresses that `α` is a type with a unique term `default`.

This is implemented as a type, rather than a `Prop`-valued predicate,
for good definitional properties of the default term. -/
@[ext]
structure Unique (α : Sort u) extends Inhabited α where
  uniq : ∀ a : α, a = default
#align unique Unique
-/

attribute [class] Unique

#print unique_iff_exists_unique /-
theorem unique_iff_exists_unique (α : Sort u) : Nonempty (Unique α) ↔ ∃! a : α, True :=
  ⟨fun ⟨u⟩ => ⟨u.default, trivial, fun a _ => u.uniq a⟩, fun ⟨a, _, h⟩ =>
    ⟨⟨⟨a⟩, fun _ => h _ trivial⟩⟩⟩
#align unique_iff_exists_unique unique_iff_exists_unique
-/

#print unique_subtype_iff_exists_unique /-
theorem unique_subtype_iff_exists_unique {α} (p : α → Prop) :
    Nonempty (Unique (Subtype p)) ↔ ∃! a, p a :=
  ⟨fun ⟨u⟩ => ⟨u.default.1, u.default.2, fun a h => congr_arg Subtype.val (u.uniq ⟨a, h⟩)⟩,
    fun ⟨a, ha, he⟩ =>
    ⟨⟨⟨⟨a, ha⟩⟩, fun ⟨b, hb⟩ => by 
        congr
        exact he b hb⟩⟩⟩
#align unique_subtype_iff_exists_unique unique_subtype_iff_exists_unique
-/

#print uniqueOfSubsingleton /-
/-- Given an explicit `a : α` with `[subsingleton α]`, we can construct
a `[unique α]` instance. This is a def because the typeclass search cannot
arbitrarily invent the `a : α` term. Nevertheless, these instances are all
equivalent by `unique.subsingleton.unique`.

See note [reducible non-instances]. -/
@[reducible]
def uniqueOfSubsingleton {α : Sort _} [Subsingleton α] (a : α) :
    Unique α where 
  default := a
  uniq _ := Subsingleton.elim _ _
#align unique_of_subsingleton uniqueOfSubsingleton
-/

#print PUnit.unique /-
instance PUnit.unique : Unique
      PUnit.{u} where 
  default := PUnit.unit
  uniq x := PUnit.subsingleton x _
#align punit.unique PUnit.unique
-/

#print PUnit.default_eq_unit /-
@[simp]
theorem PUnit.default_eq_unit : (default : PUnit) = PUnit.unit :=
  rfl
#align punit.default_eq_star PUnit.default_eq_unit
-/

#print uniqueProp /-
/-- Every provable proposition is unique, as all proofs are equal. -/
def uniqueProp {p : Prop} (h : p) :
    Unique p where 
  default := h
  uniq x := rfl
#align unique_prop uniqueProp
-/

instance : Unique True :=
  uniqueProp trivial

#print Fin.eq_zero /-
theorem Fin.eq_zero : ∀ n : Fin 1, n = 0
  | ⟨n, hn⟩ => Fin.eq_of_veq (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn))
#align fin.eq_zero Fin.eq_zero
-/

instance {n : ℕ} : Inhabited (Fin n.succ) :=
  ⟨0⟩

#print inhabitedFinOneAdd /-
instance inhabitedFinOneAdd (n : ℕ) : Inhabited (Fin (1 + n)) :=
  ⟨⟨0, Nat.zero_lt_one_add n⟩⟩
#align inhabited_fin_one_add inhabitedFinOneAdd
-/

/- warning: fin.default_eq_zero -> Fin.default_eq_zero is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (Fin (Nat.succ n)) (Inhabited.default.{1} (Fin (Nat.succ n)) (Fin.inhabited n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZero n))))
but is expected to have type
  forall (n : Nat), Eq.{1} (Fin (Nat.succ n)) (Inhabited.default.{1} (Fin (Nat.succ n)) (instInhabitedFinSucc n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFinHAddNatInstHAddInstAddNatOfNat n 0))
Case conversion may be inaccurate. Consider using '#align fin.default_eq_zero Fin.default_eq_zeroₓ'. -/
@[simp]
theorem Fin.default_eq_zero (n : ℕ) : (default : Fin n.succ) = 0 :=
  rfl
#align fin.default_eq_zero Fin.default_eq_zero

#print Fin.unique /-
instance Fin.unique : Unique (Fin 1) :=
  { Fin.inhabited with uniq := Fin.eq_zero }
#align fin.unique Fin.unique
-/

namespace Unique

open Function

section

variable [Unique α]

-- see Note [lower instance priority]
instance (priority := 100) : Inhabited α :=
  toInhabited ‹Unique α›

#print Unique.eq_default /-
theorem eq_default (a : α) : a = default :=
  uniq _ a
#align unique.eq_default Unique.eq_default
-/

#print Unique.default_eq /-
theorem default_eq (a : α) : default = a :=
  (uniq _ a).symm
#align unique.default_eq Unique.default_eq
-/

-- see Note [lower instance priority]
instance (priority := 100) : Subsingleton α :=
  subsingleton_of_forall_eq _ eq_default

#print Unique.forall_iff /-
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ p default :=
  ⟨fun h => h _, fun h x => by rwa [Unique.eq_default x]⟩
#align unique.forall_iff Unique.forall_iff
-/

#print Unique.exists_iff /-
theorem exists_iff {p : α → Prop} : Exists p ↔ p default :=
  ⟨fun ⟨a, ha⟩ => eq_default a ▸ ha, Exists.intro default⟩
#align unique.exists_iff Unique.exists_iff
-/

end

#print Unique.subsingleton_unique' /-
@[ext]
protected theorem subsingleton_unique' : ∀ h₁ h₂ : Unique α, h₁ = h₂
  | ⟨⟨x⟩, h⟩, ⟨⟨y⟩, _⟩ => by congr <;> rw [h x, h y]
#align unique.subsingleton_unique' Unique.subsingleton_unique'
-/

#print Unique.subsingleton_unique /-
instance subsingleton_unique : Subsingleton (Unique α) :=
  ⟨Unique.subsingleton_unique'⟩
#align unique.subsingleton_unique Unique.subsingleton_unique
-/

#print Unique.mk' /-
/-- Construct `unique` from `inhabited` and `subsingleton`. Making this an instance would create
a loop in the class inheritance graph. -/
@[reducible]
def mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α :=
  { h₁ with uniq := fun x => Subsingleton.elim _ _ }
#align unique.mk' Unique.mk'
-/

end Unique

#print unique_iff_subsingleton_and_nonempty /-
theorem unique_iff_subsingleton_and_nonempty (α : Sort u) :
    Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α :=
  ⟨fun ⟨u⟩ => by constructor <;> exact inferInstance, fun ⟨hs, hn⟩ =>
    ⟨by 
      skip
      inhabit α
      exact Unique.mk' α⟩⟩
#align unique_iff_subsingleton_and_nonempty unique_iff_subsingleton_and_nonempty
-/

#print Pi.default_def /-
@[simp]
theorem Pi.default_def {β : α → Sort v} [∀ a, Inhabited (β a)] :
    @default (∀ a, β a) _ = fun a : α => @default (β a) _ :=
  rfl
#align pi.default_def Pi.default_def
-/

#print Pi.default_apply /-
theorem Pi.default_apply {β : α → Sort v} [∀ a, Inhabited (β a)] (a : α) :
    @default (∀ a, β a) _ a = default :=
  rfl
#align pi.default_apply Pi.default_apply
-/

/- warning: pi.unique -> Pi.unique is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}} [_inst_1 : forall (a : α), Unique.{u2} (β a)], Unique.{imax u1 u2} (forall (a : α), β a)
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}} [_inst_1 : forall (a : α), Unique.{u1} (β a)], Unique.{imax u2 u1} (forall (a : α), β a)
Case conversion may be inaccurate. Consider using '#align pi.unique Pi.uniqueₓ'. -/
instance Pi.unique {β : α → Sort v} [∀ a, Unique (β a)] : Unique (∀ a, β a) :=
  { Pi.inhabited α with uniq := fun f => funext fun x => Unique.eq_default _ }
#align pi.unique Pi.unique

/- warning: pi.unique_of_is_empty -> Pi.uniqueOfIsEmpty is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} [_inst_1 : IsEmpty.{u1} α] (β : α -> Sort.{u2}), Unique.{imax u1 u2} (forall (a : α), β a)
but is expected to have type
  forall {α : Sort.{u2}} [_inst_1 : IsEmpty.{u2} α] (β : α -> Sort.{u1}), Unique.{imax u2 u1} (forall (a : α), β a)
Case conversion may be inaccurate. Consider using '#align pi.unique_of_is_empty Pi.uniqueOfIsEmptyₓ'. -/
/-- There is a unique function on an empty domain. -/
instance Pi.uniqueOfIsEmpty [IsEmpty α] (β : α → Sort v) :
    Unique (∀ a, β a) where 
  default := isEmptyElim
  uniq f := funext isEmptyElim
#align pi.unique_of_is_empty Pi.uniqueOfIsEmpty

/- warning: eq_const_of_unique -> eq_const_of_unique is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Unique.{u1} α] (f : α -> β), Eq.{imax u1 u2} (α -> β) f (Function.const.{u2, u1} β α (f (Inhabited.default.{u1} α (Unique.inhabited.{u1} α _inst_1))))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Unique.{u2} α] (f : α -> β), Eq.{imax u2 u1} (α -> β) f (Function.const.{u1, u2} β α (f (Inhabited.default.{u2} α (Unique.instInhabited.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_const_of_unique eq_const_of_uniqueₓ'. -/
theorem eq_const_of_unique [Unique α] (f : α → β) : f = Function.const α (f default) := by
  ext x
  rw [Subsingleton.elim x default]
#align eq_const_of_unique eq_const_of_unique

#print heq_const_of_unique /-
theorem heq_const_of_unique [Unique α] {β : α → Sort v} (f : ∀ a, β a) :
    HEq f (Function.const α (f default)) :=
  (Function.hfunext rfl) fun i _ _ => by rw [Subsingleton.elim i default]
#align heq_const_of_unique heq_const_of_unique
-/

namespace Function

variable {f : α → β}

/- warning: function.injective.subsingleton -> Function.Injective.subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : α -> β}, (Function.Injective.{u1, u2} α β f) -> (forall [_inst_1 : Subsingleton.{u2} β], Subsingleton.{u1} α)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {f : α -> β}, (Function.Injective.{u2, u1} α β f) -> (forall [_inst_1 : Subsingleton.{u1} β], Subsingleton.{u2} α)
Case conversion may be inaccurate. Consider using '#align function.injective.subsingleton Function.Injective.subsingletonₓ'. -/
/-- If the codomain of an injective function is a subsingleton, then the domain
is a subsingleton as well. -/
protected theorem Injective.subsingleton (hf : Injective f) [Subsingleton β] : Subsingleton α :=
  ⟨fun x y => hf <| Subsingleton.elim _ _⟩
#align function.injective.subsingleton Function.Injective.subsingleton

/- warning: function.surjective.subsingleton -> Function.Surjective.subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : α -> β} [_inst_1 : Subsingleton.{u1} α], (Function.Surjective.{u1, u2} α β f) -> (Subsingleton.{u2} β)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {f : α -> β} [_inst_1 : Subsingleton.{u2} α], (Function.Surjective.{u2, u1} α β f) -> (Subsingleton.{u1} β)
Case conversion may be inaccurate. Consider using '#align function.surjective.subsingleton Function.Surjective.subsingletonₓ'. -/
/-- If the domain of a surjective function is a subsingleton, then the codomain is a subsingleton as
well. -/
protected theorem Surjective.subsingleton [Subsingleton α] (hf : Surjective f) : Subsingleton β :=
  ⟨hf.Forall₂.2 fun x y => congr_arg f <| Subsingleton.elim x y⟩
#align function.surjective.subsingleton Function.Surjective.subsingleton

#print Function.Surjective.unique /-
/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
protected def Surjective.unique (hf : Surjective f) [Unique α] : Unique β :=
  @Unique.mk' _ ⟨f default⟩ hf.Subsingleton
#align function.surjective.unique Function.Surjective.unique
-/

#print Function.Injective.unique /-
/-- If `α` is inhabited and admits an injective map to a subsingleton type, then `α` is `unique`. -/
protected def Injective.unique [Inhabited α] [Subsingleton β] (hf : Injective f) : Unique α :=
  @Unique.mk' _ _ hf.Subsingleton
#align function.injective.unique Function.Injective.unique
-/

#print Function.Surjective.uniqueOfSurjectiveConst /-
/-- If a constant function is surjective, then the codomain is a singleton. -/
def Surjective.uniqueOfSurjectiveConst (α : Type _) {β : Type _} (b : β)
    (h : Function.Surjective (Function.const α b)) : Unique β :=
  @uniqueOfSubsingleton _ (subsingleton_of_forall_eq b <| h.forall.mpr fun _ => rfl) b
#align function.surjective.unique_of_surjective_const Function.Surjective.uniqueOfSurjectiveConst
-/

end Function

/- warning: unique.bijective -> Unique.bijective is a dubious translation:
lean 3 declaration is
  forall {A : Sort.{u1}} {B : Sort.{u2}} [_inst_1 : Unique.{u1} A] [_inst_2 : Unique.{u2} B] {f : A -> B}, Function.Bijective.{u1, u2} A B f
but is expected to have type
  forall {A : Sort.{u2}} {B : Sort.{u1}} [_inst_1 : Unique.{u2} A] [_inst_2 : Unique.{u1} B] {f : A -> B}, Function.Bijective.{u2, u1} A B f
Case conversion may be inaccurate. Consider using '#align unique.bijective Unique.bijectiveₓ'. -/
theorem Unique.bijective {A B} [Unique A] [Unique B] {f : A → B} : Function.Bijective f := by
  rw [Function.bijective_iff_has_inverse]
  refine' ⟨default, _, _⟩ <;> intro x <;> simp
#align unique.bijective Unique.bijective

namespace Option

#print Option.subsingleton_iff_isEmpty /-
/-- `option α` is a `subsingleton` if and only if `α` is empty. -/
theorem subsingleton_iff_isEmpty {α} : Subsingleton (Option α) ↔ IsEmpty α :=
  ⟨fun h => ⟨fun x => Option.noConfusion <| @Subsingleton.elim _ h x none⟩, fun h =>
    ⟨fun x y => Option.casesOn x (Option.casesOn y rfl fun x => h.elim x) fun x => h.elim x⟩⟩
#align option.subsingleton_iff_is_empty Option.subsingleton_iff_isEmpty
-/

instance {α} [IsEmpty α] : Unique (Option α) :=
  @Unique.mk' _ _ (subsingleton_iff_isEmpty.2 ‹_›)

end Option

section Subtype

#print Unique.subtypeEq /-
instance Unique.subtypeEq (y : α) :
    Unique { x // x = y } where 
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by simpa using hx
#align unique.subtype_eq Unique.subtypeEq
-/

#print Unique.subtypeEq' /-
instance Unique.subtypeEq' (y : α) :
    Unique { x // y = x } where 
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by simpa using hx.symm
#align unique.subtype_eq' Unique.subtypeEq'
-/

end Subtype

