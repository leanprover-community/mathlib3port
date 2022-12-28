/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module data.list.func
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Order.Basic

/-!
# Lists as Functions

Definitions for using lists as finite representations of finitely-supported functions with domain
ℕ.

These include pointwise operations on lists, as well as get and set operations.

## Notations

An index notation is introduced in this file for setting a particular element of a list. With `as`
as a list `m` as an index, and `a` as a new element, the notation is `as {m ↦ a}`.

So, for example
`[1, 3, 5] {1 ↦ 9}` would result in `[1, 9, 5]`

This notation is in the locale `list.func`.
-/


open List

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

namespace Func

variable {a : α}

variable {as as1 as2 as3 : List α}

#print List.Func.neg /-
/-- Elementwise negation of a list -/
def neg [Neg α] (as : List α) :=
  as.map fun a => -a
#align list.func.neg List.Func.neg
-/

variable [Inhabited α] [Inhabited β]

#print List.Func.set /-
/-- Update element of a list by index. If the index is out of range, extend the list with default
elements
-/
@[simp]
def set (a : α) : List α → ℕ → List α
  | _ :: as, 0 => a :: as
  | [], 0 => [a]
  | h :: as, k + 1 => h :: Set as k
  | [], k + 1 => default :: Set ([] : List α) k
#align list.func.set List.Func.set
-/

-- mathport name: list.func.set
scoped notation as " {" m " ↦ " a "}" => List.Func.set a as m

#print List.Func.get /-
/-- Get element of a list by index. If the index is out of range, return the default element -/
@[simp]
def get : ℕ → List α → α
  | _, [] => default
  | 0, a :: as => a
  | n + 1, a :: as => get n as
#align list.func.get List.Func.get
-/

#print List.Func.Equiv /-
/-- Pointwise equality of lists. If lists are different lengths, compare with the default
element.
-/
def Equiv (as1 as2 : List α) : Prop :=
  ∀ m : Nat, get m as1 = get m as2
#align list.func.equiv List.Func.Equiv
-/

#print List.Func.pointwise /-
/-- Pointwise operations on lists. If lists are different lengths, use the default element. -/
@[simp]
def pointwise (f : α → β → γ) : List α → List β → List γ
  | [], [] => []
  | [], b :: bs => map (f default) (b :: bs)
  | a :: as, [] => map (fun x => f x default) (a :: as)
  | a :: as, b :: bs => f a b :: pointwise as bs
#align list.func.pointwise List.Func.pointwise
-/

#print List.Func.add /-
/-- Pointwise addition on lists. If lists are different lengths, use zero. -/
def add {α : Type u} [Zero α] [Add α] : List α → List α → List α :=
  @pointwise α α α ⟨0⟩ ⟨0⟩ (· + ·)
#align list.func.add List.Func.add
-/

#print List.Func.sub /-
/-- Pointwise subtraction on lists. If lists are different lengths, use zero. -/
def sub {α : Type u} [Zero α] [Sub α] : List α → List α → List α :=
  @pointwise α α α ⟨0⟩ ⟨0⟩ (@Sub.sub α _)
#align list.func.sub List.Func.sub
-/

/- warning: list.func.length_set -> List.Func.length_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} [_inst_1 : Inhabited.{succ u1} α] {m : Nat} {as : List.{u1} α}, Eq.{1} Nat (List.length.{u1} α (List.Func.set.{u1} α _inst_1 a as m)) (LinearOrder.max.{0} Nat Nat.linearOrder (List.length.{u1} α as) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} {a : α} [_inst_1 : Inhabited.{succ u1} α] {m : Nat} {as : List.{u1} α}, Eq.{1} Nat (List.length.{u1} α (List.Func.set.{u1} α _inst_1 a as m)) (Max.max.{0} Nat Nat.instMaxNat (List.length.{u1} α as) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align list.func.length_set List.Func.length_setₓ'. -/
-- set
theorem length_set : ∀ {m : ℕ} {as : List α}, as {m ↦ a}.length = max as.length (m + 1)
  | 0, [] => rfl
  | 0, a :: as => by
    rw [max_eq_left]
    rfl
    simp [Nat.le_add_right]
  | m + 1, [] => by simp only [Set, Nat.zero_max, length, @length_set m]
  | m + 1, a :: as => by simp only [Set, Nat.max_succ_succ, length, @length_set m]
#align list.func.length_set List.Func.length_set

#print List.Func.get_nil /-
@[simp]
theorem get_nil {k : ℕ} : (get k [] : α) = default := by cases k <;> rfl
#align list.func.get_nil List.Func.get_nil
-/

#print List.Func.get_eq_default_of_le /-
theorem get_eq_default_of_le : ∀ (k : ℕ) {as : List α}, as.length ≤ k → get k as = default
  | 0, [], h1 => rfl
  | 0, a :: as, h1 => by cases h1
  | k + 1, [], h1 => rfl
  | k + 1, a :: as, h1 => by
    apply get_eq_default_of_le k
    rw [← Nat.succ_le_succ_iff]; apply h1
#align list.func.get_eq_default_of_le List.Func.get_eq_default_of_le
-/

#print List.Func.get_set /-
@[simp]
theorem get_set {a : α} : ∀ {k : ℕ} {as : List α}, get k (as {k ↦ a}) = a
  | 0, as => by cases as <;> rfl
  | k + 1, as => by cases as <;> simp [get_set]
#align list.func.get_set List.Func.get_set
-/

/- warning: list.func.eq_get_of_mem clashes with [anonymous] -> [anonymous]
warning: list.func.eq_get_of_mem -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Inhabited.{succ u1} α] {a : α} {as : List.{u1} α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a as) -> (Exists.{1} Nat (fun (n : Nat) => α -> (Eq.{succ u1} α a (List.Func.get.{u1} α _inst_1 n as))))
but is expected to have type
  forall {α : Sort.{u1}} {_inst_1 : Nat}, ((Eq.{1} Nat _inst_1 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) -> (forall (m : Nat), (Eq.{1} Nat _inst_1 (Nat.succ m)) -> α) -> α
Case conversion may be inaccurate. Consider using '#align list.func.eq_get_of_mem [anonymous]ₓ'. -/
theorem [anonymous] {a : α} : ∀ {as : List α}, a ∈ as → ∃ n : Nat, ∀ d : α, a = get n as
  | [], h => by cases h
  | b :: as, h => by
    rw [mem_cons_iff] at h; cases h
    · exists 0
      intro d
      apply h
    · cases' eq_get_of_mem h with n h2
      exists n + 1
      apply h2
#align list.func.eq_get_of_mem[anonymous]

#print List.Func.mem_get_of_le /-
theorem mem_get_of_le : ∀ {n : ℕ} {as : List α}, n < as.length → get n as ∈ as
  | _, [], h1 => by cases h1
  | 0, a :: as, _ => Or.inl rfl
  | n + 1, a :: as, h1 => by
    apply Or.inr; unfold get
    apply mem_get_of_le
    apply Nat.lt_of_succ_lt_succ h1
#align list.func.mem_get_of_le List.Func.mem_get_of_le
-/

#print List.Func.mem_get_of_ne_zero /-
theorem mem_get_of_ne_zero : ∀ {n : ℕ} {as : List α}, get n as ≠ default → get n as ∈ as
  | _, [], h1 => by exfalso; apply h1; rw [get_nil]
  | 0, a :: as, h1 => Or.inl rfl
  | n + 1, a :: as, h1 => by
    unfold get
    apply Or.inr (mem_get_of_ne_zero _)
    apply h1
#align list.func.mem_get_of_ne_zero List.Func.mem_get_of_ne_zero
-/

#print List.Func.get_set_eq_of_ne /-
theorem get_set_eq_of_ne {a : α} :
    ∀ {as : List α} (k : ℕ) (m : ℕ), m ≠ k → get m (as {k ↦ a}) = get m as
  | as, 0, m, h1 => by
    cases m
    contradiction
    cases as <;> simp only [Set, get, get_nil]
  | as, k + 1, m, h1 => by
    cases as <;> cases m
    simp only [Set, get]
    · have h3 : get m (nil {k ↦ a}) = default :=
        by
        rw [get_set_eq_of_ne k m, get_nil]
        intro hc
        apply h1
        simp [hc]
      apply h3
    simp only [Set, get]
    · apply get_set_eq_of_ne k m
      intro hc
      apply h1
      simp [hc]
#align list.func.get_set_eq_of_ne List.Func.get_set_eq_of_ne
-/

#print List.Func.get_map /-
theorem get_map {f : α → β} :
    ∀ {n : ℕ} {as : List α}, n < as.length → get n (as.map f) = f (get n as)
  | _, [], h => by cases h
  | 0, a :: as, h => rfl
  | n + 1, a :: as, h1 =>
    by
    have h2 : n < length as := by
      rw [← Nat.succ_le_iff, ← Nat.lt_succ_iff]
      apply h1
    apply get_map h2
#align list.func.get_map List.Func.get_map
-/

#print List.Func.get_map' /-
theorem get_map' {f : α → β} {n : ℕ} {as : List α} :
    f default = default → get n (as.map f) = f (get n as) :=
  by
  intro h1; by_cases h2 : n < as.length
  · apply get_map h2
  · rw [not_lt] at h2
    rw [get_eq_default_of_le _ h2, get_eq_default_of_le, h1]
    rw [length_map]
    apply h2
#align list.func.get_map' List.Func.get_map'
-/

#print List.Func.forall_val_of_forall_mem /-
theorem forall_val_of_forall_mem {as : List α} {p : α → Prop} :
    p default → (∀ x ∈ as, p x) → ∀ n, p (get n as) :=
  by
  intro h1 h2 n
  by_cases h3 : n < as.length
  · apply h2 _ (mem_get_of_le h3)
  · rw [not_lt] at h3
    rw [get_eq_default_of_le _ h3]
    apply h1
#align list.func.forall_val_of_forall_mem List.Func.forall_val_of_forall_mem
-/

#print List.Func.equiv_refl /-
-- equiv
theorem equiv_refl : Equiv as as := fun k => rfl
#align list.func.equiv_refl List.Func.equiv_refl
-/

#print List.Func.equiv_symm /-
theorem equiv_symm : Equiv as1 as2 → Equiv as2 as1 := fun h1 k => (h1 k).symm
#align list.func.equiv_symm List.Func.equiv_symm
-/

#print List.Func.equiv_trans /-
theorem equiv_trans : Equiv as1 as2 → Equiv as2 as3 → Equiv as1 as3 := fun h1 h2 k =>
  Eq.trans (h1 k) (h2 k)
#align list.func.equiv_trans List.Func.equiv_trans
-/

#print List.Func.equiv_of_eq /-
theorem equiv_of_eq : as1 = as2 → Equiv as1 as2 := by intro h1; rw [h1]; apply equiv_refl
#align list.func.equiv_of_eq List.Func.equiv_of_eq
-/

#print List.Func.eq_of_equiv /-
theorem eq_of_equiv : ∀ {as1 as2 : List α}, as1.length = as2.length → Equiv as1 as2 → as1 = as2
  | [], [], h1, h2 => rfl
  | _ :: _, [], h1, h2 => by cases h1
  | [], _ :: _, h1, h2 => by cases h1
  | a1 :: as1, a2 :: as2, h1, h2 => by
    congr
    · apply h2 0
    have h3 : as1.length = as2.length := by simpa [add_left_inj, add_comm, length] using h1
    apply eq_of_equiv h3
    intro m
    apply h2 (m + 1)
#align list.func.eq_of_equiv List.Func.eq_of_equiv
-/

end Func

-- We want to drop the `inhabited` instances for a moment,
-- so we close and open the namespace
namespace Func

/- warning: list.func.get_neg -> List.Func.get_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] {k : Nat} {as : List.{u1} α}, Eq.{succ u1} α (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) k (List.Func.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) as)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) k as))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] {k : Nat} {as : List.{u1} α}, Eq.{succ u1} α (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) k (List.Func.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) as)) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) k as))
Case conversion may be inaccurate. Consider using '#align list.func.get_neg List.Func.get_negₓ'. -/
-- neg
@[simp]
theorem get_neg [AddGroup α] {k : ℕ} {as : List α} : @get α ⟨0⟩ k (neg as) = -@get α ⟨0⟩ k as :=
  by
  unfold neg
  rw [@get_map' α α ⟨0⟩]
  apply neg_zero
#align list.func.get_neg List.Func.get_neg

#print List.Func.length_neg /-
@[simp]
theorem length_neg [Neg α] (as : List α) : (neg as).length = as.length := by
  simp only [neg, length_map]
#align list.func.length_neg List.Func.length_neg
-/

variable [Inhabited α] [Inhabited β]

#print List.Func.nil_pointwise /-
-- pointwise
theorem nil_pointwise {f : α → β → γ} : ∀ bs : List β, pointwise f [] bs = bs.map (f default)
  | [] => rfl
  | b :: bs => by simp only [nil_pointwise bs, pointwise, eq_self_iff_true, and_self_iff, map]
#align list.func.nil_pointwise List.Func.nil_pointwise
-/

#print List.Func.pointwise_nil /-
theorem pointwise_nil {f : α → β → γ} :
    ∀ as : List α, pointwise f as [] = as.map fun a => f a default
  | [] => rfl
  | a :: as => by simp only [pointwise_nil as, pointwise, eq_self_iff_true, and_self_iff, List.map]
#align list.func.pointwise_nil List.Func.pointwise_nil
-/

#print List.Func.get_pointwise /-
theorem get_pointwise [Inhabited γ] {f : α → β → γ} (h1 : f default default = default) :
    ∀ (k : Nat) (as : List α) (bs : List β), get k (pointwise f as bs) = f (get k as) (get k bs)
  | k, [], [] => by simp only [h1, get_nil, pointwise, get]
  | 0, [], b :: bs => by simp only [get_pointwise, get_nil, pointwise, get, Nat.zero_eq, map]
  | k + 1, [], b :: bs =>
    by
    have : get k (map (f default) bs) = f default (get k bs) := by
      simpa [nil_pointwise, get_nil] using get_pointwise k [] bs
    simpa [get, get_nil, pointwise, map]
  | 0, a :: as, [] => by simp only [get_pointwise, get_nil, pointwise, get, Nat.zero_eq, map]
  | k + 1, a :: as, [] => by
    simpa [get, get_nil, pointwise, map, pointwise_nil, get_nil] using get_pointwise k as []
  | 0, a :: as, b :: bs => by simp only [pointwise, get]
  | k + 1, a :: as, b :: bs => by simp only [pointwise, get, get_pointwise k]
#align list.func.get_pointwise List.Func.get_pointwise
-/

/- warning: list.func.length_pointwise -> List.Func.length_pointwise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Inhabited.{succ u1} α] [_inst_2 : Inhabited.{succ u2} β] {f : α -> β -> γ} {as : List.{u1} α} {bs : List.{u2} β}, Eq.{1} Nat (List.length.{u3} γ (List.Func.pointwise.{u1, u2, u3} α β γ _inst_1 _inst_2 f as bs)) (LinearOrder.max.{0} Nat Nat.linearOrder (List.length.{u1} α as) (List.length.{u2} β bs))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Inhabited.{succ u1} α] [_inst_2 : Inhabited.{succ u2} β] {f : α -> β -> γ} {as : List.{u1} α} {bs : List.{u2} β}, Eq.{1} Nat (List.length.{u3} γ (List.Func.pointwise.{u1, u2, u3} α β γ _inst_1 _inst_2 f as bs)) (Max.max.{0} Nat Nat.instMaxNat (List.length.{u1} α as) (List.length.{u2} β bs))
Case conversion may be inaccurate. Consider using '#align list.func.length_pointwise List.Func.length_pointwiseₓ'. -/
theorem length_pointwise {f : α → β → γ} :
    ∀ {as : List α} {bs : List β}, (pointwise f as bs).length = max as.length bs.length
  | [], [] => rfl
  | [], b :: bs => by
    simp only [pointwise, length, length_map, max_eq_right (Nat.zero_le (length bs + 1))]
  | a :: as, [] => by
    simp only [pointwise, length, length_map, max_eq_left (Nat.zero_le (length as + 1))]
  | a :: as, b :: bs => by simp only [pointwise, length, Nat.max_succ_succ, @length_pointwise as bs]
#align list.func.length_pointwise List.Func.length_pointwise

end Func

namespace Func

/- warning: list.func.get_add -> List.Func.get_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] {k : Nat} {xs : List.{u1} α} {ys : List.{u1} α}, Eq.{succ u1} α (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))))) k (List.Func.add.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) xs ys)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))))) k xs) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))))) k ys))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] {k : Nat} {xs : List.{u1} α} {ys : List.{u1} α}, Eq.{succ u1} α (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α _inst_1)))) k (List.Func.add.{u1} α (AddMonoid.toZero.{u1} α _inst_1) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) xs ys)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α _inst_1)))) k xs) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α _inst_1)))) k ys))
Case conversion may be inaccurate. Consider using '#align list.func.get_add List.Func.get_addₓ'. -/
-- add
@[simp]
theorem get_add {α : Type u} [AddMonoid α] {k : ℕ} {xs ys : List α} :
    @get α ⟨0⟩ k (add xs ys) = @get α ⟨0⟩ k xs + @get α ⟨0⟩ k ys :=
  by
  apply get_pointwise
  apply zero_add
#align list.func.get_add List.Func.get_add

/- warning: list.func.length_add -> List.Func.length_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : Add.{u1} α] {xs : List.{u1} α} {ys : List.{u1} α}, Eq.{1} Nat (List.length.{u1} α (List.Func.add.{u1} α _inst_1 _inst_2 xs ys)) (LinearOrder.max.{0} Nat Nat.linearOrder (List.length.{u1} α xs) (List.length.{u1} α ys))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : Add.{u1} α] {xs : List.{u1} α} {ys : List.{u1} α}, Eq.{1} Nat (List.length.{u1} α (List.Func.add.{u1} α _inst_1 _inst_2 xs ys)) (Max.max.{0} Nat Nat.instMaxNat (List.length.{u1} α xs) (List.length.{u1} α ys))
Case conversion may be inaccurate. Consider using '#align list.func.length_add List.Func.length_addₓ'. -/
@[simp]
theorem length_add {α : Type u} [Zero α] [Add α] {xs ys : List α} :
    (add xs ys).length = max xs.length ys.length :=
  @length_pointwise α α α ⟨0⟩ ⟨0⟩ _ _ _
#align list.func.length_add List.Func.length_add

/- warning: list.func.nil_add -> List.Func.nil_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (as : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.Func.add.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (List.nil.{u1} α) as) as
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (as : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.Func.add.{u1} α (AddMonoid.toZero.{u1} α _inst_1) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (List.nil.{u1} α) as) as
Case conversion may be inaccurate. Consider using '#align list.func.nil_add List.Func.nil_addₓ'. -/
@[simp]
theorem nil_add {α : Type u} [AddMonoid α] (as : List α) : add [] as = as :=
  by
  rw [add, @nil_pointwise α α α ⟨0⟩ ⟨0⟩]
  apply Eq.trans _ (map_id as)
  congr with x
  rw [zero_add, id]
#align list.func.nil_add List.Func.nil_add

/- warning: list.func.add_nil -> List.Func.add_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (as : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.Func.add.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) as (List.nil.{u1} α)) as
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (as : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.Func.add.{u1} α (AddMonoid.toZero.{u1} α _inst_1) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) as (List.nil.{u1} α)) as
Case conversion may be inaccurate. Consider using '#align list.func.add_nil List.Func.add_nilₓ'. -/
@[simp]
theorem add_nil {α : Type u} [AddMonoid α] (as : List α) : add as [] = as :=
  by
  rw [add, @pointwise_nil α α α ⟨0⟩ ⟨0⟩]
  apply Eq.trans _ (map_id as)
  congr with x
  rw [add_zero, id]
#align list.func.add_nil List.Func.add_nil

/- warning: list.func.map_add_map -> List.Func.map_add_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (f : α -> α) (g : α -> α) {as : List.{u1} α}, Eq.{succ u1} (List.{u1} α) (List.Func.add.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (List.map.{u1, u1} α α f as) (List.map.{u1, u1} α α g as)) (List.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (f x) (g x)) as)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (f : α -> α) (g : α -> α) {as : List.{u1} α}, Eq.{succ u1} (List.{u1} α) (List.Func.add.{u1} α (AddMonoid.toZero.{u1} α _inst_1) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)) (List.map.{u1, u1} α α f as) (List.map.{u1, u1} α α g as)) (List.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (f x) (g x)) as)
Case conversion may be inaccurate. Consider using '#align list.func.map_add_map List.Func.map_add_mapₓ'. -/
theorem map_add_map {α : Type u} [AddMonoid α] (f g : α → α) {as : List α} :
    add (as.map f) (as.map g) = as.map fun x => f x + g x :=
  by
  apply @eq_of_equiv _ (⟨0⟩ : Inhabited α)
  · rw [length_map, length_add, max_eq_left, length_map]
    apply le_of_eq
    rw [length_map, length_map]
  intro m
  rw [get_add]
  by_cases h : m < length as
  · repeat' rw [@get_map α α ⟨0⟩ ⟨0⟩ _ _ _ h]
  rw [not_lt] at h
  repeat' rw [get_eq_default_of_le m] <;> try rw [length_map]; apply h
  apply zero_add
#align list.func.map_add_map List.Func.map_add_map

/- warning: list.func.get_sub -> List.Func.get_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] {k : Nat} {xs : List.{u1} α} {ys : List.{u1} α}, Eq.{succ u1} α (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) k (List.Func.sub.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))) (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) xs ys)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) k xs) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) k ys))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] {k : Nat} {xs : List.{u1} α} {ys : List.{u1} α}, Eq.{succ u1} α (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) k (List.Func.sub.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) xs ys)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) k xs) (List.Func.get.{u1} α (Inhabited.mk.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) k ys))
Case conversion may be inaccurate. Consider using '#align list.func.get_sub List.Func.get_subₓ'. -/
-- sub
@[simp]
theorem get_sub {α : Type u} [AddGroup α] {k : ℕ} {xs ys : List α} :
    @get α ⟨0⟩ k (sub xs ys) = @get α ⟨0⟩ k xs - @get α ⟨0⟩ k ys :=
  by
  apply get_pointwise
  apply sub_zero
#align list.func.get_sub List.Func.get_sub

/- warning: list.func.length_sub -> List.Func.length_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : Sub.{u1} α] {xs : List.{u1} α} {ys : List.{u1} α}, Eq.{1} Nat (List.length.{u1} α (List.Func.sub.{u1} α _inst_1 _inst_2 xs ys)) (LinearOrder.max.{0} Nat Nat.linearOrder (List.length.{u1} α xs) (List.length.{u1} α ys))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : Sub.{u1} α] {xs : List.{u1} α} {ys : List.{u1} α}, Eq.{1} Nat (List.length.{u1} α (List.Func.sub.{u1} α _inst_1 _inst_2 xs ys)) (Max.max.{0} Nat Nat.instMaxNat (List.length.{u1} α xs) (List.length.{u1} α ys))
Case conversion may be inaccurate. Consider using '#align list.func.length_sub List.Func.length_subₓ'. -/
@[simp]
theorem length_sub [Zero α] [Sub α] {xs ys : List α} :
    (sub xs ys).length = max xs.length ys.length :=
  @length_pointwise α α α ⟨0⟩ ⟨0⟩ _ _ _
#align list.func.length_sub List.Func.length_sub

/- warning: list.func.nil_sub -> List.Func.nil_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type} [_inst_1 : AddGroup.{0} α] (as : List.{0} α), Eq.{1} (List.{0} α) (List.Func.sub.{0} α (AddZeroClass.toHasZero.{0} α (AddMonoid.toAddZeroClass.{0} α (SubNegMonoid.toAddMonoid.{0} α (AddGroup.toSubNegMonoid.{0} α _inst_1)))) (SubNegMonoid.toHasSub.{0} α (AddGroup.toSubNegMonoid.{0} α _inst_1)) (List.nil.{0} α) as) (List.Func.neg.{0} α (SubNegMonoid.toHasNeg.{0} α (AddGroup.toSubNegMonoid.{0} α _inst_1)) as)
but is expected to have type
  forall {α : Type} [_inst_1 : AddGroup.{0} α] (as : List.{0} α), Eq.{1} (List.{0} α) (List.Func.sub.{0} α (NegZeroClass.toZero.{0} α (SubNegZeroMonoid.toNegZeroClass.{0} α (SubtractionMonoid.toSubNegZeroMonoid.{0} α (AddGroup.toSubtractionMonoid.{0} α _inst_1)))) (SubNegMonoid.toSub.{0} α (AddGroup.toSubNegMonoid.{0} α _inst_1)) (List.nil.{0} α) as) (List.Func.neg.{0} α (NegZeroClass.toNeg.{0} α (SubNegZeroMonoid.toNegZeroClass.{0} α (SubtractionMonoid.toSubNegZeroMonoid.{0} α (AddGroup.toSubtractionMonoid.{0} α _inst_1)))) as)
Case conversion may be inaccurate. Consider using '#align list.func.nil_sub List.Func.nil_subₓ'. -/
@[simp]
theorem nil_sub {α : Type} [AddGroup α] (as : List α) : sub [] as = neg as :=
  by
  rw [sub, nil_pointwise]
  congr with x
  rw [zero_sub]
#align list.func.nil_sub List.Func.nil_sub

/- warning: list.func.sub_nil -> List.Func.sub_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type} [_inst_1 : AddGroup.{0} α] (as : List.{0} α), Eq.{1} (List.{0} α) (List.Func.sub.{0} α (AddZeroClass.toHasZero.{0} α (AddMonoid.toAddZeroClass.{0} α (SubNegMonoid.toAddMonoid.{0} α (AddGroup.toSubNegMonoid.{0} α _inst_1)))) (SubNegMonoid.toHasSub.{0} α (AddGroup.toSubNegMonoid.{0} α _inst_1)) as (List.nil.{0} α)) as
but is expected to have type
  forall {α : Type} [_inst_1 : AddGroup.{0} α] (as : List.{0} α), Eq.{1} (List.{0} α) (List.Func.sub.{0} α (NegZeroClass.toZero.{0} α (SubNegZeroMonoid.toNegZeroClass.{0} α (SubtractionMonoid.toSubNegZeroMonoid.{0} α (AddGroup.toSubtractionMonoid.{0} α _inst_1)))) (SubNegMonoid.toSub.{0} α (AddGroup.toSubNegMonoid.{0} α _inst_1)) as (List.nil.{0} α)) as
Case conversion may be inaccurate. Consider using '#align list.func.sub_nil List.Func.sub_nilₓ'. -/
@[simp]
theorem sub_nil {α : Type} [AddGroup α] (as : List α) : sub as [] = as :=
  by
  rw [sub, pointwise_nil]
  apply Eq.trans _ (map_id as)
  congr with x
  rw [sub_zero, id]
#align list.func.sub_nil List.Func.sub_nil

end Func

end List

