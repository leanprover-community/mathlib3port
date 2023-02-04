/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.basic
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Lemmas
import Mathbin.Data.List.Perm

/-!
# Multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
These are implemented as the quotient of a list by permutations.
## Notation
We define the global infix notation `::ₘ` for `multiset.cons`.
-/


open List Subtype Nat

variable {α : Type _} {β : Type _} {γ : Type _}

#print Multiset /-
/-- `multiset α` is the quotient of `list α` by list permutation. The result
  is a type of finite sets with duplicates allowed.  -/
def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)
#align multiset Multiset
-/

namespace Multiset

instance : Coe (List α) (Multiset α) :=
  ⟨Quot.mk _⟩

#print Multiset.quot_mk_to_coe /-
@[simp]
theorem quot_mk_to_coe (l : List α) : @Eq (Multiset α) ⟦l⟧ l :=
  rfl
#align multiset.quot_mk_to_coe Multiset.quot_mk_to_coe
-/

#print Multiset.quot_mk_to_coe' /-
@[simp]
theorem quot_mk_to_coe' (l : List α) : @Eq (Multiset α) (Quot.mk (· ≈ ·) l) l :=
  rfl
#align multiset.quot_mk_to_coe' Multiset.quot_mk_to_coe'
-/

#print Multiset.quot_mk_to_coe'' /-
@[simp]
theorem quot_mk_to_coe'' (l : List α) : @Eq (Multiset α) (Quot.mk Setoid.r l) l :=
  rfl
#align multiset.quot_mk_to_coe'' Multiset.quot_mk_to_coe''
-/

#print Multiset.coe_eq_coe /-
@[simp]
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂ :=
  Quotient.eq'
#align multiset.coe_eq_coe Multiset.coe_eq_coe
-/

#print Multiset.decidableEq /-
instance decidableEq [DecidableEq α] : DecidableEq (Multiset α)
  | s₁, s₂ => Quotient.recOnSubsingleton₂ s₁ s₂ fun l₁ l₂ => decidable_of_iff' _ Quotient.eq'
#align multiset.has_decidable_eq Multiset.decidableEq
-/

#print Multiset.sizeOf /-
/-- defines a size for a multiset by referring to the size of the underlying list -/
protected def sizeOf [SizeOf α] (s : Multiset α) : ℕ :=
  Quot.liftOn s SizeOf.sizeOf fun l₁ l₂ => Perm.sizeOf_eq_sizeOf
#align multiset.sizeof Multiset.sizeOf
-/

instance hasSizeof [SizeOf α] : SizeOf (Multiset α) :=
  ⟨Multiset.sizeOf⟩
#align multiset.has_sizeof Multiset.hasSizeof

/-! ### Empty multiset -/


#print Multiset.zero /-
/-- `0 : multiset α` is the empty set -/
protected def zero : Multiset α :=
  @nil α
#align multiset.zero Multiset.zero
-/

instance : Zero (Multiset α) :=
  ⟨Multiset.zero⟩

instance : EmptyCollection (Multiset α) :=
  ⟨0⟩

#print Multiset.inhabitedMultiset /-
instance inhabitedMultiset : Inhabited (Multiset α) :=
  ⟨0⟩
#align multiset.inhabited_multiset Multiset.inhabitedMultiset
-/

#print Multiset.coe_nil /-
@[simp]
theorem coe_nil : (@nil α : Multiset α) = 0 :=
  rfl
#align multiset.coe_nil Multiset.coe_nil
-/

#print Multiset.empty_eq_zero /-
@[simp]
theorem empty_eq_zero : (∅ : Multiset α) = 0 :=
  rfl
#align multiset.empty_eq_zero Multiset.empty_eq_zero
-/

#print Multiset.coe_eq_zero /-
@[simp]
theorem coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ l = [] :=
  Iff.trans coe_eq_coe perm_nil
#align multiset.coe_eq_zero Multiset.coe_eq_zero
-/

#print Multiset.coe_eq_zero_iff_isEmpty /-
theorem coe_eq_zero_iff_isEmpty (l : List α) : (l : Multiset α) = 0 ↔ l.Empty :=
  Iff.trans (coe_eq_zero l) isEmpty_iff_eq_nil.symm
#align multiset.coe_eq_zero_iff_empty Multiset.coe_eq_zero_iff_isEmpty
-/

/-! ### `multiset.cons` -/


#print Multiset.cons /-
/-- `cons a s` is the multiset which contains `s` plus one more
  instance of `a`. -/
def cons (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (a :: l : Multiset α)) fun l₁ l₂ p => Quot.sound (p.cons a)
#align multiset.cons Multiset.cons
-/

-- mathport name: «expr ::ₘ »
infixr:67 " ::ₘ " => Multiset.cons

instance : Insert α (Multiset α) :=
  ⟨cons⟩

#print Multiset.insert_eq_cons /-
@[simp]
theorem insert_eq_cons (a : α) (s : Multiset α) : insert a s = a ::ₘ s :=
  rfl
#align multiset.insert_eq_cons Multiset.insert_eq_cons
-/

#print Multiset.cons_coe /-
@[simp]
theorem cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α) = (a :: l : List α) :=
  rfl
#align multiset.cons_coe Multiset.cons_coe
-/

#print Multiset.cons_inj_left /-
@[simp]
theorem cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ s = b ::ₘ s ↔ a = b :=
  ⟨Quot.inductionOn s fun l e =>
      have : [a] ++ l ~ [b] ++ l := Quotient.exact e
      singleton_perm_singleton.1 <| (perm_append_right_iff _).1 this,
    congr_arg _⟩
#align multiset.cons_inj_left Multiset.cons_inj_left
-/

#print Multiset.cons_inj_right /-
@[simp]
theorem cons_inj_right (a : α) : ∀ {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t := by
  rintro ⟨l₁⟩ ⟨l₂⟩ <;> simp
#align multiset.cons_inj_right Multiset.cons_inj_right
-/

#print Multiset.induction /-
@[recursor 5]
protected theorem induction {p : Multiset α → Prop} (h₁ : p 0)
    (h₂ : ∀ ⦃a : α⦄ {s : Multiset α}, p s → p (a ::ₘ s)) : ∀ s, p s := by
  rintro ⟨l⟩ <;> induction' l with _ _ ih <;> [exact h₁, exact h₂ ih]
#align multiset.induction Multiset.induction
-/

#print Multiset.induction_on /-
@[elab_as_elim]
protected theorem induction_on {p : Multiset α → Prop} (s : Multiset α) (h₁ : p 0)
    (h₂ : ∀ ⦃a : α⦄ {s : Multiset α}, p s → p (a ::ₘ s)) : p s :=
  Multiset.induction h₁ h₂ s
#align multiset.induction_on Multiset.induction_on
-/

#print Multiset.cons_swap /-
theorem cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
  Quot.inductionOn s fun l => Quotient.sound <| Perm.swap _ _ _
#align multiset.cons_swap Multiset.cons_swap
-/

section Rec

variable {C : Multiset α → Sort _}

#print Multiset.rec /-
/-- Dependent recursor on multisets.
TODO: should be @[recursor 6], but then the definition of `multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected def rec (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq :
      ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b)))
    (m : Multiset α) : C m :=
  Quotient.hrecOn m (@List.rec α (fun l => C ⟦l⟧) C_0 fun a l b => C_cons a ⟦l⟧ b) fun l l' h =>
    h.rec_heq
      (fun a l l' b b' hl => by
        have : ⟦l⟧ = ⟦l'⟧ := Quot.sound hl
        cc)
      fun a a' l => C_cons_heq a a' ⟦l⟧
#align multiset.rec Multiset.rec
-/

#print Multiset.recOn /-
/-- Companion to `multiset.rec` with more convenient argument order. -/
@[elab_as_elim]
protected def recOn (m : Multiset α) (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq :
      ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b))) :
    C m :=
  Multiset.rec C_0 C_cons C_cons_heq m
#align multiset.rec_on Multiset.recOn
-/

variable {C_0 : C 0} {C_cons : ∀ a m, C m → C (a ::ₘ m)}
  {C_cons_heq :
    ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b))}

#print Multiset.recOn_0 /-
@[simp]
theorem recOn_0 : @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0 :=
  rfl
#align multiset.rec_on_0 Multiset.recOn_0
-/

/- warning: multiset.rec_on_cons -> Multiset.recOn_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {C : (Multiset.{u1} α) -> Sort.{u2}} {C_0 : C (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))} {C_cons : forall (a : α) (m : Multiset.{u1} α), (C m) -> (C (Multiset.cons.{u1} α a m))} {C_cons_heq : forall (a : α) (a' : α) (m : Multiset.{u1} α) (b : C m), HEq.{u2} (C (Multiset.cons.{u1} α a (Multiset.cons.{u1} α a' m))) (C_cons a (Multiset.cons.{u1} α a' m) (C_cons a' m b)) (C (Multiset.cons.{u1} α a' (Multiset.cons.{u1} α a m))) (C_cons a' (Multiset.cons.{u1} α a m) (C_cons a m b))} (a : α) (m : Multiset.{u1} α), Eq.{u2} (C (Multiset.cons.{u1} α a m)) (Multiset.recOn.{u1, u2} α C (Multiset.cons.{u1} α a m) C_0 C_cons C_cons_heq) (C_cons a m (Multiset.recOn.{u1, u2} α C m C_0 C_cons C_cons_heq))
but is expected to have type
  forall {α : Type.{u2}} {C : (Multiset.{u2} α) -> Sort.{u1}} {C_0 : C (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α)))} {C_cons : forall (a : α) (m : Multiset.{u2} α), (C m) -> (C (Multiset.cons.{u2} α a m))} {C_cons_heq : forall (a : α) (a' : α) (m : Multiset.{u2} α) (b : C m), HEq.{u1} (C (Multiset.cons.{u2} α a (Multiset.cons.{u2} α a' m))) (C_cons a (Multiset.cons.{u2} α a' m) (C_cons a' m b)) (C (Multiset.cons.{u2} α a' (Multiset.cons.{u2} α a m))) (C_cons a' (Multiset.cons.{u2} α a m) (C_cons a m b))} (a : α) (m : Multiset.{u2} α), Eq.{u1} (C (Multiset.cons.{u2} α a m)) (Multiset.recOn.{u2, u1} α (fun (x._@.Mathlib.Data.Multiset.Basic._hyg.1938 : Multiset.{u2} α) => C x._@.Mathlib.Data.Multiset.Basic._hyg.1938) (Multiset.cons.{u2} α a m) C_0 C_cons C_cons_heq) (C_cons a m (Multiset.recOn.{u2, u1} α (fun (x._@.Mathlib.Data.Multiset.Basic._hyg.1910 : Multiset.{u2} α) => C x._@.Mathlib.Data.Multiset.Basic._hyg.1910) m C_0 C_cons C_cons_heq))
Case conversion may be inaccurate. Consider using '#align multiset.rec_on_cons Multiset.recOn_consₓ'. -/
@[simp]
theorem recOn_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).recOn C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq) :=
  Quotient.inductionOn m fun l => rfl
#align multiset.rec_on_cons Multiset.recOn_cons

end Rec

section Mem

#print Multiset.Mem /-
/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def Mem (a : α) (s : Multiset α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun l₁ l₂ (e : l₁ ~ l₂) => propext <| e.mem_iff
#align multiset.mem Multiset.Mem
-/

instance : Membership α (Multiset α) :=
  ⟨Mem⟩

#print Multiset.mem_coe /-
@[simp]
theorem mem_coe {a : α} {l : List α} : a ∈ (l : Multiset α) ↔ a ∈ l :=
  Iff.rfl
#align multiset.mem_coe Multiset.mem_coe
-/

#print Multiset.decidableMem /-
instance decidableMem [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a ∈ s) :=
  Quot.recOnSubsingleton' s <| List.decidableMem a
#align multiset.decidable_mem Multiset.decidableMem
-/

#print Multiset.mem_cons /-
@[simp]
theorem mem_cons {a b : α} {s : Multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
  Quot.inductionOn s fun l => Iff.rfl
#align multiset.mem_cons Multiset.mem_cons
-/

#print Multiset.mem_cons_of_mem /-
theorem mem_cons_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
  mem_cons.2 <| Or.inr h
#align multiset.mem_cons_of_mem Multiset.mem_cons_of_mem
-/

#print Multiset.mem_cons_self /-
@[simp]
theorem mem_cons_self (a : α) (s : Multiset α) : a ∈ a ::ₘ s :=
  mem_cons.2 (Or.inl rfl)
#align multiset.mem_cons_self Multiset.mem_cons_self
-/

#print Multiset.forall_mem_cons /-
theorem forall_mem_cons {p : α → Prop} {a : α} {s : Multiset α} :
    (∀ x ∈ a ::ₘ s, p x) ↔ p a ∧ ∀ x ∈ s, p x :=
  Quotient.inductionOn' s fun L => List.forall_mem_cons
#align multiset.forall_mem_cons Multiset.forall_mem_cons
-/

#print Multiset.exists_cons_of_mem /-
theorem exists_cons_of_mem {s : Multiset α} {a : α} : a ∈ s → ∃ t, s = a ::ₘ t :=
  Quot.inductionOn s fun l (h : a ∈ l) =>
    let ⟨l₁, l₂, e⟩ := mem_split h
    e.symm ▸ ⟨(l₁ ++ l₂ : List α), Quot.sound perm_middle⟩
#align multiset.exists_cons_of_mem Multiset.exists_cons_of_mem
-/

#print Multiset.not_mem_zero /-
@[simp]
theorem not_mem_zero (a : α) : a ∉ (0 : Multiset α) :=
  id
#align multiset.not_mem_zero Multiset.not_mem_zero
-/

#print Multiset.eq_zero_of_forall_not_mem /-
theorem eq_zero_of_forall_not_mem {s : Multiset α} : (∀ x, x ∉ s) → s = 0 :=
  Quot.inductionOn s fun l H => by rw [eq_nil_iff_forall_not_mem.mpr H] <;> rfl
#align multiset.eq_zero_of_forall_not_mem Multiset.eq_zero_of_forall_not_mem
-/

#print Multiset.eq_zero_iff_forall_not_mem /-
theorem eq_zero_iff_forall_not_mem {s : Multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
  ⟨fun h => h.symm ▸ fun _ => not_false, eq_zero_of_forall_not_mem⟩
#align multiset.eq_zero_iff_forall_not_mem Multiset.eq_zero_iff_forall_not_mem
-/

#print Multiset.exists_mem_of_ne_zero /-
theorem exists_mem_of_ne_zero {s : Multiset α} : s ≠ 0 → ∃ a : α, a ∈ s :=
  Quot.inductionOn s fun l hl =>
    match l, hl with
    | [] => fun h => False.elim <| h rfl
    | a :: l => fun _ => ⟨a, by simp⟩
#align multiset.exists_mem_of_ne_zero Multiset.exists_mem_of_ne_zero
-/

#print Multiset.empty_or_exists_mem /-
theorem empty_or_exists_mem (s : Multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
  or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero
#align multiset.empty_or_exists_mem Multiset.empty_or_exists_mem
-/

#print Multiset.zero_ne_cons /-
@[simp]
theorem zero_ne_cons {a : α} {m : Multiset α} : 0 ≠ a ::ₘ m := fun h =>
  have : a ∈ (0 : Multiset α) := h.symm ▸ mem_cons_self _ _
  not_mem_zero _ this
#align multiset.zero_ne_cons Multiset.zero_ne_cons
-/

#print Multiset.cons_ne_zero /-
@[simp]
theorem cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m ≠ 0 :=
  zero_ne_cons.symm
#align multiset.cons_ne_zero Multiset.cons_ne_zero
-/

#print Multiset.cons_eq_cons /-
theorem cons_eq_cons {a b : α} {as bs : Multiset α} :
    a ::ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a ≠ b ∧ ∃ cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs :=
  by
  haveI : DecidableEq α := Classical.decEq α
  constructor
  · intro eq
    by_cases a = b
    · subst h
      simp_all
    · have : a ∈ b ::ₘ bs := Eq ▸ mem_cons_self _ _
      have : a ∈ bs := by simpa [h]
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩
      simp [h, hcs]
      have : a ::ₘ as = b ::ₘ a ::ₘ cs := by simp [Eq, hcs]
      have : a ::ₘ as = a ::ₘ b ::ₘ cs := by rwa [cons_swap]
      simpa using this
  · intro h
    rcases h with (⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩)
    · simp [*]
    · simp [*, cons_swap a b]
#align multiset.cons_eq_cons Multiset.cons_eq_cons
-/

end Mem

/-! ### Singleton -/


instance : Singleton α (Multiset α) :=
  ⟨fun a => a ::ₘ 0⟩

instance : IsLawfulSingleton α (Multiset α) :=
  ⟨fun a => rfl⟩

#print Multiset.cons_zero /-
@[simp]
theorem cons_zero (a : α) : a ::ₘ 0 = {a} :=
  rfl
#align multiset.cons_zero Multiset.cons_zero
-/

#print Multiset.coe_singleton /-
@[simp, norm_cast]
theorem coe_singleton (a : α) : ([a] : Multiset α) = {a} :=
  rfl
#align multiset.coe_singleton Multiset.coe_singleton
-/

#print Multiset.mem_singleton /-
@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Multiset α) ↔ b = a := by
  simp only [← cons_zero, mem_cons, iff_self_iff, or_false_iff, not_mem_zero]
#align multiset.mem_singleton Multiset.mem_singleton
-/

#print Multiset.mem_singleton_self /-
theorem mem_singleton_self (a : α) : a ∈ ({a} : Multiset α) :=
  by
  rw [← cons_zero]
  exact mem_cons_self _ _
#align multiset.mem_singleton_self Multiset.mem_singleton_self
-/

#print Multiset.singleton_inj /-
@[simp]
theorem singleton_inj {a b : α} : ({a} : Multiset α) = {b} ↔ a = b :=
  by
  simp_rw [← cons_zero]
  exact cons_inj_left _
#align multiset.singleton_inj Multiset.singleton_inj
-/

@[simp, norm_cast]
theorem coe_eq_singleton {l : List α} {a : α} : (l : Multiset α) = {a} ↔ l = [a] := by
  rw [← coe_singleton, coe_eq_coe, List.perm_singleton]
#align multiset.coe_eq_singleton Multiset.coe_eq_singleton

#print Multiset.singleton_eq_cons_iff /-
@[simp]
theorem singleton_eq_cons_iff {a b : α} (m : Multiset α) : {a} = b ::ₘ m ↔ a = b ∧ m = 0 :=
  by
  rw [← cons_zero, cons_eq_cons]
  simp [eq_comm]
#align multiset.singleton_eq_cons_iff Multiset.singleton_eq_cons_iff
-/

#print Multiset.pair_comm /-
theorem pair_comm (x y : α) : ({x, y} : Multiset α) = {y, x} :=
  cons_swap x y 0
#align multiset.pair_comm Multiset.pair_comm
-/

/-! ### `multiset.subset` -/


section Subset

#print Multiset.Subset /-
/-- `s ⊆ t` is the lift of the list subset relation. It means that any
  element with nonzero multiplicity in `s` has nonzero multiplicity in `t`,
  but it does not imply that the multiplicity of `a` in `s` is less or equal than in `t`;
  see `s ≤ t` for this relation. -/
protected def Subset (s t : Multiset α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → a ∈ t
#align multiset.subset Multiset.Subset
-/

instance : HasSubset (Multiset α) :=
  ⟨Multiset.Subset⟩

instance : HasSSubset (Multiset α) :=
  ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩

#print Multiset.coe_subset /-
@[simp]
theorem coe_subset {l₁ l₂ : List α} : (l₁ : Multiset α) ⊆ l₂ ↔ l₁ ⊆ l₂ :=
  Iff.rfl
#align multiset.coe_subset Multiset.coe_subset
-/

#print Multiset.Subset.refl /-
@[simp]
theorem Subset.refl (s : Multiset α) : s ⊆ s := fun a h => h
#align multiset.subset.refl Multiset.Subset.refl
-/

#print Multiset.Subset.trans /-
theorem Subset.trans {s t u : Multiset α} : s ⊆ t → t ⊆ u → s ⊆ u := fun h₁ h₂ a m => h₂ (h₁ m)
#align multiset.subset.trans Multiset.Subset.trans
-/

#print Multiset.subset_iff /-
theorem subset_iff {s t : Multiset α} : s ⊆ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t :=
  Iff.rfl
#align multiset.subset_iff Multiset.subset_iff
-/

#print Multiset.mem_of_subset /-
theorem mem_of_subset {s t : Multiset α} {a : α} (h : s ⊆ t) : a ∈ s → a ∈ t :=
  @h _
#align multiset.mem_of_subset Multiset.mem_of_subset
-/

#print Multiset.zero_subset /-
@[simp]
theorem zero_subset (s : Multiset α) : 0 ⊆ s := fun a => (not_mem_nil a).elim
#align multiset.zero_subset Multiset.zero_subset
-/

#print Multiset.subset_cons /-
theorem subset_cons (s : Multiset α) (a : α) : s ⊆ a ::ₘ s := fun _ => mem_cons_of_mem
#align multiset.subset_cons Multiset.subset_cons
-/

#print Multiset.ssubset_cons /-
theorem ssubset_cons {s : Multiset α} {a : α} (ha : a ∉ s) : s ⊂ a ::ₘ s :=
  ⟨subset_cons _ _, fun h => ha <| h <| mem_cons_self _ _⟩
#align multiset.ssubset_cons Multiset.ssubset_cons
-/

#print Multiset.cons_subset /-
@[simp]
theorem cons_subset {a : α} {s t : Multiset α} : a ::ₘ s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp [subset_iff, or_imp, forall_and]
#align multiset.cons_subset Multiset.cons_subset
-/

#print Multiset.cons_subset_cons /-
theorem cons_subset_cons {a : α} {s t : Multiset α} : s ⊆ t → a ::ₘ s ⊆ a ::ₘ t :=
  Quotient.induction_on₂ s t fun _ _ => cons_subset_cons _
#align multiset.cons_subset_cons Multiset.cons_subset_cons
-/

#print Multiset.eq_zero_of_subset_zero /-
theorem eq_zero_of_subset_zero {s : Multiset α} (h : s ⊆ 0) : s = 0 :=
  eq_zero_of_forall_not_mem h
#align multiset.eq_zero_of_subset_zero Multiset.eq_zero_of_subset_zero
-/

#print Multiset.subset_zero /-
theorem subset_zero {s : Multiset α} : s ⊆ 0 ↔ s = 0 :=
  ⟨eq_zero_of_subset_zero, fun xeq => xeq.symm ▸ Subset.refl 0⟩
#align multiset.subset_zero Multiset.subset_zero
-/

#print Multiset.induction_on' /-
theorem induction_on' {p : Multiset α → Prop} (S : Multiset α) (h₁ : p 0)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → p s → p (insert a s)) : p S :=
  @Multiset.induction_on α (fun T => T ⊆ S → p T) S (fun _ => h₁)
    (fun a s hps hs =>
      let ⟨hS, sS⟩ := cons_subset.1 hs
      h₂ hS sS (hps sS))
    (Subset.refl S)
#align multiset.induction_on' Multiset.induction_on'
-/

end Subset

/-! ### `multiset.to_list` -/


section ToList

#print Multiset.toList /-
/-- Produces a list of the elements in the multiset using choice. -/
noncomputable def toList (s : Multiset α) :=
  s.out'
#align multiset.to_list Multiset.toList
-/

#print Multiset.coe_toList /-
@[simp, norm_cast]
theorem coe_toList (s : Multiset α) : (s.toList : Multiset α) = s :=
  s.out_eq'
#align multiset.coe_to_list Multiset.coe_toList
-/

#print Multiset.toList_eq_nil /-
@[simp]
theorem toList_eq_nil {s : Multiset α} : s.toList = [] ↔ s = 0 := by rw [← coe_eq_zero, coe_to_list]
#align multiset.to_list_eq_nil Multiset.toList_eq_nil
-/

#print Multiset.empty_toList /-
@[simp]
theorem empty_toList {s : Multiset α} : s.toList.Empty ↔ s = 0 :=
  isEmpty_iff_eq_nil.trans toList_eq_nil
#align multiset.empty_to_list Multiset.empty_toList
-/

#print Multiset.toList_zero /-
@[simp]
theorem toList_zero : (Multiset.toList 0 : List α) = [] :=
  toList_eq_nil.mpr rfl
#align multiset.to_list_zero Multiset.toList_zero
-/

#print Multiset.mem_toList /-
@[simp]
theorem mem_toList {a : α} {s : Multiset α} : a ∈ s.toList ↔ a ∈ s := by rw [← mem_coe, coe_to_list]
#align multiset.mem_to_list Multiset.mem_toList
-/

@[simp]
theorem toList_eq_singleton_iff {a : α} {m : Multiset α} : m.toList = [a] ↔ m = {a} := by
  rw [← perm_singleton, ← coe_eq_coe, coe_to_list, coe_singleton]
#align multiset.to_list_eq_singleton_iff Multiset.toList_eq_singleton_iff

@[simp]
theorem toList_singleton (a : α) : ({a} : Multiset α).toList = [a] :=
  Multiset.toList_eq_singleton_iff.2 rfl
#align multiset.to_list_singleton Multiset.toList_singleton

end ToList

/-! ### Partial order on `multiset`s -/


#print Multiset.Le /-
/-- `s ≤ t` means that `s` is a sublist of `t` (up to permutation).
  Equivalently, `s ≤ t` means that `count a s ≤ count a t` for all `a`. -/
protected def Le (s t : Multiset α) : Prop :=
  Quotient.liftOn₂ s t (· <+~ ·) fun v₁ v₂ w₁ w₂ p₁ p₂ =>
    propext (p₂.subperm_left.trans p₁.subperm_right)
#align multiset.le Multiset.Le
-/

instance : PartialOrder (Multiset α) where
  le := Multiset.Le
  le_refl := by rintro ⟨l⟩ <;> exact subperm.refl _
  le_trans := by rintro ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩ <;> exact @subperm.trans _ _ _ _
  le_antisymm := by rintro ⟨l₁⟩ ⟨l₂⟩ h₁ h₂ <;> exact Quot.sound (subperm.antisymm h₁ h₂)

/- warning: multiset.decidable_le -> Multiset.decidableLE is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], DecidableRel.{succ u1} (Multiset.{u1} α) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], DecidableRel.{succ u1} (Multiset.{u1} α) (fun (x._@.Mathlib.Data.Multiset.Basic._hyg.4358 : Multiset.{u1} α) (x._@.Mathlib.Data.Multiset.Basic._hyg.4360 : Multiset.{u1} α) => LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) x._@.Mathlib.Data.Multiset.Basic._hyg.4358 x._@.Mathlib.Data.Multiset.Basic._hyg.4360)
Case conversion may be inaccurate. Consider using '#align multiset.decidable_le Multiset.decidableLEₓ'. -/
instance decidableLE [DecidableEq α] : DecidableRel ((· ≤ ·) : Multiset α → Multiset α → Prop) :=
  fun s t => Quotient.recOnSubsingleton₂ s t List.decidableSubperm
#align multiset.decidable_le Multiset.decidableLE

section

variable {s t : Multiset α} {a : α}

/- warning: multiset.subset_of_le -> Multiset.subset_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Multiset.{u1} α) (Multiset.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Multiset.{u1} α) (Multiset.instHasSubsetMultiset.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align multiset.subset_of_le Multiset.subset_of_leₓ'. -/
theorem subset_of_le : s ≤ t → s ⊆ t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => Subperm.subset
#align multiset.subset_of_le Multiset.subset_of_le

/- warning: multiset.le.subset -> Multiset.Le.subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Multiset.{u1} α) (Multiset.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Multiset.{u1} α) (Multiset.instHasSubsetMultiset.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align multiset.le.subset Multiset.Le.subsetₓ'. -/
alias subset_of_le ← le.subset
#align multiset.le.subset Multiset.Le.subset

/- warning: multiset.mem_of_le -> Multiset.mem_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {a : α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a t)
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {a : α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a t)
Case conversion may be inaccurate. Consider using '#align multiset.mem_of_le Multiset.mem_of_leₓ'. -/
theorem mem_of_le (h : s ≤ t) : a ∈ s → a ∈ t :=
  mem_of_subset (subset_of_le h)
#align multiset.mem_of_le Multiset.mem_of_le

#print Multiset.not_mem_mono /-
theorem not_mem_mono (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| @h _
#align multiset.not_mem_mono Multiset.not_mem_mono
-/

/- warning: multiset.coe_le -> Multiset.coe_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l₂)) (List.Subperm.{u1} α l₁ l₂)
but is expected to have type
  forall {α : Type.{u1}} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.ofList.{u1} α l₁) (Multiset.ofList.{u1} α l₂)) (List.Subperm.{u1} α l₁ l₂)
Case conversion may be inaccurate. Consider using '#align multiset.coe_le Multiset.coe_leₓ'. -/
@[simp]
theorem coe_le {l₁ l₂ : List α} : (l₁ : Multiset α) ≤ l₂ ↔ l₁ <+~ l₂ :=
  Iff.rfl
#align multiset.coe_le Multiset.coe_le

/- warning: multiset.le_induction_on -> Multiset.leInductionOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {C : (Multiset.{u1} α) -> (Multiset.{u1} α) -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (forall {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Sublist.{u1} α l₁ l₂) -> (C ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l₂))) -> (C s t)
but is expected to have type
  forall {α : Type.{u1}} {C : (Multiset.{u1} α) -> (Multiset.{u1} α) -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (forall {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Sublist.{u1} α l₁ l₂) -> (C (Multiset.ofList.{u1} α l₁) (Multiset.ofList.{u1} α l₂))) -> (C s t)
Case conversion may be inaccurate. Consider using '#align multiset.le_induction_on Multiset.leInductionOnₓ'. -/
@[elab_as_elim]
theorem leInductionOn {C : Multiset α → Multiset α → Prop} {s t : Multiset α} (h : s ≤ t)
    (H : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → C l₁ l₂) : C s t :=
  Quotient.induction_on₂ s t (fun l₁ l₂ ⟨l, p, s⟩ => (show ⟦l⟧ = ⟦l₁⟧ from Quot.sound p) ▸ H s) h
#align multiset.le_induction_on Multiset.leInductionOn

/- warning: multiset.zero_le -> Multiset.zero_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))) s
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α))) s
Case conversion may be inaccurate. Consider using '#align multiset.zero_le Multiset.zero_leₓ'. -/
theorem zero_le (s : Multiset α) : 0 ≤ s :=
  Quot.inductionOn s fun l => (nil_sublist l).Subperm
#align multiset.zero_le Multiset.zero_le

instance : OrderBot (Multiset α) :=
  ⟨0, zero_le⟩

/- warning: multiset.bot_eq_zero -> Multiset.bot_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Multiset.{u1} α) (Bot.bot.{u1} (Multiset.{u1} α) (OrderBot.toHasBot.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.orderBot.{u1} α))) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Multiset.{u1} α) (Bot.bot.{u1} (Multiset.{u1} α) (OrderBot.toBot.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u1} α))) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))
Case conversion may be inaccurate. Consider using '#align multiset.bot_eq_zero Multiset.bot_eq_zeroₓ'. -/
/-- This is a `rfl` and `simp` version of `bot_eq_zero`. -/
@[simp]
theorem bot_eq_zero : (⊥ : Multiset α) = 0 :=
  rfl
#align multiset.bot_eq_zero Multiset.bot_eq_zero

/- warning: multiset.le_zero -> Multiset.le_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) (Eq.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) (Eq.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α))))
Case conversion may be inaccurate. Consider using '#align multiset.le_zero Multiset.le_zeroₓ'. -/
theorem le_zero : s ≤ 0 ↔ s = 0 :=
  le_bot_iff
#align multiset.le_zero Multiset.le_zero

/- warning: multiset.lt_cons_self -> Multiset.lt_cons_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (a : α), LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.cons.{u1} α a s)
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (a : α), LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.cons.{u1} α a s)
Case conversion may be inaccurate. Consider using '#align multiset.lt_cons_self Multiset.lt_cons_selfₓ'. -/
theorem lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ s :=
  Quot.inductionOn s fun l =>
    suffices l <+~ a :: l ∧ ¬l ~ a :: l by simpa [lt_iff_le_and_ne]
    ⟨(sublist_cons _ _).Subperm, fun p => ne_of_lt (lt_succ_self (length l)) p.length_eq⟩
#align multiset.lt_cons_self Multiset.lt_cons_self

/- warning: multiset.le_cons_self -> Multiset.le_cons_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (a : α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.cons.{u1} α a s)
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (a : α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.cons.{u1} α a s)
Case conversion may be inaccurate. Consider using '#align multiset.le_cons_self Multiset.le_cons_selfₓ'. -/
theorem le_cons_self (s : Multiset α) (a : α) : s ≤ a ::ₘ s :=
  le_of_lt <| lt_cons_self _ _
#align multiset.le_cons_self Multiset.le_cons_self

/- warning: multiset.cons_le_cons_iff -> Multiset.cons_le_cons_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} (a : α), Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.cons.{u1} α a s) (Multiset.cons.{u1} α a t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} (a : α), Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.cons.{u1} α a s) (Multiset.cons.{u1} α a t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t)
Case conversion may be inaccurate. Consider using '#align multiset.cons_le_cons_iff Multiset.cons_le_cons_iffₓ'. -/
theorem cons_le_cons_iff (a : α) : a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => subperm_cons a
#align multiset.cons_le_cons_iff Multiset.cons_le_cons_iff

/- warning: multiset.cons_le_cons -> Multiset.cons_le_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} (a : α), (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.cons.{u1} α a s) (Multiset.cons.{u1} α a t))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} (a : α), (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.cons.{u1} α a s) (Multiset.cons.{u1} α a t))
Case conversion may be inaccurate. Consider using '#align multiset.cons_le_cons Multiset.cons_le_consₓ'. -/
theorem cons_le_cons (a : α) : s ≤ t → a ::ₘ s ≤ a ::ₘ t :=
  (cons_le_cons_iff a).2
#align multiset.cons_le_cons Multiset.cons_le_cons

/- warning: multiset.le_cons_of_not_mem -> Multiset.le_cons_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s)) -> (Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.cons.{u1} α a t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {a : α}, (Not (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s)) -> (Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.cons.{u1} α a t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t))
Case conversion may be inaccurate. Consider using '#align multiset.le_cons_of_not_mem Multiset.le_cons_of_not_memₓ'. -/
theorem le_cons_of_not_mem (m : a ∉ s) : s ≤ a ::ₘ t ↔ s ≤ t :=
  by
  refine' ⟨_, fun h => le_trans h <| le_cons_self _ _⟩
  suffices ∀ {t'} (_ : s ≤ t') (_ : a ∈ t'), a ::ₘ s ≤ t' by
    exact fun h => (cons_le_cons_iff a).1 (this h (mem_cons_self _ _))
  introv h
  revert m
  refine' le_induction_on h _
  introv s m₁ m₂
  rcases mem_split m₂ with ⟨r₁, r₂, rfl⟩
  exact
    perm_middle.subperm_left.2
      ((subperm_cons _).2 <| ((sublist_or_mem_of_sublist s).resolve_right m₁).Subperm)
#align multiset.le_cons_of_not_mem Multiset.le_cons_of_not_mem

#print Multiset.singleton_ne_zero /-
@[simp]
theorem singleton_ne_zero (a : α) : ({a} : Multiset α) ≠ 0 :=
  ne_of_gt (lt_cons_self _ _)
#align multiset.singleton_ne_zero Multiset.singleton_ne_zero
-/

/- warning: multiset.singleton_le -> Multiset.singleton_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a) s) (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a) s) (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align multiset.singleton_le Multiset.singleton_leₓ'. -/
@[simp]
theorem singleton_le {a : α} {s : Multiset α} : {a} ≤ s ↔ a ∈ s :=
  ⟨fun h => mem_of_le h (mem_singleton_self _), fun h =>
    let ⟨t, e⟩ := exists_cons_of_mem h
    e.symm ▸ cons_le_cons _ (zero_le _)⟩
#align multiset.singleton_le Multiset.singleton_le

end

/-! ### Additive monoid -/


#print Multiset.add /-
/-- The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`. -/
protected def add (s₁ s₂ : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s₁ s₂ (fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun v₁ v₂ w₁ w₂ p₁ p₂ =>
    Quot.sound <| p₁.append p₂
#align multiset.add Multiset.add
-/

instance : Add (Multiset α) :=
  ⟨Multiset.add⟩

#print Multiset.coe_add /-
@[simp]
theorem coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α) :=
  rfl
#align multiset.coe_add Multiset.coe_add
-/

#print Multiset.singleton_add /-
@[simp]
theorem singleton_add (a : α) (s : Multiset α) : {a} + s = a ::ₘ s :=
  rfl
#align multiset.singleton_add Multiset.singleton_add
-/

private theorem add_le_add_iff_left' {s t u : Multiset α} : s + t ≤ s + u ↔ t ≤ u :=
  Quotient.induction_on₃ s t u fun l₁ l₂ l₃ => subperm_append_left _
#align multiset.add_le_add_iff_left' multiset.add_le_add_iff_left'

instance : CovariantClass (Multiset α) (Multiset α) (· + ·) (· ≤ ·) :=
  ⟨fun s t u => add_le_add_iff_left'.2⟩

instance : ContravariantClass (Multiset α) (Multiset α) (· + ·) (· ≤ ·) :=
  ⟨fun s t u => add_le_add_iff_left'.1⟩

instance : OrderedCancelAddCommMonoid (Multiset α) :=
  { @Multiset.partialOrder α with
    zero := 0
    add := (· + ·)
    add_comm := fun s t => Quotient.induction_on₂ s t fun l₁ l₂ => Quot.sound perm_append_comm
    add_assoc := fun s₁ s₂ s₃ =>
      Quotient.induction_on₃ s₁ s₂ s₃ fun l₁ l₂ l₃ => congr_arg coe <| append_assoc l₁ l₂ l₃
    zero_add := fun s => Quot.inductionOn s fun l => rfl
    add_zero := fun s => Quotient.inductionOn s fun l => congr_arg coe <| append_nil l
    add_le_add_left := fun s₁ s₂ => add_le_add_left
    le_of_add_le_add_left := fun s₁ s₂ s₃ => le_of_add_le_add_left }

/- warning: multiset.le_add_right -> Multiset.le_add_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t)
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t)
Case conversion may be inaccurate. Consider using '#align multiset.le_add_right Multiset.le_add_rightₓ'. -/
theorem le_add_right (s t : Multiset α) : s ≤ s + t := by simpa using add_le_add_left (zero_le t) s
#align multiset.le_add_right Multiset.le_add_right

/- warning: multiset.le_add_left -> Multiset.le_add_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) t s)
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) t s)
Case conversion may be inaccurate. Consider using '#align multiset.le_add_left Multiset.le_add_leftₓ'. -/
theorem le_add_left (s t : Multiset α) : s ≤ t + s := by simpa using add_le_add_right (zero_le t) s
#align multiset.le_add_left Multiset.le_add_left

/- warning: multiset.le_iff_exists_add -> Multiset.le_iff_exists_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) (Exists.{succ u1} (Multiset.{u1} α) (fun (u : Multiset.{u1} α) => Eq.{succ u1} (Multiset.{u1} α) t (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s u)))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) (Exists.{succ u1} (Multiset.{u1} α) (fun (u : Multiset.{u1} α) => Eq.{succ u1} (Multiset.{u1} α) t (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s u)))
Case conversion may be inaccurate. Consider using '#align multiset.le_iff_exists_add Multiset.le_iff_exists_addₓ'. -/
theorem le_iff_exists_add {s t : Multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
  ⟨fun h =>
    leInductionOn h fun l₁ l₂ s =>
      let ⟨l, p⟩ := s.exists_perm_append
      ⟨l, Quot.sound p⟩,
    fun ⟨u, e⟩ => e.symm ▸ le_add_right _ _⟩
#align multiset.le_iff_exists_add Multiset.le_iff_exists_add

instance : CanonicallyOrderedAddMonoid (Multiset α) :=
  { Multiset.orderBot,
    Multiset.orderedCancelAddCommMonoid with
    le_self_add := le_add_right
    exists_add_of_le := fun a b h =>
      leInductionOn h fun l₁ l₂ s =>
        let ⟨l, p⟩ := s.exists_perm_append
        ⟨l, Quot.sound p⟩ }

#print Multiset.cons_add /-
@[simp]
theorem cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a ::ₘ (s + t) := by
  rw [← singleton_add, ← singleton_add, add_assoc]
#align multiset.cons_add Multiset.cons_add
-/

#print Multiset.add_cons /-
@[simp]
theorem add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a ::ₘ (s + t) := by
  rw [add_comm, cons_add, add_comm]
#align multiset.add_cons Multiset.add_cons
-/

#print Multiset.mem_add /-
@[simp]
theorem mem_add {a : α} {s t : Multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => mem_append
#align multiset.mem_add Multiset.mem_add
-/

/- warning: multiset.mem_of_mem_nsmul -> Multiset.mem_of_mem_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α} {n : Nat}, (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) -> (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α} {n : Nat}, (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) -> (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align multiset.mem_of_mem_nsmul Multiset.mem_of_mem_nsmulₓ'. -/
theorem mem_of_mem_nsmul {a : α} {s : Multiset α} {n : ℕ} (h : a ∈ n • s) : a ∈ s :=
  by
  induction' n with n ih
  · rw [zero_nsmul] at h
    exact absurd h (not_mem_zero _)
  · rw [succ_nsmul, mem_add] at h
    exact h.elim id ih
#align multiset.mem_of_mem_nsmul Multiset.mem_of_mem_nsmul

/- warning: multiset.mem_nsmul -> Multiset.mem_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Iff (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Iff (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align multiset.mem_nsmul Multiset.mem_nsmulₓ'. -/
@[simp]
theorem mem_nsmul {a : α} {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : a ∈ n • s ↔ a ∈ s :=
  by
  refine' ⟨mem_of_mem_nsmul, fun h => _⟩
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h0
  rw [succ_nsmul, mem_add]
  exact Or.inl h
#align multiset.mem_nsmul Multiset.mem_nsmul

/- warning: multiset.nsmul_cons -> Multiset.nsmul_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} (n : Nat) (a : α), Eq.{succ u1} (Multiset.{u1} α) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n (Multiset.cons.{u1} α a s)) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a)) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} (n : Nat) (a : α), Eq.{succ u1} (Multiset.{u1} α) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n (Multiset.cons.{u1} α a s)) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a)) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s))
Case conversion may be inaccurate. Consider using '#align multiset.nsmul_cons Multiset.nsmul_consₓ'. -/
theorem nsmul_cons {s : Multiset α} (n : ℕ) (a : α) : n • (a ::ₘ s) = n • {a} + n • s := by
  rw [← singleton_add, nsmul_add]
#align multiset.nsmul_cons Multiset.nsmul_cons

/-! ### Cardinality -/


/- warning: multiset.card -> Multiset.card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)
but is expected to have type
  forall {α : Type.{u1}}, AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)
Case conversion may be inaccurate. Consider using '#align multiset.card Multiset.cardₓ'. -/
/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card : Multiset α →+ ℕ
    where
  toFun s := Quot.liftOn s length fun l₁ l₂ => Perm.length_eq
  map_zero' := rfl
  map_add' s t := Quotient.induction_on₂ s t length_append
#align multiset.card Multiset.card

/- warning: multiset.coe_card -> Multiset.coe_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l : List.{u1} α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) (List.length.{u1} α l)
but is expected to have type
  forall {α : Type.{u1}} (l : List.{u1} α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.ofList.{u1} α l)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.ofList.{u1} α l)) (List.length.{u1} α l)
Case conversion may be inaccurate. Consider using '#align multiset.coe_card Multiset.coe_cardₓ'. -/
@[simp]
theorem coe_card (l : List α) : card (l : Multiset α) = length l :=
  rfl
#align multiset.coe_card Multiset.coe_card

/- warning: multiset.length_to_list -> Multiset.length_toList is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α), Eq.{1} Nat (List.length.{u1} α (Multiset.toList.{u1} α s)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α), Eq.{1} Nat (List.length.{u1} α (Multiset.toList.{u1} α s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)
Case conversion may be inaccurate. Consider using '#align multiset.length_to_list Multiset.length_toListₓ'. -/
@[simp]
theorem length_toList (s : Multiset α) : s.toList.length = s.card := by rw [← coe_card, coe_to_list]
#align multiset.length_to_list Multiset.length_toList

/- warning: multiset.card_zero -> Multiset.card_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align multiset.card_zero Multiset.card_zeroₓ'. -/
@[simp]
theorem card_zero : @card α 0 = 0 :=
  rfl
#align multiset.card_zero Multiset.card_zero

/- warning: multiset.card_add -> Multiset.card_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t))
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t)) (HAdd.hAdd.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) t) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (instHAdd.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instAddNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) t))
Case conversion may be inaccurate. Consider using '#align multiset.card_add Multiset.card_addₓ'. -/
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  card.map_add s t
#align multiset.card_add Multiset.card_add

/- warning: multiset.card_nsmul -> Multiset.card_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (n : Nat), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (n : Nat), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) (HMul.hMul.{0, 0, 0} Nat ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) Nat (instHMul.{0} Nat instMulNat) n (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_nsmul Multiset.card_nsmulₓ'. -/
theorem card_nsmul (s : Multiset α) (n : ℕ) : (n • s).card = n * s.card := by
  rw [card.map_nsmul s n, Nat.nsmul_eq_mul]
#align multiset.card_nsmul Multiset.card_nsmul

/- warning: multiset.card_cons -> Multiset.card_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (s : Multiset.{u1} α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.cons.{u1} α a s)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (s : Multiset.{u1} α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.cons.{u1} α a s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.cons.{u1} α a s)) (HAdd.hAdd.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.cons.{u1} α a s)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (instHAdd.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instAddNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.cons.{u1} α a s)) 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align multiset.card_cons Multiset.card_consₓ'. -/
@[simp]
theorem card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) = card s + 1 :=
  Quot.inductionOn s fun l => rfl
#align multiset.card_cons Multiset.card_cons

/- warning: multiset.card_singleton -> Multiset.card_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall {α : Type.{u1}} (a : α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a)) 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align multiset.card_singleton Multiset.card_singletonₓ'. -/
@[simp]
theorem card_singleton (a : α) : card ({a} : Multiset α) = 1 := by
  simp only [← cons_zero, card_zero, eq_self_iff_true, zero_add, card_cons]
#align multiset.card_singleton Multiset.card_singleton

/- warning: multiset.card_pair -> Multiset.card_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (b : α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) b))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (b : α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.instInsertMultiset.{u1} α) a (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) b))) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.instInsertMultiset.{u1} α) a (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) b))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.instInsertMultiset.{u1} α) a (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) b))) 2 (instOfNatNat 2))
Case conversion may be inaccurate. Consider using '#align multiset.card_pair Multiset.card_pairₓ'. -/
theorem card_pair (a b : α) : ({a, b} : Multiset α).card = 2 := by
  rw [insert_eq_cons, card_cons, card_singleton]
#align multiset.card_pair Multiset.card_pair

/- warning: multiset.card_eq_one -> Multiset.card_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Exists.{succ u1} α (fun (a : α) => Eq.{succ u1} (Multiset.{u1} α) s (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) 1 (instOfNatNat 1))) (Exists.{succ u1} α (fun (a : α) => Eq.{succ u1} (Multiset.{u1} α) s (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a)))
Case conversion may be inaccurate. Consider using '#align multiset.card_eq_one Multiset.card_eq_oneₓ'. -/
theorem card_eq_one {s : Multiset α} : card s = 1 ↔ ∃ a, s = {a} :=
  ⟨Quot.inductionOn s fun l h => (List.length_eq_one.1 h).imp fun a => congr_arg coe, fun ⟨a, e⟩ =>
    e.symm ▸ rfl⟩
#align multiset.card_eq_one Multiset.card_eq_one

/- warning: multiset.card_le_of_le -> Multiset.card_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instLENat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) t))
Case conversion may be inaccurate. Consider using '#align multiset.card_le_of_le Multiset.card_le_of_leₓ'. -/
theorem card_le_of_le {s t : Multiset α} (h : s ≤ t) : card s ≤ card t :=
  leInductionOn h fun l₁ l₂ => Sublist.length_le
#align multiset.card_le_of_le Multiset.card_le_of_le

/- warning: multiset.card_mono -> Multiset.card_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Monotone.{u1, 0} (Multiset.{u1} α) Nat (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Monotone.{u1, 0} (Multiset.{u1} α) Nat (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α))
Case conversion may be inaccurate. Consider using '#align multiset.card_mono Multiset.card_monoₓ'. -/
@[mono]
theorem card_mono : Monotone (@card α) := fun a b => card_le_of_le
#align multiset.card_mono Multiset.card_mono

/- warning: multiset.eq_of_le_of_card_le -> Multiset.eq_of_le_of_card_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)) -> (Eq.{succ u1} (Multiset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) t) instLENat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) t) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)) -> (Eq.{succ u1} (Multiset.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align multiset.eq_of_le_of_card_le Multiset.eq_of_le_of_card_leₓ'. -/
theorem eq_of_le_of_card_le {s t : Multiset α} (h : s ≤ t) : card t ≤ card s → s = t :=
  leInductionOn h fun l₁ l₂ s h₂ => congr_arg coe <| s.eq_of_length_le h₂
#align multiset.eq_of_le_of_card_le Multiset.eq_of_le_of_card_le

/- warning: multiset.card_lt_of_lt -> Multiset.card_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LT.lt.{0} Nat Nat.hasLt (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LT.lt.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instLTNat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) t))
Case conversion may be inaccurate. Consider using '#align multiset.card_lt_of_lt Multiset.card_lt_of_ltₓ'. -/
theorem card_lt_of_lt {s t : Multiset α} (h : s < t) : card s < card t :=
  lt_of_not_ge fun h₂ => ne_of_lt h <| eq_of_le_of_card_le (le_of_lt h) h₂
#align multiset.card_lt_of_lt Multiset.card_lt_of_lt

/- warning: multiset.lt_iff_cons_le -> Multiset.lt_iff_cons_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) (Exists.{succ u1} α (fun (a : α) => LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.cons.{u1} α a s) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) (Exists.{succ u1} α (fun (a : α) => LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.cons.{u1} α a s) t))
Case conversion may be inaccurate. Consider using '#align multiset.lt_iff_cons_le Multiset.lt_iff_cons_leₓ'. -/
theorem lt_iff_cons_le {s t : Multiset α} : s < t ↔ ∃ a, a ::ₘ s ≤ t :=
  ⟨Quotient.induction_on₂ s t fun l₁ l₂ h =>
      Subperm.exists_of_length_lt (le_of_lt h) (card_lt_of_lt h),
    fun ⟨a, h⟩ => lt_of_lt_of_le (lt_cons_self _ _) h⟩
#align multiset.lt_iff_cons_le Multiset.lt_iff_cons_le

/- warning: multiset.card_eq_zero -> Multiset.card_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Eq.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) 0 (instOfNatNat 0))) (Eq.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α))))
Case conversion may be inaccurate. Consider using '#align multiset.card_eq_zero Multiset.card_eq_zeroₓ'. -/
@[simp]
theorem card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 0 :=
  ⟨fun h => (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, fun e => by simp [e]⟩
#align multiset.card_eq_zero Multiset.card_eq_zero

/- warning: multiset.card_pos -> Multiset.card_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)) (Ne.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (LT.lt.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instLTNat (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) 0 (instOfNatNat 0)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)) (Ne.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α))))
Case conversion may be inaccurate. Consider using '#align multiset.card_pos Multiset.card_posₓ'. -/
theorem card_pos {s : Multiset α} : 0 < card s ↔ s ≠ 0 :=
  pos_iff_ne_zero.trans <| not_congr card_eq_zero
#align multiset.card_pos Multiset.card_pos

/- warning: multiset.card_pos_iff_exists_mem -> Multiset.card_pos_iff_exists_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)) (Exists.{succ u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (LT.lt.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instLTNat (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) 0 (instOfNatNat 0)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)) (Exists.{succ u1} α (fun (a : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align multiset.card_pos_iff_exists_mem Multiset.card_pos_iff_exists_memₓ'. -/
theorem card_pos_iff_exists_mem {s : Multiset α} : 0 < card s ↔ ∃ a, a ∈ s :=
  Quot.inductionOn s fun l => length_pos_iff_exists_mem
#align multiset.card_pos_iff_exists_mem Multiset.card_pos_iff_exists_mem

/- warning: multiset.card_eq_two -> Multiset.card_eq_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => Eq.{succ u1} (Multiset.{u1} α) s (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.hasInsert.{u1} α) x (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) y)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) 2 (instOfNatNat 2))) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => Eq.{succ u1} (Multiset.{u1} α) s (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.instInsertMultiset.{u1} α) x (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) y)))))
Case conversion may be inaccurate. Consider using '#align multiset.card_eq_two Multiset.card_eq_twoₓ'. -/
theorem card_eq_two {s : Multiset α} : s.card = 2 ↔ ∃ x y, s = {x, y} :=
  ⟨Quot.inductionOn s fun l h =>
      (List.length_eq_two.mp h).imp fun a => Exists.imp fun b => congr_arg coe,
    fun ⟨a, b, e⟩ => e.symm ▸ rfl⟩
#align multiset.card_eq_two Multiset.card_eq_two

/- warning: multiset.card_eq_three -> Multiset.card_eq_three is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => Exists.{succ u1} α (fun (z : α) => Eq.{succ u1} (Multiset.{u1} α) s (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.hasInsert.{u1} α) x (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.hasInsert.{u1} α) y (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) z)))))))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) 3 (instOfNatNat 3))) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => Exists.{succ u1} α (fun (z : α) => Eq.{succ u1} (Multiset.{u1} α) s (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.instInsertMultiset.{u1} α) x (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.instInsertMultiset.{u1} α) y (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) z)))))))
Case conversion may be inaccurate. Consider using '#align multiset.card_eq_three Multiset.card_eq_threeₓ'. -/
theorem card_eq_three {s : Multiset α} : s.card = 3 ↔ ∃ x y z, s = {x, y, z} :=
  ⟨Quot.inductionOn s fun l h =>
      (List.length_eq_three.mp h).imp fun a =>
        Exists.imp fun b => Exists.imp fun c => congr_arg coe,
    fun ⟨a, b, c, e⟩ => e.symm ▸ rfl⟩
#align multiset.card_eq_three Multiset.card_eq_three

/-! ### Induction principles -/


/- warning: multiset.strong_induction_on -> Multiset.strongInductionOnₓ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Sort.{u2}} (s : Multiset.{u1} α), (forall (s : Multiset.{u1} α), (forall (t : Multiset.{u1} α), (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t s) -> (p t)) -> (p s)) -> (p s)
but is expected to have type
  forall {α : Type.{u2}} {p : (Multiset.{u2} α) -> Sort.{u1}} (s : Multiset.{u2} α), (forall (s : Multiset.{u2} α), (forall (t : Multiset.{u2} α), (LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.partialOrder.{u2} α))) t s) -> (p t)) -> (p s)) -> (p s)
Case conversion may be inaccurate. Consider using '#align multiset.strong_induction_on Multiset.strongInductionOnₓₓ'. -/
/-- A strong induction principle for multisets:
If you construct a value for a particular multiset given values for all strictly smaller multisets,
you can construct a value for any multiset.
-/
@[elab_as_elim]
def strongInductionOn {p : Multiset α → Sort _} :
    ∀ s : Multiset α, (∀ s, (∀ t < s, p t) → p s) → p s
  | s => fun ih =>
    ih s fun t h =>
      have : card t < card s := card_lt_of_lt h
      strong_induction_on t ih termination_by'
  ⟨_, measure_wf card⟩
#align multiset.strong_induction_on Multiset.strongInductionOnₓ

/- warning: multiset.strong_induction_eq -> Multiset.strongInductionOn_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Sort.{u2}} (s : Multiset.{u1} α) (H : forall (s : Multiset.{u1} α), (forall (t : Multiset.{u1} α), (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t s) -> (p t)) -> (p s)), Eq.{u2} (p s) (Multiset.strongInductionOnₓ.{u1, u2} α p s H) (H s (fun (t : Multiset.{u1} α) (h : LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t s) => Multiset.strongInductionOnₓ.{u1, u2} α p t H))
but is expected to have type
  forall {α : Type.{u2}} {p : (Multiset.{u2} α) -> Sort.{u1}} (s : Multiset.{u2} α) (H : forall (s : Multiset.{u2} α), (forall (t : Multiset.{u2} α), (LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) t s) -> (p t)) -> (p s)), Eq.{u1} (p s) (Multiset.strongInductionOn.{u2, u1} α p s H) (H s (fun (t : Multiset.{u2} α) (h : LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) t s) => Multiset.strongInductionOn.{u2, u1} α p t H))
Case conversion may be inaccurate. Consider using '#align multiset.strong_induction_eq Multiset.strongInductionOn_eqₓ'. -/
theorem strongInductionOn_eq {p : Multiset α → Sort _} (s : Multiset α) (H) :
    @strongInductionOn _ p s H = H s fun t h => @strongInductionOn _ p t H := by
  rw [strong_induction_on]
#align multiset.strong_induction_eq Multiset.strongInductionOn_eq

/- warning: multiset.case_strong_induction_on -> Multiset.case_strongInductionOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Prop} (s : Multiset.{u1} α), (p (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) -> (forall (a : α) (s : Multiset.{u1} α), (forall (t : Multiset.{u1} α), (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t s) -> (p t)) -> (p (Multiset.cons.{u1} α a s))) -> (p s)
but is expected to have type
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Prop} (s : Multiset.{u1} α), (p (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) -> (forall (a : α) (s : Multiset.{u1} α), (forall (t : Multiset.{u1} α), (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t s) -> (p t)) -> (p (Multiset.cons.{u1} α a s))) -> (p s)
Case conversion may be inaccurate. Consider using '#align multiset.case_strong_induction_on Multiset.case_strongInductionOnₓ'. -/
@[elab_as_elim]
theorem case_strongInductionOn {p : Multiset α → Prop} (s : Multiset α) (h₀ : p 0)
    (h₁ : ∀ a s, (∀ t ≤ s, p t) → p (a ::ₘ s)) : p s :=
  Multiset.strongInductionOn s fun s =>
    Multiset.induction_on s (fun _ => h₀) fun a s _ ih =>
      h₁ _ _ fun t h => ih _ <| lt_of_le_of_lt h <| lt_cons_self _ _
#align multiset.case_strong_induction_on Multiset.case_strongInductionOn

/- warning: multiset.strong_downward_induction -> Multiset.strongDownwardInductionₓ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Sort.{u2}} {n : Nat}, (forall (t₁ : Multiset.{u1} α), (forall {t₂ : Multiset.{u1} α}, (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t₂) n) -> (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t₁ t₂) -> (p t₂)) -> (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t₁) n) -> (p t₁)) -> (forall (s : Multiset.{u1} α), (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) n) -> (p s))
but is expected to have type
  PUnit.{imax (succ (succ u2)) (max (succ u1) (succ u2)) 1 (imax (succ u2) (imax (succ u2) u1) u1) (succ u2) u1}
Case conversion may be inaccurate. Consider using '#align multiset.strong_downward_induction Multiset.strongDownwardInductionₓₓ'. -/
/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all multisets `s` of
cardinality less than `n`, starting from multisets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strongDownwardInduction {p : Multiset α → Sort _} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    ∀ s : Multiset α, s.card ≤ n → p s
  | s =>
    H s fun t ht h =>
      have : n - card t < n - card s := (tsub_lt_tsub_iff_left_of_le ht).2 (card_lt_of_lt h)
      strong_downward_induction t ht termination_by'
  ⟨_, measure_wf fun t : Multiset α => n - t.card⟩
#align multiset.strong_downward_induction Multiset.strongDownwardInductionₓ

/- warning: multiset.strong_downward_induction_eq -> Multiset.strongDownwardInduction_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Sort.{u2}} {n : Nat} (H : forall (t₁ : Multiset.{u1} α), (forall {t₂ : Multiset.{u1} α}, (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t₂) n) -> (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t₁ t₂) -> (p t₂)) -> (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t₁) n) -> (p t₁)) (s : Multiset.{u1} α), Eq.{u2} ((LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) n) -> (p s)) (Multiset.strongDownwardInductionₓ.{u1, u2} α (fun (t₂ : Multiset.{u1} α) => p t₂) n H s) (H s (fun (t : Multiset.{u1} α) (ht : LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t) n) (hst : LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) => Multiset.strongDownwardInductionₓ.{u1, u2} α p n H t ht))
but is expected to have type
  forall {α : Type.{u2}} {p : (Multiset.{u2} α) -> Sort.{u1}} {n : Nat} (H : forall (t₁ : Multiset.{u2} α), (forall {t₂ : Multiset.{u2} α}, (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) t₂) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) t₂) n) -> (LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) t₁ t₂) -> (p t₂)) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) t₁) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) t₁) n) -> (p t₁)) (s : Multiset.{u2} α), Eq.{u1} ((LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) s) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s) n) -> (p s)) (Multiset.strongDownwardInduction.{u2, u1} α (fun (t₂ : Multiset.{u2} α) => p t₂) n H s) (H s (fun {t : Multiset.{u2} α} (ht : LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) t) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) t) n) (hst : LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) s t) => Multiset.strongDownwardInduction.{u2, u1} α (fun (t₂ : Multiset.{u2} α) => p t₂) n H t ht))
Case conversion may be inaccurate. Consider using '#align multiset.strong_downward_induction_eq Multiset.strongDownwardInduction_eqₓ'. -/
theorem strongDownwardInduction_eq {p : Multiset α → Sort _} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁)
    (s : Multiset α) :
    strongDownwardInduction H s = H s fun t ht hst => strongDownwardInduction H t ht := by
  rw [strong_downward_induction]
#align multiset.strong_downward_induction_eq Multiset.strongDownwardInduction_eq

/- warning: multiset.strong_downward_induction_on -> Multiset.strongDownwardInductionOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Sort.{u2}} {n : Nat} (s : Multiset.{u1} α), (forall (t₁ : Multiset.{u1} α), (forall {t₂ : Multiset.{u1} α}, (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t₂) n) -> (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t₁ t₂) -> (p t₂)) -> (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t₁) n) -> (p t₁)) -> (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) n) -> (p s)
but is expected to have type
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Sort.{u2}} {n : Nat} (s : Multiset.{u1} α), (forall (t₁ : Multiset.{u1} α), (forall {t₂ : Multiset.{u1} α}, (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) t₂) instLENat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) t₂) n) -> (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t₁ t₂) -> (p t₂)) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) t₁) instLENat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) t₁) n) -> (p t₁)) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instLENat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) n) -> (p s)
Case conversion may be inaccurate. Consider using '#align multiset.strong_downward_induction_on Multiset.strongDownwardInductionOnₓ'. -/
/-- Analogue of `strong_downward_induction` with order of arguments swapped. -/
@[elab_as_elim]
def strongDownwardInductionOn {p : Multiset α → Sort _} {n : ℕ} :
    ∀ s : Multiset α,
      (∀ t₁, (∀ {t₂ : Multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) →
        s.card ≤ n → p s :=
  fun s H => strongDownwardInduction H s
#align multiset.strong_downward_induction_on Multiset.strongDownwardInductionOn

/- warning: multiset.strong_downward_induction_on_eq -> Multiset.strongDownwardInductionOn_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Multiset.{u1} α) -> Sort.{u2}} (s : Multiset.{u1} α) {n : Nat} (H : forall (t₁ : Multiset.{u1} α), (forall {t₂ : Multiset.{u1} α}, (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t₂) n) -> (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t₁ t₂) -> (p t₂)) -> (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t₁) n) -> (p t₁)), Eq.{u2} ((LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) n) -> (p s)) (Multiset.strongDownwardInductionOn.{u1, u2} α (fun (t₂ : Multiset.{u1} α) => p t₂) n s H) (H s (fun (t : Multiset.{u1} α) (ht : LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t) n) (h : LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) => Multiset.strongDownwardInductionOn.{u1, u2} α (fun (t₂ : Multiset.{u1} α) => p t₂) n t H ht))
but is expected to have type
  forall {α : Type.{u2}} {p : (Multiset.{u2} α) -> Sort.{u1}} (s : Multiset.{u2} α) {n : Nat} (H : forall (t₁ : Multiset.{u2} α), (forall {t₂ : Multiset.{u2} α}, (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) t₂) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) t₂) n) -> (LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) t₁ t₂) -> (p t₂)) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) t₁) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) t₁) n) -> (p t₁)), Eq.{u1} ((LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) s) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s) n) -> (p s)) (fun (a._@.Mathlib.Data.Multiset.Basic._hyg.7925 : LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) s) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (a : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) a) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s) n) => Multiset.strongDownwardInductionOn.{u2, u1} α (fun (x._@.Mathlib.Data.Multiset.Basic._hyg.8026 : Multiset.{u2} α) => p x._@.Mathlib.Data.Multiset.Basic._hyg.8026) n s H a._@.Mathlib.Data.Multiset.Basic._hyg.7925) (H s (fun {t : Multiset.{u2} α} (ht : LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) t) instLENat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) t) n) (h : LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) s t) => Multiset.strongDownwardInductionOn.{u2, u1} α (fun (t₂ : Multiset.{u2} α) => p t₂) n t H ht))
Case conversion may be inaccurate. Consider using '#align multiset.strong_downward_induction_on_eq Multiset.strongDownwardInductionOn_eqₓ'. -/
theorem strongDownwardInductionOn_eq {p : Multiset α → Sort _} (s : Multiset α) {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun t ht h => t.strongDownwardInductionOn H ht :=
  by
  dsimp only [strong_downward_induction_on]
  rw [strong_downward_induction]
#align multiset.strong_downward_induction_on_eq Multiset.strongDownwardInductionOn_eq

/- warning: multiset.well_founded_lt -> Multiset.wellFounded_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, WellFounded.{succ u1} (Multiset.{u1} α) (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}}, WellFounded.{succ u1} (Multiset.{u1} α) (fun (x._@.Mathlib.Data.Multiset.Basic._hyg.8076 : Multiset.{u1} α) (x._@.Mathlib.Data.Multiset.Basic._hyg.8078 : Multiset.{u1} α) => LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) x._@.Mathlib.Data.Multiset.Basic._hyg.8076 x._@.Mathlib.Data.Multiset.Basic._hyg.8078)
Case conversion may be inaccurate. Consider using '#align multiset.well_founded_lt Multiset.wellFounded_ltₓ'. -/
/-- Another way of expressing `strong_induction_on`: the `(<)` relation is well-founded. -/
theorem wellFounded_lt : WellFounded ((· < ·) : Multiset α → Multiset α → Prop) :=
  Subrelation.wf (fun _ _ => Multiset.card_lt_of_lt) (measure_wf Multiset.card)
#align multiset.well_founded_lt Multiset.wellFounded_lt

/- warning: multiset.is_well_founded_lt -> Multiset.is_wellFounded_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, WellFoundedLT.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, WellFoundedLT.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)))
Case conversion may be inaccurate. Consider using '#align multiset.is_well_founded_lt Multiset.is_wellFounded_ltₓ'. -/
instance is_wellFounded_lt : WellFoundedLT (Multiset α) :=
  ⟨wellFounded_lt⟩
#align multiset.is_well_founded_lt Multiset.is_wellFounded_lt

/-! ### `multiset.replicate` -/


#print Multiset.replicate /-
/-- `replicate n a` is the multiset containing only `a` with multiplicity `n`. -/
def replicate (n : ℕ) (a : α) : Multiset α :=
  replicate n a
#align multiset.replicate Multiset.replicate
-/

#print Multiset.coe_replicate /-
theorem coe_replicate (n : ℕ) (a : α) : (List.replicate n a : Multiset α) = replicate n a :=
  rfl
#align multiset.coe_replicate Multiset.coe_replicate
-/

#print Multiset.replicate_zero /-
@[simp]
theorem replicate_zero (a : α) : replicate 0 a = 0 :=
  rfl
#align multiset.replicate_zero Multiset.replicate_zero
-/

#print Multiset.replicate_succ /-
@[simp]
theorem replicate_succ (a : α) (n) : replicate (n + 1) a = a ::ₘ replicate n a :=
  rfl
#align multiset.replicate_succ Multiset.replicate_succ
-/

#print Multiset.replicate_add /-
theorem replicate_add (m n : ℕ) (a : α) : replicate (m + n) a = replicate m a + replicate n a :=
  congr_arg _ <| List.replicate_add _ _ _
#align multiset.replicate_add Multiset.replicate_add
-/

/- warning: multiset.replicate_add_monoid_hom -> Multiset.replicateAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, α -> (AddMonoidHom.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u1}}, α -> (AddMonoidHom.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align multiset.replicate_add_monoid_hom Multiset.replicateAddMonoidHomₓ'. -/
/-- `multiset.replicate` as an `add_monoid_hom`. -/
@[simps]
def replicateAddMonoidHom (a : α) : ℕ →+ Multiset α
    where
  toFun n := replicate n a
  map_zero' := replicate_zero a
  map_add' _ _ := replicate_add _ _ a
#align multiset.replicate_add_monoid_hom Multiset.replicateAddMonoidHom

#print Multiset.replicate_one /-
theorem replicate_one (a : α) : replicate 1 a = {a} :=
  rfl
#align multiset.replicate_one Multiset.replicate_one
-/

/- warning: multiset.card_replicate -> Multiset.card_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (n : Nat) (a : α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.replicate.{u1} α n a)) n
but is expected to have type
  forall {α : Type.{u1}} (n : Nat) (a : α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.replicate.{u1} α n a)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.replicate.{u1} α n a)) n
Case conversion may be inaccurate. Consider using '#align multiset.card_replicate Multiset.card_replicateₓ'. -/
@[simp]
theorem card_replicate : ∀ (n) (a : α), card (replicate n a) = n :=
  length_replicate
#align multiset.card_replicate Multiset.card_replicate

#print Multiset.mem_replicate /-
theorem mem_replicate {a b : α} {n : ℕ} : b ∈ replicate n a ↔ n ≠ 0 ∧ b = a :=
  mem_replicate
#align multiset.mem_replicate Multiset.mem_replicate
-/

#print Multiset.eq_of_mem_replicate /-
theorem eq_of_mem_replicate {a b : α} {n} : b ∈ replicate n a → b = a :=
  eq_of_mem_replicate
#align multiset.eq_of_mem_replicate Multiset.eq_of_mem_replicate
-/

/- warning: multiset.eq_replicate_card -> Multiset.eq_replicate_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α}, Iff (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.replicate.{u1} α (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) a)) (forall (b : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) b s) -> (Eq.{succ u1} α b a))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α}, Iff (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.replicate.{u1} α (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) a)) (forall (b : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) b s) -> (Eq.{succ u1} α b a))
Case conversion may be inaccurate. Consider using '#align multiset.eq_replicate_card Multiset.eq_replicate_cardₓ'. -/
theorem eq_replicate_card {a : α} {s : Multiset α} : s = replicate s.card a ↔ ∀ b ∈ s, b = a :=
  Quot.inductionOn s fun l => coe_eq_coe.trans <| perm_replicate.trans eq_replicate_length
#align multiset.eq_replicate_card Multiset.eq_replicate_card

/- warning: multiset.eq_replicate_of_mem -> Multiset.eq_replicate_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α}, (forall (b : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) b s) -> (Eq.{succ u1} α b a)) -> (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.replicate.{u1} α (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) a))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Multiset.{u1} α}, (forall (b : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) b s) -> (Eq.{succ u1} α b a)) -> (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.replicate.{u1} α (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) a))
Case conversion may be inaccurate. Consider using '#align multiset.eq_replicate_of_mem Multiset.eq_replicate_of_memₓ'. -/
alias eq_replicate_card ↔ _ eq_replicate_of_mem
#align multiset.eq_replicate_of_mem Multiset.eq_replicate_of_mem

/- warning: multiset.eq_replicate -> Multiset.eq_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {n : Nat} {s : Multiset.{u1} α}, Iff (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.replicate.{u1} α n a)) (And (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) n) (forall (b : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) b s) -> (Eq.{succ u1} α b a)))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {n : Nat} {s : Multiset.{u1} α}, Iff (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.replicate.{u1} α n a)) (And (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) n) (forall (b : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) b s) -> (Eq.{succ u1} α b a)))
Case conversion may be inaccurate. Consider using '#align multiset.eq_replicate Multiset.eq_replicateₓ'. -/
theorem eq_replicate {a : α} {n} {s : Multiset α} :
    s = replicate n a ↔ card s = n ∧ ∀ b ∈ s, b = a :=
  ⟨fun h => h.symm ▸ ⟨card_replicate _ _, fun b => eq_of_mem_replicate⟩, fun ⟨e, al⟩ =>
    e ▸ eq_replicate_of_mem al⟩
#align multiset.eq_replicate Multiset.eq_replicate

#print Multiset.replicate_right_injective /-
theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (replicate n : α → Multiset α) := fun a b h =>
  (eq_replicate.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩
#align multiset.replicate_right_injective Multiset.replicate_right_injective
-/

#print Multiset.replicate_right_inj /-
@[simp]
theorem replicate_right_inj {a b : α} {n : ℕ} (h : n ≠ 0) : replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective h).eq_iff
#align multiset.replicate_right_inj Multiset.replicate_right_inj
-/

#print Multiset.replicate_left_injective /-
theorem replicate_left_injective (a : α) : Function.Injective fun n => replicate n a := fun m n h =>
  by rw [← (eq_replicate.1 h).1, card_replicate]
#align multiset.replicate_left_injective Multiset.replicate_left_injective
-/

#print Multiset.replicate_subset_singleton /-
theorem replicate_subset_singleton : ∀ (n) (a : α), replicate n a ⊆ {a} :=
  replicate_subset_singleton
#align multiset.replicate_subset_singleton Multiset.replicate_subset_singleton
-/

/- warning: multiset.replicate_le_coe -> Multiset.replicate_le_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {n : Nat} {l : List.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.replicate.{u1} α n a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) (List.Sublist.{u1} α (List.replicate.{u1} α n a) l)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {n : Nat} {l : List.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.replicate.{u1} α n a) (Multiset.ofList.{u1} α l)) (List.Sublist.{u1} α (List.replicate.{u1} α n a) l)
Case conversion may be inaccurate. Consider using '#align multiset.replicate_le_coe Multiset.replicate_le_coeₓ'. -/
theorem replicate_le_coe {a : α} {n} {l : List α} : replicate n a ≤ l ↔ List.replicate n a <+ l :=
  ⟨fun ⟨l', p, s⟩ => perm_replicate.1 p ▸ s, Sublist.subperm⟩
#align multiset.replicate_le_coe Multiset.replicate_le_coe

/- warning: multiset.nsmul_singleton -> Multiset.nsmul_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (n : Nat), Eq.{succ u1} (Multiset.{u1} α) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a)) (Multiset.replicate.{u1} α n a)
but is expected to have type
  forall {α : Type.{u1}} (a : α) (n : Nat), Eq.{succ u1} (Multiset.{u1} α) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a)) (Multiset.replicate.{u1} α n a)
Case conversion may be inaccurate. Consider using '#align multiset.nsmul_singleton Multiset.nsmul_singletonₓ'. -/
theorem nsmul_singleton (a : α) (n) : n • ({a} : Multiset α) = replicate n a :=
  by
  refine' eq_replicate.mpr ⟨_, fun b hb => mem_singleton.mp (mem_of_mem_nsmul hb)⟩
  rw [card_nsmul, card_singleton, mul_one]
#align multiset.nsmul_singleton Multiset.nsmul_singleton

/- warning: multiset.nsmul_replicate -> Multiset.nsmul_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} (n : Nat) (m : Nat), Eq.{succ u1} (Multiset.{u1} α) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n (Multiset.replicate.{u1} α m a)) (Multiset.replicate.{u1} α (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n m) a)
but is expected to have type
  forall {α : Type.{u1}} {a : α} (n : Nat) (m : Nat), Eq.{succ u1} (Multiset.{u1} α) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n (Multiset.replicate.{u1} α m a)) (Multiset.replicate.{u1} α (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n m) a)
Case conversion may be inaccurate. Consider using '#align multiset.nsmul_replicate Multiset.nsmul_replicateₓ'. -/
theorem nsmul_replicate {a : α} (n m : ℕ) : n • replicate m a = replicate (n * m) a :=
  ((replicateAddMonoidHom a).map_nsmul _ _).symm
#align multiset.nsmul_replicate Multiset.nsmul_replicate

/- warning: multiset.replicate_le_replicate -> Multiset.replicate_le_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) {k : Nat} {n : Nat}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.replicate.{u1} α k a) (Multiset.replicate.{u1} α n a)) (LE.le.{0} Nat Nat.hasLe k n)
but is expected to have type
  forall {α : Type.{u1}} (a : α) {k : Nat} {n : Nat}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.replicate.{u1} α k a) (Multiset.replicate.{u1} α n a)) (LE.le.{0} Nat instLENat k n)
Case conversion may be inaccurate. Consider using '#align multiset.replicate_le_replicate Multiset.replicate_le_replicateₓ'. -/
theorem replicate_le_replicate (a : α) {k n : ℕ} : replicate k a ≤ replicate n a ↔ k ≤ n :=
  replicate_le_coe.trans <| List.replicate_sublist_replicate _
#align multiset.replicate_le_replicate Multiset.replicate_le_replicate

/- warning: multiset.le_replicate_iff -> Multiset.le_replicate_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {a : α} {n : Nat}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) m (Multiset.replicate.{u1} α n a)) (Exists.{1} Nat (fun (k : Nat) => Exists.{0} (LE.le.{0} Nat Nat.hasLe k n) (fun (H : LE.le.{0} Nat Nat.hasLe k n) => Eq.{succ u1} (Multiset.{u1} α) m (Multiset.replicate.{u1} α k a))))
but is expected to have type
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {a : α} {n : Nat}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) m (Multiset.replicate.{u1} α n a)) (Exists.{1} Nat (fun (k : Nat) => And (LE.le.{0} Nat instLENat k n) (Eq.{succ u1} (Multiset.{u1} α) m (Multiset.replicate.{u1} α k a))))
Case conversion may be inaccurate. Consider using '#align multiset.le_replicate_iff Multiset.le_replicate_iffₓ'. -/
theorem le_replicate_iff {m : Multiset α} {a : α} {n : ℕ} :
    m ≤ replicate n a ↔ ∃ k ≤ n, m = replicate k a :=
  ⟨fun h =>
    ⟨m.card, (card_mono h).trans_eq (card_replicate _ _),
      eq_replicate_card.2 fun b hb => eq_of_mem_replicate <| subset_of_le h hb⟩,
    fun ⟨k, hkn, hm⟩ => hm.symm ▸ (replicate_le_replicate _).2 hkn⟩
#align multiset.le_replicate_iff Multiset.le_replicate_iff

/- warning: multiset.lt_replicate_succ -> Multiset.lt_replicate_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {x : α} {n : Nat}, Iff (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) m (Multiset.replicate.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) x)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) m (Multiset.replicate.{u1} α n x))
but is expected to have type
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {x : α} {n : Nat}, Iff (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) m (Multiset.replicate.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) x)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) m (Multiset.replicate.{u1} α n x))
Case conversion may be inaccurate. Consider using '#align multiset.lt_replicate_succ Multiset.lt_replicate_succₓ'. -/
theorem lt_replicate_succ {m : Multiset α} {x : α} {n : ℕ} :
    m < replicate (n + 1) x ↔ m ≤ replicate n x :=
  by
  rw [lt_iff_cons_le]
  constructor
  · rintro ⟨x', hx'⟩
    have := eq_of_mem_replicate (mem_of_le hx' (mem_cons_self _ _))
    rwa [this, replicate_succ, cons_le_cons_iff] at hx'
  · intro h
    rw [replicate_succ]
    exact ⟨x, cons_le_cons _ h⟩
#align multiset.lt_replicate_succ Multiset.lt_replicate_succ

/-! ### Erasing one copy of an element -/


section Erase

variable [DecidableEq α] {s t : Multiset α} {a b : α}

#print Multiset.erase /-
/-- `erase s a` is the multiset that subtracts 1 from the
  multiplicity of `a`. -/
def erase (s : Multiset α) (a : α) : Multiset α :=
  Quot.liftOn s (fun l => (l.eraseₓ a : Multiset α)) fun l₁ l₂ p => Quot.sound (p.eraseₓ a)
#align multiset.erase Multiset.erase
-/

/- warning: multiset.coe_erase -> Multiset.coe_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α) (a : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α) (a : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Multiset.ofList.{u1} α l) a) (Multiset.ofList.{u1} α (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l a))
Case conversion may be inaccurate. Consider using '#align multiset.coe_erase Multiset.coe_eraseₓ'. -/
@[simp]
theorem coe_erase (l : List α) (a : α) : erase (l : Multiset α) a = l.eraseₓ a :=
  rfl
#align multiset.coe_erase Multiset.coe_erase

#print Multiset.erase_zero /-
@[simp]
theorem erase_zero (a : α) : (0 : Multiset α).eraseₓ a = 0 :=
  rfl
#align multiset.erase_zero Multiset.erase_zero
-/

#print Multiset.erase_cons_head /-
@[simp]
theorem erase_cons_head (a : α) (s : Multiset α) : (a ::ₘ s).eraseₓ a = s :=
  Quot.inductionOn s fun l => congr_arg coe <| erase_cons_head a l
#align multiset.erase_cons_head Multiset.erase_cons_head
-/

#print Multiset.erase_cons_tail /-
@[simp]
theorem erase_cons_tail {a b : α} (s : Multiset α) (h : b ≠ a) :
    (b ::ₘ s).eraseₓ a = b ::ₘ s.eraseₓ a :=
  Quot.inductionOn s fun l => congr_arg coe <| erase_cons_tail l h
#align multiset.erase_cons_tail Multiset.erase_cons_tail
-/

#print Multiset.erase_singleton /-
@[simp]
theorem erase_singleton (a : α) : ({a} : Multiset α).eraseₓ a = 0 :=
  erase_cons_head a 0
#align multiset.erase_singleton Multiset.erase_singleton
-/

#print Multiset.erase_of_not_mem /-
@[simp]
theorem erase_of_not_mem {a : α} {s : Multiset α} : a ∉ s → s.eraseₓ a = s :=
  Quot.inductionOn s fun l h => congr_arg coe <| erase_of_not_mem h
#align multiset.erase_of_not_mem Multiset.erase_of_not_mem
-/

#print Multiset.cons_erase /-
@[simp]
theorem cons_erase {s : Multiset α} {a : α} : a ∈ s → a ::ₘ s.eraseₓ a = s :=
  Quot.inductionOn s fun l h => Quot.sound (perm_cons_erase h).symm
#align multiset.cons_erase Multiset.cons_erase
-/

/- warning: multiset.le_cons_erase -> Multiset.le_cons_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (a : α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.cons.{u1} α a (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (a : α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.cons.{u1} α a (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a))
Case conversion may be inaccurate. Consider using '#align multiset.le_cons_erase Multiset.le_cons_eraseₓ'. -/
theorem le_cons_erase (s : Multiset α) (a : α) : s ≤ a ::ₘ s.eraseₓ a :=
  if h : a ∈ s then le_of_eq (cons_erase h).symm
  else by rw [erase_of_not_mem h] <;> apply le_cons_self
#align multiset.le_cons_erase Multiset.le_cons_erase

#print Multiset.add_singleton_eq_iff /-
theorem add_singleton_eq_iff {s t : Multiset α} {a : α} : s + {a} = t ↔ a ∈ t ∧ s = t.eraseₓ a :=
  by
  rw [add_comm, singleton_add]; constructor
  · rintro rfl
    exact ⟨s.mem_cons_self a, (s.erase_cons_head a).symm⟩
  · rintro ⟨h, rfl⟩
    exact cons_erase h
#align multiset.add_singleton_eq_iff Multiset.add_singleton_eq_iff
-/

#print Multiset.erase_add_left_pos /-
theorem erase_add_left_pos {a : α} {s : Multiset α} (t) :
    a ∈ s → (s + t).eraseₓ a = s.eraseₓ a + t :=
  Quotient.induction_on₂ s t fun l₁ l₂ h => congr_arg coe <| erase_append_left l₂ h
#align multiset.erase_add_left_pos Multiset.erase_add_left_pos
-/

#print Multiset.erase_add_right_pos /-
theorem erase_add_right_pos {a : α} (s) {t : Multiset α} (h : a ∈ t) :
    (s + t).eraseₓ a = s + t.eraseₓ a := by rw [add_comm, erase_add_left_pos s h, add_comm]
#align multiset.erase_add_right_pos Multiset.erase_add_right_pos
-/

#print Multiset.erase_add_right_neg /-
theorem erase_add_right_neg {a : α} {s : Multiset α} (t) :
    a ∉ s → (s + t).eraseₓ a = s + t.eraseₓ a :=
  Quotient.induction_on₂ s t fun l₁ l₂ h => congr_arg coe <| erase_append_right l₂ h
#align multiset.erase_add_right_neg Multiset.erase_add_right_neg
-/

#print Multiset.erase_add_left_neg /-
theorem erase_add_left_neg {a : α} (s) {t : Multiset α} (h : a ∉ t) :
    (s + t).eraseₓ a = s.eraseₓ a + t := by rw [add_comm, erase_add_right_neg s h, add_comm]
#align multiset.erase_add_left_neg Multiset.erase_add_left_neg
-/

/- warning: multiset.erase_le -> Multiset.erase_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) s
Case conversion may be inaccurate. Consider using '#align multiset.erase_le Multiset.erase_leₓ'. -/
theorem erase_le (a : α) (s : Multiset α) : s.eraseₓ a ≤ s :=
  Quot.inductionOn s fun l => (erase_sublist a l).Subperm
#align multiset.erase_le Multiset.erase_le

/- warning: multiset.erase_lt -> Multiset.erase_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, Iff (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) s) (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, Iff (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) s) (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align multiset.erase_lt Multiset.erase_ltₓ'. -/
@[simp]
theorem erase_lt {a : α} {s : Multiset α} : s.eraseₓ a < s ↔ a ∈ s :=
  ⟨fun h => not_imp_comm.1 erase_of_not_mem (ne_of_lt h), fun h => by
    simpa [h] using lt_cons_self (s.erase a) a⟩
#align multiset.erase_lt Multiset.erase_lt

#print Multiset.erase_subset /-
theorem erase_subset (a : α) (s : Multiset α) : s.eraseₓ a ⊆ s :=
  subset_of_le (erase_le a s)
#align multiset.erase_subset Multiset.erase_subset
-/

#print Multiset.mem_erase_of_ne /-
theorem mem_erase_of_ne {a b : α} {s : Multiset α} (ab : a ≠ b) : a ∈ s.eraseₓ b ↔ a ∈ s :=
  Quot.inductionOn s fun l => List.mem_erase_of_ne ab
#align multiset.mem_erase_of_ne Multiset.mem_erase_of_ne
-/

#print Multiset.mem_of_mem_erase /-
theorem mem_of_mem_erase {a b : α} {s : Multiset α} : a ∈ s.eraseₓ b → a ∈ s :=
  mem_of_subset (erase_subset _ _)
#align multiset.mem_of_mem_erase Multiset.mem_of_mem_erase
-/

#print Multiset.erase_comm /-
theorem erase_comm (s : Multiset α) (a b : α) : (s.eraseₓ a).eraseₓ b = (s.eraseₓ b).eraseₓ a :=
  Quot.inductionOn s fun l => congr_arg coe <| l.erase_commₓ a b
#align multiset.erase_comm Multiset.erase_comm
-/

/- warning: multiset.erase_le_erase -> Multiset.erase_le_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} (a : α), (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} (a : α), (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t a))
Case conversion may be inaccurate. Consider using '#align multiset.erase_le_erase Multiset.erase_le_eraseₓ'. -/
theorem erase_le_erase {s t : Multiset α} (a : α) (h : s ≤ t) : s.eraseₓ a ≤ t.eraseₓ a :=
  leInductionOn h fun l₁ l₂ h => (h.eraseₓ _).Subperm
#align multiset.erase_le_erase Multiset.erase_le_erase

/- warning: multiset.erase_le_iff_le_cons -> Multiset.erase_le_iff_le_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {a : α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) t) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.cons.{u1} α a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {a : α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) t) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.cons.{u1} α a t))
Case conversion may be inaccurate. Consider using '#align multiset.erase_le_iff_le_cons Multiset.erase_le_iff_le_consₓ'. -/
theorem erase_le_iff_le_cons {s t : Multiset α} {a : α} : s.eraseₓ a ≤ t ↔ s ≤ a ::ₘ t :=
  ⟨fun h => le_trans (le_cons_erase _ _) (cons_le_cons _ h), fun h =>
    if m : a ∈ s then by rw [← cons_erase m] at h <;> exact (cons_le_cons_iff _).1 h
    else le_trans (erase_le _ _) ((le_cons_of_not_mem m).1 h)⟩
#align multiset.erase_le_iff_le_cons Multiset.erase_le_iff_le_cons

/- warning: multiset.card_erase_of_mem -> Multiset.card_erase_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (Nat.pred (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (Nat.pred (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)))
Case conversion may be inaccurate. Consider using '#align multiset.card_erase_of_mem Multiset.card_erase_of_memₓ'. -/
@[simp]
theorem card_erase_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.eraseₓ a) = pred (card s) :=
  Quot.inductionOn s fun l => length_erase_of_mem
#align multiset.card_erase_of_mem Multiset.card_erase_of_mem

/- warning: multiset.card_erase_add_one -> Multiset.card_erase_add_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (HAdd.hAdd.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (instHAdd.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) instAddNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) 1 (instOfNatNat 1))) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_erase_add_one Multiset.card_erase_add_oneₓ'. -/
@[simp]
theorem card_erase_add_one {a : α} {s : Multiset α} : a ∈ s → (s.eraseₓ a).card + 1 = s.card :=
  Quot.inductionOn s fun l => length_erase_add_one
#align multiset.card_erase_add_one Multiset.card_erase_add_one

/- warning: multiset.card_erase_lt_of_mem -> Multiset.card_erase_lt_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (LT.lt.{0} Nat Nat.hasLt (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (LT.lt.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) instLTNat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_erase_lt_of_mem Multiset.card_erase_lt_of_memₓ'. -/
theorem card_erase_lt_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.eraseₓ a) < card s :=
  fun h => card_lt_of_lt (erase_lt.mpr h)
#align multiset.card_erase_lt_of_mem Multiset.card_erase_lt_of_mem

/- warning: multiset.card_erase_le -> Multiset.card_erase_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, LE.le.{0} Nat Nat.hasLe (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, LE.le.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) instLENat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)
Case conversion may be inaccurate. Consider using '#align multiset.card_erase_le Multiset.card_erase_leₓ'. -/
theorem card_erase_le {a : α} {s : Multiset α} : card (s.eraseₓ a) ≤ card s :=
  card_le_of_le (erase_le a s)
#align multiset.card_erase_le Multiset.card_erase_le

/- warning: multiset.card_erase_eq_ite -> Multiset.card_erase_eq_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (ite.{1} Nat (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) (Multiset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Nat.pred (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (ite.{1} Nat (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) (Multiset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Nat.pred (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_erase_eq_ite Multiset.card_erase_eq_iteₓ'. -/
theorem card_erase_eq_ite {a : α} {s : Multiset α} :
    card (s.eraseₓ a) = if a ∈ s then pred (card s) else card s :=
  by
  by_cases h : a ∈ s
  · rwa [card_erase_of_mem h, if_pos]
  · rwa [erase_of_not_mem h, if_neg]
#align multiset.card_erase_eq_ite Multiset.card_erase_eq_ite

end Erase

#print Multiset.coe_reverse /-
@[simp]
theorem coe_reverse (l : List α) : (reverse l : Multiset α) = l :=
  Quot.sound <| reverse_perm _
#align multiset.coe_reverse Multiset.coe_reverse
-/

/-! ### `multiset.map` -/


#print Multiset.map /-
/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun l₁ l₂ p => Quot.sound (p.map f)
#align multiset.map Multiset.map
-/

/- warning: multiset.map_congr -> Multiset.map_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (Eq.{succ u1} (Multiset.{u1} α) s t) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x t) -> (Eq.{succ u2} β (f x) (g x))) -> (Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f s) (Multiset.map.{u1, u2} α β g t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {s : Multiset.{u2} α} {t : Multiset.{u2} α}, (Eq.{succ u2} (Multiset.{u2} α) s t) -> (forall (x : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x t) -> (Eq.{succ u1} β (f x) (g x))) -> (Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f s) (Multiset.map.{u2, u1} α β g t))
Case conversion may be inaccurate. Consider using '#align multiset.map_congr Multiset.map_congrₓ'. -/
@[congr]
theorem map_congr {f g : α → β} {s t : Multiset α} :
    s = t → (∀ x ∈ t, f x = g x) → map f s = map g t :=
  by
  rintro rfl h
  induction s using Quot.inductionOn
  exact congr_arg coe (map_congr h)
#align multiset.map_congr Multiset.map_congr

#print Multiset.map_hcongr /-
theorem map_hcongr {β' : Type _} {m : Multiset α} {f : α → β} {f' : α → β'} (h : β = β')
    (hf : ∀ a ∈ m, HEq (f a) (f' a)) : HEq (map f m) (map f' m) := by subst h; simp at hf;
  simp [map_congr rfl hf]
#align multiset.map_hcongr Multiset.map_hcongr
-/

/- warning: multiset.forall_mem_map_iff -> Multiset.forall_mem_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {p : β -> Prop} {s : Multiset.{u1} α}, Iff (forall (y : β), (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) y (Multiset.map.{u1, u2} α β f s)) -> (p y)) (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (p (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {p : β -> Prop} {s : Multiset.{u2} α}, Iff (forall (y : β), (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) y (Multiset.map.{u2, u1} α β f s)) -> (p y)) (forall (x : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s) -> (p (f x)))
Case conversion may be inaccurate. Consider using '#align multiset.forall_mem_map_iff Multiset.forall_mem_map_iffₓ'. -/
theorem forall_mem_map_iff {f : α → β} {p : β → Prop} {s : Multiset α} :
    (∀ y ∈ s.map f, p y) ↔ ∀ x ∈ s, p (f x) :=
  Quotient.inductionOn' s fun L => List.forall_mem_map_iff
#align multiset.forall_mem_map_iff Multiset.forall_mem_map_iff

/- warning: multiset.coe_map -> Multiset.coe_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (l : List.{u1} α), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (List.{u2} β) (Multiset.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (coeBase.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (Multiset.hasCoe.{u2} β)))) (List.map.{u1, u2} α β f l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (l : List.{u2} α), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f (Multiset.ofList.{u2} α l)) (Multiset.ofList.{u1} β (List.map.{u2, u1} α β f l))
Case conversion may be inaccurate. Consider using '#align multiset.coe_map Multiset.coe_mapₓ'. -/
@[simp]
theorem coe_map (f : α → β) (l : List α) : map f ↑l = l.map f :=
  rfl
#align multiset.coe_map Multiset.coe_map

#print Multiset.map_zero /-
@[simp]
theorem map_zero (f : α → β) : map f 0 = 0 :=
  rfl
#align multiset.map_zero Multiset.map_zero
-/

/- warning: multiset.map_cons -> Multiset.map_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (a : α) (s : Multiset.{u1} α), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f (Multiset.cons.{u1} α a s)) (Multiset.cons.{u2} β (f a) (Multiset.map.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (a : α) (s : Multiset.{u2} α), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f (Multiset.cons.{u2} α a s)) (Multiset.cons.{u1} β (f a) (Multiset.map.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align multiset.map_cons Multiset.map_consₓ'. -/
@[simp]
theorem map_cons (f : α → β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s :=
  Quot.inductionOn s fun l => rfl
#align multiset.map_cons Multiset.map_cons

/- warning: multiset.map_comp_cons -> Multiset.map_comp_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (t : α), Eq.{max (succ u1) (succ u2)} ((Multiset.{u1} α) -> (Multiset.{u2} β)) (Function.comp.{succ u1, succ u1, succ u2} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f) (Multiset.cons.{u1} α t)) (Function.comp.{succ u1, succ u2, succ u2} (Multiset.{u1} α) (Multiset.{u2} β) (Multiset.{u2} β) (Multiset.cons.{u2} β (f t)) (Multiset.map.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (t : α), Eq.{max (succ u2) (succ u1)} ((Multiset.{u2} α) -> (Multiset.{u1} β)) (Function.comp.{succ u2, succ u2, succ u1} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f) (Multiset.cons.{u2} α t)) (Function.comp.{succ u2, succ u1, succ u1} (Multiset.{u2} α) (Multiset.{u1} β) (Multiset.{u1} β) (Multiset.cons.{u1} β (f t)) (Multiset.map.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align multiset.map_comp_cons Multiset.map_comp_consₓ'. -/
theorem map_comp_cons (f : α → β) (t) : map f ∘ cons t = cons (f t) ∘ map f :=
  by
  ext
  simp
#align multiset.map_comp_cons Multiset.map_comp_cons

#print Multiset.map_singleton /-
@[simp]
theorem map_singleton (f : α → β) (a : α) : ({a} : Multiset α).map f = {f a} :=
  rfl
#align multiset.map_singleton Multiset.map_singleton
-/

/- warning: multiset.map_replicate -> Multiset.map_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (a : α) (k : Nat), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f (Multiset.replicate.{u1} α k a)) (Multiset.replicate.{u2} β k (f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (a : Nat) (k : α), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f (Multiset.replicate.{u1} α a k)) (Multiset.replicate.{u2} β a (f k))
Case conversion may be inaccurate. Consider using '#align multiset.map_replicate Multiset.map_replicateₓ'. -/
@[simp]
theorem map_replicate (f : α → β) (a : α) (k : ℕ) : (replicate k a).map f = replicate k (f a) := by
  simp only [← coe_replicate, coe_map, map_replicate]
#align multiset.map_replicate Multiset.map_replicate

/- warning: multiset.map_add -> Multiset.map_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t)) (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} β) (Multiset.{u2} β) (Multiset.{u2} β) (instHAdd.{u2} (Multiset.{u2} β) (Multiset.hasAdd.{u2} β)) (Multiset.map.{u1, u2} α β f s) (Multiset.map.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Multiset.{u2} α) (t : Multiset.{u2} α), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u2} α) (instHAdd.{u2} (Multiset.{u2} α) (Multiset.instAddMultiset.{u2} α)) s t)) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} β) (Multiset.{u1} β) (Multiset.{u1} β) (instHAdd.{u1} (Multiset.{u1} β) (Multiset.instAddMultiset.{u1} β)) (Multiset.map.{u2, u1} α β f s) (Multiset.map.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align multiset.map_add Multiset.map_addₓ'. -/
@[simp]
theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => congr_arg coe <| map_append _ _ _
#align multiset.map_add Multiset.map_add

#print Multiset.canLift /-
/-- If each element of `s : multiset α` can be lifted to `β`, then `s` can be lifted to
`multiset β`. -/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Multiset α) (Multiset β) (map c) fun s => ∀ x ∈ s, p x
    where prf := by
    rintro ⟨l⟩ hl
    lift l to List β using hl
    exact ⟨l, coe_map _ _⟩
#align multiset.can_lift Multiset.canLift
-/

/- warning: multiset.map_add_monoid_hom -> Multiset.mapAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (AddMonoidHom.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (AddMonoidHom.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_monoid_hom Multiset.mapAddMonoidHomₓ'. -/
/-- `multiset.map` as an `add_monoid_hom`. -/
def mapAddMonoidHom (f : α → β) : Multiset α →+ Multiset β
    where
  toFun := map f
  map_zero' := map_zero _
  map_add' := map_add _
#align multiset.map_add_monoid_hom Multiset.mapAddMonoidHom

/- warning: multiset.coe_map_add_monoid_hom -> Multiset.coe_mapAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{max (succ u1) (succ u2)} ((fun (_x : AddMonoidHom.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β))))))) => (Multiset.{u1} α) -> (Multiset.{u2} β)) (Multiset.mapAddMonoidHom.{u1, u2} α β f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β))))))) (fun (_x : AddMonoidHom.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β))))))) => (Multiset.{u1} α) -> (Multiset.{u2} β)) (AddMonoidHom.hasCoeToFun.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β))))))) (Multiset.mapAddMonoidHom.{u1, u2} α β f)) (Multiset.map.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{max (succ u2) (succ u1)} (forall (a : Multiset.{u2} α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Multiset.{u1} β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AddMonoidHom.{u2, u1} (Multiset.{u2} α) (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Multiset.{u1} β) _x) (AddHomClass.toFunLike.{max u2 u1, u2, u1} (AddMonoidHom.{u2, u1} (Multiset.{u2} α) (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) (Multiset.{u2} α) (Multiset.{u1} β) (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{u1} (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) (AddMonoidHomClass.toAddHomClass.{max u2 u1, u2, u1} (AddMonoidHom.{u2, u1} (Multiset.{u2} α) (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) (Multiset.{u2} α) (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoidHom.addMonoidHomClass.{u2, u1} (Multiset.{u2} α) (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))))) (Multiset.mapAddMonoidHom.{u2, u1} α β f)) (Multiset.map.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align multiset.coe_map_add_monoid_hom Multiset.coe_mapAddMonoidHomₓ'. -/
@[simp]
theorem coe_mapAddMonoidHom (f : α → β) : (mapAddMonoidHom f : Multiset α → Multiset β) = map f :=
  rfl
#align multiset.coe_map_add_monoid_hom Multiset.coe_mapAddMonoidHom

/- warning: multiset.map_nsmul -> Multiset.map_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (n : Nat) (s : Multiset.{u1} α), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) (SMul.smul.{0, u2} Nat (Multiset.{u2} β) (AddMonoid.SMul.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) n (Multiset.map.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (n : Nat) (s : Multiset.{u2} α), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f (HSMul.hSMul.{0, u2, u2} Nat (Multiset.{u2} α) (Multiset.{u2} α) (instHSMul.{0, u2} Nat (Multiset.{u2} α) (AddMonoid.SMul.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) n s)) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} β) (Multiset.{u1} β) (instHSMul.{0, u1} Nat (Multiset.{u1} β) (AddMonoid.SMul.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) n (Multiset.map.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align multiset.map_nsmul Multiset.map_nsmulₓ'. -/
theorem map_nsmul (f : α → β) (n : ℕ) (s) : map f (n • s) = n • map f s :=
  (mapAddMonoidHom f).map_nsmul _ _
#align multiset.map_nsmul Multiset.map_nsmul

/- warning: multiset.mem_map -> Multiset.mem_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Multiset.{u1} α}, Iff (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b (Multiset.map.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) (Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {b : β} {s : Multiset.{u2} α}, Iff (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b (Multiset.map.{u2, u1} α β f s)) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) (Eq.{succ u1} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align multiset.mem_map Multiset.mem_mapₓ'. -/
@[simp]
theorem mem_map {f : α → β} {b : β} {s : Multiset α} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
  Quot.inductionOn s fun l => mem_map'
#align multiset.mem_map Multiset.mem_map

/- warning: multiset.card_map -> Multiset.card_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Multiset.{u1} α), Eq.{1} Nat (coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} β) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} β) (Multiset.map.{u1, u2} α β f s)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Multiset.{u2} α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} β) => Nat) (Multiset.map.{u2, u1} α β f s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) (fun (_x : Multiset.{u1} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} β) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} β) (Multiset.map.{u2, u1} α β f s)) (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s)
Case conversion may be inaccurate. Consider using '#align multiset.card_map Multiset.card_mapₓ'. -/
@[simp]
theorem card_map (f : α → β) (s) : card (map f s) = card s :=
  Quot.inductionOn s fun l => length_map _ _
#align multiset.card_map Multiset.card_map

/- warning: multiset.map_eq_zero -> Multiset.map_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Multiset.{u1} α} {f : α -> β}, Iff (Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f s) (OfNat.ofNat.{u2} (Multiset.{u2} β) 0 (OfNat.mk.{u2} (Multiset.{u2} β) 0 (Zero.zero.{u2} (Multiset.{u2} β) (Multiset.hasZero.{u2} β))))) (Eq.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Multiset.{u2} α} {f : α -> β}, Iff (Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f s) (OfNat.ofNat.{u1} (Multiset.{u1} β) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} β) (Multiset.instZeroMultiset.{u1} β)))) (Eq.{succ u2} (Multiset.{u2} α) s (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α))))
Case conversion may be inaccurate. Consider using '#align multiset.map_eq_zero Multiset.map_eq_zeroₓ'. -/
@[simp]
theorem map_eq_zero {s : Multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 := by
  rw [← Multiset.card_eq_zero, Multiset.card_map, Multiset.card_eq_zero]
#align multiset.map_eq_zero Multiset.map_eq_zero

/- warning: multiset.mem_map_of_mem -> Multiset.mem_map_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) {a : α} {s : Multiset.{u1} α}, (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) (f a) (Multiset.map.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) {a : α} {s : Multiset.{u2} α}, (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) (f a) (Multiset.map.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align multiset.mem_map_of_mem Multiset.mem_map_of_memₓ'. -/
theorem mem_map_of_mem (f : α → β) {a : α} {s : Multiset α} (h : a ∈ s) : f a ∈ map f s :=
  mem_map.2 ⟨_, h, rfl⟩
#align multiset.mem_map_of_mem Multiset.mem_map_of_mem

/- warning: multiset.map_eq_singleton -> Multiset.map_eq_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Multiset.{u1} α} {b : β}, Iff (Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f s) (Singleton.singleton.{u2, u2} β (Multiset.{u2} β) (Multiset.hasSingleton.{u2} β) b)) (Exists.{succ u1} α (fun (a : α) => And (Eq.{succ u1} (Multiset.{u1} α) s (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a)) (Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Multiset.{u2} α} {b : β}, Iff (Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f s) (Singleton.singleton.{u1, u1} β (Multiset.{u1} β) (Multiset.instSingletonMultiset.{u1} β) b)) (Exists.{succ u2} α (fun (a : α) => And (Eq.{succ u2} (Multiset.{u2} α) s (Singleton.singleton.{u2, u2} α (Multiset.{u2} α) (Multiset.instSingletonMultiset.{u2} α) a)) (Eq.{succ u1} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align multiset.map_eq_singleton Multiset.map_eq_singletonₓ'. -/
theorem map_eq_singleton {f : α → β} {s : Multiset α} {b : β} :
    map f s = {b} ↔ ∃ a : α, s = {a} ∧ f a = b :=
  by
  constructor
  · intro h
    obtain ⟨a, ha⟩ : ∃ a, s = {a} := by rw [← card_eq_one, ← card_map, h, card_singleton]
    refine' ⟨a, ha, _⟩
    rw [← mem_singleton, ← h, ha, map_singleton, mem_singleton]
  · rintro ⟨a, rfl, rfl⟩
    simp
#align multiset.map_eq_singleton Multiset.map_eq_singleton

/- warning: multiset.map_eq_cons -> Multiset.map_eq_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (f : α -> β) (s : Multiset.{u1} α) (t : Multiset.{u2} β) (b : β), Iff (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) => And (Eq.{succ u2} β (f a) b) (Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) t)))) (Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f s) (Multiset.cons.{u2} β b t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (f : α -> β) (s : Multiset.{u2} α) (t : Multiset.{u1} β) (b : β), Iff (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) (And (Eq.{succ u1} β (f a) b) (Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f (Multiset.erase.{u2} α (fun (a : α) (b : α) => _inst_1 a b) s a)) t)))) (Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f s) (Multiset.cons.{u1} β b t))
Case conversion may be inaccurate. Consider using '#align multiset.map_eq_cons Multiset.map_eq_consₓ'. -/
theorem map_eq_cons [DecidableEq α] (f : α → β) (s : Multiset α) (t : Multiset β) (b : β) :
    (∃ a ∈ s, f a = b ∧ (s.eraseₓ a).map f = t) ↔ s.map f = b ::ₘ t :=
  by
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [← map_cons, Multiset.cons_erase ha]
  · intro h
    have : b ∈ s.map f := by
      rw [h]
      exact mem_cons_self _ _
    obtain ⟨a, h1, rfl⟩ := mem_map.mp this
    obtain ⟨u, rfl⟩ := exists_cons_of_mem h1
    rw [map_cons, cons_inj_right] at h
    refine' ⟨a, mem_cons_self _ _, rfl, _⟩
    rw [Multiset.erase_cons_head, h]
#align multiset.map_eq_cons Multiset.map_eq_cons

/- warning: multiset.mem_map_of_injective -> Multiset.mem_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {a : α} {s : Multiset.{u1} α}, Iff (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) (f a) (Multiset.map.{u1, u2} α β f s)) (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {a : α} {s : Multiset.{u2} α}, Iff (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) (f a) (Multiset.map.{u2, u1} α β f s)) (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s))
Case conversion may be inaccurate. Consider using '#align multiset.mem_map_of_injective Multiset.mem_map_of_injectiveₓ'. -/
theorem mem_map_of_injective {f : α → β} (H : Function.Injective f) {a : α} {s : Multiset α} :
    f a ∈ map f s ↔ a ∈ s :=
  Quot.inductionOn s fun l => mem_map_of_injective H
#align multiset.mem_map_of_injective Multiset.mem_map_of_injective

/- warning: multiset.map_map -> Multiset.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (g : β -> γ) (f : α -> β) (s : Multiset.{u1} α), Eq.{succ u3} (Multiset.{u3} γ) (Multiset.map.{u2, u3} β γ g (Multiset.map.{u1, u2} α β f s)) (Multiset.map.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (g : β -> γ) (f : α -> β) (s : Multiset.{u3} α), Eq.{succ u2} (Multiset.{u2} γ) (Multiset.map.{u1, u2} β γ g (Multiset.map.{u3, u1} α β f s)) (Multiset.map.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f) s)
Case conversion may be inaccurate. Consider using '#align multiset.map_map Multiset.map_mapₓ'. -/
@[simp]
theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) : map g (map f s) = map (g ∘ f) s :=
  Quot.inductionOn s fun l => congr_arg coe <| List.map_map _ _ _
#align multiset.map_map Multiset.map_map

#print Multiset.map_id /-
theorem map_id (s : Multiset α) : map id s = s :=
  Quot.inductionOn s fun l => congr_arg coe <| map_id _
#align multiset.map_id Multiset.map_id
-/

#print Multiset.map_id' /-
@[simp]
theorem map_id' (s : Multiset α) : map (fun x => x) s = s :=
  map_id s
#align multiset.map_id' Multiset.map_id'
-/

/- warning: multiset.map_const -> Multiset.map_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (b : β), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β (Function.const.{succ u2, succ u1} β α b) s) (Multiset.replicate.{u2} β (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α) (b : β), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β (Function.const.{succ u1, succ u2} β α b) s) (Multiset.replicate.{u1} β (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s) b)
Case conversion may be inaccurate. Consider using '#align multiset.map_const Multiset.map_constₓ'. -/
@[simp]
theorem map_const (s : Multiset α) (b : β) : map (Function.const α b) s = replicate s.card b :=
  Quot.inductionOn s fun l => congr_arg coe <| map_const _ _
#align multiset.map_const Multiset.map_const

/- warning: multiset.map_const' -> Multiset.map_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (b : β), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β (fun (_x : α) => b) s) (Multiset.replicate.{u2} β (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α) (b : β), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β (fun (_x : α) => b) s) (Multiset.replicate.{u1} β (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s) b)
Case conversion may be inaccurate. Consider using '#align multiset.map_const' Multiset.map_const'ₓ'. -/
-- Not a `simp` lemma because `function.const` is reducibel in Lean 3
theorem map_const' (s : Multiset α) (b : β) : map (fun _ => b) s = replicate s.card b :=
  map_const s b
#align multiset.map_const' Multiset.map_const'

/- warning: multiset.eq_of_mem_map_const -> Multiset.eq_of_mem_map_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {b₁ : β} {b₂ : β} {l : List.{u1} α}, (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b₁ (Multiset.map.{u1, u2} α β (Function.const.{succ u2, succ u1} β α b₂) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l))) -> (Eq.{succ u2} β b₁ b₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {b₁ : β} {b₂ : β} {l : List.{u2} α}, (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b₁ (Multiset.map.{u2, u1} α β (Function.const.{succ u1, succ u2} β α b₂) (Multiset.ofList.{u2} α l))) -> (Eq.{succ u1} β b₁ b₂)
Case conversion may be inaccurate. Consider using '#align multiset.eq_of_mem_map_const Multiset.eq_of_mem_map_constₓ'. -/
theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (Function.const α b₂) l) :
    b₁ = b₂ :=
  eq_of_mem_replicate <| by rwa [map_const] at h
#align multiset.eq_of_mem_map_const Multiset.eq_of_mem_map_const

/- warning: multiset.map_le_map -> Multiset.map_le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{u2} (Multiset.{u2} β) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))) (Multiset.map.{u1, u2} α β f s) (Multiset.map.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Multiset.{u2} α} {t : Multiset.{u2} α}, (LE.le.{u2} (Multiset.{u2} α) (Preorder.toLE.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) s t) -> (LE.le.{u1} (Multiset.{u1} β) (Preorder.toLE.{u1} (Multiset.{u1} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β))) (Multiset.map.{u2, u1} α β f s) (Multiset.map.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align multiset.map_le_map Multiset.map_le_mapₓ'. -/
@[simp]
theorem map_le_map {f : α → β} {s t : Multiset α} (h : s ≤ t) : map f s ≤ map f t :=
  leInductionOn h fun l₁ l₂ h => (h.map f).Subperm
#align multiset.map_le_map Multiset.map_le_map

/- warning: multiset.map_lt_map -> Multiset.map_lt_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LT.lt.{u2} (Multiset.{u2} β) (Preorder.toLT.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))) (Multiset.map.{u1, u2} α β f s) (Multiset.map.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Multiset.{u2} α} {t : Multiset.{u2} α}, (LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) s t) -> (LT.lt.{u1} (Multiset.{u1} β) (Preorder.toLT.{u1} (Multiset.{u1} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β))) (Multiset.map.{u2, u1} α β f s) (Multiset.map.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align multiset.map_lt_map Multiset.map_lt_mapₓ'. -/
@[simp]
theorem map_lt_map {f : α → β} {s t : Multiset α} (h : s < t) : s.map f < t.map f :=
  by
  refine' (map_le_map h.le).lt_of_not_le fun H => h.ne <| eq_of_le_of_card_le h.le _
  rw [← s.card_map f, ← t.card_map f]
  exact card_le_of_le H
#align multiset.map_lt_map Multiset.map_lt_map

/- warning: multiset.map_mono -> Multiset.map_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Monotone.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β)) (Multiset.map.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Monotone.{u2, u1} (Multiset.{u2} α) (Multiset.{u1} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β)) (Multiset.map.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align multiset.map_mono Multiset.map_monoₓ'. -/
theorem map_mono (f : α → β) : Monotone (map f) := fun _ _ => map_le_map
#align multiset.map_mono Multiset.map_mono

/- warning: multiset.map_strict_mono -> Multiset.map_strictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), StrictMono.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β)) (Multiset.map.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), StrictMono.{u2, u1} (Multiset.{u2} α) (Multiset.{u1} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β)) (Multiset.map.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align multiset.map_strict_mono Multiset.map_strictMonoₓ'. -/
theorem map_strictMono (f : α → β) : StrictMono (map f) := fun _ _ => map_lt_map
#align multiset.map_strict_mono Multiset.map_strictMono

/- warning: multiset.map_subset_map -> Multiset.map_subset_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (HasSubset.Subset.{u1} (Multiset.{u1} α) (Multiset.hasSubset.{u1} α) s t) -> (HasSubset.Subset.{u2} (Multiset.{u2} β) (Multiset.hasSubset.{u2} β) (Multiset.map.{u1, u2} α β f s) (Multiset.map.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Multiset.{u2} α} {t : Multiset.{u2} α}, (HasSubset.Subset.{u2} (Multiset.{u2} α) (Multiset.instHasSubsetMultiset.{u2} α) s t) -> (HasSubset.Subset.{u1} (Multiset.{u1} β) (Multiset.instHasSubsetMultiset.{u1} β) (Multiset.map.{u2, u1} α β f s) (Multiset.map.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align multiset.map_subset_map Multiset.map_subset_mapₓ'. -/
@[simp]
theorem map_subset_map {f : α → β} {s t : Multiset α} (H : s ⊆ t) : map f s ⊆ map f t := fun b m =>
  let ⟨a, h, e⟩ := mem_map.1 m
  mem_map.2 ⟨a, H h, e⟩
#align multiset.map_subset_map Multiset.map_subset_map

/- warning: multiset.map_erase -> Multiset.map_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (x : α) (s : Multiset.{u1} α), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s x)) (Multiset.erase.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (Multiset.map.{u1, u2} α β f s) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] (f : α -> β), (Function.Injective.{succ u2, succ u1} α β f) -> (forall (x : α) (s : Multiset.{u2} α), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f (Multiset.erase.{u2} α (fun (a : α) (b : α) => _inst_1 a b) s x)) (Multiset.erase.{u1} β (fun (a : β) (b : β) => _inst_2 a b) (Multiset.map.{u2, u1} α β f s) (f x)))
Case conversion may be inaccurate. Consider using '#align multiset.map_erase Multiset.map_eraseₓ'. -/
theorem map_erase [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f) (x : α)
    (s : Multiset α) : (s.eraseₓ x).map f = (s.map f).eraseₓ (f x) :=
  by
  induction' s using Multiset.induction_on with y s ih
  · simp
  by_cases hxy : y = x
  · cases hxy
    simp
  · rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tailₓ (hf.ne hxy), ih]
#align multiset.map_erase Multiset.map_erase

/- warning: multiset.map_surjective_of_surjective -> Multiset.map_surjective_of_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (Function.Surjective.{succ u1, succ u2} (Multiset.{u1} α) (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (Function.Surjective.{succ u2, succ u1} (Multiset.{u2} α) (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align multiset.map_surjective_of_surjective Multiset.map_surjective_of_surjectiveₓ'. -/
theorem map_surjective_of_surjective {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective (map f) := by
  intro s
  induction' s using Multiset.induction_on with x s ih
  · exact ⟨0, map_zero _⟩
  · obtain ⟨y, rfl⟩ := hf x
    obtain ⟨t, rfl⟩ := ih
    exact ⟨y ::ₘ t, map_cons _ _ _⟩
#align multiset.map_surjective_of_surjective Multiset.map_surjective_of_surjective

/-! ### `multiset.fold` -/


#print Multiset.foldl /-
/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
def foldl (f : β → α → β) (H : RightCommutative f) (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => foldl f b l) fun l₁ l₂ p => p.foldl_eq H b
#align multiset.foldl Multiset.foldl
-/

/- warning: multiset.foldl_zero -> Multiset.foldl_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (H : RightCommutative.{u1, u2} α β f) (b : β), Eq.{succ u2} β (Multiset.foldl.{u1, u2} α β f H b (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) b
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (H : RightCommutative.{u2, u1} α β f) (b : β), Eq.{succ u1} β (Multiset.foldl.{u2, u1} α β f H b (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α)))) b
Case conversion may be inaccurate. Consider using '#align multiset.foldl_zero Multiset.foldl_zeroₓ'. -/
@[simp]
theorem foldl_zero (f : β → α → β) (H b) : foldl f H b 0 = b :=
  rfl
#align multiset.foldl_zero Multiset.foldl_zero

/- warning: multiset.foldl_cons -> Multiset.foldl_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (H : RightCommutative.{u1, u2} α β f) (b : β) (a : α) (s : Multiset.{u1} α), Eq.{succ u2} β (Multiset.foldl.{u1, u2} α β f H b (Multiset.cons.{u1} α a s)) (Multiset.foldl.{u1, u2} α β f H (f b a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (H : RightCommutative.{u2, u1} α β f) (b : β) (a : α) (s : Multiset.{u2} α), Eq.{succ u1} β (Multiset.foldl.{u2, u1} α β f H b (Multiset.cons.{u2} α a s)) (Multiset.foldl.{u2, u1} α β f H (f b a) s)
Case conversion may be inaccurate. Consider using '#align multiset.foldl_cons Multiset.foldl_consₓ'. -/
@[simp]
theorem foldl_cons (f : β → α → β) (H b a s) : foldl f H b (a ::ₘ s) = foldl f H (f b a) s :=
  Quot.inductionOn s fun l => rfl
#align multiset.foldl_cons Multiset.foldl_cons

/- warning: multiset.foldl_add -> Multiset.foldl_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (H : RightCommutative.{u1, u2} α β f) (b : β) (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u2} β (Multiset.foldl.{u1, u2} α β f H b (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t)) (Multiset.foldl.{u1, u2} α β f H (Multiset.foldl.{u1, u2} α β f H b s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (H : RightCommutative.{u2, u1} α β f) (b : β) (s : Multiset.{u2} α) (t : Multiset.{u2} α), Eq.{succ u1} β (Multiset.foldl.{u2, u1} α β f H b (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u2} α) (instHAdd.{u2} (Multiset.{u2} α) (Multiset.instAddMultiset.{u2} α)) s t)) (Multiset.foldl.{u2, u1} α β f H (Multiset.foldl.{u2, u1} α β f H b s) t)
Case conversion may be inaccurate. Consider using '#align multiset.foldl_add Multiset.foldl_addₓ'. -/
@[simp]
theorem foldl_add (f : β → α → β) (H b s t) : foldl f H b (s + t) = foldl f H (foldl f H b s) t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => foldl_append _ _ _ _
#align multiset.foldl_add Multiset.foldl_add

#print Multiset.foldr /-
/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr (f : α → β → β) (H : LeftCommutative f) (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => foldr f b l) fun l₁ l₂ p => p.foldr_eq H b
#align multiset.foldr Multiset.foldr
-/

/- warning: multiset.foldr_zero -> Multiset.foldr_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (H : LeftCommutative.{u1, u2} α β f) (b : β), Eq.{succ u2} β (Multiset.foldr.{u1, u2} α β f H b (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) b
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (H : LeftCommutative.{u2, u1} α β f) (b : β), Eq.{succ u1} β (Multiset.foldr.{u2, u1} α β f H b (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α)))) b
Case conversion may be inaccurate. Consider using '#align multiset.foldr_zero Multiset.foldr_zeroₓ'. -/
@[simp]
theorem foldr_zero (f : α → β → β) (H b) : foldr f H b 0 = b :=
  rfl
#align multiset.foldr_zero Multiset.foldr_zero

/- warning: multiset.foldr_cons -> Multiset.foldr_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (H : LeftCommutative.{u1, u2} α β f) (b : β) (a : α) (s : Multiset.{u1} α), Eq.{succ u2} β (Multiset.foldr.{u1, u2} α β f H b (Multiset.cons.{u1} α a s)) (f a (Multiset.foldr.{u1, u2} α β f H b s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (H : LeftCommutative.{u2, u1} α β f) (b : β) (a : α) (s : Multiset.{u2} α), Eq.{succ u1} β (Multiset.foldr.{u2, u1} α β f H b (Multiset.cons.{u2} α a s)) (f a (Multiset.foldr.{u2, u1} α β f H b s))
Case conversion may be inaccurate. Consider using '#align multiset.foldr_cons Multiset.foldr_consₓ'. -/
@[simp]
theorem foldr_cons (f : α → β → β) (H b a s) : foldr f H b (a ::ₘ s) = f a (foldr f H b s) :=
  Quot.inductionOn s fun l => rfl
#align multiset.foldr_cons Multiset.foldr_cons

/- warning: multiset.foldr_singleton -> Multiset.foldr_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (H : LeftCommutative.{u1, u2} α β f) (b : β) (a : α), Eq.{succ u2} β (Multiset.foldr.{u1, u2} α β f H b (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a)) (f a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (H : LeftCommutative.{u2, u1} α β f) (b : β) (a : α), Eq.{succ u1} β (Multiset.foldr.{u2, u1} α β f H b (Singleton.singleton.{u2, u2} α (Multiset.{u2} α) (Multiset.instSingletonMultiset.{u2} α) a)) (f a b)
Case conversion may be inaccurate. Consider using '#align multiset.foldr_singleton Multiset.foldr_singletonₓ'. -/
@[simp]
theorem foldr_singleton (f : α → β → β) (H b a) : foldr f H b ({a} : Multiset α) = f a b :=
  rfl
#align multiset.foldr_singleton Multiset.foldr_singleton

/- warning: multiset.foldr_add -> Multiset.foldr_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (H : LeftCommutative.{u1, u2} α β f) (b : β) (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u2} β (Multiset.foldr.{u1, u2} α β f H b (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t)) (Multiset.foldr.{u1, u2} α β f H (Multiset.foldr.{u1, u2} α β f H b t) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (H : LeftCommutative.{u2, u1} α β f) (b : β) (s : Multiset.{u2} α) (t : Multiset.{u2} α), Eq.{succ u1} β (Multiset.foldr.{u2, u1} α β f H b (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u2} α) (instHAdd.{u2} (Multiset.{u2} α) (Multiset.instAddMultiset.{u2} α)) s t)) (Multiset.foldr.{u2, u1} α β f H (Multiset.foldr.{u2, u1} α β f H b t) s)
Case conversion may be inaccurate. Consider using '#align multiset.foldr_add Multiset.foldr_addₓ'. -/
@[simp]
theorem foldr_add (f : α → β → β) (H b s t) : foldr f H b (s + t) = foldr f H (foldr f H b t) s :=
  Quotient.induction_on₂ s t fun l₁ l₂ => foldr_append _ _ _ _
#align multiset.foldr_add Multiset.foldr_add

/- warning: multiset.coe_foldr -> Multiset.coe_foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (H : LeftCommutative.{u1, u2} α β f) (b : β) (l : List.{u1} α), Eq.{succ u2} β (Multiset.foldr.{u1, u2} α β f H b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) (List.foldr.{u1, u2} α β f b l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (H : LeftCommutative.{u2, u1} α β f) (b : β) (l : List.{u2} α), Eq.{succ u1} β (Multiset.foldr.{u2, u1} α β f H b (Multiset.ofList.{u2} α l)) (List.foldr.{u2, u1} α β f b l)
Case conversion may be inaccurate. Consider using '#align multiset.coe_foldr Multiset.coe_foldrₓ'. -/
@[simp]
theorem coe_foldr (f : α → β → β) (H : LeftCommutative f) (b : β) (l : List α) :
    foldr f H b l = l.foldr f b :=
  rfl
#align multiset.coe_foldr Multiset.coe_foldr

/- warning: multiset.coe_foldl -> Multiset.coe_foldl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (H : RightCommutative.{u1, u2} α β f) (b : β) (l : List.{u1} α), Eq.{succ u2} β (Multiset.foldl.{u1, u2} α β f H b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) (List.foldl.{u2, u1} β α f b l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (H : RightCommutative.{u2, u1} α β f) (b : β) (l : List.{u2} α), Eq.{succ u1} β (Multiset.foldl.{u2, u1} α β f H b (Multiset.ofList.{u2} α l)) (List.foldl.{u1, u2} β α f b l)
Case conversion may be inaccurate. Consider using '#align multiset.coe_foldl Multiset.coe_foldlₓ'. -/
@[simp]
theorem coe_foldl (f : β → α → β) (H : RightCommutative f) (b : β) (l : List α) :
    foldl f H b l = l.foldl f b :=
  rfl
#align multiset.coe_foldl Multiset.coe_foldl

/- warning: multiset.coe_foldr_swap -> Multiset.coe_foldr_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (H : LeftCommutative.{u1, u2} α β f) (b : β) (l : List.{u1} α), Eq.{succ u2} β (Multiset.foldr.{u1, u2} α β f H b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) (List.foldl.{u2, u1} β α (fun (x : β) (y : α) => f y x) b l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (H : LeftCommutative.{u2, u1} α β f) (b : β) (l : List.{u2} α), Eq.{succ u1} β (Multiset.foldr.{u2, u1} α β f H b (Multiset.ofList.{u2} α l)) (List.foldl.{u1, u2} β α (fun (x : β) (y : α) => f y x) b l)
Case conversion may be inaccurate. Consider using '#align multiset.coe_foldr_swap Multiset.coe_foldr_swapₓ'. -/
theorem coe_foldr_swap (f : α → β → β) (H : LeftCommutative f) (b : β) (l : List α) :
    foldr f H b l = l.foldl (fun x y => f y x) b :=
  (congr_arg (foldr f H b) (coe_reverse l)).symm.trans <| foldr_reverse _ _ _
#align multiset.coe_foldr_swap Multiset.coe_foldr_swap

/- warning: multiset.foldr_swap -> Multiset.foldr_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (H : LeftCommutative.{u1, u2} α β f) (b : β) (s : Multiset.{u1} α), Eq.{succ u2} β (Multiset.foldr.{u1, u2} α β f H b s) (Multiset.foldl.{u1, u2} α β (fun (x : β) (y : α) => f y x) (fun (x : β) (y : α) (z : α) => Eq.symm.{succ u2} β (f y (f z x)) (f z (f y x)) (H y z x)) b s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (H : LeftCommutative.{u2, u1} α β f) (b : β) (s : Multiset.{u2} α), Eq.{succ u1} β (Multiset.foldr.{u2, u1} α β f H b s) (Multiset.foldl.{u2, u1} α β (fun (x : β) (y : α) => f y x) (fun (x : β) (y : α) (z : α) => Eq.symm.{succ u1} β (f y (f z x)) (f z (f y x)) (H y z x)) b s)
Case conversion may be inaccurate. Consider using '#align multiset.foldr_swap Multiset.foldr_swapₓ'. -/
theorem foldr_swap (f : α → β → β) (H : LeftCommutative f) (b : β) (s : Multiset α) :
    foldr f H b s = foldl (fun x y => f y x) (fun x y z => (H _ _ _).symm) b s :=
  Quot.inductionOn s fun l => coe_foldr_swap _ _ _ _
#align multiset.foldr_swap Multiset.foldr_swap

/- warning: multiset.foldl_swap -> Multiset.foldl_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (H : RightCommutative.{u1, u2} α β f) (b : β) (s : Multiset.{u1} α), Eq.{succ u2} β (Multiset.foldl.{u1, u2} α β f H b s) (Multiset.foldr.{u1, u2} α β (fun (x : α) (y : β) => f y x) (fun (x : α) (y : α) (z : β) => Eq.symm.{succ u2} β (f (f z x) y) (f (f z y) x) (H z x y)) b s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (H : RightCommutative.{u2, u1} α β f) (b : β) (s : Multiset.{u2} α), Eq.{succ u1} β (Multiset.foldl.{u2, u1} α β f H b s) (Multiset.foldr.{u2, u1} α β (fun (x : α) (y : β) => f y x) (fun (x : α) (y : α) (z : β) => Eq.symm.{succ u1} β (f (f z x) y) (f (f z y) x) (H z x y)) b s)
Case conversion may be inaccurate. Consider using '#align multiset.foldl_swap Multiset.foldl_swapₓ'. -/
theorem foldl_swap (f : β → α → β) (H : RightCommutative f) (b : β) (s : Multiset α) :
    foldl f H b s = foldr (fun x y => f y x) (fun x y z => (H _ _ _).symm) b s :=
  (foldr_swap _ _ _ _).symm
#align multiset.foldl_swap Multiset.foldl_swap

/- warning: multiset.foldr_induction' -> Multiset.foldr_induction' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (H : LeftCommutative.{u1, u2} α β f) (x : β) (q : α -> Prop) (p : β -> Prop) (s : Multiset.{u1} α), (forall (a : α) (b : β), (q a) -> (p b) -> (p (f a b))) -> (p x) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (q a)) -> (p (Multiset.foldr.{u1, u2} α β f H x s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (H : LeftCommutative.{u2, u1} α β f) (x : β) (q : α -> Prop) (p : β -> Prop) (s : Multiset.{u2} α), (forall (a : α) (b : β), (q a) -> (p b) -> (p (f a b))) -> (p x) -> (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (q a)) -> (p (Multiset.foldr.{u2, u1} α β f H x s))
Case conversion may be inaccurate. Consider using '#align multiset.foldr_induction' Multiset.foldr_induction'ₓ'. -/
theorem foldr_induction' (f : α → β → β) (H : LeftCommutative f) (x : β) (q : α → Prop)
    (p : β → Prop) (s : Multiset α) (hpqf : ∀ a b, q a → p b → p (f a b)) (px : p x)
    (q_s : ∀ a ∈ s, q a) : p (foldr f H x s) :=
  by
  revert s
  refine' Multiset.induction (by simp [px]) _
  intro a s hs hsa
  rw [foldr_cons]
  have hps : ∀ x : α, x ∈ s → q x := fun x hxs => hsa x (mem_cons_of_mem hxs)
  exact hpqf a (foldr f H x s) (hsa a (mem_cons_self a s)) (hs hps)
#align multiset.foldr_induction' Multiset.foldr_induction'

#print Multiset.foldr_induction /-
theorem foldr_induction (f : α → α → α) (H : LeftCommutative f) (x : α) (p : α → Prop)
    (s : Multiset α) (p_f : ∀ a b, p a → p b → p (f a b)) (px : p x) (p_s : ∀ a ∈ s, p a) :
    p (foldr f H x s) :=
  foldr_induction' f H x p p s p_f px p_s
#align multiset.foldr_induction Multiset.foldr_induction
-/

/- warning: multiset.foldl_induction' -> Multiset.foldl_induction' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (H : RightCommutative.{u1, u2} α β f) (x : β) (q : α -> Prop) (p : β -> Prop) (s : Multiset.{u1} α), (forall (a : α) (b : β), (q a) -> (p b) -> (p (f b a))) -> (p x) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (q a)) -> (p (Multiset.foldl.{u1, u2} α β f H x s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (H : RightCommutative.{u2, u1} α β f) (x : β) (q : α -> Prop) (p : β -> Prop) (s : Multiset.{u2} α), (forall (a : α) (b : β), (q a) -> (p b) -> (p (f b a))) -> (p x) -> (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (q a)) -> (p (Multiset.foldl.{u2, u1} α β f H x s))
Case conversion may be inaccurate. Consider using '#align multiset.foldl_induction' Multiset.foldl_induction'ₓ'. -/
theorem foldl_induction' (f : β → α → β) (H : RightCommutative f) (x : β) (q : α → Prop)
    (p : β → Prop) (s : Multiset α) (hpqf : ∀ a b, q a → p b → p (f b a)) (px : p x)
    (q_s : ∀ a ∈ s, q a) : p (foldl f H x s) :=
  by
  rw [foldl_swap]
  exact foldr_induction' (fun x y => f y x) (fun x y z => (H _ _ _).symm) x q p s hpqf px q_s
#align multiset.foldl_induction' Multiset.foldl_induction'

#print Multiset.foldl_induction /-
theorem foldl_induction (f : α → α → α) (H : RightCommutative f) (x : α) (p : α → Prop)
    (s : Multiset α) (p_f : ∀ a b, p a → p b → p (f b a)) (px : p x) (p_s : ∀ a ∈ s, p a) :
    p (foldl f H x s) :=
  foldl_induction' f H x p p s p_f px p_s
#align multiset.foldl_induction Multiset.foldl_induction
-/

/-! ### Map for partial functions -/


#print Multiset.pmap /-
/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
def pmap {p : α → Prop} (f : ∀ a, p a → β) (s : Multiset α) : (∀ a ∈ s, p a) → Multiset β :=
  Quot.recOn' s (fun l H => ↑(pmap f l H)) fun l₁ l₂ (pp : l₁ ~ l₂) =>
    funext fun H₂ : ∀ a ∈ l₂, p a =>
      have H₁ : ∀ a ∈ l₁, p a := fun a h => H₂ a (pp.Subset h)
      have :
        ∀ {s₂ e H},
          @Eq.ndrec (Multiset α) l₁ (fun s => (∀ a ∈ s, p a) → Multiset β)
              (fun _ => ↑(pmap f l₁ H₁)) s₂ e H =
            ↑(pmap f l₁ H₁) :=
        by intro s₂ e _ <;> subst e
      this.trans <| Quot.sound <| pp.pmap f
#align multiset.pmap Multiset.pmap
-/

/- warning: multiset.coe_pmap -> Multiset.coe_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (l : List.{u1} α) (H : forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (p a)), Eq.{succ u2} (Multiset.{u2} β) (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l) H) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (List.{u2} β) (Multiset.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (coeBase.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (Multiset.hasCoe.{u2} β)))) (List.pmap.{u1, u2} α β (fun (a : α) => p a) f l H))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (l : List.{u2} α) (H : forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (p a)), Eq.{succ u1} (Multiset.{u1} β) (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f (Multiset.ofList.{u2} α l) H) (Multiset.ofList.{u1} β (List.pmap.{u2, u1} α β (fun (a : α) => p a) f l H))
Case conversion may be inaccurate. Consider using '#align multiset.coe_pmap Multiset.coe_pmapₓ'. -/
@[simp]
theorem coe_pmap {p : α → Prop} (f : ∀ a, p a → β) (l : List α) (H : ∀ a ∈ l, p a) :
    pmap f l H = l.pmap f H :=
  rfl
#align multiset.coe_pmap Multiset.coe_pmap

/- warning: multiset.pmap_zero -> Multiset.pmap_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (h : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) -> (p a)), Eq.{succ u2} (Multiset.{u2} β) (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))) h) (OfNat.ofNat.{u2} (Multiset.{u2} β) 0 (OfNat.mk.{u2} (Multiset.{u2} β) 0 (Zero.zero.{u2} (Multiset.{u2} β) (Multiset.hasZero.{u2} β))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (h : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α)))) -> (p a)), Eq.{succ u1} (Multiset.{u1} β) (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α))) h) (OfNat.ofNat.{u1} (Multiset.{u1} β) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} β) (Multiset.instZeroMultiset.{u1} β)))
Case conversion may be inaccurate. Consider using '#align multiset.pmap_zero Multiset.pmap_zeroₓ'. -/
@[simp]
theorem pmap_zero {p : α → Prop} (f : ∀ a, p a → β) (h : ∀ a ∈ (0 : Multiset α), p a) :
    pmap f 0 h = 0 :=
  rfl
#align multiset.pmap_zero Multiset.pmap_zero

/- warning: multiset.pmap_cons -> Multiset.pmap_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (a : α) (m : Multiset.{u1} α) (h : forall (b : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) b (Multiset.cons.{u1} α a m)) -> (p b)), Eq.{succ u2} (Multiset.{u2} β) (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f (Multiset.cons.{u1} α a m) h) (Multiset.cons.{u2} β (f a (h a (Multiset.mem_cons_self.{u1} α a m))) (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f m (fun (a_1 : α) (ha : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a_1 m) => h a_1 (Multiset.mem_cons_of_mem.{u1} α a_1 a m ha))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (a : α) (m : Multiset.{u2} α) (h : forall (b : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) b (Multiset.cons.{u2} α a m)) -> (p b)), Eq.{succ u1} (Multiset.{u1} β) (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f (Multiset.cons.{u2} α a m) h) (Multiset.cons.{u1} β (f a (h a (Multiset.mem_cons_self.{u2} α a m))) (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f m (fun (a_1 : α) (ha : Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a_1 m) => h a_1 (Multiset.mem_cons_of_mem.{u2} α a_1 a m ha))))
Case conversion may be inaccurate. Consider using '#align multiset.pmap_cons Multiset.pmap_consₓ'. -/
@[simp]
theorem pmap_cons {p : α → Prop} (f : ∀ a, p a → β) (a : α) (m : Multiset α) :
    ∀ h : ∀ b ∈ a ::ₘ m, p b,
      pmap f (a ::ₘ m) h =
        f a (h a (mem_cons_self a m)) ::ₘ pmap f m fun a ha => h a <| mem_cons_of_mem ha :=
  Quotient.inductionOn m fun l h => rfl
#align multiset.pmap_cons Multiset.pmap_cons

#print Multiset.attach /-
/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach (s : Multiset α) : Multiset { x // x ∈ s } :=
  pmap Subtype.mk s fun a => id
#align multiset.attach Multiset.attach
-/

#print Multiset.coe_attach /-
@[simp]
theorem coe_attach (l : List α) : @Eq (Multiset { x // x ∈ l }) (@attach α l) l.attach :=
  rfl
#align multiset.coe_attach Multiset.coe_attach
-/

#print Multiset.sizeOf_lt_sizeOf_of_mem /-
theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {s : Multiset α} (hx : x ∈ s) :
    SizeOf.sizeOf x < SizeOf.sizeOf s :=
  by
  induction' s with l a b
  exact List.sizeOf_lt_sizeOf_of_mem hx
  rfl
#align multiset.sizeof_lt_sizeof_of_mem Multiset.sizeOf_lt_sizeOf_of_mem
-/

/- warning: multiset.pmap_eq_map -> Multiset.pmap_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Prop) (f : α -> β) (s : Multiset.{u1} α) (H : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)), Eq.{succ u2} (Multiset.{u2} β) (Multiset.pmap.{u1, u2} α β p (fun (a : α) (_x : p a) => f a) s H) (Multiset.map.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : α -> Prop) (f : α -> β) (s : Multiset.{u2} α) (H : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (p a)), Eq.{succ u1} (Multiset.{u1} β) (Multiset.pmap.{u2, u1} α β p (fun (a : α) (_x : p a) => f a) s H) (Multiset.map.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align multiset.pmap_eq_map Multiset.pmap_eq_mapₓ'. -/
theorem pmap_eq_map (p : α → Prop) (f : α → β) (s : Multiset α) :
    ∀ H, @pmap _ _ p (fun a _ => f a) s H = map f s :=
  Quot.inductionOn s fun l H => congr_arg coe <| pmap_eq_map p f l H
#align multiset.pmap_eq_map Multiset.pmap_eq_map

/- warning: multiset.pmap_congr -> Multiset.pmap_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} {q : α -> Prop} {f : forall (a : α), (p a) -> β} {g : forall (a : α), (q a) -> β} (s : Multiset.{u1} α) {H₁ : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)} {H₂ : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (q a)}, (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (forall (h₁ : p a) (h₂ : q a), Eq.{succ u2} β (f a h₁) (g a h₂))) -> (Eq.{succ u2} (Multiset.{u2} β) (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f s H₁) (Multiset.pmap.{u1, u2} α β (fun (a : α) => q a) g s H₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} {q : α -> Prop} {f : forall (a : α), (p a) -> β} {g : forall (a : α), (q a) -> β} (s : Multiset.{u2} α) {H₁ : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (p a)} {H₂ : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (q a)}, (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (forall (h₁ : p a) (h₂ : q a), Eq.{succ u1} β (f a h₁) (g a h₂))) -> (Eq.{succ u1} (Multiset.{u1} β) (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f s H₁) (Multiset.pmap.{u2, u1} α β (fun (a : α) => q a) g s H₂))
Case conversion may be inaccurate. Consider using '#align multiset.pmap_congr Multiset.pmap_congrₓ'. -/
theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (s : Multiset α) {H₁ H₂} :
    (∀ a ∈ s, ∀ (h₁ h₂), f a h₁ = g a h₂) → pmap f s H₁ = pmap g s H₂ :=
  Quot.inductionOn s (fun l H₁ H₂ h => congr_arg coe <| pmap_congr l h) H₁ H₂
#align multiset.pmap_congr Multiset.pmap_congr

/- warning: multiset.map_pmap -> Multiset.map_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {p : α -> Prop} (g : β -> γ) (f : forall (a : α), (p a) -> β) (s : Multiset.{u1} α) (H : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)), Eq.{succ u3} (Multiset.{u3} γ) (Multiset.map.{u2, u3} β γ g (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f s H)) (Multiset.pmap.{u1, u3} α γ (fun (a : α) => p a) (fun (a : α) (h : p a) => g (f a h)) s H)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {p : α -> Prop} (g : β -> γ) (f : forall (a : α), (p a) -> β) (s : Multiset.{u3} α) (H : forall (a : α), (Membership.mem.{u3, u3} α (Multiset.{u3} α) (Multiset.instMembershipMultiset.{u3} α) a s) -> (p a)), Eq.{succ u2} (Multiset.{u2} γ) (Multiset.map.{u1, u2} β γ g (Multiset.pmap.{u3, u1} α β (fun (a : α) => p a) f s H)) (Multiset.pmap.{u3, u2} α γ (fun (a : α) => p a) (fun (a : α) (h : p a) => g (f a h)) s H)
Case conversion may be inaccurate. Consider using '#align multiset.map_pmap Multiset.map_pmapₓ'. -/
theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (s) :
    ∀ H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H :=
  Quot.inductionOn s fun l H => congr_arg coe <| map_pmap g f l H
#align multiset.map_pmap Multiset.map_pmap

/- warning: multiset.pmap_eq_map_attach -> Multiset.pmap_eq_map_attach is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (s : Multiset.{u1} α) (H : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)), Eq.{succ u2} (Multiset.{u2} β) (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f s H) (Multiset.map.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) β (fun (x : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s))))) x) (H ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s))))) x) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) x))) (Multiset.attach.{u1} α s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (s : Multiset.{u2} α) (H : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (p a)), Eq.{succ u1} (Multiset.{u1} β) (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f s H) (Multiset.map.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) β (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s) x) (H (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s) x) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s) x))) (Multiset.attach.{u2} α s))
Case conversion may be inaccurate. Consider using '#align multiset.pmap_eq_map_attach Multiset.pmap_eq_map_attachₓ'. -/
theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (s) :
    ∀ H, pmap f s H = s.attach.map fun x => f x (H _ x.Prop) :=
  Quot.inductionOn s fun l H => congr_arg coe <| pmap_eq_map_attach f l H
#align multiset.pmap_eq_map_attach Multiset.pmap_eq_map_attach

/- warning: multiset.attach_map_coe' -> Multiset.attach_map_val' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (f : α -> β), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) β (fun (i : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s))))) i)) (Multiset.attach.{u1} α s)) (Multiset.map.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α) (f : α -> β), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) β (fun (i : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s) i)) (Multiset.attach.{u2} α s)) (Multiset.map.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align multiset.attach_map_coe' Multiset.attach_map_val'ₓ'. -/
@[simp]
theorem attach_map_val' (s : Multiset α) (f : α → β) : (s.attach.map fun i => f i) = s.map f :=
  Quot.inductionOn s fun l => congr_arg coe <| attach_map_coe' l f
#align multiset.attach_map_coe' Multiset.attach_map_val'

/- warning: multiset.attach_map_val' clashes with multiset.attach_map_coe' -> Multiset.attach_map_val'
warning: multiset.attach_map_val' -> Multiset.attach_map_val' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (f : α -> β), Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) β (fun (i : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) i)) (Multiset.attach.{u1} α s)) (Multiset.map.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α) (f : α -> β), Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) β (fun (i : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s) i)) (Multiset.attach.{u2} α s)) (Multiset.map.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align multiset.attach_map_val' Multiset.attach_map_val'ₓ'. -/
theorem attach_map_val' (s : Multiset α) (f : α → β) : (s.attach.map fun i => f i.val) = s.map f :=
  attach_map_val' _ _
#align multiset.attach_map_val' Multiset.attach_map_val'

#print Multiset.attach_map_val /-
@[simp]
theorem attach_map_val (s : Multiset α) : s.attach.map (coe : _ → α) = s :=
  (attach_map_val' _ _).trans s.map_id
#align multiset.attach_map_coe Multiset.attach_map_val
-/

/- warning: multiset.attach_map_val clashes with multiset.attach_map_coe -> Multiset.attach_map_val
Case conversion may be inaccurate. Consider using '#align multiset.attach_map_val Multiset.attach_map_valₓ'. -/
#print Multiset.attach_map_val /-
theorem attach_map_val (s : Multiset α) : s.attach.map Subtype.val = s :=
  attach_map_val _
#align multiset.attach_map_val Multiset.attach_map_val
-/

#print Multiset.mem_attach /-
@[simp]
theorem mem_attach (s : Multiset α) : ∀ x, x ∈ s.attach :=
  Quot.inductionOn s fun l => mem_attach _
#align multiset.mem_attach Multiset.mem_attach
-/

/- warning: multiset.mem_pmap -> Multiset.mem_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {s : Multiset.{u1} α} {H : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)} {b : β}, Iff (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f s H)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) (fun (h : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) => Eq.{succ u2} β (f a (H a h)) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {s : Multiset.{u2} α} {H : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (p a)} {b : β}, Iff (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f s H)) (Exists.{succ u2} α (fun (a : α) => Exists.{0} (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) (fun (h : Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) => Eq.{succ u1} β (f a (H a h)) b)))
Case conversion may be inaccurate. Consider using '#align multiset.mem_pmap Multiset.mem_pmapₓ'. -/
@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {s H b} :
    b ∈ pmap f s H ↔ ∃ (a : _)(h : a ∈ s), f a (H a h) = b :=
  Quot.inductionOn s (fun l H => mem_pmap) H
#align multiset.mem_pmap Multiset.mem_pmap

/- warning: multiset.card_pmap -> Multiset.card_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (s : Multiset.{u1} α) (H : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)), Eq.{1} Nat (coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} β) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} β) (Multiset.pmap.{u1, u2} α β (fun (a : α) => p a) f s H)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (s : Multiset.{u2} α) (H : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (p a)), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} β) => Nat) (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f s H)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) (fun (_x : Multiset.{u1} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} β) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} β) (Multiset.pmap.{u2, u1} α β (fun (a : α) => p a) f s H)) (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s)
Case conversion may be inaccurate. Consider using '#align multiset.card_pmap Multiset.card_pmapₓ'. -/
@[simp]
theorem card_pmap {p : α → Prop} (f : ∀ a, p a → β) (s H) : card (pmap f s H) = card s :=
  Quot.inductionOn s (fun l H => length_pmap) H
#align multiset.card_pmap Multiset.card_pmap

/- warning: multiset.card_attach -> Multiset.card_attach is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Multiset.{u1} α}, Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (Multiset.orderedCancelAddCommMonoid.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (Multiset.orderedCancelAddCommMonoid.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (Multiset.orderedCancelAddCommMonoid.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))) (Multiset.attach.{u1} α m)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m)
but is expected to have type
  forall {α : Type.{u1}} {m : Multiset.{u1} α}, Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) => Nat) (Multiset.attach.{u1} α m)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (fun (_x : Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m))) (Multiset.attach.{u1} α m)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m)
Case conversion may be inaccurate. Consider using '#align multiset.card_attach Multiset.card_attachₓ'. -/
@[simp]
theorem card_attach {m : Multiset α} : card (attach m) = card m :=
  card_pmap _ _ _
#align multiset.card_attach Multiset.card_attach

#print Multiset.attach_zero /-
@[simp]
theorem attach_zero : (0 : Multiset α).attach = 0 :=
  rfl
#align multiset.attach_zero Multiset.attach_zero
-/

#print Multiset.attach_cons /-
theorem attach_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).attach =
      ⟨a, mem_cons_self a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p.2⟩ :=
  Quotient.inductionOn m fun l =>
    congr_arg coe <|
      congr_arg (List.cons _) <| by
        rw [List.map_pmap] <;> exact List.pmap_congr _ fun _ _ _ _ => Subtype.eq rfl
#align multiset.attach_cons Multiset.attach_cons
-/

section DecidablePiExists

variable {m : Multiset α}

#print Multiset.decidableForallMultiset /-
/-- If `p` is a decidable predicate,
so is the predicate that all elements of a multiset satisfy `p`. -/
protected def decidableForallMultiset {p : α → Prop} [hp : ∀ a, Decidable (p a)] :
    Decidable (∀ a ∈ m, p a) :=
  Quotient.recOnSubsingleton m fun l => decidable_of_iff (∀ a ∈ l, p a) <| by simp
#align multiset.decidable_forall_multiset Multiset.decidableForallMultiset
-/

#print Multiset.decidableDforallMultiset /-
instance decidableDforallMultiset {p : ∀ a ∈ m, Prop} [hp : ∀ (a) (h : a ∈ m), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ m), p a h) :=
  decidable_of_decidable_of_iff
    (@Multiset.decidableForallMultiset { a // a ∈ m } m.attach (fun a => p a.1 a.2) _)
    (Iff.intro (fun h a ha => h ⟨a, ha⟩ (mem_attach _ _)) fun h ⟨a, ha⟩ _ => h _ _)
#align multiset.decidable_dforall_multiset Multiset.decidableDforallMultiset
-/

#print Multiset.decidableEqPiMultiset /-
/-- decidable equality for functions whose domain is bounded by multisets -/
instance decidableEqPiMultiset {β : α → Type _} [h : ∀ a, DecidableEq (β a)] :
    DecidableEq (∀ a ∈ m, β a) := fun f g =>
  decidable_of_iff (∀ (a) (h : a ∈ m), f a h = g a h) (by simp [Function.funext_iff])
#align multiset.decidable_eq_pi_multiset Multiset.decidableEqPiMultiset
-/

/- warning: multiset.decidable_exists_multiset -> Multiset.decidableExistsMultiset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p], Decidable (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m) (fun (H : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m) => p x)))
but is expected to have type
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p], Decidable (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m) (p x)))
Case conversion may be inaccurate. Consider using '#align multiset.decidable_exists_multiset Multiset.decidableExistsMultisetₓ'. -/
/-- If `p` is a decidable predicate,
so is the existence of an element in a multiset satisfying `p`. -/
protected def decidableExistsMultiset {p : α → Prop} [DecidablePred p] : Decidable (∃ x ∈ m, p x) :=
  Quotient.recOnSubsingleton m fun l => decidable_of_iff (∃ a ∈ l, p a) <| by simp
#align multiset.decidable_exists_multiset Multiset.decidableExistsMultiset

#print Multiset.decidableDexistsMultiset /-
instance decidableDexistsMultiset {p : ∀ a ∈ m, Prop} [hp : ∀ (a) (h : a ∈ m), Decidable (p a h)] :
    Decidable (∃ (a : _)(h : a ∈ m), p a h) :=
  decidable_of_decidable_of_iff
    (@Multiset.decidableExistsMultiset { a // a ∈ m } m.attach (fun a => p a.1 a.2) _)
    (Iff.intro (fun ⟨⟨a, ha₁⟩, _, ha₂⟩ => ⟨a, ha₁, ha₂⟩) fun ⟨a, ha₁, ha₂⟩ =>
      ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩)
#align multiset.decidable_dexists_multiset Multiset.decidableDexistsMultiset
-/

end DecidablePiExists

/-! ### Subtraction -/


section

variable [DecidableEq α] {s t u : Multiset α} {a b : α}

#print Multiset.sub /-
/-- `s - t` is the multiset such that `count a (s - t) = count a s - count a t` for all `a`
  (note that it is truncated subtraction, so it is `0` if `count a t ≥ count a s`). -/
protected def sub (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.diffₓ l₂ : Multiset α)) fun v₁ v₂ w₁ w₂ p₁ p₂ =>
    Quot.sound <| p₁.diffₓ p₂
#align multiset.sub Multiset.sub
-/

instance : Sub (Multiset α) :=
  ⟨Multiset.sub⟩

/- warning: multiset.coe_sub -> Multiset.coe_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : List.{u1} α) (t : List.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.hasSub.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) t)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : List.{u1} α) (t : List.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Multiset.ofList.{u1} α s) (Multiset.ofList.{u1} α t)) (Multiset.ofList.{u1} α (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t))
Case conversion may be inaccurate. Consider using '#align multiset.coe_sub Multiset.coe_subₓ'. -/
@[simp]
theorem coe_sub (s t : List α) : (s - t : Multiset α) = (s.diffₓ t : List α) :=
  rfl
#align multiset.coe_sub Multiset.coe_sub

#print Multiset.sub_zero /-
/-- This is a special case of `tsub_zero`, which should be used instead of this.
  This is needed to prove `has_ordered_sub (multiset α)`. -/
protected theorem sub_zero (s : Multiset α) : s - 0 = s :=
  Quot.inductionOn s fun l => rfl
#align multiset.sub_zero Multiset.sub_zero
-/

#print Multiset.sub_cons /-
@[simp]
theorem sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s.eraseₓ a - t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => congr_arg coe <| diff_cons _ _ _
#align multiset.sub_cons Multiset.sub_cons
-/

/- warning: multiset.sub_le_iff_le_add -> Multiset.sub_le_iff_le_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.hasSub.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s t) u) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) u t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s t) u) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) u t))
Case conversion may be inaccurate. Consider using '#align multiset.sub_le_iff_le_add Multiset.sub_le_iff_le_addₓ'. -/
/-- This is a special case of `tsub_le_iff_right`, which should be used instead of this.
  This is needed to prove `has_ordered_sub (multiset α)`. -/
protected theorem sub_le_iff_le_add : s - t ≤ u ↔ s ≤ u + t := by
  revert s <;>
    exact
      Multiset.induction_on t (by simp [Multiset.sub_zero]) fun a t IH s => by
        simp [IH, erase_le_iff_le_cons]
#align multiset.sub_le_iff_le_add Multiset.sub_le_iff_le_add

instance : OrderedSub (Multiset α) :=
  ⟨fun n m k => Multiset.sub_le_iff_le_add⟩

/- warning: multiset.cons_sub_of_le -> Multiset.cons_sub_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t s) -> (Eq.{succ u1} (Multiset.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.hasSub.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Multiset.cons.{u1} α a s) t) (Multiset.cons.{u1} α a (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.hasSub.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t s) -> (Eq.{succ u1} (Multiset.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Multiset.cons.{u1} α a s) t) (Multiset.cons.{u1} α a (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s t)))
Case conversion may be inaccurate. Consider using '#align multiset.cons_sub_of_le Multiset.cons_sub_of_leₓ'. -/
theorem cons_sub_of_le (a : α) {s t : Multiset α} (h : t ≤ s) : a ::ₘ s - t = a ::ₘ (s - t) := by
  rw [← singleton_add, ← singleton_add, add_tsub_assoc_of_le h]
#align multiset.cons_sub_of_le Multiset.cons_sub_of_le

#print Multiset.sub_eq_fold_erase /-
theorem sub_eq_fold_erase (s t : Multiset α) : s - t = foldl erase erase_comm s t :=
  Quotient.induction_on₂ s t fun l₁ l₂ =>
    show ↑(l₁.diffₓ l₂) = foldl erase erase_comm ↑l₁ ↑l₂
      by
      rw [diff_eq_foldl l₁ l₂]
      symm
      exact foldl_hom _ _ _ _ _ fun x y => rfl
#align multiset.sub_eq_fold_erase Multiset.sub_eq_fold_erase
-/

/- warning: multiset.card_sub -> Multiset.card_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t s) -> (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.hasSub.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t s) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s t)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s t)) (HSub.hSub.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) t) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (instHSub.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instSubNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) t)))
Case conversion may be inaccurate. Consider using '#align multiset.card_sub Multiset.card_subₓ'. -/
@[simp]
theorem card_sub {s t : Multiset α} (h : t ≤ s) : card (s - t) = card s - card t :=
  (tsub_eq_of_eq_add_rev <| by rw [add_comm, ← card_add, tsub_add_cancel_of_le h]).symm
#align multiset.card_sub Multiset.card_sub

/-! ### Union -/


#print Multiset.union /-
/-- `s ∪ t` is the lattice join operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∪ t` is the maximum
  of the multiplicities in `s` and `t`. -/
def union (s t : Multiset α) : Multiset α :=
  s - t + t
#align multiset.union Multiset.union
-/

instance : Union (Multiset α) :=
  ⟨union⟩

#print Multiset.union_def /-
theorem union_def (s t : Multiset α) : s ∪ t = s - t + t :=
  rfl
#align multiset.union_def Multiset.union_def
-/

/- warning: multiset.le_union_left -> Multiset.le_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
Case conversion may be inaccurate. Consider using '#align multiset.le_union_left Multiset.le_union_leftₓ'. -/
theorem le_union_left (s t : Multiset α) : s ≤ s ∪ t :=
  le_tsub_add
#align multiset.le_union_left Multiset.le_union_left

/- warning: multiset.le_union_right -> Multiset.le_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
Case conversion may be inaccurate. Consider using '#align multiset.le_union_right Multiset.le_union_rightₓ'. -/
theorem le_union_right (s t : Multiset α) : t ≤ s ∪ t :=
  le_add_left _ _
#align multiset.le_union_right Multiset.le_union_right

/- warning: multiset.eq_union_left -> Multiset.eq_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t s) -> (Eq.{succ u1} (Multiset.{u1} α) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t s) -> (Eq.{succ u1} (Multiset.{u1} α) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s)
Case conversion may be inaccurate. Consider using '#align multiset.eq_union_left Multiset.eq_union_leftₓ'. -/
theorem eq_union_left : t ≤ s → s ∪ t = s :=
  tsub_add_cancel_of_le
#align multiset.eq_union_left Multiset.eq_union_left

/- warning: multiset.union_le_union_right -> Multiset.union_le_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (forall (u : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s u) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (forall (u : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s u) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u))
Case conversion may be inaccurate. Consider using '#align multiset.union_le_union_right Multiset.union_le_union_rightₓ'. -/
theorem union_le_union_right (h : s ≤ t) (u) : s ∪ u ≤ t ∪ u :=
  add_le_add_right (tsub_le_tsub_right h _) u
#align multiset.union_le_union_right Multiset.union_le_union_right

/- warning: multiset.union_le -> Multiset.union_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s u) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t u) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s u) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t u) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) u)
Case conversion may be inaccurate. Consider using '#align multiset.union_le Multiset.union_leₓ'. -/
theorem union_le (h₁ : s ≤ u) (h₂ : t ≤ u) : s ∪ t ≤ u := by
  rw [← eq_union_left h₂] <;> exact union_le_union_right h₁ t
#align multiset.union_le Multiset.union_le

#print Multiset.mem_union /-
@[simp]
theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  ⟨fun h => (mem_add.1 h).imp_left (mem_of_le tsub_le_self),
    Or.ndrec (mem_of_le <| le_union_left _ _) (mem_of_le <| le_union_right _ _)⟩
#align multiset.mem_union Multiset.mem_union
-/

#print Multiset.map_union /-
@[simp]
theorem map_union [DecidableEq β] {f : α → β} (finj : Function.Injective f) {s t : Multiset α} :
    map f (s ∪ t) = map f s ∪ map f t :=
  Quotient.induction_on₂ s t fun l₁ l₂ =>
    congr_arg coe (by rw [List.map_append f, List.map_diff finj])
#align multiset.map_union Multiset.map_union
-/

/-! ### Intersection -/


#print Multiset.inter /-
/-- `s ∩ t` is the lattice meet operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∩ t` is the minimum
  of the multiplicities in `s` and `t`. -/
def inter (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.bagInterₓ l₂ : Multiset α)) fun v₁ v₂ w₁ w₂ p₁ p₂ =>
    Quot.sound <| p₁.bagInterₓ p₂
#align multiset.inter Multiset.inter
-/

instance : Inter (Multiset α) :=
  ⟨inter⟩

#print Multiset.inter_zero /-
@[simp]
theorem inter_zero (s : Multiset α) : s ∩ 0 = 0 :=
  Quot.inductionOn s fun l => congr_arg coe l.bagInter_nil
#align multiset.inter_zero Multiset.inter_zero
-/

#print Multiset.zero_inter /-
@[simp]
theorem zero_inter (s : Multiset α) : 0 ∩ s = 0 :=
  Quot.inductionOn s fun l => congr_arg coe l.nil_bagInter
#align multiset.zero_inter Multiset.zero_inter
-/

#print Multiset.cons_inter_of_pos /-
@[simp]
theorem cons_inter_of_pos {a} (s : Multiset α) {t} : a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.eraseₓ a :=
  Quotient.induction_on₂ s t fun l₁ l₂ h => congr_arg coe <| cons_bagInter_of_pos _ h
#align multiset.cons_inter_of_pos Multiset.cons_inter_of_pos
-/

#print Multiset.cons_inter_of_neg /-
@[simp]
theorem cons_inter_of_neg {a} (s : Multiset α) {t} : a ∉ t → (a ::ₘ s) ∩ t = s ∩ t :=
  Quotient.induction_on₂ s t fun l₁ l₂ h => congr_arg coe <| cons_bagInter_of_neg _ h
#align multiset.cons_inter_of_neg Multiset.cons_inter_of_neg
-/

/- warning: multiset.inter_le_left -> Multiset.inter_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s
Case conversion may be inaccurate. Consider using '#align multiset.inter_le_left Multiset.inter_le_leftₓ'. -/
theorem inter_le_left (s t : Multiset α) : s ∩ t ≤ s :=
  Quotient.induction_on₂ s t fun l₁ l₂ => (bagInter_sublist_left _ _).Subperm
#align multiset.inter_le_left Multiset.inter_le_left

/- warning: multiset.inter_le_right -> Multiset.inter_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) t
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) t
Case conversion may be inaccurate. Consider using '#align multiset.inter_le_right Multiset.inter_le_rightₓ'. -/
theorem inter_le_right (s : Multiset α) : ∀ t, s ∩ t ≤ t :=
  Multiset.induction_on s (fun t => (zero_inter t).symm ▸ zero_le _) fun a s IH t =>
    if h : a ∈ t then by simpa [h] using cons_le_cons a (IH (t.erase a)) else by simp [h, IH]
#align multiset.inter_le_right Multiset.inter_le_right

/- warning: multiset.le_inter -> Multiset.le_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s u) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s u) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u))
Case conversion may be inaccurate. Consider using '#align multiset.le_inter Multiset.le_interₓ'. -/
theorem le_inter (h₁ : s ≤ t) (h₂ : s ≤ u) : s ≤ t ∩ u :=
  by
  revert s u; refine' Multiset.induction_on t _ fun a t IH => _ <;> intros
  · simp [h₁]
  by_cases a ∈ u
  · rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons]
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂)
  · rw [cons_inter_of_neg _ h]
    exact IH ((le_cons_of_not_mem <| mt (mem_of_le h₂) h).1 h₁) h₂
#align multiset.le_inter Multiset.le_inter

#print Multiset.mem_inter /-
@[simp]
theorem mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=
  ⟨fun h => ⟨mem_of_le (inter_le_left _ _) h, mem_of_le (inter_le_right _ _) h⟩, fun ⟨h₁, h₂⟩ => by
    rw [← cons_erase h₁, cons_inter_of_pos _ h₂] <;> apply mem_cons_self⟩
#align multiset.mem_inter Multiset.mem_inter
-/

instance : Lattice (Multiset α) :=
  { @Multiset.partialOrder α with
    sup := (· ∪ ·)
    sup_le := @union_le _ _
    le_sup_left := le_union_left
    le_sup_right := le_union_right
    inf := (· ∩ ·)
    le_inf := @le_inter _ _
    inf_le_left := inter_le_left
    inf_le_right := inter_le_right }

/- warning: multiset.sup_eq_union -> Multiset.sup_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (HasSup.sup.{u1} (Multiset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Multiset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} α) (Multiset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) s t) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (HasSup.sup.{u1} (Multiset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Multiset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} α) (Multiset.instLatticeMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) s t) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
Case conversion may be inaccurate. Consider using '#align multiset.sup_eq_union Multiset.sup_eq_unionₓ'. -/
@[simp]
theorem sup_eq_union (s t : Multiset α) : s ⊔ t = s ∪ t :=
  rfl
#align multiset.sup_eq_union Multiset.sup_eq_union

/- warning: multiset.inf_eq_inter -> Multiset.inf_eq_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (HasInf.inf.{u1} (Multiset.{u1} α) (SemilatticeInf.toHasInf.{u1} (Multiset.{u1} α) (Lattice.toSemilatticeInf.{u1} (Multiset.{u1} α) (Multiset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) s t) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (HasInf.inf.{u1} (Multiset.{u1} α) (Lattice.toHasInf.{u1} (Multiset.{u1} α) (Multiset.instLatticeMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s t) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
Case conversion may be inaccurate. Consider using '#align multiset.inf_eq_inter Multiset.inf_eq_interₓ'. -/
@[simp]
theorem inf_eq_inter (s t : Multiset α) : s ⊓ t = s ∩ t :=
  rfl
#align multiset.inf_eq_inter Multiset.inf_eq_inter

/- warning: multiset.le_inter_iff -> Multiset.le_inter_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u)) (And (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u)) (And (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s u))
Case conversion may be inaccurate. Consider using '#align multiset.le_inter_iff Multiset.le_inter_iffₓ'. -/
@[simp]
theorem le_inter_iff : s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u :=
  le_inf_iff
#align multiset.le_inter_iff Multiset.le_inter_iff

/- warning: multiset.union_le_iff -> Multiset.union_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) u) (And (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s u) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) u) (And (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s u) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t u))
Case conversion may be inaccurate. Consider using '#align multiset.union_le_iff Multiset.union_le_iffₓ'. -/
@[simp]
theorem union_le_iff : s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u :=
  sup_le_iff
#align multiset.union_le_iff Multiset.union_le_iff

#print Multiset.union_comm /-
theorem union_comm (s t : Multiset α) : s ∪ t = t ∪ s :=
  sup_comm
#align multiset.union_comm Multiset.union_comm
-/

#print Multiset.inter_comm /-
theorem inter_comm (s t : Multiset α) : s ∩ t = t ∩ s :=
  inf_comm
#align multiset.inter_comm Multiset.inter_comm
-/

/- warning: multiset.eq_union_right -> Multiset.eq_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (Eq.{succ u1} (Multiset.{u1} α) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (Eq.{succ u1} (Multiset.{u1} α) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) t)
Case conversion may be inaccurate. Consider using '#align multiset.eq_union_right Multiset.eq_union_rightₓ'. -/
theorem eq_union_right (h : s ≤ t) : s ∪ t = t := by rw [union_comm, eq_union_left h]
#align multiset.eq_union_right Multiset.eq_union_right

/- warning: multiset.union_le_union_left -> Multiset.union_le_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (forall (u : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) u s) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) u t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (forall (u : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) u s) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) u t))
Case conversion may be inaccurate. Consider using '#align multiset.union_le_union_left Multiset.union_le_union_leftₓ'. -/
theorem union_le_union_left (h : s ≤ t) (u) : u ∪ s ≤ u ∪ t :=
  sup_le_sup_left h _
#align multiset.union_le_union_left Multiset.union_le_union_left

/- warning: multiset.union_le_add -> Multiset.union_le_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t)
Case conversion may be inaccurate. Consider using '#align multiset.union_le_add Multiset.union_le_addₓ'. -/
theorem union_le_add (s t : Multiset α) : s ∪ t ≤ s + t :=
  union_le (le_add_right _ _) (le_add_left _ _)
#align multiset.union_le_add Multiset.union_le_add

#print Multiset.union_add_distrib /-
theorem union_add_distrib (s t u : Multiset α) : s ∪ t + u = s + u ∪ (t + u) := by
  simpa [(· ∪ ·), union, eq_comm, add_assoc] using
    show s + u - (t + u) = s - t by rw [add_comm t, tsub_add_eq_tsub_tsub, add_tsub_cancel_right]
#align multiset.union_add_distrib Multiset.union_add_distrib
-/

#print Multiset.add_union_distrib /-
theorem add_union_distrib (s t u : Multiset α) : s + (t ∪ u) = s + t ∪ (s + u) := by
  rw [add_comm, union_add_distrib, add_comm s, add_comm s]
#align multiset.add_union_distrib Multiset.add_union_distrib
-/

#print Multiset.cons_union_distrib /-
theorem cons_union_distrib (a : α) (s t : Multiset α) : a ::ₘ (s ∪ t) = a ::ₘ s ∪ a ::ₘ t := by
  simpa using add_union_distrib (a ::ₘ 0) s t
#align multiset.cons_union_distrib Multiset.cons_union_distrib
-/

#print Multiset.inter_add_distrib /-
theorem inter_add_distrib (s t u : Multiset α) : s ∩ t + u = (s + u) ∩ (t + u) :=
  by
  by_contra h
  cases'
    lt_iff_cons_le.1
      (lt_of_le_of_ne
        (le_inter (add_le_add_right (inter_le_left s t) u)
          (add_le_add_right (inter_le_right s t) u))
        h) with
    a hl
  rw [← cons_add] at hl
  exact
    not_le_of_lt (lt_cons_self (s ∩ t) a)
      (le_inter (le_of_add_le_add_right (le_trans hl (inter_le_left _ _)))
        (le_of_add_le_add_right (le_trans hl (inter_le_right _ _))))
#align multiset.inter_add_distrib Multiset.inter_add_distrib
-/

#print Multiset.add_inter_distrib /-
theorem add_inter_distrib (s t u : Multiset α) : s + t ∩ u = (s + t) ∩ (s + u) := by
  rw [add_comm, inter_add_distrib, add_comm s, add_comm s]
#align multiset.add_inter_distrib Multiset.add_inter_distrib
-/

#print Multiset.cons_inter_distrib /-
theorem cons_inter_distrib (a : α) (s t : Multiset α) : a ::ₘ s ∩ t = (a ::ₘ s) ∩ (a ::ₘ t) := by
  simp
#align multiset.cons_inter_distrib Multiset.cons_inter_distrib
-/

#print Multiset.union_add_inter /-
theorem union_add_inter (s t : Multiset α) : s ∪ t + s ∩ t = s + t :=
  by
  apply le_antisymm
  · rw [union_add_distrib]
    refine' union_le (add_le_add_left (inter_le_right _ _) _) _
    rw [add_comm]
    exact add_le_add_right (inter_le_left _ _) _
  · rw [add_comm, add_inter_distrib]
    refine' le_inter (add_le_add_right (le_union_right _ _) _) _
    rw [add_comm]
    exact add_le_add_right (le_union_left _ _) _
#align multiset.union_add_inter Multiset.union_add_inter
-/

#print Multiset.sub_add_inter /-
theorem sub_add_inter (s t : Multiset α) : s - t + s ∩ t = s :=
  by
  rw [inter_comm]
  revert s; refine' Multiset.induction_on t (by simp) fun a t IH s => _
  by_cases a ∈ s
  · rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h]
  · rw [cons_inter_of_neg _ h, sub_cons, erase_of_not_mem h, IH]
#align multiset.sub_add_inter Multiset.sub_add_inter
-/

#print Multiset.sub_inter /-
theorem sub_inter (s t : Multiset α) : s - s ∩ t = s - t :=
  add_right_cancel <| by rw [sub_add_inter s t, tsub_add_cancel_of_le (inter_le_left s t)]
#align multiset.sub_inter Multiset.sub_inter
-/

end

/-! ### `multiset.filter` -/


section

variable (p : α → Prop) [DecidablePred p]

#print Multiset.filter /-
/-- `filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (filter p l : Multiset α)) fun l₁ l₂ h => Quot.sound <| h.filterₓ p
#align multiset.filter Multiset.filter
-/

/- warning: multiset.coe_filter -> Multiset.coe_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) (Multiset.ofList.{u1} α l)) (Multiset.ofList.{u1} α (List.filter.{u1} α (fun (a : α) => Decidable.decide (p a) ((fun (a : α) => _inst_1 a) a)) l))
Case conversion may be inaccurate. Consider using '#align multiset.coe_filter Multiset.coe_filterₓ'. -/
@[simp]
theorem coe_filter (l : List α) : filter p ↑l = l.filterₓ p :=
  rfl
#align multiset.coe_filter Multiset.coe_filter

#print Multiset.filter_zero /-
@[simp]
theorem filter_zero : filter p 0 = 0 :=
  rfl
#align multiset.filter_zero Multiset.filter_zero
-/

#print Multiset.filter_congr /-
theorem filter_congr {p q : α → Prop} [DecidablePred p] [DecidablePred q] {s : Multiset α} :
    (∀ x ∈ s, p x ↔ q x) → filter p s = filter q s :=
  Quot.inductionOn s fun l h => congr_arg coe <| filter_congr' h
#align multiset.filter_congr Multiset.filter_congr
-/

#print Multiset.filter_add /-
@[simp]
theorem filter_add (s t : Multiset α) : filter p (s + t) = filter p s + filter p t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => congr_arg coe <| filter_append _ _
#align multiset.filter_add Multiset.filter_add
-/

/- warning: multiset.filter_le -> Multiset.filter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) s
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) s
Case conversion may be inaccurate. Consider using '#align multiset.filter_le Multiset.filter_leₓ'. -/
@[simp]
theorem filter_le (s : Multiset α) : filter p s ≤ s :=
  Quot.inductionOn s fun l => (filter_sublist _).Subperm
#align multiset.filter_le Multiset.filter_le

#print Multiset.filter_subset /-
@[simp]
theorem filter_subset (s : Multiset α) : filter p s ⊆ s :=
  subset_of_le <| filter_le _ _
#align multiset.filter_subset Multiset.filter_subset
-/

/- warning: multiset.filter_le_filter -> Multiset.filter_le_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) t))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) t))
Case conversion may be inaccurate. Consider using '#align multiset.filter_le_filter Multiset.filter_le_filterₓ'. -/
theorem filter_le_filter {s t} (h : s ≤ t) : filter p s ≤ filter p t :=
  leInductionOn h fun l₁ l₂ h => (h.filterₓ p).Subperm
#align multiset.filter_le_filter Multiset.filter_le_filter

/- warning: multiset.monotone_filter_left -> Multiset.monotone_filter_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Monotone.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Monotone.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a))
Case conversion may be inaccurate. Consider using '#align multiset.monotone_filter_left Multiset.monotone_filter_leftₓ'. -/
theorem monotone_filter_left : Monotone (filter p) := fun s t => filter_le_filter p
#align multiset.monotone_filter_left Multiset.monotone_filter_left

/- warning: multiset.monotone_filter_right -> Multiset.monotone_filter_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α) {{p : α -> Prop}} {{q : α -> Prop}} [_inst_2 : DecidablePred.{succ u1} α p] [_inst_3 : DecidablePred.{succ u1} α q], (LE.le.{u1} (α -> Prop) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.le)) p q) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.filter.{u1} α p (fun (a : α) => _inst_2 a) s) (Multiset.filter.{u1} α q (fun (a : α) => _inst_3 a) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α) {{p : α -> Prop}} {{q : α -> Prop}} [_inst_2 : DecidablePred.{succ u1} α p] [_inst_3 : DecidablePred.{succ u1} α q], (forall (b : α), (p b) -> (q b)) -> (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.filter.{u1} α p (fun (a : α) => _inst_2 a) s) (Multiset.filter.{u1} α q (fun (a : α) => _inst_3 a) s))
Case conversion may be inaccurate. Consider using '#align multiset.monotone_filter_right Multiset.monotone_filter_rightₓ'. -/
theorem monotone_filter_right (s : Multiset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : p ≤ q) : s.filterₓ p ≤ s.filterₓ q :=
  Quotient.inductionOn s fun l => (l.monotone_filter_right h).Subperm
#align multiset.monotone_filter_right Multiset.monotone_filter_right

variable {p}

#print Multiset.filter_cons_of_pos /-
@[simp]
theorem filter_cons_of_pos {a : α} (s) : p a → filter p (a ::ₘ s) = a ::ₘ filter p s :=
  Quot.inductionOn s fun l h => congr_arg coe <| filter_cons_of_pos l h
#align multiset.filter_cons_of_pos Multiset.filter_cons_of_pos
-/

#print Multiset.filter_cons_of_neg /-
@[simp]
theorem filter_cons_of_neg {a : α} (s) : ¬p a → filter p (a ::ₘ s) = filter p s :=
  Quot.inductionOn s fun l h => @congr_arg _ _ _ _ coe <| filter_cons_of_neg l h
#align multiset.filter_cons_of_neg Multiset.filter_cons_of_neg
-/

#print Multiset.mem_filter /-
@[simp]
theorem mem_filter {a : α} {s} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
  Quot.inductionOn s fun l => mem_filter
#align multiset.mem_filter Multiset.mem_filter
-/

#print Multiset.of_mem_filter /-
theorem of_mem_filter {a : α} {s} (h : a ∈ filter p s) : p a :=
  (mem_filter.1 h).2
#align multiset.of_mem_filter Multiset.of_mem_filter
-/

#print Multiset.mem_of_mem_filter /-
theorem mem_of_mem_filter {a : α} {s} (h : a ∈ filter p s) : a ∈ s :=
  (mem_filter.1 h).1
#align multiset.mem_of_mem_filter Multiset.mem_of_mem_filter
-/

#print Multiset.mem_filter_of_mem /-
theorem mem_filter_of_mem {a : α} {l} (m : a ∈ l) (h : p a) : a ∈ filter p l :=
  mem_filter.2 ⟨m, h⟩
#align multiset.mem_filter_of_mem Multiset.mem_filter_of_mem
-/

#print Multiset.filter_eq_self /-
theorem filter_eq_self {s} : filter p s = s ↔ ∀ a ∈ s, p a :=
  Quot.inductionOn s fun l =>
    Iff.trans ⟨fun h => (filter_sublist _).eq_of_length (@congr_arg _ _ _ _ card h), congr_arg coe⟩
      filter_eq_self
#align multiset.filter_eq_self Multiset.filter_eq_self
-/

#print Multiset.filter_eq_nil /-
theorem filter_eq_nil {s} : filter p s = 0 ↔ ∀ a ∈ s, ¬p a :=
  Quot.inductionOn s fun l =>
    Iff.trans ⟨fun h => eq_nil_of_length_eq_zero (@congr_arg _ _ _ _ card h), congr_arg coe⟩
      filter_eq_nil
#align multiset.filter_eq_nil Multiset.filter_eq_nil
-/

/- warning: multiset.le_filter -> Multiset.le_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) t)) (And (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) t)) (And (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (p a)))
Case conversion may be inaccurate. Consider using '#align multiset.le_filter Multiset.le_filterₓ'. -/
theorem le_filter {s t} : s ≤ filter p t ↔ s ≤ t ∧ ∀ a ∈ s, p a :=
  ⟨fun h => ⟨le_trans h (filter_le _ _), fun a m => of_mem_filter (mem_of_le h m)⟩, fun ⟨h, al⟩ =>
    filter_eq_self.2 al ▸ filter_le_filter p h⟩
#align multiset.le_filter Multiset.le_filter

#print Multiset.filter_cons /-
theorem filter_cons {a : α} (s : Multiset α) :
    filter p (a ::ₘ s) = (if p a then {a} else 0) + filter p s :=
  by
  split_ifs with h
  · rw [filter_cons_of_pos _ h, singleton_add]
  · rw [filter_cons_of_neg _ h, zero_add]
#align multiset.filter_cons Multiset.filter_cons
-/

#print Multiset.filter_singleton /-
theorem filter_singleton {a : α} (p : α → Prop) [DecidablePred p] :
    filter p {a} = if p a then {a} else ∅ := by
  simp only [singleton, filter_cons, filter_zero, add_zero, empty_eq_zero]
#align multiset.filter_singleton Multiset.filter_singleton
-/

/- warning: multiset.filter_nsmul -> Multiset.filter_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α) (n : Nat), Eq.{succ u1} (Multiset.{u1} α) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α) (n : Nat), Eq.{succ u1} (Multiset.{u1} α) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s))
Case conversion may be inaccurate. Consider using '#align multiset.filter_nsmul Multiset.filter_nsmulₓ'. -/
theorem filter_nsmul (s : Multiset α) (n : ℕ) : filter p (n • s) = n • filter p s :=
  by
  refine' s.induction_on _ _
  · simp only [filter_zero, nsmul_zero]
  · intro a ha ih
    rw [nsmul_cons, filter_add, ih, filter_cons, nsmul_add]
    congr
    split_ifs with hp <;>
      · simp only [filter_eq_self, nsmul_zero, filter_eq_nil]
        intro b hb
        rwa [mem_singleton.mp (mem_of_mem_nsmul hb)]
#align multiset.filter_nsmul Multiset.filter_nsmul

variable (p)

#print Multiset.filter_sub /-
@[simp]
theorem filter_sub [DecidableEq α] (s t : Multiset α) :
    filter p (s - t) = filter p s - filter p t :=
  by
  revert s; refine' Multiset.induction_on t (by simp) fun a t IH s => _
  rw [sub_cons, IH]
  by_cases p a
  · rw [filter_cons_of_pos _ h, sub_cons]
    congr
    by_cases m : a ∈ s
    ·
      rw [← cons_inj_right a, ← filter_cons_of_pos _ h, cons_erase (mem_filter_of_mem m h),
        cons_erase m]
    · rw [erase_of_not_mem m, erase_of_not_mem (mt mem_of_mem_filter m)]
  · rw [filter_cons_of_neg _ h]
    by_cases m : a ∈ s
    ·
      rw [(by rw [filter_cons_of_neg _ h] : Filter p (erase s a) = Filter p (a ::ₘ erase s a)),
        cons_erase m]
    · rw [erase_of_not_mem m]
#align multiset.filter_sub Multiset.filter_sub
-/

#print Multiset.filter_union /-
@[simp]
theorem filter_union [DecidableEq α] (s t : Multiset α) :
    filter p (s ∪ t) = filter p s ∪ filter p t := by simp [(· ∪ ·), union]
#align multiset.filter_union Multiset.filter_union
-/

#print Multiset.filter_inter /-
@[simp]
theorem filter_inter [DecidableEq α] (s t : Multiset α) :
    filter p (s ∩ t) = filter p s ∩ filter p t :=
  le_antisymm
      (le_inter (filter_le_filter _ <| inter_le_left _ _)
        (filter_le_filter _ <| inter_le_right _ _)) <|
    le_filter.2
      ⟨inf_le_inf (filter_le _ _) (filter_le _ _), fun a h =>
        of_mem_filter (mem_of_le (inter_le_left _ _) h)⟩
#align multiset.filter_inter Multiset.filter_inter
-/

#print Multiset.filter_filter /-
@[simp]
theorem filter_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter (fun a => p a ∧ q a) s :=
  Quot.inductionOn s fun l => congr_arg coe <| filter_filter p q l
#align multiset.filter_filter Multiset.filter_filter
-/

#print Multiset.filter_add_filter /-
theorem filter_add_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p s + filter q s = filter (fun a => p a ∨ q a) s + filter (fun a => p a ∧ q a) s :=
  Multiset.induction_on s rfl fun a s IH => by by_cases p a <;> by_cases q a <;> simp [*]
#align multiset.filter_add_filter Multiset.filter_add_filter
-/

#print Multiset.filter_add_not /-
theorem filter_add_not (s : Multiset α) : filter p s + filter (fun a => ¬p a) s = s := by
  rw [filter_add_filter, filter_eq_self.2, filter_eq_nil.2] <;> simp [Decidable.em]
#align multiset.filter_add_not Multiset.filter_add_not
-/

#print Multiset.map_filter /-
theorem map_filter (f : β → α) (s : Multiset β) : filter p (map f s) = map f (filter (p ∘ f) s) :=
  Quot.inductionOn s fun l => by simp [map_filter]
#align multiset.map_filter Multiset.map_filter
-/

/-! ### Simultaneously filter and map elements of a multiset -/


#print Multiset.filterMap /-
/-- `filter_map f s` is a combination filter/map operation on `s`.
  The function `f : α → option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset. -/
def filterMap (f : α → Option β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l => (filterMap f l : Multiset β)) fun l₁ l₂ h => Quot.sound <| h.filterMap f
#align multiset.filter_map Multiset.filterMap
-/

#print Multiset.coe_filterMap /-
@[simp]
theorem coe_filterMap (f : α → Option β) (l : List α) : filterMap f l = l.filterMap f :=
  rfl
#align multiset.coe_filter_map Multiset.coe_filterMap
-/

#print Multiset.filterMap_zero /-
@[simp]
theorem filterMap_zero (f : α → Option β) : filterMap f 0 = 0 :=
  rfl
#align multiset.filter_map_zero Multiset.filterMap_zero
-/

#print Multiset.filterMap_cons_none /-
@[simp]
theorem filterMap_cons_none {f : α → Option β} (a : α) (s : Multiset α) (h : f a = none) :
    filterMap f (a ::ₘ s) = filterMap f s :=
  Quot.inductionOn s fun l => @congr_arg _ _ _ _ coe <| filterMap_cons_none a l h
#align multiset.filter_map_cons_none Multiset.filterMap_cons_none
-/

#print Multiset.filterMap_cons_some /-
@[simp]
theorem filterMap_cons_some (f : α → Option β) (a : α) (s : Multiset α) {b : β} (h : f a = some b) :
    filterMap f (a ::ₘ s) = b ::ₘ filterMap f s :=
  Quot.inductionOn s fun l => @congr_arg _ _ _ _ coe <| filterMap_cons_some f a l h
#align multiset.filter_map_cons_some Multiset.filterMap_cons_some
-/

/- warning: multiset.filter_map_eq_map -> Multiset.filterMap_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{max (succ u1) (succ u2)} ((Multiset.{u1} α) -> (Multiset.{u2} β)) (Multiset.filterMap.{u1, u2} α β (Function.comp.{succ u1, succ u2, succ u2} α β (Option.{u2} β) (Option.some.{u2} β) f)) (Multiset.map.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{max (succ u2) (succ u1)} ((Multiset.{u2} α) -> (Multiset.{u1} β)) (Multiset.filterMap.{u2, u1} α β (Function.comp.{succ u2, succ u1, succ u1} α β (Option.{u1} β) (Option.some.{u1} β) f)) (Multiset.map.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align multiset.filter_map_eq_map Multiset.filterMap_eq_mapₓ'. -/
theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f :=
  funext fun s =>
    Quot.inductionOn s fun l => @congr_arg _ _ _ _ coe <| congr_fun (filterMap_eq_map f) l
#align multiset.filter_map_eq_map Multiset.filterMap_eq_map

#print Multiset.filterMap_eq_filter /-
theorem filterMap_eq_filter : filterMap (Option.guard p) = filter p :=
  funext fun s =>
    Quot.inductionOn s fun l => @congr_arg _ _ _ _ coe <| congr_fun (filterMap_eq_filter p) l
#align multiset.filter_map_eq_filter Multiset.filterMap_eq_filter
-/

/- warning: multiset.filter_map_filter_map -> Multiset.filterMap_filterMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> (Option.{u2} β)) (g : β -> (Option.{u3} γ)) (s : Multiset.{u1} α), Eq.{succ u3} (Multiset.{u3} γ) (Multiset.filterMap.{u2, u3} β γ g (Multiset.filterMap.{u1, u2} α β f s)) (Multiset.filterMap.{u1, u3} α γ (fun (x : α) => Option.bind.{u2, u3} β γ (f x) g) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : α -> (Option.{u3} β)) (g : β -> (Option.{u2} γ)) (s : Multiset.{u1} α), Eq.{succ u2} (Multiset.{u2} γ) (Multiset.filterMap.{u3, u2} β γ g (Multiset.filterMap.{u1, u3} α β f s)) (Multiset.filterMap.{u1, u2} α γ (fun (x : α) => Option.bind.{u3, u2} β γ (f x) g) s)
Case conversion may be inaccurate. Consider using '#align multiset.filter_map_filter_map Multiset.filterMap_filterMapₓ'. -/
theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (filterMap f s) = filterMap (fun x => (f x).bind g) s :=
  Quot.inductionOn s fun l => congr_arg coe <| filterMap_filterMap f g l
#align multiset.filter_map_filter_map Multiset.filterMap_filterMap

/- warning: multiset.map_filter_map -> Multiset.map_filterMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> (Option.{u2} β)) (g : β -> γ) (s : Multiset.{u1} α), Eq.{succ u3} (Multiset.{u3} γ) (Multiset.map.{u2, u3} β γ g (Multiset.filterMap.{u1, u2} α β f s)) (Multiset.filterMap.{u1, u3} α γ (fun (x : α) => Option.map.{u2, u3} β γ g (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} (f : α -> (Option.{u3} β)) (g : β -> γ) (s : Multiset.{u2} α), Eq.{succ u1} (Multiset.{u1} γ) (Multiset.map.{u3, u1} β γ g (Multiset.filterMap.{u2, u3} α β f s)) (Multiset.filterMap.{u2, u1} α γ (fun (x : α) => Option.map.{u3, u1} β γ g (f x)) s)
Case conversion may be inaccurate. Consider using '#align multiset.map_filter_map Multiset.map_filterMapₓ'. -/
theorem map_filterMap (f : α → Option β) (g : β → γ) (s : Multiset α) :
    map g (filterMap f s) = filterMap (fun x => (f x).map g) s :=
  Quot.inductionOn s fun l => congr_arg coe <| map_filterMap f g l
#align multiset.map_filter_map Multiset.map_filterMap

/- warning: multiset.filter_map_map -> Multiset.filterMap_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : β -> (Option.{u3} γ)) (s : Multiset.{u1} α), Eq.{succ u3} (Multiset.{u3} γ) (Multiset.filterMap.{u2, u3} β γ g (Multiset.map.{u1, u2} α β f s)) (Multiset.filterMap.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β (Option.{u3} γ) g f) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (f : α -> β) (g : β -> (Option.{u3} γ)) (s : Multiset.{u2} α), Eq.{succ u3} (Multiset.{u3} γ) (Multiset.filterMap.{u1, u3} β γ g (Multiset.map.{u2, u1} α β f s)) (Multiset.filterMap.{u2, u3} α γ (Function.comp.{succ u2, succ u1, succ u3} α β (Option.{u3} γ) g f) s)
Case conversion may be inaccurate. Consider using '#align multiset.filter_map_map Multiset.filterMap_mapₓ'. -/
theorem filterMap_map (f : α → β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (map f s) = filterMap (g ∘ f) s :=
  Quot.inductionOn s fun l => congr_arg coe <| filterMap_map f g l
#align multiset.filter_map_map Multiset.filterMap_map

#print Multiset.filter_filterMap /-
theorem filter_filterMap (f : α → Option β) (p : β → Prop) [DecidablePred p] (s : Multiset α) :
    filter p (filterMap f s) = filterMap (fun x => (f x).filterₓ p) s :=
  Quot.inductionOn s fun l => congr_arg coe <| filter_filterMap f p l
#align multiset.filter_filter_map Multiset.filter_filterMap
-/

#print Multiset.filterMap_filter /-
theorem filterMap_filter (f : α → Option β) (s : Multiset α) :
    filterMap f (filter p s) = filterMap (fun x => if p x then f x else none) s :=
  Quot.inductionOn s fun l => congr_arg coe <| filterMap_filter p f l
#align multiset.filter_map_filter Multiset.filterMap_filter
-/

#print Multiset.filterMap_some /-
@[simp]
theorem filterMap_some (s : Multiset α) : filterMap some s = s :=
  Quot.inductionOn s fun l => congr_arg coe <| filterMap_some l
#align multiset.filter_map_some Multiset.filterMap_some
-/

#print Multiset.mem_filterMap /-
@[simp]
theorem mem_filterMap (f : α → Option β) (s : Multiset α) {b : β} :
    b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b :=
  Quot.inductionOn s fun l => mem_filterMap f l
#align multiset.mem_filter_map Multiset.mem_filterMap
-/

#print Multiset.map_filterMap_of_inv /-
theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (s : Multiset α) : map g (filterMap f s) = s :=
  Quot.inductionOn s fun l => congr_arg coe <| map_filterMap_of_inv f g H l
#align multiset.map_filter_map_of_inv Multiset.map_filterMap_of_inv
-/

/- warning: multiset.filter_map_le_filter_map -> Multiset.filterMap_le_filterMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> (Option.{u2} β)) {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{u2} (Multiset.{u2} β) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))) (Multiset.filterMap.{u1, u2} α β f s) (Multiset.filterMap.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> (Option.{u2} β)) {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{u2} (Multiset.{u2} β) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.instPartialOrderMultiset.{u2} β))) (Multiset.filterMap.{u1, u2} α β f s) (Multiset.filterMap.{u1, u2} α β f t))
Case conversion may be inaccurate. Consider using '#align multiset.filter_map_le_filter_map Multiset.filterMap_le_filterMapₓ'. -/
theorem filterMap_le_filterMap (f : α → Option β) {s t : Multiset α} (h : s ≤ t) :
    filterMap f s ≤ filterMap f t :=
  leInductionOn h fun l₁ l₂ h => (h.filterMap _).Subperm
#align multiset.filter_map_le_filter_map Multiset.filterMap_le_filterMap

/-! ### countp -/


#print Multiset.countp /-
/-- `countp p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countp (s : Multiset α) : ℕ :=
  Quot.liftOn s (countp p) fun l₁ l₂ => Perm.countp_eq p
#align multiset.countp Multiset.countp
-/

#print Multiset.coe_countp /-
@[simp]
theorem coe_countp (l : List α) : countp p l = l.countp p :=
  rfl
#align multiset.coe_countp Multiset.coe_countp
-/

#print Multiset.countp_zero /-
@[simp]
theorem countp_zero : countp p 0 = 0 :=
  rfl
#align multiset.countp_zero Multiset.countp_zero
-/

variable {p}

#print Multiset.countp_cons_of_pos /-
@[simp]
theorem countp_cons_of_pos {a : α} (s) : p a → countp p (a ::ₘ s) = countp p s + 1 :=
  Quot.inductionOn s <| countp_cons_of_pos p
#align multiset.countp_cons_of_pos Multiset.countp_cons_of_pos
-/

#print Multiset.countp_cons_of_neg /-
@[simp]
theorem countp_cons_of_neg {a : α} (s) : ¬p a → countp p (a ::ₘ s) = countp p s :=
  Quot.inductionOn s <| countp_cons_of_neg p
#align multiset.countp_cons_of_neg Multiset.countp_cons_of_neg
-/

variable (p)

#print Multiset.countp_cons /-
theorem countp_cons (b : α) (s) : countp p (b ::ₘ s) = countp p s + if p b then 1 else 0 :=
  Quot.inductionOn s <| by simp [List.countp_cons]
#align multiset.countp_cons Multiset.countp_cons
-/

/- warning: multiset.countp_eq_card_filter -> Multiset.countp_eq_card_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α), Eq.{1} Nat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α), Eq.{1} Nat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s))
Case conversion may be inaccurate. Consider using '#align multiset.countp_eq_card_filter Multiset.countp_eq_card_filterₓ'. -/
theorem countp_eq_card_filter (s) : countp p s = card (filter p s) :=
  Quot.inductionOn s fun l => l.countp_eq_length_filter p
#align multiset.countp_eq_card_filter Multiset.countp_eq_card_filter

/- warning: multiset.countp_le_card -> Multiset.countp_le_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α), LE.le.{0} Nat Nat.hasLe (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α), LE.le.{0} Nat instLENat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)
Case conversion may be inaccurate. Consider using '#align multiset.countp_le_card Multiset.countp_le_cardₓ'. -/
theorem countp_le_card (s) : countp p s ≤ card s :=
  Quot.inductionOn s fun l => countp_le_length p
#align multiset.countp_le_card Multiset.countp_le_card

#print Multiset.countp_add /-
@[simp]
theorem countp_add (s t) : countp p (s + t) = countp p s + countp p t := by
  simp [countp_eq_card_filter]
#align multiset.countp_add Multiset.countp_add
-/

/- warning: multiset.countp_nsmul -> Multiset.countp_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α) (n : Nat), Eq.{1} Nat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α) (n : Nat), Eq.{1} Nat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s))
Case conversion may be inaccurate. Consider using '#align multiset.countp_nsmul Multiset.countp_nsmulₓ'. -/
@[simp]
theorem countp_nsmul (s) (n : ℕ) : countp p (n • s) = n * countp p s := by
  induction n <;> simp [*, succ_nsmul', succ_mul, zero_nsmul]
#align multiset.countp_nsmul Multiset.countp_nsmul

/- warning: multiset.card_eq_countp_add_countp -> Multiset.card_eq_countp_add_countp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (Multiset.countp.{u1} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (_inst_1 a)) s))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Multiset.{u1} α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (Multiset.countp.{u1} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (_inst_1 a)) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_eq_countp_add_countp Multiset.card_eq_countp_add_countpₓ'. -/
theorem card_eq_countp_add_countp (s) : card s = countp p s + countp (fun x => ¬p x) s :=
  Quot.inductionOn s fun l => by simp [l.length_eq_countp_add_countp p]
#align multiset.card_eq_countp_add_countp Multiset.card_eq_countp_add_countp

/- warning: multiset.countp_add_monoid_hom -> Multiset.countpAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)
Case conversion may be inaccurate. Consider using '#align multiset.countp_add_monoid_hom Multiset.countpAddMonoidHomₓ'. -/
/-- `countp p`, the number of elements of a multiset satisfying `p`, promoted to an
`add_monoid_hom`. -/
def countpAddMonoidHom : Multiset α →+ ℕ
    where
  toFun := countp p
  map_zero' := countp_zero _
  map_add' := countp_add _
#align multiset.countp_add_monoid_hom Multiset.countpAddMonoidHom

/- warning: multiset.coe_countp_add_monoid_hom -> Multiset.coe_countpAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Eq.{succ u1} ((fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (Multiset.countpAddMonoidHom.{u1} α p (fun (a : α) => _inst_1 a))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.countpAddMonoidHom.{u1} α p (fun (a : α) => _inst_1 a))) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Eq.{succ u1} (forall (a : Multiset.{u1} α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) a) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.countpAddMonoidHom.{u1} α p (fun (a : α) => _inst_1 a))) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a))
Case conversion may be inaccurate. Consider using '#align multiset.coe_countp_add_monoid_hom Multiset.coe_countpAddMonoidHomₓ'. -/
@[simp]
theorem coe_countpAddMonoidHom : (countpAddMonoidHom p : Multiset α → ℕ) = countp p :=
  rfl
#align multiset.coe_countp_add_monoid_hom Multiset.coe_countpAddMonoidHom

/- warning: multiset.countp_sub -> Multiset.countp_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t s) -> (Eq.{1} Nat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.hasSub.{u1} α (fun (a : α) (b : α) => _inst_2 a b))) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) t)))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t s) -> (Eq.{1} Nat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => _inst_2 a b))) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) t)))
Case conversion may be inaccurate. Consider using '#align multiset.countp_sub Multiset.countp_subₓ'. -/
@[simp]
theorem countp_sub [DecidableEq α] {s t : Multiset α} (h : t ≤ s) :
    countp p (s - t) = countp p s - countp p t := by
  simp [countp_eq_card_filter, h, filter_le_filter]
#align multiset.countp_sub Multiset.countp_sub

/- warning: multiset.countp_le_of_le -> Multiset.countp_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{0} Nat Nat.hasLe (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) t))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{0} Nat instLENat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) t))
Case conversion may be inaccurate. Consider using '#align multiset.countp_le_of_le Multiset.countp_le_of_leₓ'. -/
theorem countp_le_of_le {s t} (h : s ≤ t) : countp p s ≤ countp p t := by
  simpa [countp_eq_card_filter] using card_le_of_le (filter_le_filter p h)
#align multiset.countp_le_of_le Multiset.countp_le_of_le

#print Multiset.countp_filter /-
@[simp]
theorem countp_filter (q) [DecidablePred q] (s : Multiset α) :
    countp p (filter q s) = countp (fun a => p a ∧ q a) s := by simp [countp_eq_card_filter]
#align multiset.countp_filter Multiset.countp_filter
-/

#print Multiset.countp_eq_countp_filter_add /-
theorem countp_eq_countp_filter_add (s) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    countp p s = (filter q s).countp p + (filter (fun a => ¬q a) s).countp p :=
  Quot.inductionOn s fun l => l.countp_eq_countp_filter_add _ _
#align multiset.countp_eq_countp_filter_add Multiset.countp_eq_countp_filter_add
-/

/- warning: multiset.countp_true -> Multiset.countp_True is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Eq.{1} Nat (Multiset.countp.{u1} α (fun (_x : α) => True) (fun (a : α) => Decidable.true) s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α}, Eq.{1} Nat (Multiset.countp.{u1} α (fun (_x : α) => True) (fun (a : α) => instDecidableTrue) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)
Case conversion may be inaccurate. Consider using '#align multiset.countp_true Multiset.countp_Trueₓ'. -/
@[simp]
theorem countp_True {s : Multiset α} : countp (fun _ => True) s = card s :=
  Quot.inductionOn s fun l => List.countp_true
#align multiset.countp_true Multiset.countp_True

#print Multiset.countp_False /-
@[simp]
theorem countp_False {s : Multiset α} : countp (fun _ => False) s = 0 :=
  Quot.inductionOn s fun l => List.countp_false
#align multiset.countp_false Multiset.countp_False
-/

/- warning: multiset.countp_map -> Multiset.countp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Multiset.{u1} α) (p : β -> Prop) [_inst_2 : DecidablePred.{succ u2} β p], Eq.{1} Nat (Multiset.countp.{u2} β p (fun (a : β) => _inst_2 a) (Multiset.map.{u1, u2} α β f s)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.filter.{u1} α (fun (a : α) => p (f a)) (fun (a : α) => _inst_2 (f a)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Multiset.{u2} α) (p : β -> Prop) [_inst_2 : DecidablePred.{succ u1} β p], Eq.{1} Nat (Multiset.countp.{u1} β p (fun (a : β) => _inst_2 a) (Multiset.map.{u2, u1} α β f s)) (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) (Multiset.filter.{u2} α (fun (a : α) => p (f a)) (fun (a : α) => _inst_2 (f a)) s))
Case conversion may be inaccurate. Consider using '#align multiset.countp_map Multiset.countp_mapₓ'. -/
theorem countp_map (f : α → β) (s : Multiset α) (p : β → Prop) [DecidablePred p] :
    countp p (map f s) = (s.filterₓ fun a => p (f a)).card :=
  by
  refine' Multiset.induction_on s _ fun a t IH => _
  · rw [map_zero, countp_zero, filter_zero, card_zero]
  ·
    rw [map_cons, countp_cons, IH, filter_cons, card_add, apply_ite card, card_zero, card_singleton,
      add_comm]
#align multiset.countp_map Multiset.countp_map

variable {p}

/- warning: multiset.countp_pos -> Multiset.countp_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α}, Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) => p a)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α}, Iff (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) (p a)))
Case conversion may be inaccurate. Consider using '#align multiset.countp_pos Multiset.countp_posₓ'. -/
theorem countp_pos {s} : 0 < countp p s ↔ ∃ a ∈ s, p a :=
  Quot.inductionOn s fun l => List.countp_pos p
#align multiset.countp_pos Multiset.countp_pos

#print Multiset.countp_eq_zero /-
theorem countp_eq_zero {s} : countp p s = 0 ↔ ∀ a ∈ s, ¬p a :=
  Quot.inductionOn s fun l => List.countp_eq_zero p
#align multiset.countp_eq_zero Multiset.countp_eq_zero
-/

/- warning: multiset.countp_eq_card -> Multiset.countp_eq_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α}, Iff (Eq.{1} Nat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)) (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Multiset.{u1} α}, Iff (Eq.{1} Nat (Multiset.countp.{u1} α p (fun (a : α) => _inst_1 a) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)) (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (p a))
Case conversion may be inaccurate. Consider using '#align multiset.countp_eq_card Multiset.countp_eq_cardₓ'. -/
theorem countp_eq_card {s} : countp p s = card s ↔ ∀ a ∈ s, p a :=
  Quot.inductionOn s fun l => List.countp_eq_length p
#align multiset.countp_eq_card Multiset.countp_eq_card

#print Multiset.countp_pos_of_mem /-
theorem countp_pos_of_mem {s a} (h : a ∈ s) (pa : p a) : 0 < countp p s :=
  countp_pos.2 ⟨_, h, pa⟩
#align multiset.countp_pos_of_mem Multiset.countp_pos_of_mem
-/

#print Multiset.countp_congr /-
theorem countp_congr {s s' : Multiset α} (hs : s = s') {p p' : α → Prop} [DecidablePred p]
    [DecidablePred p'] (hp : ∀ x ∈ s, p x = p' x) : s.countp p = s'.countp p' :=
  Quot.induction_on₂ s s'
    (fun l l' hs hp => by
      simp only [quot_mk_to_coe'', coe_eq_coe] at hs
      exact hs.countp_congr hp)
    hs hp
#align multiset.countp_congr Multiset.countp_congr
-/

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α]

#print Multiset.count /-
/-- `count a s` is the multiplicity of `a` in `s`. -/
def count (a : α) : Multiset α → ℕ :=
  countp (Eq a)
#align multiset.count Multiset.count
-/

#print Multiset.coe_count /-
@[simp]
theorem coe_count (a : α) (l : List α) : count a ↑l = l.count a :=
  coe_countp _ _
#align multiset.coe_count Multiset.coe_count
-/

#print Multiset.count_zero /-
@[simp]
theorem count_zero (a : α) : count a 0 = 0 :=
  rfl
#align multiset.count_zero Multiset.count_zero
-/

#print Multiset.count_cons_self /-
@[simp]
theorem count_cons_self (a : α) (s : Multiset α) : count a (a ::ₘ s) = succ (count a s) :=
  countp_cons_of_pos _ rfl
#align multiset.count_cons_self Multiset.count_cons_self
-/

#print Multiset.count_cons_of_ne /-
@[simp]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (s : Multiset α) : count a (b ::ₘ s) = count a s :=
  countp_cons_of_neg _ h
#align multiset.count_cons_of_ne Multiset.count_cons_of_ne
-/

/- warning: multiset.count_le_card -> Multiset.count_le_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α), LE.le.{0} Nat Nat.hasLe (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α), LE.le.{0} Nat instLENat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)
Case conversion may be inaccurate. Consider using '#align multiset.count_le_card Multiset.count_le_cardₓ'. -/
theorem count_le_card (a : α) (s) : count a s ≤ card s :=
  countp_le_card _ _
#align multiset.count_le_card Multiset.count_le_card

/- warning: multiset.count_le_of_le -> Multiset.count_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (LE.le.{0} Nat Nat.hasLe (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (LE.le.{0} Nat instLENat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a t))
Case conversion may be inaccurate. Consider using '#align multiset.count_le_of_le Multiset.count_le_of_leₓ'. -/
theorem count_le_of_le (a : α) {s t} : s ≤ t → count a s ≤ count a t :=
  countp_le_of_le _
#align multiset.count_le_of_le Multiset.count_le_of_le

#print Multiset.count_le_count_cons /-
theorem count_le_count_cons (a b : α) (s : Multiset α) : count a s ≤ count a (b ::ₘ s) :=
  count_le_of_le _ (le_cons_self _ _)
#align multiset.count_le_count_cons Multiset.count_le_count_cons
-/

#print Multiset.count_cons /-
theorem count_cons (a b : α) (s : Multiset α) :
    count a (b ::ₘ s) = count a s + if a = b then 1 else 0 :=
  countp_cons _ _ _
#align multiset.count_cons Multiset.count_cons
-/

#print Multiset.count_singleton_self /-
theorem count_singleton_self (a : α) : count a ({a} : Multiset α) = 1 :=
  count_eq_one_of_mem (nodup_singleton a) <| mem_singleton_self a
#align multiset.count_singleton_self Multiset.count_singleton_self
-/

#print Multiset.count_singleton /-
theorem count_singleton (a b : α) : count a ({b} : Multiset α) = if a = b then 1 else 0 := by
  simp only [count_cons, ← cons_zero, count_zero, zero_add]
#align multiset.count_singleton Multiset.count_singleton
-/

#print Multiset.count_add /-
@[simp]
theorem count_add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
  countp_add _
#align multiset.count_add Multiset.count_add
-/

/- warning: multiset.count_add_monoid_hom -> Multiset.countAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], α -> (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], α -> (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid))
Case conversion may be inaccurate. Consider using '#align multiset.count_add_monoid_hom Multiset.countAddMonoidHomₓ'. -/
/-- `count a`, the multiplicity of `a` in a multiset, promoted to an `add_monoid_hom`. -/
def countAddMonoidHom (a : α) : Multiset α →+ ℕ :=
  countpAddMonoidHom (Eq a)
#align multiset.count_add_monoid_hom Multiset.countAddMonoidHom

/- warning: multiset.coe_count_add_monoid_hom -> Multiset.coe_countAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α}, Eq.{succ u1} ((fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (Multiset.countAddMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.countAddMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a)) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α}, Eq.{succ u1} (forall (a : Multiset.{u1} α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) a) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.countAddMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a)) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a)
Case conversion may be inaccurate. Consider using '#align multiset.coe_count_add_monoid_hom Multiset.coe_countAddMonoidHomₓ'. -/
@[simp]
theorem coe_countAddMonoidHom {a : α} : (countAddMonoidHom a : Multiset α → ℕ) = count a :=
  rfl
#align multiset.coe_count_add_monoid_hom Multiset.coe_countAddMonoidHom

/- warning: multiset.count_nsmul -> Multiset.count_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (n : Nat) (s : Multiset.{u1} α), Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (n : Nat) (s : Multiset.{u1} α), Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s))
Case conversion may be inaccurate. Consider using '#align multiset.count_nsmul Multiset.count_nsmulₓ'. -/
@[simp]
theorem count_nsmul (a : α) (n s) : count a (n • s) = n * count a s := by
  induction n <;> simp [*, succ_nsmul', succ_mul, zero_nsmul]
#align multiset.count_nsmul Multiset.count_nsmul

#print Multiset.count_pos /-
theorem count_pos {a : α} {s : Multiset α} : 0 < count a s ↔ a ∈ s := by simp [count, countp_pos]
#align multiset.count_pos Multiset.count_pos
-/

#print Multiset.one_le_count_iff_mem /-
theorem one_le_count_iff_mem {a : α} {s : Multiset α} : 1 ≤ count a s ↔ a ∈ s := by
  rw [succ_le_iff, count_pos]
#align multiset.one_le_count_iff_mem Multiset.one_le_count_iff_mem
-/

#print Multiset.count_eq_zero_of_not_mem /-
@[simp]
theorem count_eq_zero_of_not_mem {a : α} {s : Multiset α} (h : a ∉ s) : count a s = 0 :=
  by_contradiction fun h' => h <| count_pos.1 (Nat.pos_of_ne_zero h')
#align multiset.count_eq_zero_of_not_mem Multiset.count_eq_zero_of_not_mem
-/

#print Multiset.count_eq_zero /-
@[simp]
theorem count_eq_zero {a : α} {s : Multiset α} : count a s = 0 ↔ a ∉ s :=
  iff_not_comm.1 <| count_pos.symm.trans pos_iff_ne_zero
#align multiset.count_eq_zero Multiset.count_eq_zero
-/

#print Multiset.count_ne_zero /-
theorem count_ne_zero {a : α} {s : Multiset α} : count a s ≠ 0 ↔ a ∈ s := by
  simp [Ne.def, count_eq_zero]
#align multiset.count_ne_zero Multiset.count_ne_zero
-/

/- warning: multiset.count_eq_card -> Multiset.count_eq_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, Iff (Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)) (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (Eq.{succ u1} α a x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α}, Iff (Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)) (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (Eq.{succ u1} α a x))
Case conversion may be inaccurate. Consider using '#align multiset.count_eq_card Multiset.count_eq_cardₓ'. -/
theorem count_eq_card {a : α} {s} : count a s = card s ↔ ∀ x ∈ s, a = x :=
  countp_eq_card
#align multiset.count_eq_card Multiset.count_eq_card

#print Multiset.count_replicate_self /-
@[simp]
theorem count_replicate_self (a : α) (n : ℕ) : count a (replicate n a) = n :=
  count_replicate_self _ _
#align multiset.count_replicate_self Multiset.count_replicate_self
-/

#print Multiset.count_replicate /-
theorem count_replicate (a b : α) (n : ℕ) : count a (replicate n b) = if a = b then n else 0 :=
  count_replicate _ _ _
#align multiset.count_replicate Multiset.count_replicate
-/

#print Multiset.count_erase_self /-
@[simp]
theorem count_erase_self (a : α) (s : Multiset α) : count a (erase s a) = pred (count a s) :=
  Quotient.inductionOn s <| count_erase_self a
#align multiset.count_erase_self Multiset.count_erase_self
-/

#print Multiset.count_erase_of_ne /-
@[simp]
theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (s : Multiset α) :
    count a (erase s b) = count a s :=
  Quotient.inductionOn s <| count_erase_of_ne ab
#align multiset.count_erase_of_ne Multiset.count_erase_of_ne
-/

#print Multiset.count_sub /-
@[simp]
theorem count_sub (a : α) (s t : Multiset α) : count a (s - t) = count a s - count a t :=
  by
  revert s; refine' Multiset.induction_on t (by simp) fun b t IH s => _
  rw [sub_cons, IH]
  by_cases ab : a = b
  · subst b
    rw [count_erase_self, count_cons_self, sub_succ, pred_sub]
  · rw [count_erase_of_ne ab, count_cons_of_ne ab]
#align multiset.count_sub Multiset.count_sub
-/

/- warning: multiset.count_union -> Multiset.count_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (LinearOrder.max.{0} Nat Nat.linearOrder (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Max.max.{0} Nat Nat.instMaxNat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a t))
Case conversion may be inaccurate. Consider using '#align multiset.count_union Multiset.count_unionₓ'. -/
@[simp]
theorem count_union (a : α) (s t : Multiset α) : count a (s ∪ t) = max (count a s) (count a t) := by
  simp [(· ∪ ·), union, tsub_add_eq_max, -add_comm]
#align multiset.count_union Multiset.count_union

/- warning: multiset.count_inter -> Multiset.count_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (LinearOrder.min.{0} Nat Nat.linearOrder (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Min.min.{0} Nat instMinNat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a t))
Case conversion may be inaccurate. Consider using '#align multiset.count_inter Multiset.count_interₓ'. -/
@[simp]
theorem count_inter (a : α) (s t : Multiset α) : count a (s ∩ t) = min (count a s) (count a t) :=
  by
  apply @Nat.add_left_cancel (count a (s - t))
  rw [← count_add, sub_add_inter, count_sub, tsub_add_min]
#align multiset.count_inter Multiset.count_inter

/- warning: multiset.le_count_iff_replicate_le -> Multiset.le_count_iff_replicate_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α} {n : Nat}, Iff (LE.le.{0} Nat Nat.hasLe n (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.replicate.{u1} α n a) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {s : Multiset.{u1} α} {n : Nat}, Iff (LE.le.{0} Nat instLENat n (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.replicate.{u1} α n a) s)
Case conversion may be inaccurate. Consider using '#align multiset.le_count_iff_replicate_le Multiset.le_count_iff_replicate_leₓ'. -/
theorem le_count_iff_replicate_le {a : α} {s : Multiset α} {n : ℕ} :
    n ≤ count a s ↔ replicate n a ≤ s :=
  Quot.inductionOn s fun l => le_count_iff_replicate_sublist.trans replicate_le_coe.symm
#align multiset.le_count_iff_replicate_le Multiset.le_count_iff_replicate_le

#print Multiset.count_filter_of_pos /-
@[simp]
theorem count_filter_of_pos {p} [DecidablePred p] {a} {s : Multiset α} (h : p a) :
    count a (filter p s) = count a s :=
  Quot.inductionOn s fun l => count_filter h
#align multiset.count_filter_of_pos Multiset.count_filter_of_pos
-/

#print Multiset.count_filter_of_neg /-
@[simp]
theorem count_filter_of_neg {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a) :
    count a (filter p s) = 0 :=
  Multiset.count_eq_zero_of_not_mem fun t => h (of_mem_filter t)
#align multiset.count_filter_of_neg Multiset.count_filter_of_neg
-/

#print Multiset.count_filter /-
theorem count_filter {p} [DecidablePred p] {a} {s : Multiset α} :
    count a (filter p s) = if p a then count a s else 0 :=
  by
  split_ifs with h
  · exact count_filter_of_pos h
  · exact count_filter_of_neg h
#align multiset.count_filter Multiset.count_filter
-/

#print Multiset.ext /-
theorem ext {s t : Multiset α} : s = t ↔ ∀ a, count a s = count a t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => Quotient.eq'.trans perm_iff_count
#align multiset.ext Multiset.ext
-/

#print Multiset.ext' /-
@[ext]
theorem ext' {s t : Multiset α} : (∀ a, count a s = count a t) → s = t :=
  ext.2
#align multiset.ext' Multiset.ext'
-/

/- warning: multiset.coe_inter -> Multiset.coe_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : List.{u1} α) (t : List.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) t)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) (List.bagInterₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : List.{u1} α) (t : List.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.ofList.{u1} α s) (Multiset.ofList.{u1} α t)) (Multiset.ofList.{u1} α (List.bagInter.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t))
Case conversion may be inaccurate. Consider using '#align multiset.coe_inter Multiset.coe_interₓ'. -/
@[simp]
theorem coe_inter (s t : List α) : (s ∩ t : Multiset α) = (s.bagInterₓ t : List α) := by
  ext <;> simp
#align multiset.coe_inter Multiset.coe_inter

/- warning: multiset.le_iff_count -> Multiset.le_iff_count is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) (forall (a : α), LE.le.{0} Nat Nat.hasLe (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) (forall (a : α), LE.le.{0} Nat instLENat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a t))
Case conversion may be inaccurate. Consider using '#align multiset.le_iff_count Multiset.le_iff_countₓ'. -/
theorem le_iff_count {s t : Multiset α} : s ≤ t ↔ ∀ a, count a s ≤ count a t :=
  ⟨fun h a => count_le_of_le a h, fun al => by
    rw [← (ext.2 fun a => by simp [max_eq_right (al a)] : s ∪ t = t)] <;> apply le_union_left⟩
#align multiset.le_iff_count Multiset.le_iff_count

instance : DistribLattice (Multiset α) :=
  { Multiset.lattice with
    le_sup_inf := fun s t u =>
      le_of_eq <|
        Eq.symm <|
          ext.2 fun a => by
            simp only [max_min_distrib_left, Multiset.count_inter, Multiset.sup_eq_union,
              Multiset.count_union, Multiset.inf_eq_inter] }

/- warning: multiset.count_map -> Multiset.count_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Multiset.{u1} α) [_inst_2 : DecidableEq.{succ u2} β] (b : β), Eq.{1} Nat (Multiset.count.{u2} β (fun (a : β) (b : β) => _inst_2 a b) b (Multiset.map.{u1, u2} α β f s)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.filter.{u1} α (fun (a : α) => Eq.{succ u2} β b (f a)) (fun (a : α) => _inst_2 b (f a)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Multiset.{u2} α) [_inst_2 : DecidableEq.{succ u1} β] (b : β), Eq.{1} Nat (Multiset.count.{u1} β (fun (a : β) (b : β) => _inst_2 a b) b (Multiset.map.{u2, u1} α β f s)) (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) (Multiset.filter.{u2} α (fun (a : α) => Eq.{succ u1} β b (f a)) (fun (a : α) => _inst_2 b (f a)) s))
Case conversion may be inaccurate. Consider using '#align multiset.count_map Multiset.count_mapₓ'. -/
theorem count_map {α β : Type _} (f : α → β) (s : Multiset α) [DecidableEq β] (b : β) :
    count b (map f s) = (s.filterₓ fun a => b = f a).card :=
  countp_map _ _ _
#align multiset.count_map Multiset.count_map

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ∈ » s) -/
#print Multiset.count_map_eq_count /-
/-- `multiset.map f` preserves `count` if `f` is injective on the set of elements contained in
the multiset -/
theorem count_map_eq_count [DecidableEq β] (f : α → β) (s : Multiset α)
    (hf : Set.InjOn f { x : α | x ∈ s }) (x) (_ : x ∈ s) : (s.map f).count (f x) = s.count x :=
  by
  suffices (Filter (fun a : α => f x = f a) s).count x = card (Filter (fun a : α => f x = f a) s)
    by
    rw [count, countp_map, ← this]
    exact count_filter_of_pos rfl
  ·
    rw [eq_replicate_card.2 fun b hb => ((hf H (mem_filter.1 hb).left) (mem_filter.1 hb).2).symm,
      count_replicate_self, card_replicate]
#align multiset.count_map_eq_count Multiset.count_map_eq_count
-/

#print Multiset.count_map_eq_count' /-
/-- `multiset.map f` preserves `count` if `f` is injective -/
theorem count_map_eq_count' [DecidableEq β] (f : α → β) (s : Multiset α) (hf : Function.Injective f)
    (x : α) : (s.map f).count (f x) = s.count x :=
  by
  by_cases H : x ∈ s
  · exact count_map_eq_count f _ (Set.injOn_of_injective hf _) _ H
  · rw [count_eq_zero_of_not_mem H, count_eq_zero, mem_map]
    rintro ⟨k, hks, hkx⟩
    rw [hf hkx] at *
    contradiction
#align multiset.count_map_eq_count' Multiset.count_map_eq_count'
-/

/- warning: multiset.attach_count_eq_count_coe -> Multiset.attach_count_eq_count_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α) (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)), Eq.{1} Nat (Multiset.count.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)) (fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)) (b : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)) => Subtype.decidableEq.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m) (fun (a : α) (b : α) => _inst_1 a b) a b) a (Multiset.attach.{u1} α m)) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m))))) a) m)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α) (a : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)), Eq.{1} Nat (Multiset.count.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)) (fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)) (b : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m)) => Subtype.instDecidableEqSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m) (fun (a : α) (b : α) => _inst_1 a b) a b) a (Multiset.attach.{u1} α m)) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m) a) m)
Case conversion may be inaccurate. Consider using '#align multiset.attach_count_eq_count_coe Multiset.attach_count_eq_count_coeₓ'. -/
@[simp]
theorem attach_count_eq_count_coe (m : Multiset α) (a) : m.attach.count a = m.count (a : α) :=
  calc
    m.attach.count a = (m.attach.map (coe : _ → α)).count (a : α) :=
      (Multiset.count_map_eq_count' _ _ Subtype.coe_injective _).symm
    _ = m.count (a : α) := congr_arg _ m.attach_map_val
    
#align multiset.attach_count_eq_count_coe Multiset.attach_count_eq_count_coe

#print Multiset.filter_eq' /-
theorem filter_eq' (s : Multiset α) (b : α) : s.filterₓ (· = b) = replicate (count b s) b :=
  Quotient.inductionOn s fun l => congr_arg coe <| filter_eq' l b
#align multiset.filter_eq' Multiset.filter_eq'
-/

#print Multiset.filter_eq /-
theorem filter_eq (s : Multiset α) (b : α) : s.filterₓ (Eq b) = replicate (count b s) b := by
  simp_rw [← filter_eq', eq_comm]
#align multiset.filter_eq Multiset.filter_eq
-/

/- warning: multiset.replicate_inter -> Multiset.replicate_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (n : Nat) (x : α) (s : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.replicate.{u1} α n x) s) (Multiset.replicate.{u1} α (LinearOrder.min.{0} Nat Nat.linearOrder n (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) x s)) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (n : Nat) (x : α) (s : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.replicate.{u1} α n x) s) (Multiset.replicate.{u1} α (Min.min.{0} Nat instMinNat n (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) x s)) x)
Case conversion may be inaccurate. Consider using '#align multiset.replicate_inter Multiset.replicate_interₓ'. -/
@[simp]
theorem replicate_inter (n : ℕ) (x : α) (s : Multiset α) :
    replicate n x ∩ s = replicate (min n (s.count x)) x :=
  by
  ext y
  rw [count_inter, count_replicate, count_replicate]
  by_cases y = x
  · simp only [h, if_pos rfl]
  · simp only [h, if_false, zero_min]
#align multiset.replicate_inter Multiset.replicate_inter

/- warning: multiset.inter_replicate -> Multiset.inter_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (x : α) (n : Nat), Eq.{succ u1} (Multiset.{u1} α) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s (Multiset.replicate.{u1} α n x)) (Multiset.replicate.{u1} α (LinearOrder.min.{0} Nat Nat.linearOrder (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) x s) n) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (x : Nat) (n : α), Eq.{succ u1} (Multiset.{u1} α) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s (Multiset.replicate.{u1} α x n)) (Multiset.replicate.{u1} α (Min.min.{0} Nat instMinNat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) n s) x) n)
Case conversion may be inaccurate. Consider using '#align multiset.inter_replicate Multiset.inter_replicateₓ'. -/
@[simp]
theorem inter_replicate (s : Multiset α) (x : α) (n : ℕ) :
    s ∩ replicate n x = replicate (min (s.count x) n) x := by
  rw [inter_comm, replicate_inter, min_comm]
#align multiset.inter_replicate Multiset.inter_replicate

end

/- warning: multiset.add_hom_ext -> Multiset.addHom_ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddZeroClass.{u2} β] {{f : AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1}} {{g : AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1}}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1) (fun (_x : AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1) => (Multiset.{u1} α) -> β) (AddMonoidHom.hasCoeToFun.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1) f (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1) (fun (_x : AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1) => (Multiset.{u1} α) -> β) (AddMonoidHom.hasCoeToFun.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1) g (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) x))) -> (Eq.{max (succ u2) (succ u1)} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) _inst_1) f g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddZeroClass.{u2} β] {{f : AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1}} {{g : AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1}}, (forall (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => β) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => β) _x) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1) (Multiset.{u1} α) β (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{u2} β _inst_1) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1) (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1 (AddMonoidHom.addMonoidHomClass.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1))) f (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => β) _x) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1) (Multiset.{u1} α) β (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{u2} β _inst_1) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1) (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1 (AddMonoidHom.addMonoidHomClass.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1))) g (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) x))) -> (Eq.{max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (Multiset.{u1} α) β (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) _inst_1) f g)
Case conversion may be inaccurate. Consider using '#align multiset.add_hom_ext Multiset.addHom_extₓ'. -/
@[ext]
theorem addHom_ext [AddZeroClass β] ⦃f g : Multiset α →+ β⦄ (h : ∀ x, f {x} = g {x}) : f = g :=
  by
  ext s
  induction' s using Multiset.induction_on with a s ih
  · simp only [_root_.map_zero]
  · simp only [← singleton_add, _root_.map_add, ih, h]
#align multiset.add_hom_ext Multiset.addHom_ext

section Embedding

/- warning: multiset.map_le_map_iff -> Multiset.map_le_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u2} (Multiset.{u2} β) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))) (Multiset.map.{u1, u2} α β f s) (Multiset.map.{u1, u2} α β f t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {s : Multiset.{u2} α} {t : Multiset.{u2} α}, Iff (LE.le.{u1} (Multiset.{u1} β) (Preorder.toLE.{u1} (Multiset.{u1} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β))) (Multiset.map.{u2, u1} α β f s) (Multiset.map.{u2, u1} α β f t)) (LE.le.{u2} (Multiset.{u2} α) (Preorder.toLE.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) s t))
Case conversion may be inaccurate. Consider using '#align multiset.map_le_map_iff Multiset.map_le_map_iffₓ'. -/
@[simp]
theorem map_le_map_iff {f : α → β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f ≤ t.map f ↔ s ≤ t := by
  classical
    refine' ⟨fun h => le_iff_count.mpr fun a => _, map_le_map⟩
    simpa [count_map_eq_count' f _ hf] using le_iff_count.mp h (f a)
#align multiset.map_le_map_iff Multiset.map_le_map_iff

/- warning: multiset.map_embedding -> Multiset.mapEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (Function.Embedding.{succ u1, succ u2} α β) -> (OrderEmbedding.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Function.Embedding.{succ u1, succ u2} α β) -> (OrderEmbedding.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.instPartialOrderMultiset.{u2} β))))
Case conversion may be inaccurate. Consider using '#align multiset.map_embedding Multiset.mapEmbeddingₓ'. -/
/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a multiset to its
image under `f`. -/
@[simps]
def mapEmbedding (f : α ↪ β) : Multiset α ↪o Multiset β :=
  OrderEmbedding.ofMapLeIff (map f) fun _ _ => map_le_map_iff f.inj'
#align multiset.map_embedding Multiset.mapEmbedding

end Embedding

/- warning: multiset.count_eq_card_filter_eq -> Multiset.count_eq_card_filter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (a : α), Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.filter.{u1} α (Eq.{succ u1} α a) (fun (a_1 : α) => _inst_1 a a_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (a : α), Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.filter.{u1} α (fun (x._@.Mathlib.Data.Multiset.Basic._hyg.25610 : α) => Eq.{succ u1} α x._@.Mathlib.Data.Multiset.Basic._hyg.25610 a) (fun (a_1 : α) => _inst_1 a_1 a) s))
Case conversion may be inaccurate. Consider using '#align multiset.count_eq_card_filter_eq Multiset.count_eq_card_filter_eqₓ'. -/
theorem count_eq_card_filter_eq [DecidableEq α] (s : Multiset α) (a : α) :
    s.count a = (s.filterₓ (Eq a)).card := by rw [count, countp_eq_card_filter]
#align multiset.count_eq_card_filter_eq Multiset.count_eq_card_filter_eq

/- warning: multiset.map_count_true_eq_filter_card -> Multiset.map_count_True_eq_filter_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Eq.{1} Nat (Multiset.count.{0} Prop (fun (a : Prop) (b : Prop) => Eq.decidable.{0} Prop Prop.linearOrder a b) True (Multiset.map.{u1, 0} α Prop p s)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α) (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Eq.{1} Nat (Multiset.count.{0} Prop (fun (a : Prop) (b : Prop) => instDecidableEq.{0} Prop Prop.linearOrder a b) True (Multiset.map.{u1, 0} α Prop p s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.filter.{u1} α p (fun (a : α) => _inst_1 a) s))
Case conversion may be inaccurate. Consider using '#align multiset.map_count_true_eq_filter_card Multiset.map_count_True_eq_filter_cardₓ'. -/
/--
Mapping a multiset through a predicate and counting the `true`s yields the cardinality of the set
filtered by the predicate. Note that this uses the notion of a multiset of `Prop`s - due to the
decidability requirements of `count`, the decidability instance on the LHS is different from the
RHS. In particular, the decidability instance on the left leaks `classical.dec_eq`.
See [here](https://github.com/leanprover-community/mathlib/pull/11306#discussion_r782286812)
for more discussion.
-/
@[simp]
theorem map_count_True_eq_filter_card (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.map p).count True = (s.filterₓ p).card := by
  simp only [count_eq_card_filter_eq, map_filter, card_map, Function.comp.left_id, eq_true_eq_id]
#align multiset.map_count_true_eq_filter_card Multiset.map_count_True_eq_filter_card

/-! ### Lift a relation to `multiset`s -/


section Rel

#print Multiset.Rel /-
/-- `rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping betweem elements in `s` and `t` following `r`. -/
@[mk_iff]
inductive Rel (r : α → β → Prop) : Multiset α → Multiset β → Prop
  | zero : Rel 0 0
  | cons {a b as bs} : r a b → Rel as bs → Rel (a ::ₘ as) (b ::ₘ bs)
#align multiset.rel Multiset.Rel
-/

variable {δ : Type _} {r : α → β → Prop} {p : γ → δ → Prop}

private theorem rel_flip_aux {s t} (h : Rel r s t) : Rel (flip r) t s :=
  Rel.rec_on h Rel.zero fun _ _ _ _ h₀ h₁ ih => Rel.cons h₀ ih
#align multiset.rel_flip_aux multiset.rel_flip_aux

#print Multiset.rel_flip /-
theorem rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s :=
  ⟨rel_flip_aux, rel_flip_aux⟩
#align multiset.rel_flip Multiset.rel_flip
-/

#print Multiset.rel_refl_of_refl_on /-
theorem rel_refl_of_refl_on {m : Multiset α} {r : α → α → Prop} : (∀ x ∈ m, r x x) → Rel r m m :=
  by
  apply m.induction_on
  · intros
    apply rel.zero
  · intro a m ih h
    exact rel.cons (h _ (mem_cons_self _ _)) (ih fun _ ha => h _ (mem_cons_of_mem ha))
#align multiset.rel_refl_of_refl_on Multiset.rel_refl_of_refl_on
-/

#print Multiset.rel_eq_refl /-
theorem rel_eq_refl {s : Multiset α} : Rel (· = ·) s s :=
  rel_refl_of_refl_on fun x hx => rfl
#align multiset.rel_eq_refl Multiset.rel_eq_refl
-/

#print Multiset.rel_eq /-
theorem rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t :=
  by
  constructor
  · intro h
    induction h <;> simp [*]
  · intro h
    subst h
    exact rel_eq_refl
#align multiset.rel_eq Multiset.rel_eq
-/

/- warning: multiset.rel.mono -> Multiset.Rel.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {p : α -> β -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u2} β}, (Multiset.Rel.{u1, u2} α β r s t) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b t) -> (r a b) -> (p a b))) -> (Multiset.Rel.{u1, u2} α β p s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {p : α -> β -> Prop} {s : Multiset.{u2} α} {t : Multiset.{u1} β}, (Multiset.Rel.{u2, u1} α β r s t) -> (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (forall (b : β), (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b t) -> (r a b) -> (p a b))) -> (Multiset.Rel.{u2, u1} α β p s t)
Case conversion may be inaccurate. Consider using '#align multiset.rel.mono Multiset.Rel.monoₓ'. -/
theorem Rel.mono {r p : α → β → Prop} {s t} (hst : Rel r s t)
    (h : ∀ a ∈ s, ∀ b ∈ t, r a b → p a b) : Rel p s t :=
  by
  induction hst
  case zero => exact rel.zero
  case
    cons a b s t hab hst ih =>
    apply rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab)
    exact ih fun a' ha' b' hb' h' => h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h'
#align multiset.rel.mono Multiset.Rel.mono

/- warning: multiset.rel.add -> Multiset.Rel.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u2} β} {u : Multiset.{u1} α} {v : Multiset.{u2} β}, (Multiset.Rel.{u1, u2} α β r s t) -> (Multiset.Rel.{u1, u2} α β r u v) -> (Multiset.Rel.{u1, u2} α β r (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s u) (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} β) (Multiset.{u2} β) (Multiset.{u2} β) (instHAdd.{u2} (Multiset.{u2} β) (Multiset.hasAdd.{u2} β)) t v))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {s : Multiset.{u2} α} {t : Multiset.{u1} β} {u : Multiset.{u2} α} {v : Multiset.{u1} β}, (Multiset.Rel.{u2, u1} α β r s t) -> (Multiset.Rel.{u2, u1} α β r u v) -> (Multiset.Rel.{u2, u1} α β r (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u2} α) (instHAdd.{u2} (Multiset.{u2} α) (Multiset.instAddMultiset.{u2} α)) s u) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} β) (Multiset.{u1} β) (Multiset.{u1} β) (instHAdd.{u1} (Multiset.{u1} β) (Multiset.instAddMultiset.{u1} β)) t v))
Case conversion may be inaccurate. Consider using '#align multiset.rel.add Multiset.Rel.addₓ'. -/
theorem Rel.add {s t u v} (hst : Rel r s t) (huv : Rel r u v) : Rel r (s + u) (t + v) :=
  by
  induction hst
  case zero => simpa using huv
  case cons a b s t hab hst ih => simpa using ih.cons hab
#align multiset.rel.add Multiset.Rel.add

#print Multiset.rel_flip_eq /-
theorem rel_flip_eq {s t : Multiset α} : Rel (fun a b => b = a) s t ↔ s = t :=
  show Rel (flip (· = ·)) s t ↔ s = t by rw [rel_flip, rel_eq, eq_comm]
#align multiset.rel_flip_eq Multiset.rel_flip_eq
-/

#print Multiset.rel_zero_left /-
@[simp]
theorem rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b = 0 := by rw [rel_iff] <;> simp
#align multiset.rel_zero_left Multiset.rel_zero_left
-/

/- warning: multiset.rel_zero_right -> Multiset.rel_zero_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {a : Multiset.{u1} α}, Iff (Multiset.Rel.{u1, u2} α β r a (OfNat.ofNat.{u2} (Multiset.{u2} β) 0 (OfNat.mk.{u2} (Multiset.{u2} β) 0 (Zero.zero.{u2} (Multiset.{u2} β) (Multiset.hasZero.{u2} β))))) (Eq.{succ u1} (Multiset.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {a : Multiset.{u2} α}, Iff (Multiset.Rel.{u2, u1} α β r a (OfNat.ofNat.{u1} (Multiset.{u1} β) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} β) (Multiset.instZeroMultiset.{u1} β)))) (Eq.{succ u2} (Multiset.{u2} α) a (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α))))
Case conversion may be inaccurate. Consider using '#align multiset.rel_zero_right Multiset.rel_zero_rightₓ'. -/
@[simp]
theorem rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a = 0 := by rw [rel_iff] <;> simp
#align multiset.rel_zero_right Multiset.rel_zero_right

/- warning: multiset.rel_cons_left -> Multiset.rel_cons_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {a : α} {as : Multiset.{u1} α} {bs : Multiset.{u2} β}, Iff (Multiset.Rel.{u1, u2} α β r (Multiset.cons.{u1} α a as) bs) (Exists.{succ u2} β (fun (b : β) => Exists.{succ u2} (Multiset.{u2} β) (fun (bs' : Multiset.{u2} β) => And (r a b) (And (Multiset.Rel.{u1, u2} α β r as bs') (Eq.{succ u2} (Multiset.{u2} β) bs (Multiset.cons.{u2} β b bs'))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {a : α} {as : Multiset.{u2} α} {bs : Multiset.{u1} β}, Iff (Multiset.Rel.{u2, u1} α β r (Multiset.cons.{u2} α a as) bs) (Exists.{succ u1} β (fun (b : β) => Exists.{succ u1} (Multiset.{u1} β) (fun (bs' : Multiset.{u1} β) => And (r a b) (And (Multiset.Rel.{u2, u1} α β r as bs') (Eq.{succ u1} (Multiset.{u1} β) bs (Multiset.cons.{u1} β b bs'))))))
Case conversion may be inaccurate. Consider using '#align multiset.rel_cons_left Multiset.rel_cons_leftₓ'. -/
theorem rel_cons_left {a as bs} :
    Rel r (a ::ₘ as) bs ↔ ∃ b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs' :=
  by
  constructor
  · generalize hm : a ::ₘ as = m
    intro h
    induction h generalizing as
    case zero => simp at hm; contradiction
    case
      cons a' b as' bs ha'b h ih =>
      rcases cons_eq_cons.1 hm with (⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩)
      · subst eq₁
        subst eq₂
        exact ⟨b, bs, ha'b, h, rfl⟩
      · rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩
        exact ⟨b', b ::ₘ bs', h₁, eq₁.symm ▸ rel.cons ha'b h₂, Eq.symm ▸ cons_swap _ _ _⟩
  · exact fun ⟨b, bs', hab, h, Eq⟩ => Eq.symm ▸ rel.cons hab h
#align multiset.rel_cons_left Multiset.rel_cons_left

/- warning: multiset.rel_cons_right -> Multiset.rel_cons_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {as : Multiset.{u1} α} {b : β} {bs : Multiset.{u2} β}, Iff (Multiset.Rel.{u1, u2} α β r as (Multiset.cons.{u2} β b bs)) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} (Multiset.{u1} α) (fun (as' : Multiset.{u1} α) => And (r a b) (And (Multiset.Rel.{u1, u2} α β r as' bs) (Eq.{succ u1} (Multiset.{u1} α) as (Multiset.cons.{u1} α a as'))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {as : Multiset.{u2} α} {b : β} {bs : Multiset.{u1} β}, Iff (Multiset.Rel.{u2, u1} α β r as (Multiset.cons.{u1} β b bs)) (Exists.{succ u2} α (fun (a : α) => Exists.{succ u2} (Multiset.{u2} α) (fun (as' : Multiset.{u2} α) => And (r a b) (And (Multiset.Rel.{u2, u1} α β r as' bs) (Eq.{succ u2} (Multiset.{u2} α) as (Multiset.cons.{u2} α a as'))))))
Case conversion may be inaccurate. Consider using '#align multiset.rel_cons_right Multiset.rel_cons_rightₓ'. -/
theorem rel_cons_right {as b bs} :
    Rel r as (b ::ₘ bs) ↔ ∃ a as', r a b ∧ Rel r as' bs ∧ as = a ::ₘ as' :=
  by
  rw [← rel_flip, rel_cons_left]
  refine' exists₂_congr fun a as' => _
  rw [rel_flip, flip]
#align multiset.rel_cons_right Multiset.rel_cons_right

/- warning: multiset.rel_add_left -> Multiset.rel_add_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {as₀ : Multiset.{u1} α} {as₁ : Multiset.{u1} α} {bs : Multiset.{u2} β}, Iff (Multiset.Rel.{u1, u2} α β r (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) as₀ as₁) bs) (Exists.{succ u2} (Multiset.{u2} β) (fun (bs₀ : Multiset.{u2} β) => Exists.{succ u2} (Multiset.{u2} β) (fun (bs₁ : Multiset.{u2} β) => And (Multiset.Rel.{u1, u2} α β r as₀ bs₀) (And (Multiset.Rel.{u1, u2} α β r as₁ bs₁) (Eq.{succ u2} (Multiset.{u2} β) bs (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} β) (Multiset.{u2} β) (Multiset.{u2} β) (instHAdd.{u2} (Multiset.{u2} β) (Multiset.hasAdd.{u2} β)) bs₀ bs₁))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {as₀ : Multiset.{u2} α} {as₁ : Multiset.{u2} α} {bs : Multiset.{u1} β}, Iff (Multiset.Rel.{u2, u1} α β r (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u2} α) (instHAdd.{u2} (Multiset.{u2} α) (Multiset.instAddMultiset.{u2} α)) as₀ as₁) bs) (Exists.{succ u1} (Multiset.{u1} β) (fun (bs₀ : Multiset.{u1} β) => Exists.{succ u1} (Multiset.{u1} β) (fun (bs₁ : Multiset.{u1} β) => And (Multiset.Rel.{u2, u1} α β r as₀ bs₀) (And (Multiset.Rel.{u2, u1} α β r as₁ bs₁) (Eq.{succ u1} (Multiset.{u1} β) bs (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} β) (Multiset.{u1} β) (Multiset.{u1} β) (instHAdd.{u1} (Multiset.{u1} β) (Multiset.instAddMultiset.{u1} β)) bs₀ bs₁))))))
Case conversion may be inaccurate. Consider using '#align multiset.rel_add_left Multiset.rel_add_leftₓ'. -/
theorem rel_add_left {as₀ as₁} :
    ∀ {bs}, Rel r (as₀ + as₁) bs ↔ ∃ bs₀ bs₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ bs = bs₀ + bs₁ :=
  Multiset.induction_on as₀ (by simp)
    (by
      intro a s ih bs
      simp only [ih, cons_add, rel_cons_left]
      constructor
      · intro h
        rcases h with ⟨b, bs', hab, h, rfl⟩
        rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩
        exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩
      · intro h
        rcases h with ⟨bs₀, bs₁, h, h₁, rfl⟩
        rcases h with ⟨b, bs, hab, h₀, rfl⟩
        exact ⟨b, bs + bs₁, hab, ⟨bs, bs₁, h₀, h₁, rfl⟩, by simp⟩)
#align multiset.rel_add_left Multiset.rel_add_left

/- warning: multiset.rel_add_right -> Multiset.rel_add_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {as : Multiset.{u1} α} {bs₀ : Multiset.{u2} β} {bs₁ : Multiset.{u2} β}, Iff (Multiset.Rel.{u1, u2} α β r as (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} β) (Multiset.{u2} β) (Multiset.{u2} β) (instHAdd.{u2} (Multiset.{u2} β) (Multiset.hasAdd.{u2} β)) bs₀ bs₁)) (Exists.{succ u1} (Multiset.{u1} α) (fun (as₀ : Multiset.{u1} α) => Exists.{succ u1} (Multiset.{u1} α) (fun (as₁ : Multiset.{u1} α) => And (Multiset.Rel.{u1, u2} α β r as₀ bs₀) (And (Multiset.Rel.{u1, u2} α β r as₁ bs₁) (Eq.{succ u1} (Multiset.{u1} α) as (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) as₀ as₁))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {as : Multiset.{u2} α} {bs₀ : Multiset.{u1} β} {bs₁ : Multiset.{u1} β}, Iff (Multiset.Rel.{u2, u1} α β r as (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} β) (Multiset.{u1} β) (Multiset.{u1} β) (instHAdd.{u1} (Multiset.{u1} β) (Multiset.instAddMultiset.{u1} β)) bs₀ bs₁)) (Exists.{succ u2} (Multiset.{u2} α) (fun (as₀ : Multiset.{u2} α) => Exists.{succ u2} (Multiset.{u2} α) (fun (as₁ : Multiset.{u2} α) => And (Multiset.Rel.{u2, u1} α β r as₀ bs₀) (And (Multiset.Rel.{u2, u1} α β r as₁ bs₁) (Eq.{succ u2} (Multiset.{u2} α) as (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u2} α) (instHAdd.{u2} (Multiset.{u2} α) (Multiset.instAddMultiset.{u2} α)) as₀ as₁))))))
Case conversion may be inaccurate. Consider using '#align multiset.rel_add_right Multiset.rel_add_rightₓ'. -/
theorem rel_add_right {as bs₀ bs₁} :
    Rel r as (bs₀ + bs₁) ↔ ∃ as₀ as₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ as = as₀ + as₁ := by
  rw [← rel_flip, rel_add_left] <;> simp [rel_flip]
#align multiset.rel_add_right Multiset.rel_add_right

#print Multiset.rel_map_left /-
theorem rel_map_left {s : Multiset γ} {f : γ → α} :
    ∀ {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }) [rel_cons_left])
#align multiset.rel_map_left Multiset.rel_map_left
-/

/- warning: multiset.rel_map_right -> Multiset.rel_map_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> β -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u3} γ} {f : γ -> β}, Iff (Multiset.Rel.{u1, u2} α β r s (Multiset.map.{u3, u2} γ β f t)) (Multiset.Rel.{u1, u3} α γ (fun (a : α) (b : γ) => r a (f b)) s t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {r : α -> β -> Prop} {s : Multiset.{u3} α} {t : Multiset.{u2} γ} {f : γ -> β}, Iff (Multiset.Rel.{u3, u1} α β r s (Multiset.map.{u2, u1} γ β f t)) (Multiset.Rel.{u3, u2} α γ (fun (a : α) (b : γ) => r a (f b)) s t)
Case conversion may be inaccurate. Consider using '#align multiset.rel_map_right Multiset.rel_map_rightₓ'. -/
theorem rel_map_right {s : Multiset α} {t : Multiset γ} {f : γ → β} :
    Rel r s (t.map f) ↔ Rel (fun a b => r a (f b)) s t := by
  rw [← rel_flip, rel_map_left, ← rel_flip] <;> rfl
#align multiset.rel_map_right Multiset.rel_map_right

/- warning: multiset.rel_map -> Multiset.rel_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {p : γ -> δ -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u2} β} {f : α -> γ} {g : β -> δ}, Iff (Multiset.Rel.{u3, u4} γ δ p (Multiset.map.{u1, u3} α γ f s) (Multiset.map.{u2, u4} β δ g t)) (Multiset.Rel.{u1, u2} α β (fun (a : α) (b : β) => p (f a) (g b)) s t)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} {p : γ -> δ -> Prop} {s : Multiset.{u4} α} {t : Multiset.{u3} β} {f : α -> γ} {g : β -> δ}, Iff (Multiset.Rel.{u2, u1} γ δ p (Multiset.map.{u4, u2} α γ f s) (Multiset.map.{u3, u1} β δ g t)) (Multiset.Rel.{u4, u3} α β (fun (a : α) (b : β) => p (f a) (g b)) s t)
Case conversion may be inaccurate. Consider using '#align multiset.rel_map Multiset.rel_mapₓ'. -/
theorem rel_map {s : Multiset α} {t : Multiset β} {f : α → γ} {g : β → δ} :
    Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t :=
  rel_map_left.trans rel_map_right
#align multiset.rel_map Multiset.rel_map

/- warning: multiset.card_eq_card_of_rel -> Multiset.card_eq_card_of_rel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u2} β}, (Multiset.Rel.{u1, u2} α β r s t) -> (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} β) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} β) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {s : Multiset.{u2} α} {t : Multiset.{u1} β}, (Multiset.Rel.{u2, u1} α β r s t) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) s) (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) (fun (_x : Multiset.{u1} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} β) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} β) t))
Case conversion may be inaccurate. Consider using '#align multiset.card_eq_card_of_rel Multiset.card_eq_card_of_relₓ'. -/
theorem card_eq_card_of_rel {r : α → β → Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) :
    card s = card t := by induction h <;> simp [*]
#align multiset.card_eq_card_of_rel Multiset.card_eq_card_of_rel

/- warning: multiset.exists_mem_of_rel_of_mem -> Multiset.exists_mem_of_rel_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u2} β}, (Multiset.Rel.{u1, u2} α β r s t) -> (forall {a : α}, (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Exists.{succ u2} β (fun (b : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b t) (fun (H : Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b t) => r a b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {s : Multiset.{u2} α} {t : Multiset.{u1} β}, (Multiset.Rel.{u2, u1} α β r s t) -> (forall {a : α}, (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (Exists.{succ u1} β (fun (b : β) => And (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b t) (r a b))))
Case conversion may be inaccurate. Consider using '#align multiset.exists_mem_of_rel_of_mem Multiset.exists_mem_of_rel_of_memₓ'. -/
theorem exists_mem_of_rel_of_mem {r : α → β → Prop} {s : Multiset α} {t : Multiset β}
    (h : Rel r s t) : ∀ {a : α} (ha : a ∈ s), ∃ b ∈ t, r a b :=
  by
  induction' h with x y s t hxy hst ih
  · simp
  · intro a ha
    cases' mem_cons.1 ha with ha ha
    · exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩
    · rcases ih ha with ⟨b, hbt, hab⟩
      exact ⟨b, mem_cons.2 (Or.inr hbt), hab⟩
#align multiset.exists_mem_of_rel_of_mem Multiset.exists_mem_of_rel_of_mem

/- warning: multiset.rel_of_forall -> Multiset.rel_of_forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m1 : Multiset.{u1} α} {m2 : Multiset.{u1} α} {r : α -> α -> Prop}, (forall (a : α) (b : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m1) -> (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) b m2) -> (r a b)) -> (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m1) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m2)) -> (Multiset.Rel.{u1, u1} α α r m1 m2)
but is expected to have type
  forall {α : Type.{u1}} {m1 : Multiset.{u1} α} {m2 : Multiset.{u1} α} {r : α -> α -> Prop}, (forall (a : α) (b : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a m1) -> (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) b m2) -> (r a b)) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) m1) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m1) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m2)) -> (Multiset.Rel.{u1, u1} α α r m1 m2)
Case conversion may be inaccurate. Consider using '#align multiset.rel_of_forall Multiset.rel_of_forallₓ'. -/
theorem rel_of_forall {m1 m2 : Multiset α} {r : α → α → Prop} (h : ∀ a b, a ∈ m1 → b ∈ m2 → r a b)
    (hc : card m1 = card m2) : m1.Rel r m2 :=
  by
  revert m1
  apply m2.induction_on
  · intro m h hc
    rw [rel_zero_right, ← card_eq_zero, hc, card_zero]
  · intro a t ih m h hc
    rw [card_cons] at hc
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m from hc.symm ▸ Nat.succ_pos _)
    obtain ⟨m', rfl⟩ := exists_cons_of_mem hb
    refine' rel_cons_right.mpr ⟨b, m', h _ _ hb (mem_cons_self _ _), ih _ _, rfl⟩
    · exact fun _ _ ha hb => h _ _ (mem_cons_of_mem ha) (mem_cons_of_mem hb)
    · simpa using hc
#align multiset.rel_of_forall Multiset.rel_of_forall

/- warning: multiset.rel_replicate_left -> Multiset.rel_replicate_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {a : α} {r : α -> α -> Prop} {n : Nat}, Iff (Multiset.Rel.{u1, u1} α α r (Multiset.replicate.{u1} α n a) m) (And (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m) n) (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m) -> (r a x)))
but is expected to have type
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {a : α} {r : α -> α -> Prop} {n : Nat}, Iff (Multiset.Rel.{u1, u1} α α r (Multiset.replicate.{u1} α n a) m) (And (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) m) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m) n) (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m) -> (r a x)))
Case conversion may be inaccurate. Consider using '#align multiset.rel_replicate_left Multiset.rel_replicate_leftₓ'. -/
theorem rel_replicate_left {m : Multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
    (replicate n a).Rel r m ↔ m.card = n ∧ ∀ x, x ∈ m → r a x :=
  ⟨fun h =>
    ⟨(card_eq_card_of_rel h).symm.trans (card_replicate _ _), fun x hx =>
      by
      obtain ⟨b, hb1, hb2⟩ := exists_mem_of_rel_of_mem (rel_flip.2 h) hx
      rwa [eq_of_mem_replicate hb1] at hb2⟩,
    fun h =>
    rel_of_forall (fun x y hx hy => (eq_of_mem_replicate hx).symm ▸ h.2 _ hy)
      (Eq.trans (card_replicate _ _) h.1.symm)⟩
#align multiset.rel_replicate_left Multiset.rel_replicate_left

/- warning: multiset.rel_replicate_right -> Multiset.rel_replicate_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {a : α} {r : α -> α -> Prop} {n : Nat}, Iff (Multiset.Rel.{u1, u1} α α r m (Multiset.replicate.{u1} α n a)) (And (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m) n) (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m) -> (r x a)))
but is expected to have type
  forall {α : Type.{u1}} {m : Multiset.{u1} α} {a : α} {r : α -> α -> Prop} {n : Nat}, Iff (Multiset.Rel.{u1, u1} α α r m (Multiset.replicate.{u1} α n a)) (And (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) m) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m) n) (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m) -> (r x a)))
Case conversion may be inaccurate. Consider using '#align multiset.rel_replicate_right Multiset.rel_replicate_rightₓ'. -/
theorem rel_replicate_right {m : Multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
    m.Rel r (replicate n a) ↔ m.card = n ∧ ∀ x, x ∈ m → r x a :=
  rel_flip.trans rel_replicate_left
#align multiset.rel_replicate_right Multiset.rel_replicate_right

#print Multiset.Rel.trans /-
theorem Rel.trans (r : α → α → Prop) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t)
    (r2 : Rel r t u) : Rel r s u :=
  by
  induction' t using Multiset.induction_on with x t ih generalizing s u
  · rw [rel_zero_right.mp r1, rel_zero_left.mp r2, rel_zero_left]
  · obtain ⟨a, as, ha1, ha2, rfl⟩ := rel_cons_right.mp r1
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp r2
    exact Multiset.Rel.cons (trans ha1 hb1) (ih ha2 hb2)
#align multiset.rel.trans Multiset.Rel.trans
-/

#print Multiset.Rel.countp_eq /-
theorem Rel.countp_eq (r : α → α → Prop) [IsTrans α r] [IsSymm α r] {s t : Multiset α} (x : α)
    [DecidablePred (r x)] (h : Rel r s t) : countp (r x) s = countp (r x) t :=
  by
  induction' s using Multiset.induction_on with y s ih generalizing t
  · rw [rel_zero_left.mp h]
  · obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp h
    rw [countp_cons, countp_cons, ih hb2]
    exact congr_arg _ (if_congr ⟨fun h => trans h hb1, fun h => trans h (symm hb1)⟩ rfl rfl)
#align multiset.rel.countp_eq Multiset.Rel.countp_eq
-/

end Rel

section Map

/- warning: multiset.map_eq_map -> Multiset.map_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (Eq.{succ u2} (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f s) (Multiset.map.{u1, u2} α β f t)) (Eq.{succ u1} (Multiset.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {s : Multiset.{u2} α} {t : Multiset.{u2} α}, Iff (Eq.{succ u1} (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f s) (Multiset.map.{u2, u1} α β f t)) (Eq.{succ u2} (Multiset.{u2} α) s t))
Case conversion may be inaccurate. Consider using '#align multiset.map_eq_map Multiset.map_eq_mapₓ'. -/
theorem map_eq_map {f : α → β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f = t.map f ↔ s = t := by
  rw [← rel_eq, ← rel_eq, rel_map]
  simp only [hf.eq_iff]
#align multiset.map_eq_map Multiset.map_eq_map

/- warning: multiset.map_injective -> Multiset.map_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Function.Injective.{succ u1, succ u2} (Multiset.{u1} α) (Multiset.{u2} β) (Multiset.map.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Function.Injective.{succ u2, succ u1} (Multiset.{u2} α) (Multiset.{u1} β) (Multiset.map.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align multiset.map_injective Multiset.map_injectiveₓ'. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Multiset.map f) := fun x y => (map_eq_map hf).1
#align multiset.map_injective Multiset.map_injective

end Map

section Quot

#print Multiset.map_mk_eq_map_mk_of_rel /-
theorem map_mk_eq_map_mk_of_rel {r : α → α → Prop} {s t : Multiset α} (hst : s.Rel r t) :
    s.map (Quot.mk r) = t.map (Quot.mk r) :=
  Rel.rec_on hst rfl fun a b s t hab hst ih => by simp [ih, Quot.sound hab]
#align multiset.map_mk_eq_map_mk_of_rel Multiset.map_mk_eq_map_mk_of_rel
-/

#print Multiset.exists_multiset_eq_map_quot_mk /-
theorem exists_multiset_eq_map_quot_mk {r : α → α → Prop} (s : Multiset (Quot r)) :
    ∃ t : Multiset α, s = t.map (Quot.mk r) :=
  Multiset.induction_on s ⟨0, rfl⟩ fun a s ⟨t, ht⟩ =>
    Quot.inductionOn a fun a => ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩
#align multiset.exists_multiset_eq_map_quot_mk Multiset.exists_multiset_eq_map_quot_mk
-/

#print Multiset.induction_on_multiset_quot /-
theorem induction_on_multiset_quot {r : α → α → Prop} {p : Multiset (Quot r) → Prop}
    (s : Multiset (Quot r)) : (∀ s : Multiset α, p (s.map (Quot.mk r))) → p s :=
  match s, exists_multiset_eq_map_quot_mk s with
  | _, ⟨t, rfl⟩ => fun h => h _
#align multiset.induction_on_multiset_quot Multiset.induction_on_multiset_quot
-/

end Quot

/-! ### Disjoint multisets -/


#print Multiset.Disjoint /-
/-- `disjoint s t` means that `s` and `t` have no elements in common. -/
def Disjoint (s t : Multiset α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → a ∈ t → False
#align multiset.disjoint Multiset.Disjoint
-/

#print Multiset.coe_disjoint /-
@[simp]
theorem coe_disjoint (l₁ l₂ : List α) : @Disjoint α l₁ l₂ ↔ l₁.Disjoint l₂ :=
  Iff.rfl
#align multiset.coe_disjoint Multiset.coe_disjoint
-/

#print Multiset.Disjoint.symm /-
theorem Disjoint.symm {s t : Multiset α} (d : Disjoint s t) : Disjoint t s
  | a, i₂, i₁ => d i₁ i₂
#align multiset.disjoint.symm Multiset.Disjoint.symm
-/

#print Multiset.disjoint_comm /-
theorem disjoint_comm {s t : Multiset α} : Disjoint s t ↔ Disjoint t s :=
  ⟨Disjoint.symm, Disjoint.symm⟩
#align multiset.disjoint_comm Multiset.disjoint_comm
-/

#print Multiset.disjoint_left /-
theorem disjoint_left {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
  Iff.rfl
#align multiset.disjoint_left Multiset.disjoint_left
-/

#print Multiset.disjoint_right /-
theorem disjoint_right {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
  disjoint_comm
#align multiset.disjoint_right Multiset.disjoint_right
-/

#print Multiset.disjoint_iff_ne /-
theorem disjoint_iff_ne {s t : Multiset α} : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp [disjoint_left, imp_not_comm]
#align multiset.disjoint_iff_ne Multiset.disjoint_iff_ne
-/

#print Multiset.disjoint_of_subset_left /-
theorem disjoint_of_subset_left {s t u : Multiset α} (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t
  | x, m₁ => d (h m₁)
#align multiset.disjoint_of_subset_left Multiset.disjoint_of_subset_left
-/

#print Multiset.disjoint_of_subset_right /-
theorem disjoint_of_subset_right {s t u : Multiset α} (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t
  | x, m, m₁ => d m (h m₁)
#align multiset.disjoint_of_subset_right Multiset.disjoint_of_subset_right
-/

/- warning: multiset.disjoint_of_le_left -> Multiset.disjoint_of_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s u) -> (Multiset.Disjoint.{u1} α u t) -> (Multiset.Disjoint.{u1} α s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s u) -> (Multiset.Disjoint.{u1} α u t) -> (Multiset.Disjoint.{u1} α s t)
Case conversion may be inaccurate. Consider using '#align multiset.disjoint_of_le_left Multiset.disjoint_of_le_leftₓ'. -/
theorem disjoint_of_le_left {s t u : Multiset α} (h : s ≤ u) : Disjoint u t → Disjoint s t :=
  disjoint_of_subset_left (subset_of_le h)
#align multiset.disjoint_of_le_left Multiset.disjoint_of_le_left

/- warning: multiset.disjoint_of_le_right -> Multiset.disjoint_of_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) t u) -> (Multiset.Disjoint.{u1} α s u) -> (Multiset.Disjoint.{u1} α s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {u : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) t u) -> (Multiset.Disjoint.{u1} α s u) -> (Multiset.Disjoint.{u1} α s t)
Case conversion may be inaccurate. Consider using '#align multiset.disjoint_of_le_right Multiset.disjoint_of_le_rightₓ'. -/
theorem disjoint_of_le_right {s t u : Multiset α} (h : t ≤ u) : Disjoint s u → Disjoint s t :=
  disjoint_of_subset_right (subset_of_le h)
#align multiset.disjoint_of_le_right Multiset.disjoint_of_le_right

#print Multiset.zero_disjoint /-
@[simp]
theorem zero_disjoint (l : Multiset α) : Disjoint 0 l
  | a => (not_mem_nil a).elim
#align multiset.zero_disjoint Multiset.zero_disjoint
-/

#print Multiset.singleton_disjoint /-
@[simp]
theorem singleton_disjoint {l : Multiset α} {a : α} : Disjoint {a} l ↔ a ∉ l := by
  simp [Disjoint] <;> rfl
#align multiset.singleton_disjoint Multiset.singleton_disjoint
-/

#print Multiset.disjoint_singleton /-
@[simp]
theorem disjoint_singleton {l : Multiset α} {a : α} : Disjoint l {a} ↔ a ∉ l := by
  rw [disjoint_comm, singleton_disjoint]
#align multiset.disjoint_singleton Multiset.disjoint_singleton
-/

#print Multiset.disjoint_add_left /-
@[simp]
theorem disjoint_add_left {s t u : Multiset α} : Disjoint (s + t) u ↔ Disjoint s u ∧ Disjoint t u :=
  by simp [Disjoint, or_imp, forall_and]
#align multiset.disjoint_add_left Multiset.disjoint_add_left
-/

#print Multiset.disjoint_add_right /-
@[simp]
theorem disjoint_add_right {s t u : Multiset α} :
    Disjoint s (t + u) ↔ Disjoint s t ∧ Disjoint s u := by
  rw [disjoint_comm, disjoint_add_left] <;> tauto
#align multiset.disjoint_add_right Multiset.disjoint_add_right
-/

#print Multiset.disjoint_cons_left /-
@[simp]
theorem disjoint_cons_left {a : α} {s t : Multiset α} :
    Disjoint (a ::ₘ s) t ↔ a ∉ t ∧ Disjoint s t :=
  (@disjoint_add_left _ {a} s t).trans <| by rw [singleton_disjoint]
#align multiset.disjoint_cons_left Multiset.disjoint_cons_left
-/

#print Multiset.disjoint_cons_right /-
@[simp]
theorem disjoint_cons_right {a : α} {s t : Multiset α} :
    Disjoint s (a ::ₘ t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [disjoint_comm, disjoint_cons_left] <;> tauto
#align multiset.disjoint_cons_right Multiset.disjoint_cons_right
-/

#print Multiset.inter_eq_zero_iff_disjoint /-
theorem inter_eq_zero_iff_disjoint [DecidableEq α] {s t : Multiset α} : s ∩ t = 0 ↔ Disjoint s t :=
  by rw [← subset_zero] <;> simp [subset_iff, Disjoint]
#align multiset.inter_eq_zero_iff_disjoint Multiset.inter_eq_zero_iff_disjoint
-/

#print Multiset.disjoint_union_left /-
@[simp]
theorem disjoint_union_left [DecidableEq α] {s t u : Multiset α} :
    Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := by simp [Disjoint, or_imp, forall_and]
#align multiset.disjoint_union_left Multiset.disjoint_union_left
-/

#print Multiset.disjoint_union_right /-
@[simp]
theorem disjoint_union_right [DecidableEq α] {s t u : Multiset α} :
    Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := by simp [Disjoint, or_imp, forall_and]
#align multiset.disjoint_union_right Multiset.disjoint_union_right
-/

#print Multiset.add_eq_union_iff_disjoint /-
theorem add_eq_union_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s + t = s ∪ t ↔ Disjoint s t := by
  simp_rw [← inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero,
    Nat.min_eq_zero_iff, Nat.add_eq_max_iff]
#align multiset.add_eq_union_iff_disjoint Multiset.add_eq_union_iff_disjoint
-/

/- warning: multiset.disjoint_map_map -> Multiset.disjoint_map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> γ} {g : β -> γ} {s : Multiset.{u1} α} {t : Multiset.{u2} β}, Iff (Multiset.Disjoint.{u3} γ (Multiset.map.{u1, u3} α γ f s) (Multiset.map.{u2, u3} β γ g t)) (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b t) -> (Ne.{succ u3} γ (f a) (g b))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> γ} {g : β -> γ} {s : Multiset.{u3} α} {t : Multiset.{u2} β}, Iff (Multiset.Disjoint.{u1} γ (Multiset.map.{u3, u1} α γ f s) (Multiset.map.{u2, u1} β γ g t)) (forall (a : α), (Membership.mem.{u3, u3} α (Multiset.{u3} α) (Multiset.instMembershipMultiset.{u3} α) a s) -> (forall (b : β), (Membership.mem.{u2, u2} β (Multiset.{u2} β) (Multiset.instMembershipMultiset.{u2} β) b t) -> (Ne.{succ u1} γ (f a) (g b))))
Case conversion may be inaccurate. Consider using '#align multiset.disjoint_map_map Multiset.disjoint_map_mapₓ'. -/
theorem disjoint_map_map {f : α → γ} {g : β → γ} {s : Multiset α} {t : Multiset β} :
    Disjoint (s.map f) (t.map g) ↔ ∀ a ∈ s, ∀ b ∈ t, f a ≠ g b :=
  by
  simp [Disjoint, @eq_comm _ (f _) (g _)]
  rfl
#align multiset.disjoint_map_map Multiset.disjoint_map_map

#print Multiset.Pairwise /-
/-- `pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this
list. -/
def Pairwise (r : α → α → Prop) (m : Multiset α) : Prop :=
  ∃ l : List α, m = l ∧ l.Pairwise r
#align multiset.pairwise Multiset.Pairwise
-/

#print Multiset.pairwise_nil /-
@[simp]
theorem pairwise_nil (r : α → α → Prop) : Multiset.Pairwise r 0 :=
  ⟨[], rfl, List.Pairwise.nil⟩
#align multiset.pairwise_nil Multiset.pairwise_nil
-/

#print Multiset.pairwise_coe_iff /-
theorem pairwise_coe_iff {r : α → α → Prop} {l : List α} :
    Multiset.Pairwise r l ↔ ∃ l' : List α, l ~ l' ∧ l'.Pairwise r :=
  exists_congr <| by simp
#align multiset.pairwise_coe_iff Multiset.pairwise_coe_iff
-/

#print Multiset.pairwise_coe_iff_pairwise /-
theorem pairwise_coe_iff_pairwise {r : α → α → Prop} (hr : Symmetric r) {l : List α} :
    Multiset.Pairwise r l ↔ l.Pairwise r :=
  Iff.intro (fun ⟨l', Eq, h⟩ => ((Quotient.exact Eq).pairwise_iff hr).2 h) fun h => ⟨l, rfl, h⟩
#align multiset.pairwise_coe_iff_pairwise Multiset.pairwise_coe_iff_pairwise
-/

/- warning: multiset.map_set_pairwise -> Multiset.map_set_pairwise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {r : β -> β -> Prop} {m : Multiset.{u1} α}, (Set.Pairwise.{u1} α (setOf.{u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m)) (fun (a₁ : α) (a₂ : α) => r (f a₁) (f a₂))) -> (Set.Pairwise.{u2} β (setOf.{u2} β (fun (b : β) => Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b (Multiset.map.{u1, u2} α β f m))) r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {r : β -> β -> Prop} {m : Multiset.{u2} α}, (Set.Pairwise.{u2} α (setOf.{u2} α (fun (a : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m)) (fun (a₁ : α) (a₂ : α) => r (f a₁) (f a₂))) -> (Set.Pairwise.{u1} β (setOf.{u1} β (fun (b : β) => Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b (Multiset.map.{u2, u1} α β f m))) r)
Case conversion may be inaccurate. Consider using '#align multiset.map_set_pairwise Multiset.map_set_pairwiseₓ'. -/
theorem map_set_pairwise {f : α → β} {r : β → β → Prop} {m : Multiset α}
    (h : { a | a ∈ m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)) : { b | b ∈ m.map f }.Pairwise r :=
  fun b₁ h₁ b₂ h₂ hn =>
  by
  obtain ⟨⟨a₁, H₁, rfl⟩, a₂, H₂, rfl⟩ := Multiset.mem_map.1 h₁, Multiset.mem_map.1 h₂
  exact h H₁ H₂ (mt (congr_arg f) hn)
#align multiset.map_set_pairwise Multiset.map_set_pairwise

end Multiset

namespace Multiset

section Choose

variable (p : α → Prop) [DecidablePred p] (l : Multiset α)

#print Multiset.chooseX /-
/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose_x p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`. -/
def chooseX : ∀ hp : ∃! a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a } :=
  Quotient.recOn l (fun l' ex_unique => List.chooseX p l' (ExistsUnique.exists ex_unique))
    (by
      intros
      funext hp
      suffices all_equal : ∀ x y : { t // t ∈ b ∧ p t }, x = y
      · apply all_equal
      · rintro ⟨x, px⟩ ⟨y, py⟩
        rcases hp with ⟨z, ⟨z_mem_l, pz⟩, z_unique⟩
        congr
        calc
          x = z := z_unique x px
          _ = y := (z_unique y py).symm
          )
#align multiset.choose_x Multiset.chooseX
-/

#print Multiset.choose /-
/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose p l hp` returns
that `a`. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  chooseX p l hp
#align multiset.choose Multiset.choose
-/

#print Multiset.choose_spec /-
theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property
#align multiset.choose_spec Multiset.choose_spec
-/

#print Multiset.choose_mem /-
theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1
#align multiset.choose_mem Multiset.choose_mem
-/

#print Multiset.choose_property /-
theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2
#align multiset.choose_property Multiset.choose_property
-/

end Choose

variable (α)

#print Multiset.subsingletonEquiv /-
/-- The equivalence between lists and multisets of a subsingleton type. -/
def subsingletonEquiv [Subsingleton α] : List α ≃ Multiset α
    where
  toFun := coe
  invFun :=
    Quot.lift id fun (a b : List α) (h : a ~ b) =>
      List.ext_nthLe h.length_eq fun n h₁ h₂ => Subsingleton.elim _ _
  left_inv l := rfl
  right_inv m := Quot.inductionOn m fun l => rfl
#align multiset.subsingleton_equiv Multiset.subsingletonEquiv
-/

variable {α}

#print Multiset.coe_subsingletonEquiv /-
@[simp]
theorem coe_subsingletonEquiv [Subsingleton α] :
    (subsingletonEquiv α : List α → Multiset α) = coe :=
  rfl
#align multiset.coe_subsingleton_equiv Multiset.coe_subsingletonEquiv
-/

end Multiset

