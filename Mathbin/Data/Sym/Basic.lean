/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Multiset.Basic
import Mathbin.Data.Vector.Basic
import Mathbin.Data.Setoid.Basic
import Mathbin.Tactic.ApplyFun

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `data.sym.sym2`.

TODO: This was created as supporting material for `sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/


universe u

/-- The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def Sym (α : Type u) (n : ℕ) :=
  { s : Multiset α // s.card = n }

instance Sym.hasCoe (α : Type _) (n : ℕ) : Coe (Sym α n) (Multiset α) :=
  coeSubtype

/-- This is the `list.perm` setoid lifted to `vector`.

See note [reducible non-instances].
-/
@[reducible]
def Vector.Perm.isSetoid (α : Type u) (n : ℕ) : Setoidₓ (Vector α n) :=
  (List.isSetoid α).comap Subtype.val

attribute [local instance] Vector.Perm.isSetoid

namespace Sym

variable {α : Type u} {n : ℕ} {s : Sym α n} {a b : α}

/-- The unique element in `sym α 0`.
-/
@[matchPattern]
def nil : Sym α 0 :=
  ⟨0, Multiset.card_zero⟩

/-- Inserts an element into the term of `sym α n`, increasing the length by one.
-/
@[matchPattern]
def cons (a : α) (s : Sym α n) : Sym α (Nat.succ n) :=
  ⟨a ::ₘ s.1, by
    rw [Multiset.card_cons, s.2]⟩

@[simp]
theorem cons_inj_right (a : α) (s s' : Sym α n) : a :: s = a :: s' ↔ s = s' :=
  Subtype.ext_iff.trans <| (Multiset.cons_inj_right _).trans Subtype.ext_iff.symm

@[simp]
theorem cons_inj_left (a a' : α) (s : Sym α n) : a :: s = a' :: s ↔ a = a' :=
  Subtype.ext_iff.trans <| Multiset.cons_inj_left _

theorem cons_swap (a b : α) (s : Sym α n) : a :: b :: s = b :: a :: s :=
  Subtype.ext <| Multiset.cons_swap a b s.1

/-- This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
instance : HasLift (Vector α n) (Sym α n) where
  lift := fun x => ⟨↑x.val, (Multiset.coe_card _).trans x.2⟩

@[simp]
theorem of_vector_nil : ↑(Vector.nil : Vector α 0) = (Sym.nil : Sym α 0) :=
  rfl

@[simp]
theorem of_vector_cons (a : α) (v : Vector α n) : ↑(Vector.cons a v) = a :: (↑v : Sym α n) := by
  cases v
  rfl

/-- `α ∈ s` means that `a` appears as one of the factors in `s`.
-/
instance : HasMem α (Sym α n) :=
  ⟨fun a s => a ∈ s.1⟩

instance decidableMem [DecidableEq α] (a : α) (s : Sym α n) : Decidable (a ∈ s) :=
  s.1.decidableMem _

@[simp]
theorem mem_cons {a b : α} {s : Sym α n} : a ∈ b :: s ↔ a = b ∨ a ∈ s :=
  Multiset.mem_cons

theorem mem_cons_of_mem {a b : α} {s : Sym α n} (h : a ∈ s) : a ∈ b :: s :=
  Multiset.mem_cons_of_mem h

@[simp]
theorem mem_cons_self (a : α) (s : Sym α n) : a ∈ a :: s :=
  Multiset.mem_cons_self a s.1

theorem cons_of_coe_eq (a : α) (v : Vector α n) : a :: (↑v : Sym α n) = ↑(a::ᵥv) :=
  Subtype.ext <| by
    cases v
    rfl

theorem sound {a b : Vector α n} (h : a.val ~ b.val) : (↑a : Sym α n) = ↑b :=
  Subtype.ext <| Quotientₓ.sound h

/-- `erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if a is present in the sym. -/
def erase [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a ∈ s) : Sym α n :=
  ⟨s.val.erase a, (Multiset.card_erase_of_mem h).trans <| s.property.symm ▸ n.pred_succ⟩

@[simp]
theorem cons_erase [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a ∈ s) : a :: s.erase a h = s :=
  Subtype.ext <| Multiset.cons_erase h

/-- Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def Sym' (α : Type u) (n : ℕ) :=
  Quotientₓ (Vector.Perm.isSetoid α n)

/-- This is `cons` but for the alternative `sym'` definition.
-/
def cons' {α : Type u} {n : ℕ} : α → Sym' α n → Sym' α (Nat.succ n) := fun a =>
  Quotientₓ.map (Vector.cons a) fun h => List.Perm.cons _ h

/-- Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def symEquivSym' {α : Type u} {n : ℕ} : Sym α n ≃ Sym' α n :=
  Equivₓ.subtypeQuotientEquivQuotientSubtype _ _
    (fun _ => by
      rfl)
    fun _ _ => by
    rfl

theorem cons_equiv_eq_equiv_cons (α : Type u) (n : ℕ) (a : α) (s : Sym α n) :
    a :: symEquivSym' s = symEquivSym' (a :: s) := by
  rcases s with ⟨⟨l⟩, _⟩
  rfl

instance : Zero (Sym α 0) :=
  ⟨⟨0, rfl⟩⟩

instance : HasEmptyc (Sym α 0) :=
  ⟨0⟩

theorem eq_nil_of_card_zero (s : Sym α 0) : s = nil :=
  Subtype.ext <| Multiset.card_eq_zero.1 s.2

instance uniqueZero : Unique (Sym α 0) :=
  ⟨⟨nil⟩, eq_nil_of_card_zero⟩

/-- `repeat a n` is the sym containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : Sym α n :=
  ⟨Multiset.repeat a n, Multiset.card_repeat _ _⟩

theorem repeat_succ {a : α} {n : ℕ} : repeat a n.succ = a :: repeat a n :=
  rfl

theorem coe_repeat : (repeat a n : Multiset α) = Multiset.repeat a n :=
  rfl

@[simp]
theorem mem_repeat : b ∈ repeat a n ↔ n ≠ 0 ∧ b = a :=
  Multiset.mem_repeat

theorem eq_repeat_iff : s = repeat a n ↔ ∀, ∀ b ∈ s, ∀, b = a := by
  rw [Subtype.ext_iff, coe_repeat]
  convert Multiset.eq_repeat'
  exact s.2.symm

theorem exists_mem (s : Sym α n.succ) : ∃ a, a ∈ s :=
  Multiset.card_pos_iff_exists_mem.1 <| s.2.symm ▸ n.succ_pos

theorem exists_eq_cons_of_succ (s : Sym α n.succ) : ∃ (a : α)(s' : Sym α n), s = a :: s' := by
  obtain ⟨a, ha⟩ := exists_mem s
  classical
  exact ⟨a, s.erase a ha, (s.cons_erase _ _).symm⟩

theorem eq_repeat {a : α} {n : ℕ} {s : Sym α n} : s = repeat a n ↔ ∀, ∀ b ∈ s, ∀, b = a :=
  Subtype.ext_iff.trans <| Multiset.eq_repeat.trans <| and_iff_right s.Prop

theorem eq_repeat_of_subsingleton [Subsingleton α] (a : α) {n : ℕ} (s : Sym α n) : s = repeat a n :=
  eq_repeat.2 fun b hb => Subsingleton.elimₓ _ _

instance [Subsingleton α] (n : ℕ) : Subsingleton (Sym α n) :=
  ⟨by
    cases n
    · simp
      
    · intro s s'
      obtain ⟨b, -⟩ := exists_mem s
      rw [eq_repeat_of_subsingleton b s', eq_repeat_of_subsingleton b s]
      ⟩

instance inhabitedSym [Inhabited α] (n : ℕ) : Inhabited (Sym α n) :=
  ⟨repeat default n⟩

instance inhabitedSym' [Inhabited α] (n : ℕ) : Inhabited (Sym' α n) :=
  ⟨Quotientₓ.mk' (Vector.repeat default n)⟩

instance (n : ℕ) [IsEmpty α] : IsEmpty (Sym α n.succ) :=
  ⟨fun s => by
    obtain ⟨a, -⟩ := exists_mem s
    exact isEmptyElim a⟩

instance (n : ℕ) [Unique α] : Unique (Sym α n) :=
  Unique.mk' _

theorem repeat_left_inj {a b : α} {n : ℕ} (h : n ≠ 0) : repeat a n = repeat b n ↔ a = b :=
  Subtype.ext_iff.trans (Multiset.repeat_left_inj h)

theorem repeat_left_injective {n : ℕ} (h : n ≠ 0) : Function.Injective fun x : α => repeat x n := fun a b =>
  (repeat_left_inj h).1

instance (n : ℕ) [Nontrivial α] : Nontrivial (Sym α (n + 1)) :=
  (repeat_left_injective n.succ_ne_zero).Nontrivial

/-- A function `α → β` induces a function `sym α n → sym β n` by applying it to every element of
the underlying `n`-tuple. -/
def map {α β : Type _} {n : ℕ} (f : α → β) (x : Sym α n) : Sym β n :=
  ⟨x.val.map f, by
    simpa [Multiset.card_map] using x.property⟩

@[simp]
theorem mem_map {α β : Type _} {n : ℕ} {f : α → β} {b : β} {l : Sym α n} : b ∈ Sym.map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
  Multiset.mem_map

@[simp]
theorem map_id {α : Type _} {n : ℕ} (s : Sym α n) : Sym.map id s = s := by
  simp [Sym.map]

@[simp]
theorem map_map {α β γ : Type _} {n : ℕ} (g : β → γ) (f : α → β) (s : Sym α n) :
    Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s := by
  simp [Sym.map]

@[simp]
theorem map_zero {α β : Type _} (f : α → β) : Sym.map f (0 : Sym α 0) = (0 : Sym β 0) :=
  rfl

@[simp]
theorem map_cons {α β : Type _} {n : ℕ} (f : α → β) (a : α) (s : Sym α n) : (a :: s).map f = f a :: s.map f := by
  simp [map, cons]

/-- Mapping an equivalence `α ≃ β` using `sym.map` gives an equivalence between `sym α n` and
`sym β n`. -/
@[simps]
def equivCongr {β : Type u} (e : α ≃ β) : Sym α n ≃ Sym β n where
  toFun := map e
  invFun := map e.symm
  left_inv := fun x => by
    rw [map_map, Equivₓ.symm_comp_self, map_id]
  right_inv := fun x => by
    rw [map_map, Equivₓ.self_comp_symm, map_id]

end Sym

