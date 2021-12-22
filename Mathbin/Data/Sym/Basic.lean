import Mathbin.Data.Multiset.Basic
import Mathbin.Data.Vector.Basic
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

/-- 
The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def Sym (α : Type u) (n : ℕ) :=
  { s : Multiset α // s.card = n }

/-- 
This is the `list.perm` setoid lifted to `vector`.

See note [reducible non-instances].
-/
@[reducible]
def Vector.Perm.isSetoid (α : Type u) (n : ℕ) : Setoidₓ (Vector α n) :=
  { R := fun a b => List.Perm a.1 b.1,
    iseqv := by
      rcases List.Perm.eqv α with ⟨hr, hs, ht⟩
      tidy }

attribute [local instance] Vector.Perm.isSetoid

namespace Sym

variable {α : Type u} {n : ℕ}

/-- 
This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
def of_vector (x : Vector α n) : Sym α n :=
  ⟨↑x.val, by
    rw [Multiset.coe_card]
    exact x.2⟩

instance : HasLift (Vector α n) (Sym α n) where
  lift := of_vector

/-- 
The unique element in `sym α 0`.
-/
@[matchPattern]
def nil : Sym α 0 :=
  ⟨0, by
    tidy⟩

/-- 
Inserts an element into the term of `sym α n`, increasing the length by one.
-/
@[matchPattern]
def cons : α → Sym α n → Sym α (Nat.succ n)
  | a, ⟨s, h⟩ =>
    ⟨a ::ₘ s, by
      rw [Multiset.card_cons, h]⟩

@[simp]
theorem cons_inj_right (a : α) (s s' : Sym α n) : a :: s = a :: s' ↔ s = s' := by
  cases s
  cases s'
  delta' cons
  simp

@[simp]
theorem cons_inj_left (a a' : α) (s : Sym α n) : a :: s = a' :: s ↔ a = a' := by
  cases s
  delta' cons
  simp

theorem cons_swap (a b : α) (s : Sym α n) : a :: b :: s = b :: a :: s := by
  cases s
  ext
  delta' cons
  rw [Subtype.coe_mk]
  dsimp
  exact Multiset.cons_swap a b s_val

/-- 
`α ∈ s` means that `a` appears as one of the factors in `s`.
-/
def mem (a : α) (s : Sym α n) : Prop :=
  a ∈ s.1

instance : HasMem α (Sym α n) :=
  ⟨mem⟩

instance decidable_mem [DecidableEq α] (a : α) (s : Sym α n) : Decidable (a ∈ s) := by
  cases s
  change Decidable (a ∈ s_val)
  infer_instance

@[simp]
theorem mem_cons {a b : α} {s : Sym α n} : a ∈ b :: s ↔ a = b ∨ a ∈ s := by
  cases s
  change a ∈ b ::ₘ s_val ↔ a = b ∨ a ∈ s_val
  simp

theorem mem_cons_of_mem {a b : α} {s : Sym α n} (h : a ∈ s) : a ∈ b :: s :=
  mem_cons.2 (Or.inr h)

@[simp]
theorem mem_cons_self (a : α) (s : Sym α n) : a ∈ a :: s :=
  mem_cons.2 (Or.inl rfl)

theorem cons_of_coe_eq (a : α) (v : Vector α n) : a :: (↑v : Sym α n) = ↑(a::ᵥv) := by
  unfold_coes
  delta' of_vector
  delta' cons
  delta' Vector.cons
  tidy

theorem sound {a b : Vector α n} (h : a.val ~ b.val) : (↑a : Sym α n) = ↑b := by
  cases a
  cases b
  unfold_coes
  dunfold of_vector
  simp only [Subtype.mk_eq_mk, Multiset.coe_eq_coe]
  exact h

/-- 
Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def sym' (α : Type u) (n : ℕ) :=
  Quotientₓ (Vector.Perm.isSetoid α n)

/-- 
This is `cons` but for the alternative `sym'` definition.
-/
def cons' {α : Type u} {n : ℕ} : α → sym' α n → sym' α (Nat.succ n) := fun a =>
  Quotientₓ.map (Vector.cons a) fun ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h => List.Perm.cons _ h

/-- 
Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def sym_equiv_sym' {α : Type u} {n : ℕ} : Sym α n ≃ sym' α n :=
  Equivₓ.subtypeQuotientEquivQuotientSubtype _ _
    (fun _ => by
      rfl)
    fun _ _ => by
    rfl

theorem cons_equiv_eq_equiv_cons (α : Type u) (n : ℕ) (a : α) (s : Sym α n) :
    a :: sym_equiv_sym' s = sym_equiv_sym' (a :: s) := by
  tidy

section Inhabited

instance inhabited_sym [Inhabited α] (n : ℕ) : Inhabited (Sym α n) :=
  ⟨⟨Multiset.repeat (default α) n, Multiset.card_repeat _ _⟩⟩

instance inhabited_sym' [Inhabited α] (n : ℕ) : Inhabited (sym' α n) :=
  ⟨Quotientₓ.mk' (Vector.repeat (default α) n)⟩

end Inhabited

end Sym

