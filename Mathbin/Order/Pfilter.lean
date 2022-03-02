/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
import Mathbin.Order.Ideal

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections
require more structure, such as a bottom element, a top element, or
a join-semilattice structure.

- `order.pfilter P`: The type of nonempty, downward directed, upward closed
               subsets of `P`. This is dual to `order.ideal`, so it
               simply wraps `order.ideal (order_dual P)`.
- `order.is_pfilter P`: a predicate for when a `set P` is a filter.


Note the relation between `order/filter` and `order/pfilter`: for any
type `α`, `filter α` represents the same mathematical object as
`pfilter (set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/


namespace Order

variable {P : Type _}

/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
structure Pfilter (P) [Preorderₓ P] where
  dual : Ideal (OrderDual P)

/-- A predicate for when a subset of `P` is a filter. -/
def IsPfilter [Preorderₓ P] (F : Set P) : Prop :=
  @IsIdeal (OrderDual P) _ F

theorem IsPfilter.of_def [Preorderₓ P] {F : Set P} (nonempty : F.Nonempty) (directed : DirectedOn (· ≥ ·) F)
    (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) : IsPfilter F := by
  use Nonempty, Directed
  exact fun _ _ _ _ => mem_of_le ‹_› ‹_›

/-- Create an element of type `order.pfilter` from a set satisfying the predicate
`order.is_pfilter`. -/
def IsPfilter.toPfilter [Preorderₓ P] {F : Set P} (h : IsPfilter F) : Pfilter P :=
  ⟨h.toIdeal⟩

namespace Pfilter

section Preorderₓ

variable [Preorderₓ P] {x y : P} (F : Pfilter P)

/-- A filter on `P` is a subset of `P`. -/
instance : Coe (Pfilter P) (Set P) :=
  ⟨fun F => F.dual.Carrier⟩

/-- For the notation `x ∈ F`. -/
instance : HasMem P (Pfilter P) :=
  ⟨fun x F => x ∈ (F : Set P)⟩

@[simp]
theorem mem_coe : x ∈ (F : Set P) ↔ x ∈ F :=
  iff_of_eq rfl

theorem is_pfilter : IsPfilter (F : Set P) :=
  F.dual.IsIdeal

theorem nonempty : (F : Set P).Nonempty :=
  F.dual.Nonempty

theorem directed : DirectedOn (· ≥ ·) (F : Set P) :=
  F.dual.Directed

theorem mem_of_le {F : Pfilter P} : x ≤ y → x ∈ F → y ∈ F := fun h => F.dual.mem_of_le h

/-- The smallest filter containing a given element. -/
def principal (p : P) : Pfilter P :=
  ⟨Ideal.principal p⟩

instance [Inhabited P] : Inhabited (Pfilter P) :=
  ⟨⟨default⟩⟩

/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
theorem ext : ∀ F G : Pfilter P, (F : Set P) = G → F = G
  | ⟨⟨_, _, _, _⟩⟩, ⟨⟨_, _, _, _⟩⟩, rfl => rfl

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
instance : PartialOrderₓ (Pfilter P) :=
  PartialOrderₓ.lift coe ext

@[trans]
theorem mem_of_mem_of_le {F G : Pfilter P} : x ∈ F → F ≤ G → x ∈ G :=
  ideal.mem_of_mem_of_le

@[simp]
theorem principal_le_iff {F : Pfilter P} : principal x ≤ F ↔ x ∈ F :=
  ideal.principal_le_iff

end Preorderₓ

section OrderTop

variable [Preorderₓ P] [OrderTop P] {F : Pfilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp]
theorem top_mem : ⊤ ∈ F :=
  ideal.bot_mem

/-- There is a bottom filter when `P` has a top element. -/
instance : OrderBot (Pfilter P) where
  bot := ⟨⊥⟩
  bot_le := fun F => (bot_le : ⊥ ≤ F.dual)

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [Preorderₓ P] [OrderBot P] : OrderTop (Pfilter P) where
  top := ⟨⊤⟩
  le_top := fun F => (le_top : F.dual ≤ ⊤)

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {F : Pfilter P}

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (x y «expr ∈ » F)
/-- A specific witness of `pfilter.directed` when `P` has meets. -/
theorem inf_mem x y (_ : x ∈ F) (_ : y ∈ F) : x⊓y ∈ F :=
  Ideal.sup_mem x ‹x ∈ F› y ‹y ∈ F›

@[simp]
theorem inf_mem_iff : x⊓y ∈ F ↔ x ∈ F ∧ y ∈ F :=
  ideal.sup_mem_iff

end SemilatticeInf

end Pfilter

end Order

