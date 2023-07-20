/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
import Mathbin.Order.Ideal

#align_import order.pfilter from "leanprover-community/mathlib"@"23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6"

/-!
# Order filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections
require more structure, such as a bottom element, a top element, or
a join-semilattice structure.

- `order.pfilter P`: The type of nonempty, downward directed, upward closed
               subsets of `P`. This is dual to `order.ideal`, so it
               simply wraps `order.ideal Pᵒᵈ`.
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

#print Order.PFilter /-
/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
structure PFilter (P) [Preorder P] where
  dual : Ideal Pᵒᵈ
#align order.pfilter Order.PFilter
-/

#print Order.IsPFilter /-
/-- A predicate for when a subset of `P` is a filter. -/
def IsPFilter [Preorder P] (F : Set P) : Prop :=
  @IsIdeal Pᵒᵈ _ F
#align order.is_pfilter Order.IsPFilter
-/

#print Order.IsPFilter.of_def /-
theorem IsPFilter.of_def [Preorder P] {F : Set P} (nonempty : F.Nonempty)
    (directed : DirectedOn (· ≥ ·) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) :
    IsPFilter F :=
  ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, Nonempty, Directed⟩
#align order.is_pfilter.of_def Order.IsPFilter.of_def
-/

#print Order.IsPFilter.toPFilter /-
/-- Create an element of type `order.pfilter` from a set satisfying the predicate
`order.is_pfilter`. -/
def IsPFilter.toPFilter [Preorder P] {F : Set P} (h : IsPFilter F) : PFilter P :=
  ⟨h.toIdeal⟩
#align order.is_pfilter.to_pfilter Order.IsPFilter.toPFilter
-/

namespace Pfilter

section Preorder

variable [Preorder P] {x y : P} (F s t : PFilter P)

instance [Inhabited P] : Inhabited (PFilter P) :=
  ⟨⟨default⟩⟩

/-- A filter on `P` is a subset of `P`. -/
instance : Coe (PFilter P) (Set P) :=
  ⟨fun F => F.dual.carrier⟩

/-- For the notation `x ∈ F`. -/
instance : Membership P (PFilter P) :=
  ⟨fun x F => x ∈ (F : Set P)⟩

@[simp]
theorem SetLike.mem_coe : x ∈ (F : Set P) ↔ x ∈ F :=
  iff_of_eq rfl
#align order.pfilter.mem_coe SetLike.mem_coeₓ

#print Order.PFilter.isPFilter /-
theorem isPFilter : IsPFilter (F : Set P) :=
  F.dual.IsIdeal
#align order.pfilter.is_pfilter Order.PFilter.isPFilter
-/

#print Order.PFilter.nonempty /-
theorem nonempty : (F : Set P).Nonempty :=
  F.dual.Nonempty
#align order.pfilter.nonempty Order.PFilter.nonempty
-/

#print Order.PFilter.directed /-
theorem directed : DirectedOn (· ≥ ·) (F : Set P) :=
  F.dual.Directed
#align order.pfilter.directed Order.PFilter.directed
-/

#print Order.PFilter.mem_of_le /-
theorem mem_of_le {F : PFilter P} : x ≤ y → x ∈ F → y ∈ F := fun h => F.dual.lower h
#align order.pfilter.mem_of_le Order.PFilter.mem_of_le
-/

#print Order.PFilter.ext /-
/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
theorem ext (h : (s : Set P) = t) : s = t := by cases s; cases t; exact congr_arg _ (Ideal.ext h)
#align order.pfilter.ext Order.PFilter.ext
-/

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
instance : PartialOrder (PFilter P) :=
  PartialOrder.lift coe ext

#print Order.PFilter.mem_of_mem_of_le /-
@[trans]
theorem mem_of_mem_of_le {F G : PFilter P} : x ∈ F → F ≤ G → x ∈ G :=
  Ideal.mem_of_mem_of_le
#align order.pfilter.mem_of_mem_of_le Order.PFilter.mem_of_mem_of_le
-/

#print Order.PFilter.principal /-
/-- The smallest filter containing a given element. -/
def principal (p : P) : PFilter P :=
  ⟨Ideal.principal p⟩
#align order.pfilter.principal Order.PFilter.principal
-/

#print Order.PFilter.mem_mk /-
@[simp]
theorem mem_mk (x : P) (I : Ideal Pᵒᵈ) : x ∈ (⟨I⟩ : PFilter P) ↔ OrderDual.toDual x ∈ I :=
  Iff.rfl
#align order.pfilter.mem_def Order.PFilter.mem_mk
-/

#print Order.PFilter.principal_le_iff /-
@[simp]
theorem principal_le_iff {F : PFilter P} : principal x ≤ F ↔ x ∈ F :=
  Ideal.principal_le_iff
#align order.pfilter.principal_le_iff Order.PFilter.principal_le_iff
-/

#print Order.PFilter.mem_principal /-
@[simp]
theorem mem_principal : x ∈ principal y ↔ y ≤ x :=
  Ideal.mem_principal
#align order.pfilter.mem_principal Order.PFilter.mem_principal
-/

#print Order.PFilter.antitone_principal /-
-- defeq abuse
theorem antitone_principal : Antitone (principal : P → PFilter P) := by delta Antitone <;> simp
#align order.pfilter.antitone_principal Order.PFilter.antitone_principal
-/

#print Order.PFilter.principal_le_principal_iff /-
theorem principal_le_principal_iff {p q : P} : principal q ≤ principal p ↔ p ≤ q := by simp
#align order.pfilter.principal_le_principal_iff Order.PFilter.principal_le_principal_iff
-/

end Preorder

section OrderTop

variable [Preorder P] [OrderTop P] {F : PFilter P}

#print Order.PFilter.top_mem /-
/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp]
theorem top_mem : ⊤ ∈ F :=
  Ideal.bot_mem _
#align order.pfilter.top_mem Order.PFilter.top_mem
-/

/-- There is a bottom filter when `P` has a top element. -/
instance : OrderBot (PFilter P) where
  bot := ⟨⊥⟩
  bot_le F := (bot_le : ⊥ ≤ F.dual)

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [Preorder P] [OrderBot P] : OrderTop (PFilter P)
    where
  top := ⟨⊤⟩
  le_top F := (le_top : F.dual ≤ ⊤)

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {F : PFilter P}

#print Order.PFilter.inf_mem /-
/-- A specific witness of `pfilter.directed` when `P` has meets. -/
theorem inf_mem (hx : x ∈ F) (hy : y ∈ F) : x ⊓ y ∈ F :=
  Ideal.sup_mem hx hy
#align order.pfilter.inf_mem Order.PFilter.inf_mem
-/

#print Order.PFilter.inf_mem_iff /-
@[simp]
theorem inf_mem_iff : x ⊓ y ∈ F ↔ x ∈ F ∧ y ∈ F :=
  Ideal.sup_mem_iff
#align order.pfilter.inf_mem_iff Order.PFilter.inf_mem_iff
-/

end SemilatticeInf

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf P] {F : PFilter P}

#print Order.PFilter.sInf_gc /-
theorem sInf_gc :
    GaloisConnection (fun x => OrderDual.toDual (principal x)) fun F =>
      sInf (OrderDual.ofDual F : PFilter P) :=
  fun x F => by simp; rfl
#align order.pfilter.Inf_gc Order.PFilter.sInf_gc
-/

#print Order.PFilter.infGi /-
/-- If a poset `P` admits arbitrary `Inf`s, then `principal` and `Inf` form a Galois coinsertion. -/
def infGi :
    GaloisCoinsertion (fun x => OrderDual.toDual (principal x)) fun F =>
      sInf (OrderDual.ofDual F : PFilter P)
    where
  choice F _ := sInf (id F : PFilter P)
  gc := sInf_gc
  u_l_le s := sInf_le <| mem_principal.2 <| le_refl s
  choice_eq _ _ := rfl
#align order.pfilter.Inf_gi Order.PFilter.infGi
-/

end CompleteSemilatticeInf

end Pfilter

end Order

