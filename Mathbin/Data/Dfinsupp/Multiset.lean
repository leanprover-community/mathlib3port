/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.dfinsupp.multiset
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Dfinsupp.Order

/-!
# Equivalence between `multiset` and `ℕ`-valued finitely supported functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `dfinsupp.to_multiset` the equivalence between `Π₀ a : α, ℕ` and `multiset α`, along
with `multiset.to_dfinsupp` the reverse equivalence.

Note that this provides a computable alternative to `finsupp.to_multiset`.
-/


variable {α : Type _} {β : α → Type _}

namespace DFinsupp

#print DFinsupp.addZeroClass' /-
/-- Non-dependent special case of `dfinsupp.add_zero_class` to help typeclass search. -/
instance addZeroClass' {β} [AddZeroClass β] : AddZeroClass (Π₀ a : α, β) :=
  @DFinsupp.addZeroClass α (fun _ => β) _
#align dfinsupp.add_zero_class' DFinsupp.addZeroClass'
-/

variable [DecidableEq α]

#print DFinsupp.toMultiset /-
/-- A computable version of `finsupp.to_multiset`. -/
def toMultiset : (Π₀ a : α, ℕ) →+ Multiset α :=
  DFinsupp.sumAddHom fun a : α => Multiset.replicateAddMonoidHom a
#align dfinsupp.to_multiset DFinsupp.toMultiset
-/

#print DFinsupp.toMultiset_single /-
@[simp]
theorem toMultiset_single (a : α) (n : ℕ) :
    toMultiset (DFinsupp.single a n) = Multiset.replicate n a :=
  DFinsupp.sumAddHom_single _ _ _
#align dfinsupp.to_multiset_single DFinsupp.toMultiset_single
-/

end DFinsupp

namespace Multiset

variable [DecidableEq α]

#print Multiset.toDFinsupp /-
/-- A computable version of `multiset.to_finsupp` -/
def toDFinsupp : Multiset α →+ Π₀ a : α, ℕ
    where
  toFun s :=
    { toFun := fun n => s.count n
      support' := Trunc.mk ⟨s, fun i => (em (i ∈ s)).imp_right Multiset.count_eq_zero_of_not_mem⟩ }
  map_zero' := rfl
  map_add' s t := DFinsupp.ext fun _ => Multiset.count_add _ _ _
#align multiset.to_dfinsupp Multiset.toDFinsupp
-/

#print Multiset.toDFinsupp_apply /-
@[simp]
theorem toDFinsupp_apply (s : Multiset α) (a : α) : s.toDFinsupp a = s.count a :=
  rfl
#align multiset.to_dfinsupp_apply Multiset.toDFinsupp_apply
-/

#print Multiset.toDFinsupp_support /-
@[simp]
theorem toDFinsupp_support (s : Multiset α) : s.toDFinsupp.support = s.toFinset :=
  (Finset.filter_eq_self _).mpr fun x hx => count_ne_zero.mpr <| Multiset.mem_toFinset.1 hx
#align multiset.to_dfinsupp_support Multiset.toDFinsupp_support
-/

#print Multiset.toDFinsupp_replicate /-
@[simp]
theorem toDFinsupp_replicate (a : α) (n : ℕ) :
    toDFinsupp (Multiset.replicate n a) = DFinsupp.single a n :=
  by
  ext i
  dsimp [to_dfinsupp]
  simp [count_replicate, eq_comm]
#align multiset.to_dfinsupp_replicate Multiset.toDFinsupp_replicate
-/

#print Multiset.toDFinsupp_singleton /-
@[simp]
theorem toDFinsupp_singleton (a : α) : toDFinsupp {a} = DFinsupp.single a 1 := by
  rw [← replicate_one, to_dfinsupp_replicate]
#align multiset.to_dfinsupp_singleton Multiset.toDFinsupp_singleton
-/

#print Multiset.equivDFinsupp /-
/-- `multiset.to_dfinsupp` as an `add_equiv`. -/
@[simps apply symm_apply]
def equivDFinsupp : Multiset α ≃+ Π₀ a : α, ℕ :=
  AddMonoidHom.toAddEquiv Multiset.toDFinsupp DFinsupp.toMultiset (by ext x : 1; simp)
    (by refine' @DFinsupp.addHom_ext α (fun _ => ℕ) _ _ _ _ _ _ fun i hi => _; simp)
#align multiset.equiv_dfinsupp Multiset.equivDFinsupp
-/

#print Multiset.toDFinsupp_toMultiset /-
@[simp]
theorem toDFinsupp_toMultiset (s : Multiset α) : s.toDFinsupp.toMultiset = s :=
  equivDFinsupp.symm_apply_apply s
#align multiset.to_dfinsupp_to_multiset Multiset.toDFinsupp_toMultiset
-/

#print Multiset.toDFinsupp_le_toDFinsupp /-
@[simp]
theorem toDFinsupp_le_toDFinsupp (s t : Multiset α) : toDFinsupp s ≤ toDFinsupp t ↔ s ≤ t := by
  simp [Multiset.le_iff_count, DFinsupp.le_def]
#align multiset.to_dfinsupp_le_to_dfinsupp Multiset.toDFinsupp_le_toDFinsupp
-/

end Multiset

#print DFinsupp.toMultiset_toDFinsupp /-
@[simp]
theorem DFinsupp.toMultiset_toDFinsupp [DecidableEq α] (f : Π₀ a : α, ℕ) :
    f.toMultiset.toDFinsupp = f :=
  Multiset.equivDFinsupp.apply_symm_apply f
#align dfinsupp.to_multiset_to_dfinsupp DFinsupp.toMultiset_toDFinsupp
-/

