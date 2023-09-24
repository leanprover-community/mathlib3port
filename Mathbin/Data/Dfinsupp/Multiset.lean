/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Data.Dfinsupp.Order

#align_import data.dfinsupp.multiset from "leanprover-community/mathlib"@"442a83d738cb208d3600056c489be16900ba701d"

/-!
# Equivalence between `multiset` and `ℕ`-valued finitely supported functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `dfinsupp.to_multiset` the equivalence between `Π₀ a : α, ℕ` and `multiset α`, along
with `multiset.to_dfinsupp` the reverse equivalence.

Note that this provides a computable alternative to `finsupp.to_multiset`.
-/


open Function

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

variable [DecidableEq α] {s t : Multiset α}

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
  Finset.filter_true_of_mem fun x hx => count_ne_zero.mpr <| Multiset.mem_toFinset.1 hx
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

#print Multiset.toDFinsupp_injective /-
theorem toDFinsupp_injective : Injective (toDFinsupp : Multiset α → Π₀ a, ℕ) :=
  equivDFinsupp.Injective
#align multiset.to_dfinsupp_injective Multiset.toDFinsupp_injective
-/

#print Multiset.toDFinsupp_inj /-
@[simp]
theorem toDFinsupp_inj : toDFinsupp s = toDFinsupp t ↔ s = t :=
  toDFinsupp_injective.eq_iff
#align multiset.to_dfinsupp_inj Multiset.toDFinsupp_inj
-/

#print Multiset.toDFinsupp_le_toDFinsupp /-
@[simp]
theorem toDFinsupp_le_toDFinsupp : toDFinsupp s ≤ toDFinsupp t ↔ s ≤ t := by
  simp [Multiset.le_iff_count, DFinsupp.le_def]
#align multiset.to_dfinsupp_le_to_dfinsupp Multiset.toDFinsupp_le_toDFinsupp
-/

#print Multiset.toDFinsupp_lt_toDFinsupp /-
@[simp]
theorem toDFinsupp_lt_toDFinsupp : toDFinsupp s < toDFinsupp t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' toDFinsupp_le_toDFinsupp toDFinsupp_le_toDFinsupp
#align multiset.to_dfinsupp_lt_to_dfinsupp Multiset.toDFinsupp_lt_toDFinsupp
-/

#print Multiset.toDFinsupp_inter /-
@[simp]
theorem toDFinsupp_inter (s t : Multiset α) : toDFinsupp (s ∩ t) = s.toDFinsupp ⊓ t.toDFinsupp := by
  ext i; simp [inf_eq_min]
#align multiset.to_dfinsupp_inter Multiset.toDFinsupp_inter
-/

#print Multiset.toDFinsupp_union /-
@[simp]
theorem toDFinsupp_union (s t : Multiset α) : toDFinsupp (s ∪ t) = s.toDFinsupp ⊔ t.toDFinsupp := by
  ext i; simp [sup_eq_max]
#align multiset.to_dfinsupp_union Multiset.toDFinsupp_union
-/

end Multiset

namespace DFinsupp

variable [DecidableEq α] {f g : Π₀ a : α, ℕ}

#print DFinsupp.toMultiset_toDFinsupp /-
@[simp]
theorem toMultiset_toDFinsupp : f.toMultiset.toDFinsupp = f :=
  Multiset.equivDFinsupp.apply_symm_apply f
#align dfinsupp.to_multiset_to_dfinsupp DFinsupp.toMultiset_toDFinsupp
-/

#print DFinsupp.toMultiset_injective /-
theorem toMultiset_injective : Injective (toMultiset : (Π₀ a, ℕ) → Multiset α) :=
  Multiset.equivDFinsupp.symm.Injective
#align dfinsupp.to_multiset_injective DFinsupp.toMultiset_injective
-/

#print DFinsupp.toMultiset_inj /-
@[simp]
theorem toMultiset_inj : toMultiset f = toMultiset g ↔ f = g :=
  toMultiset_injective.eq_iff
#align dfinsupp.to_multiset_inj DFinsupp.toMultiset_inj
-/

#print DFinsupp.toMultiset_le_toMultiset /-
@[simp]
theorem toMultiset_le_toMultiset : toMultiset f ≤ toMultiset g ↔ f ≤ g := by
  simp_rw [← Multiset.toDFinsupp_le_toDFinsupp, to_multiset_to_dfinsupp]
#align dfinsupp.to_multiset_le_to_multiset DFinsupp.toMultiset_le_toMultiset
-/

#print DFinsupp.toMultiset_lt_toMultiset /-
@[simp]
theorem toMultiset_lt_toMultiset : toMultiset f < toMultiset g ↔ f < g := by
  simp_rw [← Multiset.toDFinsupp_lt_toDFinsupp, to_multiset_to_dfinsupp]
#align dfinsupp.to_multiset_lt_to_multiset DFinsupp.toMultiset_lt_toMultiset
-/

variable (f g)

#print DFinsupp.toMultiset_inf /-
@[simp]
theorem toMultiset_inf : toMultiset (f ⊓ g) = f.toMultiset ∩ g.toMultiset :=
  Multiset.toDFinsupp_injective <| by simp
#align dfinsupp.to_multiset_inf DFinsupp.toMultiset_inf
-/

#print DFinsupp.toMultiset_sup /-
@[simp]
theorem toMultiset_sup : toMultiset (f ⊔ g) = f.toMultiset ∪ g.toMultiset :=
  Multiset.toDFinsupp_injective <| by simp
#align dfinsupp.to_multiset_sup DFinsupp.toMultiset_sup
-/

end DFinsupp

