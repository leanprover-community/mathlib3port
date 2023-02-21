/-
Copyright (c) 2022 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies

! This file was ported from Lean 3 source module combinatorics.set_family.lym
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Combinatorics.DoubleCounting
import Mathbin.Combinatorics.SetFamily.Shadow
import Mathbin.Data.Rat.Order

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `finset.card_div_choose_le_card_shadow_div_choose`: Local Lubell-Yamamoto-Meshalkin inequality.
  The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜` does.
* `finset.sum_card_slice_div_choose_le_one`: Lubell-Yamamoto-Meshalkin inequality. The sum of
  densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `is_antichain.sperner`: Sperner's theorem. The size of any antichain in `finset α` is at most the
  size of the maximal layer of `finset α`. It is a corollary of `sum_card_slice_div_choose_le_one`.

## TODO

Prove upward local LYM.

Provide equality cases. Local LYM gives that the equality case of LYM and Sperner is precisely when
`𝒜` is a middle layer.

`falling` could be useful more generally in grade orders.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/


open Finset Nat

open BigOperators FinsetFamily

variable {𝕜 α : Type _} [LinearOrderedField 𝕜]

namespace Finset

/-! ### Local LYM inequality -/


section LocalLym

variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {r : ℕ}

#print Finset.card_mul_le_card_shadow_mul /-
/-- The downward **local LYM inequality**, with cancelled denominators. `𝒜` takes up less of `α^(r)`
(the finsets of card `r`) than `∂𝒜` takes up of `α^(r - 1)`. -/
theorem card_mul_le_card_shadow_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    𝒜.card * r ≤ ((∂ ) 𝒜).card * (Fintype.card α - r + 1) :=
  by
  refine' card_mul_le_card_mul' (· ⊆ ·) (fun s hs => _) fun s hs => _
  · rw [← h𝒜 hs, ← card_image_of_inj_on s.erase_inj_on]
    refine' card_le_of_subset _
    simp_rw [image_subset_iff, mem_bipartite_below]
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
  refine' le_trans _ tsub_tsub_le_tsub_add
  rw [← h𝒜.shadow hs, ← card_compl, ← card_image_of_inj_on (insert_inj_on' _)]
  refine' card_le_of_subset fun t ht => _
  infer_instance
  rw [mem_bipartite_above] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe, h𝒜.empty_mem_iff, coe_eq_singleton]
    rintro rfl
    rwa [shadow_singleton_empty] at hs
  obtain ⟨a, ha, rfl⟩ :=
    exists_eq_insert_iff.2 ⟨ht.2, by rw [(sized_shadow_iff this).1 h𝒜.shadow ht.1, h𝒜.shadow hs]⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)
#align finset.card_mul_le_card_shadow_mul Finset.card_mul_le_card_shadow_mul
-/

/- warning: finset.card_div_choose_le_card_shadow_div_choose -> Finset.card_div_choose_le_card_shadow_div_choose is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Fintype.{u2} α] {𝒜 : Finset.{u2} (Finset.{u2} α)} {r : Nat}, (Ne.{1} Nat r (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Set.Sized.{u2} α r ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (Finset.Set.hasCoeT.{u2} (Finset.{u2} α)))) 𝒜)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} (Finset.{u2} α) 𝒜)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Nat.choose (Fintype.card.{u2} α _inst_3) r))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} (Finset.{u2} α) (Finset.shadow.{u2} α (fun (a : α) (b : α) => _inst_2 a b) 𝒜))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Nat.choose (Fintype.card.{u2} α _inst_3) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) r (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Fintype.{u2} α] {𝒜 : Finset.{u2} (Finset.{u2} α)} {r : Nat}, (Ne.{1} Nat r (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Set.Sized.{u2} α r (Finset.toSet.{u2} (Finset.{u2} α) 𝒜)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} (Finset.{u2} α) 𝒜)) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Nat.choose (Fintype.card.{u2} α _inst_3) r))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} (Finset.{u2} α) (Finset.shadow.{u2} α (fun (a : α) (b : α) => _inst_2 a b) 𝒜))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Nat.choose (Fintype.card.{u2} α _inst_3) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) r (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align finset.card_div_choose_le_card_shadow_div_choose Finset.card_div_choose_le_card_shadow_div_chooseₓ'. -/
/-- The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` (the finsets of card `r`)
than `∂𝒜` takes up of `α^(r - 1)`. -/
theorem card_div_choose_le_card_shadow_div_choose (hr : r ≠ 0) (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (𝒜.card : 𝕜) / (Fintype.card α).choose r ≤ ((∂ ) 𝒜).card / (Fintype.card α).choose (r - 1) :=
  by
  obtain hr' | hr' := lt_or_le (Fintype.card α) r
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  replace h𝒜 := card_mul_le_card_shadow_mul h𝒜
  rw [div_le_div_iff] <;> norm_cast
  · cases r
    · exact (hr rfl).elim
    rw [Nat.succ_eq_add_one] at *
    rw [tsub_add_eq_add_tsub hr', add_tsub_add_eq_tsub_right] at h𝒜
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    · simp [mul_assoc, Nat.choose_succ_right_eq]
      exact Or.inl (mul_comm _ _)
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
  · exact Nat.choose_pos hr'
  · exact Nat.choose_pos (r.pred_le.trans hr')
#align finset.card_div_choose_le_card_shadow_div_choose Finset.card_div_choose_le_card_shadow_div_choose

end LocalLym

/-! ### LYM inequality -/


section Lym

section Falling

variable [DecidableEq α] (k : ℕ) (𝒜 : Finset (Finset α))

#print Finset.falling /-
/-- `falling k 𝒜` is all the finsets of cardinality `k` which are a subset of something in `𝒜`. -/
def falling : Finset (Finset α) :=
  𝒜.sup <| powersetLen k
#align finset.falling Finset.falling
-/

variable {𝒜 k} {s : Finset α}

/- warning: finset.mem_falling -> Finset.mem_falling is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] {k : Nat} {𝒜 : Finset.{u1} (Finset.{u1} α)} {s : Finset.{u1} α}, Iff (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) s (Finset.falling.{u1} α (fun (a : α) (b : α) => _inst_2 a b) k 𝒜)) (And (Exists.{succ u1} (Finset.{u1} α) (fun (t : Finset.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) t 𝒜) (fun (H : Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) t 𝒜) => HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t))) (Eq.{1} Nat (Finset.card.{u1} α s) k))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] {k : Nat} {𝒜 : Finset.{u1} (Finset.{u1} α)} {s : Finset.{u1} α}, Iff (Membership.mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.instMembershipFinset.{u1} (Finset.{u1} α)) s (Finset.falling.{u1} α (fun (a : α) (b : α) => _inst_2 a b) k 𝒜)) (And (Exists.{succ u1} (Finset.{u1} α) (fun (t : Finset.{u1} α) => And (Membership.mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.instMembershipFinset.{u1} (Finset.{u1} α)) t 𝒜) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t))) (Eq.{1} Nat (Finset.card.{u1} α s) k))
Case conversion may be inaccurate. Consider using '#align finset.mem_falling Finset.mem_fallingₓ'. -/
theorem mem_falling : s ∈ falling k 𝒜 ↔ (∃ t ∈ 𝒜, s ⊆ t) ∧ s.card = k := by
  simp_rw [falling, mem_sup, mem_powerset_len, exists_and_right]
#align finset.mem_falling Finset.mem_falling

variable (𝒜 k)

#print Finset.sized_falling /-
theorem sized_falling : (falling k 𝒜 : Set (Finset α)).Sized k := fun s hs => (mem_falling.1 hs).2
#align finset.sized_falling Finset.sized_falling
-/

#print Finset.slice_subset_falling /-
theorem slice_subset_falling : 𝒜 # k ⊆ falling k 𝒜 := fun s hs =>
  mem_falling.2 <| (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩
#align finset.slice_subset_falling Finset.slice_subset_falling
-/

#print Finset.falling_zero_subset /-
theorem falling_zero_subset : falling 0 𝒜 ⊆ {∅} :=
  subset_singleton_iff'.2 fun t ht => card_eq_zero.1 <| sized_falling _ _ ht
#align finset.falling_zero_subset Finset.falling_zero_subset
-/

#print Finset.slice_union_shadow_falling_succ /-
theorem slice_union_shadow_falling_succ : 𝒜 # k ∪ (∂ ) (falling (k + 1) 𝒜) = falling k 𝒜 :=
  by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, exists_prop, mem_falling]
  constructor
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    · exact ⟨⟨s, h.1, subset.refl _⟩, h.2⟩
    refine' ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, _⟩
    rw [card_erase_of_mem ha, hs]
    rfl
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    by_cases s ∈ 𝒜
    · exact Or.inl ⟨h, hs⟩
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_not_mem h).symm)
    refine' Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, _⟩, a, mem_insert_self _ _, erase_insert ha⟩
    rw [card_insert_of_not_mem ha, hs]
#align finset.slice_union_shadow_falling_succ Finset.slice_union_shadow_falling_succ
-/

variable {𝒜 k}

/-- The shadow of `falling m 𝒜` is disjoint from the `n`-sized elements of `𝒜`, thanks to the
antichain property. -/
theorem IsAntichain.disjoint_slice_shadow_falling {m n : ℕ}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) : Disjoint (𝒜 # m) ((∂ ) (falling n 𝒜)) :=
  disjoint_right.2 fun s h₁ h₂ =>
    by
    simp_rw [mem_shadow_iff, exists_prop, mem_falling] at h₁
    obtain ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩ := h₁
    refine' h𝒜 (slice_subset h₂) ht _ ((erase_subset _ _).trans hst)
    rintro rfl
    exact not_mem_erase _ _ (hst ha)
#align is_antichain.disjoint_slice_shadow_falling IsAntichain.disjoint_slice_shadow_falling

/- warning: finset.le_card_falling_div_choose -> Finset.le_card_falling_div_choose is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] {k : Nat} {𝒜 : Finset.{u2} (Finset.{u2} α)} [_inst_3 : Fintype.{u2} α], (LE.le.{0} Nat Nat.hasLe k (Fintype.card.{u2} α _inst_3)) -> (IsAntichain.{u2} (Finset.{u2} α) (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.hasSubset.{u2} α)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (Finset.Set.hasCoeT.{u2} (Finset.{u2} α)))) 𝒜)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (Finset.sum.{u1, 0} 𝕜 Nat (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (OrderedAddCommGroup.toAddCommGroup.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (r : Nat) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} (Finset.{u2} α) (Finset.slice.{u2} α 𝒜 (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Fintype.card.{u2} α _inst_3) r)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Nat.choose (Fintype.card.{u2} α _inst_3) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Fintype.card.{u2} α _inst_3) r))))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} (Finset.{u2} α) (Finset.falling.{u2} α (fun (a : α) (b : α) => _inst_2 a b) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Fintype.card.{u2} α _inst_3) k) 𝒜))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Nat.choose (Fintype.card.{u2} α _inst_3) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Fintype.card.{u2} α _inst_3) k)))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] {k : Nat} {𝒜 : Finset.{u2} (Finset.{u2} α)} [_inst_3 : Fintype.{u2} α], (LE.le.{0} Nat instLENat k (Fintype.card.{u2} α _inst_3)) -> (IsAntichain.{u2} (Finset.{u2} α) (fun (x._@.Mathlib.Combinatorics.SetFamily.LYM._hyg.1705 : Finset.{u2} α) (x._@.Mathlib.Combinatorics.SetFamily.LYM._hyg.1707 : Finset.{u2} α) => HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) x._@.Mathlib.Combinatorics.SetFamily.LYM._hyg.1705 x._@.Mathlib.Combinatorics.SetFamily.LYM._hyg.1707) (Finset.toSet.{u2} (Finset.{u2} α) 𝒜)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (Finset.sum.{u1, 0} 𝕜 Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (r : Nat) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} (Finset.{u2} α) (Finset.slice.{u2} α 𝒜 (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fintype.card.{u2} α _inst_3) r)))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Nat.choose (Fintype.card.{u2} α _inst_3) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fintype.card.{u2} α _inst_3) r))))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} (Finset.{u2} α) (Finset.falling.{u2} α (fun (a : α) (b : α) => _inst_2 a b) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fintype.card.{u2} α _inst_3) k) 𝒜))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Nat.choose (Fintype.card.{u2} α _inst_3) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fintype.card.{u2} α _inst_3) k)))))
Case conversion may be inaccurate. Consider using '#align finset.le_card_falling_div_choose Finset.le_card_falling_div_chooseₓ'. -/
/-- A bound on any top part of the sum in LYM in terms of the size of `falling k 𝒜`. -/
theorem le_card_falling_div_choose [Fintype α] (hk : k ≤ Fintype.card α)
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r in range (k + 1),
        ((𝒜 # (Fintype.card α - r)).card : 𝕜) / (Fintype.card α).choose (Fintype.card α - r)) ≤
      (falling (Fintype.card α - k) 𝒜).card / (Fintype.card α).choose (Fintype.card α - k) :=
  by
  induction' k with k ih
  · simp only [tsub_zero, cast_one, cast_le, sum_singleton, div_one, choose_self, range_one]
    exact card_le_of_subset (slice_subset_falling _ _)
  rw [succ_eq_add_one] at *
  rw [sum_range_succ, ← slice_union_shadow_falling_succ,
    card_disjoint_union h𝒜.disjoint_slice_shadow_falling, cast_add, _root_.add_div, add_comm]
  rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
  exact
    add_le_add_left
      ((ih <| le_of_succ_le hk).trans <|
        card_div_choose_le_card_shadow_div_choose (tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' <|
          sized_falling _ _)
      _
#align finset.le_card_falling_div_choose Finset.le_card_falling_div_choose

end Falling

variable {𝒜 : Finset (Finset α)} {s : Finset α} {k : ℕ}

/- warning: finset.sum_card_slice_div_choose_le_one -> Finset.sum_card_slice_div_choose_le_one is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {𝒜 : Finset.{u2} (Finset.{u2} α)} [_inst_2 : Fintype.{u2} α], (IsAntichain.{u2} (Finset.{u2} α) (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.hasSubset.{u2} α)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (Finset.Set.hasCoeT.{u2} (Finset.{u2} α)))) 𝒜)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (Finset.sum.{u1, 0} 𝕜 Nat (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (OrderedAddCommGroup.toAddCommGroup.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Fintype.card.{u2} α _inst_2) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (r : Nat) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} (Finset.{u2} α) (Finset.slice.{u2} α 𝒜 r))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Nat.choose (Fintype.card.{u2} α _inst_2) r)))) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {𝒜 : Finset.{u2} (Finset.{u2} α)} [_inst_2 : Fintype.{u2} α], (IsAntichain.{u2} (Finset.{u2} α) (fun (x._@.Mathlib.Combinatorics.SetFamily.LYM._hyg.2008 : Finset.{u2} α) (x._@.Mathlib.Combinatorics.SetFamily.LYM._hyg.2010 : Finset.{u2} α) => HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) x._@.Mathlib.Combinatorics.SetFamily.LYM._hyg.2008 x._@.Mathlib.Combinatorics.SetFamily.LYM._hyg.2010) (Finset.toSet.{u2} (Finset.{u2} α) 𝒜)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (Finset.sum.{u1, 0} 𝕜 Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fintype.card.{u2} α _inst_2) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (r : Nat) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} (Finset.{u2} α) (Finset.slice.{u2} α 𝒜 r))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Nat.choose (Fintype.card.{u2} α _inst_2) r)))) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (NonAssocRing.toOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align finset.sum_card_slice_div_choose_le_one Finset.sum_card_slice_div_choose_le_oneₓ'. -/
/-- The **Lubell-Yamamoto-Meshalkin inequality**. If `𝒜` is an antichain, then the sum of the
proportion of elements it takes from each layer is less than `1`. -/
theorem sum_card_slice_div_choose_le_one [Fintype α]
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r in range (Fintype.card α + 1), ((𝒜 # r).card : 𝕜) / (Fintype.card α).choose r) ≤ 1 := by
  classical
    rw [← sum_flip]
    refine' (le_card_falling_div_choose le_rfl h𝒜).trans _
    rw [div_le_iff] <;> norm_cast
    ·
      simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        (sized_falling 0 𝒜).card_le
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one
#align finset.sum_card_slice_div_choose_le_one Finset.sum_card_slice_div_choose_le_one

end Lym

/-! ### Sperner's theorem -/


/-- **Sperner's theorem**. The size of an antichain in `finset α` is bounded by the size of the
maximal layer in `finset α`. This precisely means that `finset α` is a Sperner order. -/
theorem IsAntichain.sperner [Fintype α] {𝒜 : Finset (Finset α)}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  classical
    suffices
      (∑ r in Iic (Fintype.card α),
          ((𝒜 # r).card : ℚ) / (Fintype.card α).choose (Fintype.card α / 2)) ≤
        1
      by
      rwa [← sum_div, ← Nat.cast_sum, div_le_one, cast_le, sum_card_slice] at this
      norm_cast
      exact choose_pos (Nat.div_le_self _ _)
    rw [Iic_eq_Icc, ← Ico_succ_right, bot_eq_zero, Ico_zero_eq_range]
    refine' (sum_le_sum fun r hr => _).trans (sum_card_slice_div_choose_le_one h𝒜)
    rw [mem_range] at hr
    refine' div_le_div_of_le_left _ _ _ <;> norm_cast
    · exact Nat.zero_le _
    · exact choose_pos (lt_succ_iff.1 hr)
    · exact choose_le_middle _ _
#align is_antichain.sperner IsAntichain.sperner

end Finset

